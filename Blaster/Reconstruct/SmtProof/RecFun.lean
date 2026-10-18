import Lean
import Blaster.Reconstruct.SmtProof.Z3
import Blaster.Reconstruct.SmtProof.Replay

/-!
# Recursive functions (Z3)

Blaster translates a recursive function `f` to a declaration `(declare-fun F (S⃗) T)`, the macro
`(define-fun F_LRec ((x S)⃗) T body[F])` and the axiom `(assert (forall ((x S)⃗) (= (F x⃗) (F_LRec x⃗))))`,
which Z3's `recfun-finder` simplifier turns into a recursive function definition. The simplifier does nothing
when proofs are produced: Z3 then reasons on the axioms by quantifier instantiation, which may not terminate
in practice (e.g., on the CEK evaluation of validators). This module:
 1. rewrites such queries at the SMT-LIB level, as `recfun-finder` does (`rewriteQuery`): the functions are
    defined by a `define-funs-rec` block;
 2. extends the interpretation (`addProofDefs`) with the auxiliary functions defined in the header of Z3's
    proofs (`fold-rec-n`, which name subterms of the bodies, interpreted as macros), and with the case
    predicates `((_ case-def k f) a⃗)` of the recursive functions (see `interpCaseDef`);
 3. replays the lemmas of Z3's theory of recursive functions (`th-lemma recfun`) with exact proofs
    (`proveLemma`): unfoldings `¬ g₁ ∨ ... ∨ ¬ gₙ ∨ f a⃗ = r` of a function in the case of the guards `gᵢ` are
    proved by instantiating the definitional equation `∀ x⃗, f x⃗ = body` (proved once, with the bridge tactics)
    and reducing the conditionals of the body with the guards; lemmas on case predicates are propositional.
-/

open Lean Meta Elab Term

namespace Blaster.Reconstruct.SmtProof.RecFun

/-! ## Query transformation -/

/-- Head symbol and arguments of a command or an application `(h args)`. -/
def headArgs? (e : SExpr) : Option (String × Array SExpr) :=
  match e with
  | SExpr.list xs => match xs[0]? with
    | some (SExpr.atom h) => some (h, xs.extract 1 xs.size)
    | _ => none
  | _ => none

/-- A function definition of the query. -/
structure Defn where
  params : Array (String × SExpr)
  sort : SExpr
  body : SExpr
  isRec : Bool
  deriving Inhabited

/-- A recursive function `fn` of the query, defined by the axiom `∀ x⃗, fn x⃗ = defn x⃗` (either orientation). -/
structure Pair where
  fn : String
  defn : String
  /-- index of the axiom in the query -/
  assertIdx : Nat
  /-- the formula of the axiom -/
  formula : SExpr
  deriving Inhabited

structure InlineCtx where
  /-- functions renamed in bodies (the definitions `F_LRec` of the recursive functions `F`) -/
  ren : Std.HashMap String String
  /-- macros (`define-fun`), inlined in bodies -/
  macros : Std.HashMap String Defn

/-- Inlining of macros, with the bodies of the macros memoized. -/
abbrev InlineM := ReaderT InlineCtx (StateT (Std.HashMap String SExpr) (Except String))

mutual
/-- Inline the macros of `e` (as `let` bindings of their parameters) and rename the functions of `ren`; `bound`
    are the variables in scope. -/
partial def inline (bound : Std.HashSet String) (e : SExpr) : InlineM SExpr := do
  let ctx ← read
  match e with
  | SExpr.atom a =>
      if bound.contains a then return e
      if let some f := ctx.ren.get? a then return SExpr.atom f
      if let some d := ctx.macros.get? a then
        if d.params.isEmpty then return ← macroBody a d
      return e
  | SExpr.str _ => return e
  | SExpr.list xs =>
      match xs[0]? with
      | some (SExpr.atom "let") =>
          let some binds := xs[1]? >>= SExpr.list? | throw s!"ill-formed let: {e}"
          let mut binds' := #[]
          let mut bound' := bound
          for b in binds do
            let some #[SExpr.atom x, t] := b.list? | throw s!"ill-formed binding: {b}"
            -- NOTE: `let` is parallel (bound terms are in the outer scope)
            binds' := binds'.push (SExpr.list #[SExpr.atom x, ← inline bound t])
            bound' := bound'.insert x
          return SExpr.list #[SExpr.atom "let", SExpr.list binds', ← inline bound' xs[2]!]
      | some (SExpr.atom "forall") | some (SExpr.atom "exists") | some (SExpr.atom "lambda") =>
          let some vs := xs[1]? >>= SExpr.list? | throw s!"ill-formed binder: {e}"
          let bound' := vs.foldl (fun acc v => match v with | SExpr.list #[SExpr.atom x, _] => acc.insert x | _ => acc) bound
          return SExpr.list #[xs[0]!, xs[1]!, ← inline bound' xs[2]!]
      | some (SExpr.atom "!") => return SExpr.list (#[xs[0]!, ← inline bound xs[1]!] ++ xs.extract 2 xs.size)
      | some (SExpr.atom "match") => throw "match is not supported"
      | some (SExpr.atom "as") | some (SExpr.atom "_") => return e
      | some (SExpr.atom h) =>
          let args ← (xs.extract 1 xs.size).mapM (inline bound)
          if !bound.contains h then
            if let some f := ctx.ren.get? h then return SExpr.list (#[SExpr.atom f] ++ args)
            if let some d := ctx.macros.get? h then
              if d.params.size != args.size then throw s!"wrong number of arguments for {h}"
              let body ← macroBody h d
              return SExpr.list #[SExpr.atom "let", SExpr.list ((d.params.zip args).map fun ((x, _), a) => SExpr.list #[SExpr.atom x, a]), body]
          return SExpr.list (#[SExpr.atom h] ++ args)
      | some hd => return SExpr.list (#[hd] ++ (← (xs.extract 1 xs.size).mapM (inline bound)))
      | none => return e

/-- Body of macro `n` with its macros inlined (memoized). -/
partial def macroBody (n : String) (d : Defn) : InlineM SExpr := do
  if let some b := (← get).get? n then return b
  let b ← inline (d.params.foldl (fun acc (x, _) => acc.insert x) {}) d.body
  modify (·.insert n b)
  return b
end

/-- Symbols of `e`. -/
partial def symbols (e : SExpr) (acc : Std.HashSet String := {}) : Std.HashSet String :=
  match e with
  | SExpr.atom a => acc.insert a
  | SExpr.list xs => xs.foldl (fun acc x => symbols x acc) acc
  | _ => acc

/-- Maximal size (in characters) of the `define-funs-rec` block of the rewritten query. -/
def maxBlockSize : Nat := 16000000

/-- Rewrite Blaster's query `cmds` such that its recursive functions (see `Pair`) are defined by a
    `define-funs-rec` block, as Z3's `recfun-finder` simplifier does: each function `F` is defined by the body of
    its definition `F_LRec` (with `F_LRec` renamed to `F` and the macros inlined), and its declaration and axiom
    are removed. The recursive definitions (`define-fun-rec`) used by the bodies are moved to the block. The
    axioms of the type predicates of recursive datatypes (`@is…` functions, interpreted as `True` by the replay)
    are dropped, which only weakens the query. The other commands are kept in order, after the declarations
    and the block. Returns the rewritten query and the recursive functions. Functions with parameters of sort
    `Nat` are not rewritten (their axioms are guarded by `0 ≤ x`, see `guardNatQuantifiers`). -/
def rewriteQuery (cmds : Array SExpr) : Except String (Array SExpr × Array Pair) := do
  let mut declared : Std.HashMap String Nat := {}
  let mut defs : Std.HashMap String Defn := {}
  for c in cmds do
    match headArgs? c with
    | some ("declare-fun", #[SExpr.atom f, SExpr.list sorts, _]) => declared := declared.insert f sorts.size
    | some ("define-fun", #[SExpr.atom f, ps, s, b]) =>
        defs := defs.insert f { params := ← Z3.sortedVars ps, sort := s, body := b, isRec := false }
    | some ("define-fun-rec", #[SExpr.atom f, ps, s, b]) =>
        defs := defs.insert f { params := ← Z3.sortedVars ps, sort := s, body := b, isRec := true }
    | _ => pure ()
  -- axioms `∀ x⃗, F x⃗ = G x⃗`
  let mut found : Array Pair := #[]
  let mut paired : Std.HashSet String := {}
  for h : i in [:cmds.size] do
    let some ("assert", #[φ]) := headArgs? cmds[i] | continue
    let some ("forall", #[SExpr.list vs, body]) := headArgs? φ | continue
    let vars := vs.filterMap fun v => match v with
      | SExpr.list #[SExpr.atom x, s] => if s == SExpr.atom "Nat" then none else some (SExpr.atom x)
      | _ => none
    if vars.size != vs.size then continue
    let body := match headArgs? body with
      | some ("!", as) => as[0]?.getD body
      | _ => body
    let some ("=", #[l, r]) := headArgs? body | continue
    for (fa, ga) in [(l, r), (r, l)] do
      let some (f, fargs) := headArgs? fa | continue
      let some (g, gargs) := headArgs? ga | continue
      if fargs != vars || gargs != vars || paired.contains f then continue
      let some n := declared.get? f | continue
      let some d := defs.get? g | continue
      if n != vars.size || d.params.size != vars.size then continue
      found := found.push { fn := f, defn := g, assertIdx := i, formula := φ }
      paired := paired.insert f
      break
  let dropped : Std.HashSet Nat := found.foldl (fun s p => s.insert p.assertIdx) {}
  let pairs := found.filter (!·.fn.startsWith "@is")
  if pairs.isEmpty then throw "no recursive function"
  let fns : Std.HashSet String := pairs.foldl (fun s p => s.insert p.fn) {}
  let ictx : InlineCtx := {
    ren := pairs.foldl (fun m p => m.insert p.defn p.fn) {}
    macros := defs.filter fun _ d => !d.isRec }
  -- bodies of the block: the recursive functions, and the recursive definitions they use
  let block : InlineM (Array (String × Defn × SExpr)) := do
    let mut out := #[]
    let mut seen : Std.HashSet String := {}
    let mut todo : Array (String × Defn) := pairs.reverse.filterMap fun p => (defs.get? p.defn).map (p.fn, ·)
    while !todo.isEmpty do
      let (f, d) := todo.back!
      todo := todo.pop
      if seen.contains f then continue
      seen := seen.insert f
      let b ← inline (d.params.foldl (fun acc (x, _) => acc.insert x) {}) d.body
      out := out.push (f, d, b)
      for s in symbols b do
        if let some d' := defs.get? s then
          if d'.isRec && !seen.contains s && !ictx.ren.contains s then todo := todo.push (s, d')
    return out
  let (block, _) ← (block.run ictx).run {}
  let moved : Std.HashSet String := block.foldl (fun s (f, _) => if fns.contains f then s else s.insert f) {}
  let blockCmd := SExpr.list #[SExpr.atom "define-funs-rec",
    SExpr.list (block.map fun (f, d, _) =>
      SExpr.list #[SExpr.atom f, SExpr.list (d.params.map fun (x, s) => SExpr.list #[SExpr.atom x, s]), d.sort]),
    SExpr.list (block.map (·.2.2))]
  if (toString blockCmd).length > maxBlockSize then throw "definitions too large"
  let mut opts := #[]
  let mut sorts := #[]
  let mut decls := #[]
  let mut rest := #[]
  for h : i in [:cmds.size] do
    let c := cmds[i]
    let some (hd, args) := headArgs? c | rest := rest.push c; continue
    let name := (args[0]?.bind SExpr.atom?).getD ""
    if ["set-option", "set-simplifier", "set-logic", "set-info"].contains hd then opts := opts.push c
    else if ["declare-datatype", "declare-datatypes", "declare-sort", "define-sort"].contains hd then sorts := sorts.push c
    else if hd == "declare-fun" || hd == "declare-const" then
      if !fns.contains name then decls := decls.push c
    else if dropped.contains i || ["check-sat", "get-proof", "get-model", "exit"].contains hd then continue
    else if hd == "define-fun-rec" && moved.contains name then continue
    else rest := rest.push c
  return (opts ++ sorts ++ decls ++ #[blockCmd] ++ rest, pairs)

/-! ## Interpretation -/

/-- Extend the interpretation with the functions defined in the proof output that are not symbols of the query
    (Z3's auxiliary functions `fold-rec-n`, interpreted as macros), and with the guards of the case predicates of
    recursive functions given by the lemmas `(or (not ((_ case-def k f) a⃗)) g)` (see `interpCaseDef`). -/
def addProofDefs (proof : Proof) (tbl : SymTable) : SymTable := Id.run do
  let mut tbl := tbl
  for d in proof.defs do
    if !tbl.syms.contains d.name then
      tbl := { tbl with syms := tbl.syms.insert d.name (.macro d.params d.body) }
  for s in proof.steps do
    if s.rule != "th-lemma" || s.attrs[0]? != some (SExpr.atom "recfun") || !s.premises.isEmpty then continue
    let .app "or" #[l₁, l₂] := s.concl.stripAnnot | continue
    for (l, g) in [(l₁, l₂), (l₂, l₁)] do
      let some c := l.not? | continue
      let .iapp "case-def" idx args := c.stripAnnot | continue
      let some key := caseDefKey? idx | continue
      tbl := { tbl with caseGuards := tbl.caseGuards.insert key ((tbl.caseGuards.getD key #[]).push (args, g)) }
      break
  return tbl

/-! ## Lemmas -/

/-- Definitional equation `∀ x⃗, f x⃗ = body` of a recursive function, proved on first use. The candidate
    statements are tried in order: the body of the function in the header of Z3's proof (on which Z3's lemmas
    are expressed), then the body of the query (Blaster's normal form). -/
structure DefEq where
  stmts : Array Expr
  /-- head constant of the left-hand side (see `lhsHead?`) -/
  head : Name
  /-- the proved statement and its proof (`none` when not attempted yet) -/
  proof : IO.Ref (Option (Option (Expr × Expr)))

structure Ctx where
  eqs : Array DefEq := #[]
  /-- proof of a definitional equation (e.g., with the bridge tactics) -/
  proveDef : Expr → TermElabM (Option Expr) := fun _ => pure none
  /-- proof of `g₁ → ... → gₙ → l = r` for the rewritten sides `l` and `r` of an unfolding under the guards `gᵢ`
      when they differ (e.g., in the normal forms of Blaster and Z3, like `0 < x` and `¬ x ≤ 0`) -/
  proveImp : Expr → TermElabM (Option Expr) := fun _ => pure none

/-- Head constant of an application `f a⃗`, through the conversions of the interpretation (`↑(f a⃗)` for
    functions returning `Nat`, `f a⃗ = true` for functions returning `Bool`). -/
def lhsHead? (e : Expr) : Option Name :=
  let e := if e.isAppOfArity ``Eq 3 && (e.getArg! 0).isConstOf ``Bool && (e.getArg! 2).isConstOf ``Bool.true then
    e.getArg! 1 else e
  let e := if e.isAppOfArity ``Nat.cast 3 then e.appArg! else e
  e.getAppFn.constName?

/-- Definitional equations of the recursive functions `pairs`: the interpretation of `∀ x⃗, f x⃗ = body` for the
    body of `f` in the definitions `defs` of the proof output, and of the axiom of `f` in the query. -/
def mkCtx (tbl : SymTable) (pairs : Array Pair) (defs : Array FunDef) (proveDef proveImp : Expr → TermElabM (Option Expr)) :
    TermElabM Ctx := do
  if !pairs.isEmpty then debugLog m!"recfun: {pairs.size} recursive functions, {defs.size} definitions in the proof"
  let interpStmt (φ : STerm) : TermElabM (Option (Expr × Name)) := do
    try
      let stmt ← instantiateMVars (← (interpProp φ).run { table := tbl })
      if stmt.hasMVar then return none
      let some head ← forallTelescope stmt fun _ b => do
          let some (_, l, _) := b.eq? | return none
          return lhsHead? l
        | return none
      return some (stmt, head)
    catch ex =>
      debugLog m!"recfun: no definitional equation for {φ}: {ex.toMessageData}"
      return none
  let mut eqs := #[]
  for p in pairs do
    let mut cands := #[]
    if let some d := defs.find? (·.name == p.fn) then
      let lhs := STerm.app p.fn (d.params.map (STerm.sym ·.1))
      cands := cands.push (STerm.quant .forall d.params (.app "=" #[lhs, d.body]))
    if let .ok φ := STerm.ofSExpr {} p.formula then cands := cands.push φ
    let mut stmts := #[]
    let mut head := Name.anonymous
    for φ in cands do
      if let some (stmt, h) ← interpStmt φ then
        if head.isAnonymous then head := h
        if h == head then stmts := stmts.push stmt
    if !stmts.isEmpty then eqs := eqs.push { stmts, head, proof := ← IO.mkRef none }
  return { eqs, proveDef, proveImp }

/-- Proof of the definitional equation `eq` (attempted once; the proof is shared by the lemmas using it). -/
def DefEq.get (eq : DefEq) (ctx : Ctx) : TermElabM (Option (Expr × Expr)) := do
  if let some r ← eq.proof.get then return r
  let mut r := none
  for stmt in eq.stmts do
    if let some p ← (try ctx.proveDef stmt catch _ => pure none) then
      let m ← mkFreshExprMVar stmt
      m.mvarId!.assign p
      r := some (stmt, m)
      break
    debugLog m!"recfun: definitional equation not proved: {stmt}"
  eq.proof.set (some r)
  return r

/-- Instance of the equation `pf : stmt` (`∀ x⃗, l = r`) whose left-hand side is `t`: `r[a⃗]` and the proof of `t = r[a⃗]`. -/
def instantiateEq (stmt pf t : Expr) : MetaM (Option (Expr × Expr)) := do
  let (ms, _, body) ← forallMetaTelescopeReducing stmt
  let some (_, l, r) := body.eq? | return none
  if !(← withReducible (isDefEq l t)) then return none
  let r ← instantiateMVars r
  let p ← instantiateMVars (mkAppN pf ms)
  if r.hasExprMVar || p.hasExprMVar then return none
  return some (r, p)

/-- Facts (propositions with their proofs), with the consequences of conjunctions, negated disjunctions and
    double negations. -/
partial def addFact (facts : Std.HashMap Expr Expr) (t p : Expr) : MetaM (Std.HashMap Expr Expr) := do
  if facts.contains t then return facts
  let facts := facts.insert t p
  if let some (a, b) := t.and? then
    return ← addFact (← addFact facts a (mkApp3 (mkConst ``And.left) a b p)) b (mkApp3 (mkConst ``And.right) a b p)
  if let some na := t.not? then
    if let some a := na.not? then
      return ← addFact facts a (mkApp2 (mkConst ``Classical.byContradiction) a p)
    if let some (a, b) := na.app2? ``Or then
      let pa ← withLam `h a fun h => return mkApp p (mkApp3 (mkConst ``Or.inl) a b h)
      let pb ← withLam `h b fun h => return mkApp p (mkApp3 (mkConst ``Or.inr) a b h)
      return ← addFact (← addFact facts (mkNot a) pa) (mkNot b) pb
  return facts

/-- Rewrite steps on `t`: unfolding of the recursive functions with their definitional equations, and reduction of
    the conditionals whose condition is decided by the facts. Returns the terms `t = t₀, t₁, ...` with the proofs
    of `t = tᵢ`. -/
def rewriteChain (ctx : Ctx) (facts : Std.HashMap Expr Expr) (t : Expr) (fuel := 64) : TermElabM (Array (Expr × Expr)) := do
  let mut cur := t
  let mut pf ← mkEqRefl t
  let mut out := #[(t, pf)]
  for _ in [0:fuel] do
    let some (next, p) ← step cur | break
    pf ← mkEqTrans pf p
    cur := next
    out := out.push (cur, pf)
  return out
where
  /-- The truth value of `c` given by the facts (with a proof of `c` or `¬ c`), also through the normal forms of
      Z3 (`a < b` as `¬ b ≤ a`, equalities up to symmetry). -/
  decide? (c : Expr) : MetaM (Option (Bool × Expr)) := do
    if let some p := facts.get? c then return some (true, p)
    if let some p := facts.get? (mkNot c) then return some (false, p)
    if c.isAppOfArity ``LT.lt 4 && (c.getArg! 0).isConstOf ``Int then
      let (a, b) := (c.getArg! 2, c.getArg! 3)
      if let some p := facts.get? (mkNot (mkIntLe b a)) then return some (true, ← mkAppM ``Int.lt_of_not_ge #[p])
      if let some p := facts.get? (mkIntLe b a) then return some (false, ← mkAppM ``Int.not_lt_of_ge #[p])
    if let some (_, a, b) := c.eq? then
      let c' ← mkEq b a
      if let some p := facts.get? c' then return some (true, ← mkEqSymm p)
      if let some p := facts.get? (mkNot c') then
        return some (false, ← withLam `h c fun h => do return mkApp p (← mkEqSymm h))
    return none
  step (t : Expr) : TermElabM (Option (Expr × Expr)) := do
    if t.isAppOfArity ``ite 5 then
      let args := t.getAppArgs
      let (α, c, inst, a, b) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
      let us := t.getAppFn.constLevels!
      match ← decide? c with
      | some (true, hc) => return some (a, mkAppN (mkConst ``if_pos us) #[c, inst, hc, α, a, b])
      | some (false, hn) => return some (b, mkAppN (mkConst ``if_neg us) #[c, inst, hn, α, a, b])
      | none => return none
    let some h := lhsHead? t | return none
    for eq in ctx.eqs do
      if eq.head != h then continue
      let some (stmt, pf) ← eq.get ctx | continue
      if let some r ← instantiateEq stmt pf t then return some r
    return none

/-- Proof of `goal` from the hypotheses `hyps` (propositions and proofs) with `ctx.proveImp`. -/
def proveUnder (ctx : Ctx) (hyps : Array (Expr × Expr)) (goal : Expr) : TermElabM (Option Expr) := do
  let stmt := hyps.foldr (fun (t, _) acc => mkForall `h .default t acc) goal
  return (← ctx.proveImp stmt).map (mkAppN · (hyps.map (·.2)))

/-- Proof of the literal `l` from the facts: the sides of an equality are rewritten to a common term (see
    `rewriteChain`), a proposition to `True`, a negated proposition to `False`. When the rewritten terms differ,
    their equality is proved under the guards `hyps`. -/
def proveLit (ctx : Ctx) (facts : Std.HashMap Expr Expr) (hyps : Array (Expr × Expr)) (l : Expr) :
    TermElabM (Option Expr) := do
  if let some (_, a, b) := l.eq? then
    let ca ← rewriteChain ctx facts a
    let cb ← rewriteChain ctx facts b
    if ca.size == 1 && cb.size == 1 then return none
    for (x, px) in ca do
      for (y, py) in cb do
        if x == y then return some (← mkEqTrans px (← mkEqSymm py))
    for (x, px) in ca do
      for (y, py) in cb do
        if x.getAppFn == y.getAppFn && (← propEq x y) then return some (← mkEqTrans px (← mkEqSymm py))
    -- differences of the rewritten sides
    let (x, px) := ca.back!
    let (y, py) := cb.back!
    if let some p ← proveUnder ctx hyps (← mkEq x y) then
      return some (← mkEqTrans (← mkEqTrans px p) (← mkEqSymm py))
    debugLog m!"recfun: no common rewrite of {ca.map (·.1)} and {cb.map (·.1)} (facts {facts.toArray.map (·.1)})"
    return none
  if let some q := l.not? then
    let cq ← rewriteChain ctx facts q
    if cq.size == 1 then return none
    let pq ← match cq.find? (·.1.isConstOf ``False) with
      | some (_, pq) => pure pq
      | none =>
          let (x, px) := cq.back!
          let some p ← proveUnder ctx hyps (← mkEq x (mkConst ``False)) | return none
          mkEqTrans px p
    return some (← withLam `h q fun h => mkEqMP pq h)
  let cl ← rewriteChain ctx facts l
  if cl.size == 1 then return none
  let pl ← match cl.find? (·.1.isConstOf ``True) with
    | some (_, pl) => pure pl
    | none =>
        let (x, px) := cl.back!
        let some p ← proveUnder ctx hyps (← mkEq x (mkConst ``True)) | return none
        mkEqTrans px p
  return some (← mkEqMPR pl (mkConst ``True.intro))

/-- Proof of the clause `concl` (literals `lits`) from a proof of its `j`-th literal assuming the others false. -/
def proveByLit (ctx : Ctx) (lits : Array Expr) (concl : Expr) (j : Nat) : TermElabM (Option Expr) := do
  let r ← withLocalDeclD `hn (mkNot concl) fun hn => do
    let mut facts : Std.HashMap Expr Expr := {}
    let mut hyps := #[]
    for i in [:lits.size] do
      if i == j then continue
      let l := lits[i]!
      let nl ← withLam `h l fun h => return mkApp hn (← mkOrInj lits i h)
      facts ← addFact facts (mkNot l) nl
      hyps := hyps.push (mkNot l, nl)
    let some p ← proveLit ctx facts hyps lits[j]! | return none
    return some (mkLambda `hn .default (mkNot concl) ((mkApp hn (← mkOrInj lits j p)).abstract #[hn]))
  return r.map (mkApp2 (mkConst ``Classical.byContradiction) concl ·)

/-- Proof of `goal` by case splits on `atoms` (in order), each case by unit propagation (see `PropEngine`), e.g.,
    the disjunction of the case predicates of a function (the conjunctions of the guards of its cases). -/
partial def splitProve (hyps : Array (Expr × Expr)) (goal : Expr) (atoms : List Expr) (budget : IO.Ref Nat) :
    MetaM (Option Expr) := do
  if let some p ← PropEngine.prove hyps goal (splits := 0) then return some p
  let n ← budget.get
  if n == 0 then return none
  budget.set (n - 1)
  match atoms with
  | [] => return none
  | c :: rest =>
      let some pos ← withLocalDeclD `hc c fun hc => do
          return (← splitProve (hyps.push (c, hc)) goal rest budget).map fun p => mkLambda `hc .default c (p.abstract #[hc])
        | return none
      let some neg ← withLocalDeclD `hc (mkNot c) fun hc => do
          return (← splitProve (hyps.push (mkNot c, hc)) goal rest budget).map fun p =>
            mkLambda `hc .default (mkNot c) (p.abstract #[hc])
        | return none
      return some (mkApp6 (mkConst ``Or.elim) c (mkNot c) goal (mkApp (mkConst ``Classical.em) c) pos neg)

/-- Atoms of the conjunctions of the literals `lits` (e.g., the guards of case predicates), by decreasing number of
    literals containing them. -/
def guardAtoms (lits : Array Expr) : Array Expr := Id.run do
  let rec conjuncts (e : Expr) (fuel : Nat) : List Expr :=
    match fuel, e.and? with
    | fuel + 1, some (a, b) => a :: conjuncts b fuel
    | _, _ => [e]
  let mut counts : Array (Expr × Nat) := #[]
  for l in lits do
    for g in conjuncts l 64 do
      let a := g.not?.getD g
      match counts.findIdx? (·.1 == a) with
      | some i => counts := counts.modify i fun (a, n) => (a, n + 1)
      | none => counts := counts.push (a, 1)
  return (counts.zipIdx.qsort fun ((_, n₁), i₁) ((_, n₂), i₂) => n₁ > n₂ || (n₁ == n₂ && i₁ < i₂)).map (·.1.1)

/-- Proof of a lemma of Z3's theory of recursive functions (`th-lemma recfun`), given the interpretation of its
    clause `concl` with `n` literals:
     - propositional lemmas on case predicates (e.g., `¬ case(a⃗) ∨ g`, `case(a⃗) ∨ ¬ g₁ ∨ ... ∨ ¬ gₙ`), by unit
       propagation;
     - unfoldings `¬ g₁ ∨ ... ∨ ¬ gₙ ∨ f a⃗ = r` (also of the auxiliary functions `fold-rec-n`, whose
       interpretation is their body), by rewriting (see `proveLit`);
     - disjunctions of the case predicates of a function at `a⃗`, by case splits on the guards. -/
def proveLemma (ctx : Ctx) (concl : Expr) (n : Nat) : TermElabM (Option Expr) := do
  if let some p ← PropEngine.prove #[] concl (splits := 0) then return some p
  let lits := disjuncts concl n
  if lits.size ≥ 1 then
    for j in (List.range lits.size).reverse do
      if let some p ← proveByLit ctx lits concl j then return some p
  if lits.size ≥ 2 then
    let atoms := guardAtoms lits
    if atoms.size ≤ 16 then
      return ← splitProve #[] concl atoms.toList (← IO.mkRef 512)
  return none

end Blaster.Reconstruct.SmtProof.RecFun
