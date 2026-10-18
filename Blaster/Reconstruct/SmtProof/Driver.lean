import Lean
import Blaster.Smt.Translate
import Blaster.Reconstruct.Discharge
import Blaster.Reconstruct.SmtProof.Z3
import Blaster.Reconstruct.SmtProof.Alethe
import Blaster.Reconstruct.SmtProof.Replay

/-!
# Proof reconstruction from SMT proofs

Given a residual goal proved valid by the SMT solver, this module:
 1. translates the goal to SMT-LIB with Blaster's translation (top-level variables are introduced
    as Lean free variables such that the SMT constants can be mapped back to them);
 2. runs a proof producing backend (see `Backend`) on the query and parses its proof
    into the backend independent representation (`Proof`);
 3. builds the interpretation of the SMT symbols in Lean (`SymTable`) from the query and from
    Blaster's translation caches;
 4. replays the proof (see `Replay.lean`) to obtain a proof of `False` from the negation of the goal.
-/

open Lean Meta Elab Term Tactic Blaster.Smt Blaster.Optimize Blaster.Options

namespace Blaster.Reconstruct.SmtProof

/-! ## Backends -/

def isZ3SpecificCommand (c : SExpr) : Bool :=
  match c with
  | .list xs =>
      match xs[0]?, xs[1]? with
      | some (SExpr.atom "set-simplifier"), _ => true
      | some (SExpr.atom "set-option"), some (SExpr.atom o) =>
          -- options set by the backend preamble, and options incompatible with proofs
          o == ":print-success" || o == ":produce-models" || o == ":produce-proofs" ||
          o == ":smt.macro_finder" || o == ":timeout" ||
          -- version specific options
          o.startsWith ":smt.arith.nl"
      | _, _ => false
  | _ => false

/-- Z3 with legacy proof objects. -/
def z3Backend (cmd : String) (timeoutSec : Nat) : Backend where
  name := "z3"
  cmd := cmd
  args := #["-smt2", s!"-T:{timeoutSec}"]
  -- NOTE: `pp.simplify_implies` prints `(=> a (=> b c))` as `(=> (and a b) c)` by default
  preamble := #["(set-option :produce-proofs true)", "(set-option :pp.simplify_implies false)"]
  dropCommand := isZ3SpecificCommand
  parseProof := Z3.parseProof

/-- Guard the top-level universally quantified assertions over `Nat` (e.g., the definitions of recursive
    functions `∀ x, f x = f_LRec x`) with `0 ≤ x`, such that they hold for the interpretation of `Nat`
    functions in Lean (see `Interp.lean`). This only weakens the query. -/
def guardNatQuantifiers (c : SExpr) : SExpr :=
  match c with
  | .list #[.atom "assert", .list #[.atom "forall", .list vars, body]] =>
      let natVars := vars.filterMap fun v => match v with
        | .list #[.atom x, .atom "Nat"] => some x
        | _ => none
      if natVars.isEmpty then c else
      let guard (b : SExpr) : SExpr :=
        natVars.foldr (fun x acc => .list #[.atom "=>", .list #[.atom "<=", .atom "0", .atom x], acc]) b
      let body' := match body with
        | .list xs => if xs[0]? == some (.atom "!") then .list (xs.set! 1 (guard xs[1]!)) else guard body
        | _ => guard body
      .list #[.atom "assert", .list #[.atom "forall", .list vars, body']]
  | c => c

/-- Commands of Blaster's query that are specific to Z3 (all options are set by the backend preamble). -/
def isZ3OnlyCommand (c : SExpr) : Bool :=
  match c.head? with
  | some "set-simplifier" | some "set-option" | some "set-logic" => true
  | _ => false

/-- cvc5 with Alethe proofs. -/
def cvc5Backend (cmd : String) (timeoutSec : Nat) : Backend where
  name := "cvc5"
  cmd := cmd
  args := #["--lang=smt2", "--parsing-mode=lenient", s!"--tlimit={timeoutSec * 1000}", "--proof-format-mode=alethe",
            "--proof-granularity=dsl-rewrite"]
  preamble := #["(set-option :produce-proofs true)", "(set-logic ALL)"]
  dropCommand := isZ3OnlyCommand
  parseProof := Alethe.parseProof

/-- Run `backend` on the query `cmds`, returning the raw proof output. The query is written to a
    temporary file (no interaction with the solver's pipes during the run). -/
def runBackend (backend : Backend) (cmds : Array SExpr) : IO (Except String String) := do
  let query := String.intercalate "\n" (backend.preamble.toList ++
    (cmds.filter (!backend.dropCommand ·)).toList.map toString ++ ["(check-sat)", "(get-proof)", "(exit)"])
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_DUMP" then IO.FS.writeFile f query
  let (h, path) ← IO.FS.createTempFile
  try
    h.putStr query
    h.flush
    let out ← IO.Process.output { cmd := backend.cmd, args := backend.args.push path.toString }
    -- the first line among `sat`, `unsat` and `unknown` (e.g., after warnings on unsupported options)
    let lines := out.stdout.splitOn "\n"
    match lines.findIdx? (fun l => ["sat", "unsat", "unknown"].contains l.trim) with
    | some i =>
        if lines[i]!.trim == "unsat" then
          return .ok (String.intercalate "\n" (lines.drop (i + 1)))
        return .error s!"{backend.name}: {lines[i]!.trim}"
    | none => return .error s!"{backend.name}: {out.stdout.take 300} {out.stderr.take 300}"
  finally
    IO.FS.removeFile path

/-! ## Interpretation of the query symbols -/

/-- Lean name of an SMT symbol produced by `nameToSmtSymbol` (possibly quoted). -/
def symbolToName (s : String) : Name :=
  let s := if s.startsWith "|" && s.endsWith "|" then (s.drop 1 |>.dropRight 1) else s
  s.toName

/-- Interpretation of Blaster's auxiliary recursive functions (as Lean functions on `Int`). -/
def auxiliaryInterp (s : String) : MetaM (Option Expr) := do
  let int := Lean.mkConst ``Int
  let toNat (x : Expr) := mkApp (Lean.mkConst ``Int.toNat) x
  let ofNat (n : Expr) := mkApp3 (Lean.mkConst ``Nat.cast [levelZero]) int (Lean.mkConst ``instNatCastInt) n
  match s with
  | "@Nat.pow" =>
      withLocalDeclD `x int fun x => withLocalDeclD `y int fun y => do
        mkLambdaFVars #[x, y] (ofNat (← mkAppM ``HPow.hPow #[toNat x, toNat y]))
  | "@Int.pow" =>
      withLocalDeclD `x int fun x => withLocalDeclD `y int fun y => do
        mkLambdaFVars #[x, y] (← mkAppM ``HPow.hPow #[x, toNat y])
  | "@Nat.log2" =>
      withLocalDeclD `x int fun x => do
        mkLambdaFVars #[x] (ofNat (mkApp (Lean.mkConst ``Nat.log2) (toNat x)))
  | _ => return none

/-- Remove the bars of a quoted symbol. -/
def unquote (s : String) : String :=
  if s.startsWith "|" && s.endsWith "|" && s.length ≥ 2 then (s.drop 1).dropRight 1 else s

/-- Build the interpretation of the symbols of the query `cmds`, given the translation environment
    and the map from SMT constants (`$k`) to Lean free variables. -/
def buildSymTable (cmds : Array SExpr) (env : TranslateEnv) (consts : Std.HashMap String Expr) :
    MetaM SymTable := do
  let mut tbl : SymTable := {}
  -- Lean functions of the translation
  let mut funs : Std.HashMap String Expr := {}
  for (k, v) in env.smtEnv.funInstCache.toList do
    let nm := match v with
      | .SimpleIdent s => toString s
      | .QualifiedIdent s _ => toString s
    funs := funs.insert nm k.expr
  let mut datatypeSorts : Array SExpr := #[]
  for c in cmds do
    let some xs := c.list? | continue
    match xs[0]?.bind SExpr.atom?, xs[1]?.bind SExpr.atom? with
    | some "define-sort", some n =>
        if let some (SExpr.list #[]) := xs[2]? then
          tbl := { tbl with aliases := tbl.aliases.insert n xs[3]! }
    | some "declare-const", some n =>
        if let some e := consts.get? n then
          tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
        if let some s := xs[2]? then datatypeSorts := datatypeSorts.push s
    | some "declare-fun", some n =>
        if let some e := funs.get? n then
          tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
        else if n.startsWith "@apply" then
          tbl := { tbl with syms := tbl.syms.insert n .apply }
        else if n.startsWith "@is" then
          tbl := { tbl with syms := tbl.syms.insert n .trueFun }
    | some "define-fun", some n =>
        let some (SExpr.list ps) := xs[2]? | continue
        let params := ps.filterMap fun p => match p with
          | .list #[.atom x, s] => some (x, s)
          | _ => none
        match STerm.ofSExpr {} xs[4]! with
        | .ok body => tbl := { tbl with syms := tbl.syms.insert n (.macro params body) }
        | .error _ => pure ()
    | some "define-fun-rec", some n =>
        if n.startsWith "@is" then
          tbl := { tbl with syms := tbl.syms.insert n .trueFun }
        else if let some e ← auxiliaryInterp n then
          tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
        else if (unquote n).endsWith "_LRec" then
          -- the definition of a recursive function: same interpretation as the function
          let base := (unquote n).dropRight 5
          if let some e := funs.get? base <|> funs.get? s!"|{base}|" then
            tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
    | some "declare-datatype", some n =>
        tbl ← addDatatype tbl n xs[2]!
    | some "declare-datatypes", _ =>
        let some (SExpr.list sorts) := xs[1]? | continue
        let some (SExpr.list decls) := xs[2]? | continue
        for (s, d) in sorts.zip decls do
          let some (SExpr.atom n) := s.list? >>= (·[0]?) | continue
          tbl ← addDatatype tbl n d
    | _, _ => pure ()
  -- datatype sorts of the query as they occur in proofs (with expanded aliases)
  let ctx : InterpCtx := { table := tbl }
  let mut expanded : Std.HashMap String (Option Expr) := {}
  for s in datatypeSorts do
    let some _ := s.list? | continue
    try
      let t ← (sortToType s).run ctx
      let key := toString (expandSort tbl s)
      match expanded.get? key with
      | some (some t') => if !(← isDefEq t t') then expanded := expanded.insert key none
      | some none => pure ()
      | none => expanded := expanded.insert key (some t)
    catch _ => pure ()
  for (k, v) in expanded.toList do
    if let some t := v then tbl := { tbl with expandedSorts := tbl.expandedSorts.insert k t }
  return tbl
where
  addDatatype (tbl : SymTable) (n : String) (decl : SExpr) : MetaM SymTable := do
    -- `(par (params) (ctors))` or `(ctors)`
    let ctors := match decl with
      | .list #[.atom "par", _, .list cs] => cs
      | .list cs => cs
      | _ => #[]
    let mut tbl := tbl
    for c in ctors do
      let (cname, fields) := match c with
        | .atom a => (a, #[])
        | .list xs => (xs[0]!.atom?.getD "", xs.extract 1 xs.size)
        | _ => ("", #[])
      let leanCtor := symbolToName cname
      let some (.ctorInfo info) := (← getEnv).find? leanCtor | continue
      tbl := { tbl with
        syms := tbl.syms.insert cname (.ctor leanCtor) |>.insert s!"is-{cname}" (.tester leanCtor),
        sorts := tbl.sorts.insert n (mkConst info.induct) }
      for h : i in [:fields.size] do
        if let some (SExpr.atom sel) := fields[i].list? >>= (·[0]?) then
          tbl := { tbl with syms := tbl.syms.insert sel (.selector leanCtor i) }
    return tbl

/-- Interpretation of the skolem constants introduced by `sk` steps (Z3): for
    `(~ (not (forall ((x S)) φ)) (not φ[x := c]))` (resp. `(~ (exists ((x S)) φ) φ[x := c])`),
    the constant `c` (named `x!n`) is interpreted as `Classical.epsilon (fun x => ¬ φ)`
    (resp. `Classical.epsilon (fun x => φ)`). Only steps with a single bound variable are handled. -/
partial def addSkolems (proof : Proof) (tbl : SymTable) : MetaM SymTable := do
  let mut tbl := tbl
  -- names introduced by `intro-def` (Z3's Tseitin names): `(= t k)` defines `k` as `t`
  for step in proof.steps do
    if step.rule != "intro-def" then continue
    match step.concl.stripAnnot with
    | .app "=" #[t, .sym k] | .app "=" #[.sym k, t] =>
        if !tbl.syms.contains k then tbl := { tbl with syms := tbl.syms.insert k (.macro #[] t) }
    | _ => pure ()
  for step in proof.steps do
    if step.rule != "sk" then continue
    let .app _ #[a, b] := step.concl.stripAnnot | continue
    let (vars, body, neg) := match a.stripAnnot with
      | .app "not" #[.quant .forall vs φ] => (vs, φ, true)
      | .quant .exists vs φ => (vs, φ, false)
      | _ => (#[], .sym "true", false)
    let #[(x, sort)] := vars | continue
    -- the skolem constant: a symbol of `b` named `x!n`, not occurring in `a` and not yet interpreted
    let some c := findSkolem (x ++ "!") b fun c => !tbl.syms.contains c && (findSkolem c a fun _ => true).isNone
      | continue
    try
      let e ← (do
        let ty ← sortToType sort
        let u ← getLevel ty
        let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) ty)
        withLocalDeclD (Name.mkSimple x) ty fun fx => do
          let φ ← withReader (fun c => { c with locals := c.locals.insert x fx }) (interp body)
          let p ← mkLambdaFVars #[fx] (if neg then mkNot φ else φ)
          return mkApp3 (mkConst ``Classical.epsilon [u]) ty inst p : InterpM Expr).run { table := tbl }
      tbl := { tbl with syms := tbl.syms.insert c (.expr e) }
    catch _ => pure ()
  return tbl
where
  findSkolem (pre : String) (t : STerm) (ok : String → Bool) : Option String :=
    match t with
    | .sym s => if s.startsWith pre && ok s then some s else none
    | .app f args =>
        if f.startsWith pre && args.isEmpty && ok f then some f else args.findSome? (findSkolem pre · ok)
    | .iapp _ _ args | .qual _ _ args => args.findSome? (findSkolem pre · ok)
    | .quant _ _ b => findSkolem pre b ok
    | .annot t _ => findSkolem pre t ok
    | _ => none

/-! ## Bridge tactics -/

/-- Introduce the universally quantified variables of the goal, substituting `x := ↑n` for the
    `Int` variables guarded by `0 ≤ x`. -/
macro "blaster_nat_intros" : tactic =>
  `(tactic| repeat (first | (intro x hx; obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hx; subst hn) | intro _))

syntax (name := blasterCasesNat) "blaster_cases_nat" : tactic

/-- Case analysis (`0` / `n + 1`) on the local variables of type `Nat`. -/
@[tactic blasterCasesNat] def evalBlasterCasesNat : Tactic := fun _ => do
  let vars ← withMainContext do
    let mut vs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← whnfR d.type).isConstOf ``Nat then vs := vs.push d.fvarId
    return vs
  if vars.isEmpty then throwError "blaster_cases_nat: no Nat variable"
  for v in vars do
    let gs ← getGoals
    let mut gs' := #[]
    for g in gs do
      if (← g.getDecl).lctx.contains v then
        let subgoals ← g.cases v
        gs' := gs' ++ subgoals.map (·.mvarId)
      else gs' := gs'.push g
    setGoals gs'.toList

/-- Tactics proving the interpretation of asserted formulas (and conclusions of steps that can't be
    replayed) from the negated goal and the definitions of user functions. -/
def bridgeTactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("assumption", ← `(tactic| assumption)),
    -- definitions of functions over `Nat` (see `guardNatQuantifiers`)
    ("nat def", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                              blaster_cases_nat <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_unfold_user) <;> grind))),
    ("omega", ← `(tactic| (intros; omega))),
    -- Blaster's normal forms (e.g., `Nat.add x y`, `Nat.mod x y`) in the negated goal
    ("denorm+omega", ← `(tactic| (intros; blaster_denorm; omega))),
    ("simp", ← `(tactic| (intros; simp_all [Int.toNat_natCast] <;> done))),
    ("simp+omega", ← `(tactic| (intros; blaster_denorm; simp_all [Int.toNat_natCast] <;> omega))),
    -- casts of `Nat` division and modulo (Blaster's encoding: `ite (0 = y) 0 (div x y)`)
    ("casts", ← `(tactic| (intros; blaster_denorm; simp only [Int.natCast_ediv, Int.natCast_emod, Int.natCast_add, Int.natCast_mul,
                            Int.toNat_natCast, Int.ediv_zero, Int.emod_zero] at * <;> (try split) <;> (try split) <;>
                            first | omega | (simp_all; done) | grind))),
    ("grind", ← `(tactic| (intros; grind))),
    ("unfold", ← `(tactic| (intros; blaster_unfold_user <;> (try simp_all [Int.toNat_natCast]) <;>
                            (try split) <;> (try split) <;> first | done | omega | grind))),
    ("cases", ← `(tactic| (intros; blaster_cases_vars <;> blaster_unfold_user <;>
                            (try simp_all [Int.toNat_natCast]) <;> first | done | omega | grind)))
  ]

def stepTactics (rule : String) : TermElabM (Array (String × TSyntax `tactic)) := do
  let arith := #[
    ("omega", ← `(tactic| (intros; omega))),
    ("propext+omega", ← `(tactic| (intros; apply propext; constructor <;> intro <;> omega))),
    ("split+omega", ← `(tactic| (intros; (repeat' split) <;> omega)))]
  let simp := #[
    ("rfl", ← `(tactic| (intros; rfl))),
    ("simp", ← `(tactic| (intros; simp_all <;> done))),
    ("simp only", ← `(tactic| (intros; simp only [*] <;> done)))]
  let grind := #[("grind", ← `(tactic| (intros; grind)))]
  let quant := #[
    ("forall_congr", ← `(tactic| (intro h; exact forall_congr h))),
    ("forall_imp", ← `(tactic| (intro h h' x; exact h x (h' x))))]
  let unfold := #[
    ("nat def", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_cases_nat) <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_unfold_user) <;> grind))),
    ("unfold", ← `(tactic| (intros; blaster_unfold_user <;> (try simp_all [Int.toNat_natCast]) <;> grind)))]
  match rule with
  | "th-lemma" => return arith ++ simp ++ grind ++ unfold
  | "quant-intro" => return quant ++ simp ++ grind
  | "def-axiom" | "not-or-elim" | "and-elim" | "iff~" | "nnf-pos" | "nnf-neg" => return simp ++ grind
  | _ => return simp ++ arith ++ grind

/-- Per rule and tactic: number of successes and time spent (ms, including failed attempts), used to
    order the tactic portfolios by efficiency (adaptive, per process). -/
initialize tacticStats : IO.Ref (Std.HashMap (String × String) (Nat × Nat)) ← IO.mkRef {}

/-- Coarse shape of a goal, refining the statistics of the adaptive ordering: `arith` for (in)equalities
    and propositional combinations of linear arithmetic atoms, `nat` for universally quantified formulas
    guarded by `0 ≤ x` (definitions of `Nat` functions), `data` for formulas with constructors or case
    analyses, `other` otherwise. -/
partial def goalShape (e : Expr) : MetaM String := do
  let some kind ← go e 0 | return "other"
  return kind
where
  go (e : Expr) (depth : Nat) : MetaM (Option String) := do
    if depth > 64 then return none
    if e.isForall then
      if let .forallE _ t b _ := e then
        if (← whnfR t).isConstOf ``Int then
          if let .forallE _ g _ _ := b then
            if g.isAppOfArity ``LE.le 4 then return some "nat"
      return none
    let env ← getEnv
    let isData (s : Expr) : Bool := match s with
      | .const n _ =>
          (n.isStr && n.getString!.endsWith "casesOn") ||
          (isCtorName env n && n != ``Int.ofNat && n != ``True && n != ``False && n != ``Int.negSucc)
      | _ => false
    if (e.find? isData).isSome then return some "data"
    let arith := e.find? (fun s => s.isAppOfArity ``LE.le 4 || s.isAppOfArity ``LT.lt 4 || s.isAppOfArity ``HAdd.hAdd 6 || s.isAppOfArity ``HMul.hMul 6) |>.isSome
    return some (if arith then "arith" else "other")
  isCtorName (env : Environment) (n : Name) : Bool := (env.find? n).any (·.isCtor)

def portfolio (tacs : Array (String × TSyntax `tactic)) (goal : Expr) (rule := "") : TermElabM (Option (Expr × String)) := do
  let rule := s!"{rule}/{← goalShape goal}"
  let stats ← tacticStats.get
  -- most efficient tactics first, i.e., highest number of successes per time unit (with a prior
  -- favoring the given order)
  let score (n : String) (i : Nat) : Float :=
    let (succ, ms) := stats.getD (rule, n) (0, 0)
    (succ.toFloat + 1.0 / (i.toFloat + 1.0)) / (ms.toFloat + 50.0)
  let tacs := (tacs.zipIdx.qsort fun ((n₁, _), i₁) ((n₂, _), i₂) => score n₁ i₁ > score n₂ i₂).map (·.1)
  for (name, tac) in tacs do
    let start ← IO.monoMsNow
    let r ← proveWithTactic goal tac
    let ms := (← IO.monoMsNow) - start
    let succ := if r.isSome then 1 else 0
    tacticStats.modify fun m => let (a, b) := m.getD (rule, name) (0, 0); m.insert (rule, name) (a + succ, b + ms)
    if let some p := r then return some (p, name)
  return none

/-! ## Main entry point -/

/-- Split the leading binders of `e` which are neither propositions nor sorts (i.e., data variables). -/
partial def dataBinders (e : Expr) (k : Array Expr → Expr → TermElabM α) (acc : Array Expr := #[]) : TermElabM α := do
  match e with
  | .forallE n t b bi =>
      if (← isProp t) || t.isSort || (← whnfR t).isSort then k acc e
      else withLocalDecl n bi t fun x => dataBinders (b.instantiate1 x) k (acc.push x)
  | _ => k acc e

structure SmtProofResult where
  proof : Expr
  backend : String
  steps : Nat
  stats : ReplayStats

/-- Given `e := ∀ b₁ ... bₙ, C` (leading binders), return `∀ xs, hs → C` where `xs` are the data binders and
    `hs` the propositions among the `bᵢ` (only when no data binder depends on a proposition), together with
    a function turning a proof of the latter into a proof of `e`. Blaster declares the data variables of
    the leading binders as SMT constants, including the ones following hypotheses. -/
def prenex (e : Expr) : MetaM (Option (Expr × (Expr → MetaM Expr))) := do
  forallTelescope e fun bs c => do
    if bs.isEmpty then return none
    let mut data := #[]
    let mut hyps := #[]
    for b in bs do
      let t ← inferType b
      if (← isProp t) then hyps := hyps.push b
      else
        if hyps.any (fun h => t.containsFVar h.fvarId!) then return none
        data := data.push b
    if hyps.isEmpty || data.isEmpty then return none
    -- already in prenex form
    if bs == data ++ hyps then return none
    let e' ← mkForallFVars (data ++ hyps) c
    let back (p : Expr) : MetaM Expr :=
      forallTelescope e fun bs' _ => do
        -- bs' follow the order of `bs`
        let m := (bs.zip bs').toList
        let get (x : Expr) := (m.find? (·.1 == x)).map (·.2) |>.getD x
        mkLambdaFVars bs' (mkAppN p ((data ++ hyps).map get))
    return some (e', back)

/-- Try to prove `e` (a closed proposition proved valid by the SMT solver) by replaying a proof of the
    SMT backend. -/
partial def proveBySmtProof (e : Expr) (sOpts : BlasterOptions) : TermElabM (Except String SmtProofResult) := do
  if let some (e', back) ← prenex e then
    match ← proveBySmtProof e' sOpts with
    | .ok r => return .ok { r with proof := ← back r.proof }
    | .error msg => return .error msg
  -- NOTE: each tactic attempt has its own heartbeat budget (see `proveWithTactic`)
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
  dataBinders e fun xs body => do
  try
    -- NOTE: polymorphic goals (Blaster's `@Type`/`@Instance` encoding) are not supported yet
    if let .forallE _ t _ _ := body then
      if (← whnfR t).isSort then throwError "smt proof: polymorphic goals are not supported"
    -- 1. translation
    -- NOTE: commands are only recorded when `dumpSmtLib` is set (nothing is printed)
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := { sOpts with onlySmtLib := true, dumpSmtLib := true }}
    let (body', tenv) ← (do
        -- NOTE: the optimizer populates the caches used by the translation (e.g., the definitions of
        -- recursive functions); `body` being already optimized, `body'` is expected to be `body`.
        let (body', _) ← Optimize.mainPf body (track := false)
        setBlasterProcess
        let st ← translateExpr body'
        assertTerm (notSmt st)
        return body' : TranslateEnvT Expr).run env
    let cmds ← tenv.smtEnv.smtCommands.mapM fun c => ofExcept (parseSExpr (toString c))
    let cmds := cmds.map guardNatQuantifiers
    -- 2. backend
    -- backends tried in order (environment variable `BLASTER_SMTPROOF_BACKENDS`, e.g., `z3,cvc5`)
    let names := ((← IO.getEnv "BLASTER_SMTPROOF_BACKENDS").getD "z3").splitOn ","
    let timeout := sOpts.timeout.getD 20
    let mut res : Option (Backend × Proof) := none
    let mut errors := #[]
    for n in names do
      let backend ← match n.trim with
        | "z3" => pure (z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout)
        | "cvc5" => pure (cvc5Backend ((← IO.getEnv "BLASTER_SMTPROOF_CVC5").getD "cvc5") timeout)
        | b => throwError "unknown proof backend {b}"
      match ← runBackend backend cmds with
      | .error msg => errors := errors.push msg
      | .ok out =>
          match backend.parseProof out with
          | .ok p => res := some (backend, p); break
          | .error msg => errors := errors.push s!"{backend.name}: {msg}"
    let some (backend, sproof) := res | throwError "no proof: {errors}"
    -- 3. interpretation
    -- SMT constants of the free variables of the goal (the introduced variables, as well as the
    -- variables of the local context, e.g., section variables)
    let mut consts : Std.HashMap String Expr := {}
    let lctx ← getLCtx
    for (v, idx) in tenv.smtEnv.fvarsCache.toList do
      if lctx.contains v then consts := consts.insert s!"${idx}" (mkFVar v)
    let tbl ← buildSymTable cmds tenv consts
    let tbl ← addSkolems sproof tbl
    -- 4. replay
    let bridge ← bridgeTactics
    let pf ← withLocalDeclD `hneg (mkNot body) fun hneg => do
      let cfg : ReplayConfig := {
        proveDirect := fun c => do
          if ← withReducible (isDefEq c (mkNot body)) then return some hneg
          if ← withReducible (isDefEq c (mkNot body')) then return some hneg
          let r ← portfolio bridge c "bridge"
          if r.isNone && (← IO.getEnv "BLASTER_SMTPROOF_DEBUG").isSome then
            logInfo m!"bridge failed: {c}"
          return r.map (·.1)
        proveStep := fun rule stmt => do portfolio (← stepTactics rule) stmt rule }
      let cache ← IO.mkRef {}
      let deadline := (← IO.monoMsNow) + 1000 * ((← IO.getEnv "BLASTER_SMTPROOF_DEADLINE").bind String.toNat? |>.getD 300)
      let ctx : ReplayCtx := { proof := sproof, interp := { table := tbl, cache := some cache }, cfg, deadline }
      let (p?, st) ← ((do try prepass; return Except.ok (← replay sproof.root)
                            catch ex => return Except.error ex) |>.run ctx).run {}
      let p ← match p? with
        | .ok p => pure p
        | .error ex =>
            -- report the first steps that could not be replayed (i.e., the deepest failures)
            let fs := st.stats.failures.extract 0 3
            throwError "{ex.toMessageData}; first failures: {fs}"
      let pt ← inferType p
      if !pt.isConstOf ``False then throwError "smt proof: root does not prove False: {pt}"
      -- NOTE: the proofs of the steps are instantiated once (see `replay`)
      return (← mkLambdaFVars #[hneg] (← instantiateMVars p), st.stats)
    let (pf, stats) := pf
    let proofBody := mkApp2 (mkConst ``Classical.byContradiction) body pf
    let proof ← instantiateMVars (← mkLambdaFVars xs proofBody)
    return .ok { proof, backend := backend.name, steps := sproof.steps.size, stats }
  catch ex =>
    return .error (← ex.toMessageData.toString)

end Blaster.Reconstruct.SmtProof
