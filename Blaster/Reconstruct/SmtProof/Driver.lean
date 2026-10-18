import Lean
import Blaster.Smt.Translate
import Blaster.Reconstruct.Discharge
import Blaster.Reconstruct.SmtProof.Z3
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
  args := #["-in", "-smt2", s!"-T:{timeoutSec}"]
  preamble := #["(set-option :produce-proofs true)"]
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

/-- Run `backend` on the query `cmds`, returning the raw proof output. -/
def runBackend (backend : Backend) (cmds : Array SExpr) : IO (Except String String) := do
  let query := String.intercalate "\n" (backend.preamble.toList ++
    (cmds.filter (!backend.dropCommand ·)).toList.map toString ++ ["(check-sat)", "(get-proof)", "(exit)"])
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_DUMP" then IO.FS.writeFile f query
  let child ← IO.Process.spawn { cmd := backend.cmd, args := backend.args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr query
  stdin.flush
  let (_, child) := ((), child)
  -- NOTE: closing stdin by dropping the handle
  let out ← IO.asTask child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let _ ← child.wait
  let out ← IO.ofExcept out.get
  let out := out.trimLeft
  if out.startsWith "unsat" then return .ok (out.drop 5)
  return .error s!"{backend.name}: {out.take 200} {err.take 200}"

/-! ## Interpretation of the query symbols -/

/-- Lean name of an SMT symbol produced by `nameToSmtSymbol` (possibly quoted). -/
def symbolToName (s : String) : Name :=
  let s := if s.startsWith "|" && s.endsWith "|" then (s.drop 1 |>.dropRight 1) else s
  s.toName

/-- Interpretation of Blaster's auxiliary functions. -/
def auxiliaryInterp (s : String) : MetaM (Option Expr) := do
  let parse (str : String) : TermElabM Expr := do
    let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term str)
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let src? : Option String := match s with
    | "@Nat.pow" => some "fun (x y : Int) => ((x.toNat ^ y.toNat : Nat) : Int)"
    | "@Int.pow" => some "fun (x y : Int) => x ^ y.toNat"
    | "@Nat.log2" => some "fun (x : Int) => ((Nat.log2 x.toNat : Nat) : Int)"
    | _ => none
  let some src := src? | return none
  let ((e, _), _) ← (parse src).run {} |>.run {}
  return some e

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
        else if n.endsWith "_LRec" then
          -- the definition of a recursive function: same interpretation as the function
          if let some e := funs.get? (n.dropRight 5) then
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
    ("simp", ← `(tactic| (intros; simp_all [Int.toNat_natCast] <;> done))),
    ("simp+omega", ← `(tactic| (intros; simp_all [Int.toNat_natCast] <;> omega))),
    ("grind", ← `(tactic| (intros; grind))),
    ("unfold", ← `(tactic| (intros; blaster_unfold_user <;> (try simp_all [Int.toNat_natCast]) <;>
                            (try split) <;> (try split) <;> first | done | omega | grind))),
    ("cases", ← `(tactic| (intros; blaster_cases_vars <;> blaster_unfold_user <;>
                            (try simp_all [Int.toNat_natCast]) <;> first | done | omega | grind)))
  ]

def stepTactics (rule : String) : TermElabM (Array (String × TSyntax `tactic)) := do
  let arith := #[
    ("omega", ← `(tactic| (intros; omega))),
    ("split+omega", ← `(tactic| (intros; (repeat' split) <;> omega)))]
  let simp := #[
    ("rfl", ← `(tactic| (intros; rfl))),
    ("simp", ← `(tactic| (intros; simp_all <;> done))),
    ("simp only", ← `(tactic| (intros; simp only [*] <;> done)))]
  let grind := #[("grind", ← `(tactic| (intros; grind)))]
  let quant := #[
    ("forall_congr", ← `(tactic| (intro h; exact forall_congr h))),
    ("forall_imp", ← `(tactic| (intro h h' x; exact h x (h' x))))]
  match rule with
  | "th-lemma" => return arith ++ simp ++ grind
  | "quant-intro" => return quant ++ simp ++ grind
  | "def-axiom" | "not-or-elim" | "and-elim" | "iff~" | "nnf-pos" | "nnf-neg" => return simp ++ grind
  | _ => return simp ++ arith ++ grind

def portfolio (tacs : Array (String × TSyntax `tactic)) (goal : Expr) : TermElabM (Option (Expr × String)) := do
  for (name, tac) in tacs do
    if let some p ← proveWithTactic goal tac then return some (p, name)
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

/-- Try to prove `e` (a closed proposition proved valid by the SMT solver) by replaying a proof of the
    SMT backend. -/
def proveBySmtProof (e : Expr) (sOpts : BlasterOptions) : TermElabM (Except String SmtProofResult) :=
  -- NOTE: each tactic attempt has its own heartbeat budget (see `proveWithTactic`)
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
  dataBinders e fun xs body => do
  try
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
    let z3 := (← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3"
    let backend := z3Backend z3 (sOpts.timeout.getD 20)
    let out ← runBackend backend cmds
    let out ← match out with | .ok o => pure o | .error msg => throwError msg
    let sproof ← ofExcept (backend.parseProof out)
    -- 3. interpretation
    let mut consts : Std.HashMap String Expr := {}
    for x in xs do
      if let some idx := tenv.smtEnv.fvarsCache.get? x.fvarId! then
        consts := consts.insert s!"${idx}" x
    let tbl ← buildSymTable cmds tenv consts
    -- 4. replay
    let bridge ← bridgeTactics
    let pf ← withLocalDeclD `hneg (mkNot body) fun hneg => do
      let cfg : ReplayConfig := {
        proveDirect := fun c => do
          if ← isDefEq c (mkNot body) then return some hneg
          if ← isDefEq c (mkNot body') then return some hneg
          let r ← portfolio bridge c
          if r.isNone && (← IO.getEnv "BLASTER_SMTPROOF_DEBUG").isSome then
            logInfo m!"bridge failed: {c}"
          return r.map (·.1)
        proveStep := fun rule stmt => do portfolio (← stepTactics rule) stmt }
      let ctx : ReplayCtx := { proof := sproof, interp := { table := tbl }, cfg }
      let (p, st) ← (replay sproof.root |>.run ctx).run {}
      let pt ← inferType p
      if !pt.isConstOf ``False then throwError "smt proof: root does not prove False: {pt}"
      return (← mkLambdaFVars #[hneg] p, st.stats)
    let (pf, stats) := pf
    let proofBody := mkApp2 (mkConst ``Classical.byContradiction) body pf
    let proof ← instantiateMVars (← mkLambdaFVars xs proofBody)
    return .ok { proof, backend := backend.name, steps := sproof.steps.size, stats }
  catch ex =>
    return .error (← ex.toMessageData.toString)

end Blaster.Reconstruct.SmtProof
