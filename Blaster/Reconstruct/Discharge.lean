import Lean
import Blaster.Reconstruct.Types
import Blaster.Reconstruct.Proof
import Blaster.Reconstruct.Lemmas
import Blaster.Reconstruct.Match

open Lean Meta Elab Term Tactic

namespace Blaster.Reconstruct

/-! # Discharging proof obligations

A proof term produced by the instrumented optimizer may contain proof obligations (holes)
of the form `lhs = rhs` for rewrites that do not (yet) carry an explicit justification.
Each hole is discharged in its own local context (i.e., with all the binders and hypotheses
under which the rewrite has been performed) using a portfolio of decision procedures.
-/

/-- Statistics on discharged proof obligations. -/
structure DischargeStats where
  /-- Number of proof obligations encountered. -/
  total : Nat := 0
  /-- Number of proof obligations discharged per method. -/
  byMethod : Std.HashMap String Nat := {}
  /-- Pretty printed proof obligations that could not be discharged. -/
  failures : Array MessageData := #[]
  /-- Proof obligations per label (see `HoleInfo`), i.e., `label := (method ↦ count)`
      with method `failed` for undischarged obligations. -/
  byLabel : Std.HashMap String (Std.HashMap String Nat) := {}
deriving Inhabited

def DischargeStats.record (s : DischargeStats) (method : String) (label : String) : DischargeStats :=
  let m := s.byLabel.getD label {}
  { s with byMethod := s.byMethod.insert method (s.byMethod.getD method 0 + 1),
           byLabel := s.byLabel.insert label (m.insert method (m.getD method 0 + 1)) }

def DischargeStats.merge (s t : DischargeStats) : DischargeStats :=
  let byMethod := t.byMethod.fold (init := s.byMethod) fun acc m n => acc.insert m (acc.getD m 0 + n)
  let byLabel := t.byLabel.fold (init := s.byLabel) fun acc l ms =>
    acc.insert l (ms.fold (init := acc.getD l {}) fun acc' m n => acc'.insert m (acc'.getD m 0 + n))
  { total := s.total + t.total, byMethod, failures := s.failures ++ t.failures, byLabel }

def DischargeStats.summary (s : DischargeStats) : String :=
  let entries := s.byMethod.toList.toArray.qsort (fun a b => a.1 < b.1)
  ", ".intercalate (entries.map (fun (m, n) => s!"{m}: {n}")).toList

/-- Maximum number of heartbeats (in thousands) allowed for each discharge attempt. -/
def dischargeHeartbeats : Nat := 50000

/-- Execute `x` with a fresh heartbeat budget of `n` thousand heartbeats. -/
@[inline] def withHeartbeatBudget [Monad m] [MonadWithReaderOf Core.Context m] [MonadLiftT BaseIO m]
  [MonadControlT CoreM m] (n : Nat) (x : m α) : m α :=
  withCurrHeartbeats <| withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := n * 1000 }) x

/-- Maximum recursion depth allowed for each discharge attempt. -/
def dischargeMaxRecDepth : Nat := 8192

/-- Execute `x` within a bounded resource budget (heartbeats and recursion depth) and return `none`
    on any exception, including runtime exceptions (e.g., heartbeats or maximum recursion depth).
    The state is restored on failure.
-/
def attempt [Monad m] [MonadBacktrack s m] [MonadExcept Exception m] [MonadRuntimeException m]
  [MonadWithReaderOf Core.Context m] [MonadLiftT BaseIO m] [MonadControlT CoreM m]
  [MonadStateOf Core.State m]
  (budget : Nat) (x : m (Option α)) : m (Option α) := do
  let st ← saveState
  -- NOTE: asynchronous subtasks spawned by a failed attempt (e.g., the on-demand generation of
  -- auxiliary lemmas) are discarded, such that their errors are not reported.
  let tasks := (← getThe Core.State).snapshotTasks
  let failed : m (Option α) := do
    restoreState st
    modifyThe Core.State fun s => { s with snapshotTasks := tasks }
    return none
  tryCatchRuntimeEx
    (do
      let r ← withHeartbeatBudget budget <|
        withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := dischargeMaxRecDepth }) x
      if r.isNone then failed else return r)
    (fun _ => failed)

/-- Try to close goal `type` with tactic `tac`. The elaboration state is restored on failure. -/
def proveWithTactic (type : Expr) (tac : TSyntax `tactic) (budget := dischargeHeartbeats) : TermElabM (Option Expr) := do
  let s ← saveState
  -- NOTE: info trees and messages produced by internal tactic runs are discarded (e.g., linters
  -- would process the info trees).
  let infoState ← getInfoState
  let msgs ← Core.getMessageLog
  -- NOTE: Diagnostics reported asynchronously during an attempt (e.g., failures when generating the
  -- equations of a matcher via `realizeConst`) are discarded, as they don't affect the resulting proof.
  let tasks := (← getThe Core.State).snapshotTasks
  let r ← try
      attempt budget do
        let mvar ← mkFreshExprMVar type
        -- NOTE: asynchronous elaboration is disabled such that kernel errors on auxiliary declarations
        -- created by tactics are reported as exceptions instead of messages.
        let gs ← withOptions (fun o => Elab.async.set o false) <|
                   withoutErrToSorry <| Tactic.run mvar.mvarId! (evalTactic tac)
        let prf ← instantiateMVars mvar
        if !gs.isEmpty || prf.hasMVar || prf.hasSorry then return none
        return some prf
    finally modifyThe Core.State fun st => { st with snapshotTasks := tasks }
  if r.isNone then s.restore
  setInfoState infoState
  Core.setMessageLog msgs
  return r

/-- Try to prove `lhs = rhs` by definitional unfolding. -/
def proveByDefEq (type : Expr) (budget := dischargeHeartbeats) : MetaM (Option Expr) := do
  let some (_, lhs, rhs) := type.eq? | return none
  attempt budget do
    if ← withTransparency .default <| isDefEq lhs rhs then
      return some (← mkExpectedTypeHint (← mkEqRefl lhs) type)
    return none

/-- Return `true` if `type` is type correct. -/
def isTypeCorrectObligation (type : Expr) : MetaM Bool := do
  return (← attempt dischargeHeartbeats (do Meta.check type; return some ())).isSome

/-! ## Unfolding user definitions

The SMT solver receives the definitions of the (recursive) functions occurring in the residual
goal. Lean decision procedures do not unfold them automatically. The following tactics unfold
definitions that are not part of the Lean/Blaster libraries and perform a bounded case analysis
on variables of inductive types.
-/

/-- Return `true` if `n` is a user definition, i.e., a definition not defined in Lean's core libraries. -/
def isUserDefinition (env : Environment) (n : Name) : Bool := Id.run do
  let some info := env.find? n | return false
  if !info.isDefinition || isAuxRecursor env n || isMatcherCore env n then return false
  match env.getModuleIdxFor? n with
  | none => return true
  | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      return !(mod.getRoot ∈ [`Init, `Lean, `Std, `Lake, `Blaster])

syntax (name := blasterUnfoldUser) "blaster_unfold_user" : tactic

/-- Unfold (up to 5 rounds) the user definitions occurring in the main goal and its hypotheses. -/
@[tactic blasterUnfoldUser] def evalBlasterUnfoldUser : Tactic := fun _ => do
  let env ← getEnv
  for _ in [0:5] do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let mut t ← instantiateMVars (← g.getType)
    for d in ← g.withContext getLCtx do
      if !d.isImplementationDetail then t := mkApp t (← instantiateMVars d.type)
    let consts := t.getUsedConstants.filter (isUserDefinition env)
    if consts.isEmpty then return
    -- NOTE: `simp` does not rewrite instance arguments, user instances (e.g., derived `BEq`
    -- instances) are unfolded with `delta` instead.
    let mut insts := #[]
    let mut defs := #[]
    for n in consts do
      if ← isInstance n then insts := insts.push n else defs := defs.push n
    let mut progress := false
    if !insts.isEmpty then
      let ids := insts.map mkIdent
      try
        evalTactic (← `(tactic| delta $ids* at *))
        progress := true
      catch _ => pure ()
    if !defs.isEmpty then
      let lemmas ← defs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
      try
        evalTactic (← `(tactic| simp only [$lemmas,*] at *))
        progress := true
      catch _ => pure ()
    if !progress then return

/-- Maximum number of goals produced by `blaster_cases_vars`. -/
def maxCaseGoals : Nat := 128

syntax (name := blasterCasesVars) "blaster_cases_vars" (num)? : tactic
/-- Same as `blaster_cases_vars` but only for variables of non-recursive types (e.g., structures, enumerations). -/
syntax (name := blasterCasesNonRec) "blaster_cases_nonrec" (num)? : tactic

/-- Return the variables of (non-indexed) inductive types in the local context of `g`, together
    with their number of constructors.
-/
def inductiveVars (g : MVarId) (nonRec := false) : MetaM (Array (FVarId × Nat)) := g.withContext do
  let mut vars := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← whnfR d.type
    let .const n _ := t.getAppFn | continue
    let .inductInfo info ← getConstInfo n | continue
    if info.numIndices != 0 || (← isProp d.type) then continue
    -- NOTE: integers are handled by arithmetic decision procedures instead
    if nonRec && (info.isRec || n == ``Int) then continue
    vars := vars.push (d.fvarId, info.ctors.length)
  return vars

/-- Perform case analysis on the variables of inductive types (bounded by `maxCaseGoals`). The fields
    of the constructors are themselves case-analyzed (up to four rounds), e.g., for structures.
-/
def casesVars (maxCaseGoals : Nat) (nonRecOnly : Bool) : TacticM Unit := do
  let mut goals := [← getMainGoal]
  let mut done : Std.HashSet FVarId := {}
  for round in [0:4] do
    let mut progress := false
    let mut newGoals := []
    -- NOTE: goals share the free variables of their common ancestor
    let doneBefore := done
    for g in goals do
      -- NOTE: only fields of non-recursive types are case-analyzed (e.g., not `Nat` fields)
      let vars := (← inductiveVars g (nonRec := nonRecOnly || round > 0)).filter (!doneBefore.contains ·.1)
      let mut gs := [g]
      for (v, nbCtors) in vars do
        if (goals.length + newGoals.length + gs.length) * nbCtors > maxCaseGoals then break
        let mut gs' := []
        for g' in gs do
          -- the variable may have been substituted in some goals
          if !(← g'.withContext (return (← getLCtx).contains v)) then
            gs' := gs' ++ [g']
            continue
          let subgoals ← g'.cases v
          gs' := gs' ++ subgoals.toList.map (·.mvarId)
        gs := gs'
        done := done.insert v
        progress := true
      newGoals := newGoals ++ gs
    goals := newGoals
    if !progress then
      if round == 0 && nonRecOnly then throwError "blaster_cases_nonrec: no variable"
      break
  replaceMainGoal goals

@[tactic blasterCasesVars] def evalBlasterCasesVars : Tactic := fun stx =>
  casesVars (if stx[1].isNone then maxCaseGoals else stx[1][0].toNat) false

@[tactic blasterCasesNonRec] def evalBlasterCasesNonRec : Tactic := fun stx =>
  casesVars (if stx[1].isNone then maxCaseGoals else stx[1][0].toNat) true

syntax (name := introFacts) "intro_facts" : tactic

/-- Introduce the leading `blaster_fact` hypotheses (see `dischargeWithFacts`). -/
@[tactic introFacts] def evalIntroFacts : Tactic := fun _ => do
  let mut g ← getMainGoal
  repeat
    let .forallE n _ _ _ := (← whnfR (← g.getType)) | break
    if n != `blaster_fact then break
    let (_, g') ← g.intro (← mkFreshUserName `blaster_fact)
    g := g'
  replaceMainGoal [g]

/-! ## Existential witnesses

The SMT solver proves `∃ x, P x` without providing a witness. For `Nat`/`Int` existentials, a few
candidate witnesses built from the variables in context are tried, the remaining goal being closed by `omega`.
-/

syntax (name := blasterDivModFacts) "blaster_divmod_facts" : tactic

/-- Add the basic facts on each `a / b` and `a % b` (over `Nat`) occurring in the main goal, i.e.,
    `b * (a / b) + a % b = a`, `a / b ≤ a`, and, when `0 < b` holds by `omega`, `a % b < b` and
    `a < b * (a / b + 1)`.
-/
@[tactic blasterDivModFacts] def evalBlasterDivModFacts : Tactic := fun _ => do
  let g ← getMainGoal
  let pairs ← g.withContext do
    let mut ts := #[← instantiateMVars (← g.getType)]
    for d in ← getLCtx do
      if !d.isImplementationDetail then ts := ts.push (← instantiateMVars d.type)
    let mut pairs : Array (Expr × Expr) := #[]
    for t in ts do
      for s in collect t #[] do
        if !pairs.contains s then pairs := pairs.push s
    return pairs
  for (a, b) in pairs.extract 0 8 do
    withMainContext do
      let a ← Term.exprToSyntax a
      let b ← Term.exprToSyntax b
      evalTactic (← `(tactic| (have := Nat.div_add_mod $a $b; have := Nat.div_le_self $a $b;
                               (try have := Nat.mod_lt $a (show 0 < $b by omega));
                               (try have := Nat.lt_mul_div_succ $a (show 0 < $b by omega)))))
where
  collect (e : Expr) (acc : Array (Expr × Expr)) : Array (Expr × Expr) :=
    let acc := match e.getAppFn, e.getAppArgs with
      | .const n _, args =>
          if (n == ``HDiv.hDiv || n == ``HMod.hMod) && args.size == 6 && args[0]!.isConstOf ``Nat
             && !e.hasLooseBVars then
            acc.push (args[4]!, args[5]!)
          else acc
      | _, _ => acc
    match e with
    | .app f a => collect a (collect f acc)
    | .lam _ t b _ | .forallE _ t b _ => collect b (collect t acc)
    | .letE _ t v b _ => collect b (collect v (collect t acc))
    | .mdata _ e | .proj _ _ e => collect e acc
    | _ => acc

syntax (name := blasterLitAdd) "blaster_lit_add" : tactic

/-- Rewrite `k + n` into `n + k` (over `Nat`), for every numeral `k` and non-numeral `n`, i.e.,
    the form expected by equation lemmas of recursive functions (e.g., `f (n + 1) = ...`).
-/
@[tactic blasterLitAdd] def evalBlasterLitAdd : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let mut ts := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    if !d.isImplementationDetail then ts := ts.push (← instantiateMVars d.type)
  let mut pairs : Array (Expr × Expr) := #[]
  for t in ts do
    for s in collect t #[] do
      if !pairs.contains s then pairs := pairs.push s
  if pairs.isEmpty then throwError "blaster_lit_add: no numeral addition"
  let mut lemmas := #[]
  for (k, n) in pairs.extract 0 8 do
    lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma|
      Nat.add_comm $(← Term.exprToSyntax k) $(← Term.exprToSyntax n)))
  evalTactic (← `(tactic| simp only [$lemmas,*] at *))
where
  collect (e : Expr) (acc : Array (Expr × Expr)) : Array (Expr × Expr) :=
    let acc := match e.getAppFn, e.getAppArgs with
      | .const n _, args =>
          if n == ``HAdd.hAdd && args.size == 6 && args[0]!.isConstOf ``Nat && !e.hasLooseBVars
             && (args[4]!.nat?).isSome && (args[5]!.nat?).isNone then
            acc.push (args[4]!, args[5]!)
          else acc
      | _, _ => acc
    match e with
    | .app f a => collect a (collect f acc)
    | .lam _ t b _ | .forallE _ t b _ => collect b (collect t acc)
    | .letE _ t v b _ => collect b (collect v (collect t acc))
    | .mdata _ e | .proj _ _ e => collect e acc
    | _ => acc

syntax (name := blasterByCases) "blaster_by_cases" : tactic

/-- Case analysis on the conditions of the `dite`/`ite` expressions of the main goal (up to 3 conditions),
    including those applied to additional arguments (not supported by `split`).
-/
@[tactic blasterByCases] def evalBlasterByCases : Tactic := fun _ => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let conds := collect target #[]
  if conds.isEmpty then throwError "blaster_by_cases: no condition"
  for c in conds.extract 0 3 do
    let c ← Term.exprToSyntax c
    evalTactic (← `(tactic| all_goals by_cases $c))
where
  collect (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := match e.getAppFn with
      | .const n _ =>
          if (n == ``dite || n == ``ite) && e.getAppNumArgs ≥ 5 then
            let c := e.getArg! 1
            if c.hasLooseBVars || acc.contains c then acc else acc.push c
          else acc
      | _ => acc
    match e with
    | .app f a => collect a (collect f acc)
    | .lam _ t b _ | .forallE _ t b _ => collect b (collect t acc)
    | .letE _ t v b _ => collect b (collect v (collect t acc))
    | .mdata _ e | .proj _ _ e => collect e acc
    | _ => acc

syntax (name := blasterExists) "blaster_exists" : tactic

/-- Return the natural number literals occurring in `e` (and their neighbours). -/
def literalSeeds (e : Expr) : Array Nat := Id.run do
  let mut ns : Std.HashSet Nat := {0, 1}
  let rec collect (e : Expr) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
    match e with
    | .lit (.natVal n) => (acc.insert n).insert (n + 1) |>.insert (n - 1)
    | .app f a => collect a (collect f acc)
    | .lam _ t b _ | .forallE _ t b _ => collect b (collect t acc)
    | .mdata _ b => collect b acc
    | .letE _ t v b _ => collect b (collect v (collect t acc))
    | _ => acc
  ns := collect e ns
  return ns.toArray.qsort (· < ·)

/-- Candidate witnesses (as terms) of type `t` up to `depth` nested constructors. -/
partial def witnessCandidates (t : Expr) (seeds : Array Nat) (vars : Array Ident) (depth : Nat) :
    MetaM (Array Term) := do
  let t ← whnfR t
  if t.isConstOf ``Nat || t.isConstOf ``Int then
    let mut cs : Array Term := #[]
    for n in seeds do cs := cs.push (← `($(Syntax.mkNumLit (toString n))))
    for x in vars do cs := cs ++ #[← `($x), ← `($x - 1), ← `($x + 1)]
    return cs
  let .const n _ := t.getAppFn | return #[]
  let .inductInfo info ← getConstInfo n | return #[]
  if info.numIndices != 0 then return #[]
  let mut cs : Array Term := #[]
  for ctor in info.ctors do
    let cinfo ← getConstInfo ctor
    let fieldsOk ← forallTelescopeReducing cinfo.type fun xs _ => do
      let fields := xs.extract info.numParams xs.size
      let mut args : Array (Array Term) := #[#[]]
      for x in fields do
        let xt ← inferType x
        let opts ← if (← isProp xt) then pure #[← `(?_)]
          else if depth == 0 && (xt.getAppFn.constName? == some n) then pure #[]
          else witnessCandidates xt seeds #[] (if xt.getAppFn.constName? == some n then depth - 1 else depth)
        if opts.isEmpty then return none
        let mut next := #[]
        for a in args do
          for o in opts.extract 0 6 do
            if next.size < 64 then next := next.push (a.push o)
        args := next
      return some args
    let some argss := fieldsOk | continue
    for args in argss do
      cs := cs.push (← `($(mkIdent ctor) $args*))
  return cs.extract 0 64

@[tactic blasterExists] def evalBlasterExists : Tactic := fun _ => do
  let g ← getMainGoal
  let target ← instantiateMVars (← g.getType)
  let some (_, .lam _ t _ _) := (← whnfR target).app2? ``Exists
    | throwError "blaster_exists: existential expected"
  let mut vars : Array Ident := #[]
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail || d.userName.isInaccessibleUserName then continue
    if ← g.withContext (isDefEq d.type t) then vars := vars.push (mkIdent d.userName)
  let candidates ← g.withContext (witnessCandidates t (literalSeeds target) vars 2)
  let s ← saveState
  for c in candidates do
    try
      evalTactic (← `(tactic| (refine ⟨$c, ?_⟩ <;>
        (try blaster_unfold_user) <;> first | omega | decide | (simp_all; done) | (simp_all <;> omega))))
      if (← getUnsolvedGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "blaster_exists: no witness found"

/-! ## Equivalence of recursive functions

The optimizer replaces a recursive function with a structurally equivalent one (see `storeRecFunDef`),
e.g., a user-defined `power` with `Nat.pow`. Such rewrites are justified by induction.
-/

/-- Return `true` if `f` is defined by structural or well-founded recursion.
    NOTE: functional induction principles are generated on demand and their generation is costly,
    e.g., for non-recursive functions with large `match` expressions.
-/
def isRecursiveDef (env : Environment) (f : Name) : Bool := Id.run do
  if env.contains (f ++ `_unary) then return true
  let some info := env.find? f | return false
  let some v := info.value? | return false
  return v.getUsedConstants.any fun n =>
    n == f || n == ``WellFounded.fix || (n.isStr && n.getString! == "brecOn")

/-- Return the applications of recursive user functions in the main goal, i.e., the candidates for
    functional induction (at most 4).
-/
partial def funInductionCandidates : TacticM (Array Expr) := do
  let g ← getMainGoal
  g.withContext do
    let env ← getEnv
    let target ← instantiateMVars (← g.getType)
    let mut res := #[]
    for app in collectApps target #[] do
      let .const f _ := app.getAppFn | continue
      if !isUserDefinition env f || !(isRecursiveDef env f) then continue
      if res.any (·.getAppFn == app.getAppFn) || res.size ≥ 4 then continue
      res := res.push app
    return res
where
  collectApps (e : Expr) (acc : Array Expr) : Array Expr :=
    match e with
    | .app .. =>
        let acc := if e.getAppFn.isConst && !e.hasLooseBVars then acc.push e else acc
        e.getAppArgs.foldl (fun acc a => collectApps a acc) acc
    | .lam _ t b _ | .forallE _ t b _ => collectApps b (collectApps t acc)
    | .letE _ t v b _ => collectApps b (collectApps v (collectApps t acc))
    | .mdata _ e | .proj _ _ e => collectApps e acc
    | _ => acc

/-- Return the head functions of both sides of the main goal `lhs = rhs` that can be unfolded. -/
def eqHeads : TacticM (Array Name) := do
  let g ← getMainGoal
  g.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? | return #[]
    let env ← getEnv
    let mut res := #[]
    for side in [lhs, rhs] do
      let .const f _ := side.getAppFn | continue
      let some info := env.find? f | continue
      if !info.isDefinition || isMatcherCore env f || isAuxRecursor env f then continue
      if (← isInstance f) then continue
      res := res.push f
    return res

syntax (name := blasterFunInd) "blaster_funind" : tactic

/-- Prove `f = g` (or `f a₁ ... aₙ = g a₁ ... aₙ`) by function extensionality and induction on
    one of the arguments, unfolding user definitions in each case.
-/
@[tactic blasterFunInd] def evalBlasterFunInd : Tactic := fun _ => do
  -- function extensionality
  let mut vars : Array Ident := #[]
  for i in [0:8] do
    let g ← getMainGoal
    let some (t, _, _) := (← whnfR (← instantiateMVars (← g.getType))).eq? | break
    if !(← whnfR t).isForall then break
    let x := mkIdent (Name.mkSimple s!"x_{i}")
    evalTactic (← `(tactic| (apply funext; intro $x:ident)))
    vars := vars.push x
  -- variables of the goal (when not a function equality): give them accessible names
  if vars.isEmpty then
    evalTactic (← `(tactic| intros))
    let g ← getMainGoal
    let target ← instantiateMVars (← g.getType)
    let mut g := g
    for d in ← g.withContext getLCtx do
      if d.isImplementationDetail || !target.containsFVar d.fvarId then continue
      if (← g.withContext (isProp d.type)) then continue
      let n := Name.mkSimple s!"y_{vars.size}"
      g ← g.rename d.fvarId n
      vars := vars.push (mkIdent n)
    replaceMainGoal [g]
  if vars.isEmpty then throwError "blaster_funind: no variable"
  -- clear the hypotheses not related to the equation (they only hinder the induction)
  let g ← getMainGoal
  let g ← g.withContext do
    let target ← instantiateMVars (← g.getType)
    let mut g := g
    for d in (← getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail || target.containsFVar d.fvarId then continue
      -- keep the facts introduced by `intro_facts`
      if d.userName.toString.startsWith "blaster_fact" then continue
      try g ← g.clear d.fvarId catch _ => pure ()
    return g
  replaceMainGoal [g]
  let finish ← `(tactic| (blaster_unfold_user <;> blaster_denorm <;>
                           (try simp_all [Nat.pow_succ, Int.pow_succ]) <;> grind))
  let mut alts : Array (TSyntax `tactic) := #[]
  -- functional induction following the recursion of a user function occurring in the equation
  let heads ← eqHeads
  for app in ← funInductionCandidates do
    let t ← Term.exprToSyntax app
    -- NOTE: the function inducted on is already unfolded by `fun_induction` (unfolding it again may loop)
    let heads := heads.filter (· != app.getAppFn.constName!)
    let lemmas ← heads.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    alts := alts.push (← `(tactic| (fun_induction $t:term <;> blaster_denorm <;>
                                     (try simp_all [$lemmas,*]) <;> grind)))
    alts := alts.push (← `(tactic| (fun_induction $t:term <;> $finish)))
    alts := alts.push (← `(tactic| (fun_induction $t:term <;> (try cases ‹Nat›) <;> $finish)))
  -- try induction on each variable (last one first), then with the other variables generalized
  for x in vars.reverse do
    alts := alts.push (← `(tactic| (induction $x:ident <;> $finish)))
  for x in vars do
    let others := vars.filter (· != x)
    if others.isEmpty then continue
    alts := alts.push (← `(tactic| (induction $x:ident generalizing $others* <;>
                                     (try (cases $(others[0]!):ident)) <;> $finish)))
  let s ← saveState
  for tac in alts do
    try
      evalTactic tac
      if (← getUnsolvedGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "blaster_funind: failed"

/-- Maximum number of alternatives of a `match` expression for case analysis strategies. -/
def maxMatchAlts : Nat := 32

/-- Return `true` if `e` contains a matcher with more than `maxMatchAlts` alternatives, possibly
    within the body of a (non-recursive) user definition occurring in `e`.
-/
def involvesLargeMatch (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let isLarge (n : Name) : MetaM Bool := do
    let some info ← getMatcherInfo? n | return false
    return info.numAlts > maxMatchAlts
  for n in e.getUsedConstants do
    if ← isLarge n then return true
    if isUserDefinition env n then
      let some v := (env.find? n).bind (·.value?) | continue
      for m in v.getUsedConstants do
        if ← isLarge m then return true
  return false

/-- Case analysis on variables of non-recursive inductive types, producing up to 1024 goals, then unfolding of user definitions. -/
def deepCases : TermElabM (TSyntax `tactic) :=
  `(tactic| (intros <;> blaster_denorm <;> blaster_cases_nonrec 1024 <;> blaster_unfold_user <;>
             (try simp_all) <;> (try blaster_unfold_user) <;>
             (try simp_all [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]) <;>
             (try decide) <;> first | done | ((repeat' split) <;> (try simp_all) <;> omega)))

/-- The portfolio of tactics used to discharge proof obligations, in order of application. -/
def dischargeTactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("simp", ← `(tactic| (blaster_denorm <;> simp [*] <;> done))),
    ("omega", ← `(tactic| ((try apply propext) <;> blaster_denorm <;> omega))),
    ("grind", ← `(tactic| (blaster_denorm <;> grind))),
    -- cancellation of non-zero divisors (side conditions proved by `omega`)
    ("arith simp", ← `(tactic| (blaster_denorm <;>
        simp (disch := omega) only [Nat.mul_div_cancel, Nat.mul_div_cancel_left, Nat.mul_mod_left,
          Nat.mul_mod_right, Nat.div_self, Nat.mod_self, Int.mul_ediv_cancel, Int.mul_ediv_cancel_left,
          Int.mul_emod_left, Int.mul_emod_right, Int.ediv_self, Int.emod_self] <;> done))),
    -- case analysis (e.g., `match` expressions normalized to `Blaster.dite'`)
    ("split", ← `(tactic| (blaster_denorm <;> (repeat' split) <;> first | omega | (simp_all; done) | grind))),
    -- case analysis on conditions applied to additional arguments
    ("split", ← `(tactic| (blaster_denorm <;> blaster_by_cases <;> (try simp_all [Int.sub_eq_add_neg]) <;>
                          first | done | omega | grind))),
    -- case analysis with cancellation of non-zero factors
    ("split", ← `(tactic| (blaster_denorm <;> (repeat' split) <;> (try simp_all) <;> (try blaster_mul_cancel) <;>
                          first | (simp_all; done) | omega | grind))),
    -- case analysis on inductive variables (e.g., derived `BEq` instances)
    ("cases", ← `(tactic| (blaster_denorm <;> blaster_cases_vars <;> blaster_unfold_user <;>
                          (try simp_all) <;> (try blaster_unfold_user) <;>
                          (try simp_all [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]) <;>
                          (try decide) <;> first | done | ((repeat' split) <;> (try simp_all) <;> omega)))),
    -- equivalence of recursive functions
    ("induction", ← `(tactic| blaster_funind))
  ]

/-- Maximum number of nested case splits over `match` alternatives (see `proveByMatchCases`). -/
def matchCasesDepth : Nat := 2

/-- Maximum number of alternatives considered for a case split over a `match` (see `proveByMatchCases`). -/
def matchCasesMaxAlts : Nat := 32

/-- Given a `match` application `m` with discriminants `ds` and `rhs`, return `rhs` with the occurrences
    of the discriminants abstracted, i.e., `rhsFn xs := rhs[xs/ds]`.
-/
def abstractDiscrs (ds : Array Expr) (rhs : Expr) : MetaM Expr := do
  let types ← ds.mapM inferType
  withLocalDeclsDND (types.map (`x, ·)) fun ys => do
    let mut r := rhs
    for d in ds, y in ys do
      r := (← kabstract r d).instantiate1 y
    return r.abstract ys

mutual
/-- Try to discharge proof obligation `type` (expected to be an equality) and return
    the proof together with the method used.
-/
partial def dischargeOne (type : Expr) (depth := matchCasesDepth) : TermElabM (Option (Expr × String)) := do
  let type ← instantiateMVars type
  -- ill-typed proof obligations (e.g., due to ill-typed optimized expressions) can't be discharged
  if !(← isTypeCorrectObligation type) then
    if (← IO.getEnv "BLASTER_RECON_DEBUG").isSome then
      try Meta.check type catch ex => logInfo m!"ill-typed proof obligation: {ex.toMessageData}"
    return none
  if let some prf ← proveByDefEq type then return some (prf, "rfl")
  -- closed obligations (e.g., concrete computations) are decided by kernel evaluation
  if !type.hasFVar && !type.hasMVar then
    if let some prf ← proveWithTactic type (← `(tactic| decide +kernel)) then return some (prf, "decide")
  -- NOTE: case analysis on (or unfolding of) large `match` expressions requires the generation of
  -- costly auxiliary lemmas (e.g., splitters), which are not subject to the discharge budget.
  let large ← involvesLargeMatch type
  for (name, tac) in (← dischargeTactics) do
    if large && name ∈ ["split", "cases", "induction"] then continue
    if let some prf ← proveWithTactic type tac then return some (prf, name)
  -- deeper case analysis with a larger budget (e.g., equality of nested structures)
  if !large then
    if let some prf ← proveWithTactic type (← deepCases) (budget := 8 * dischargeHeartbeats) then
      return some (prf, "cases")
  if let some prf ← proveByMatchCases type depth then return some (prf, "match cases")
  return none

/-- Try to discharge `m = rhs` (or `rhs = m`) with `m` a `match` application by a case split over the
    alternatives of `m` via its splitter (see `mkMatchCasesProof`). The obligation for each alternative,
    i.e., `altᵢ args = rhs[pᵢ/ds]`, is discharged in a local context with the equalities between the
    discriminants and the patterns, as well as the overlap hypotheses of the splitter.
-/
partial def proveByMatchCases (type : Expr) (depth : Nat) : TermElabM (Option Expr) := do
  if depth == 0 then return none
  let some (_, lhs, rhs) := type.eq? | return none
  let (m, other, symm) ←
    if ← isMatchCasesApp lhs then pure (lhs, rhs, false)
    else if ← isMatchCasesApp rhs then pure (rhs, lhs, true)
    else return none
  let some app ← matchMatcherApp? m (alsoCasesOn := true) | return none
  if app.alts.size > matchCasesMaxAlts then return none
  let altPf (_ : Nat) (_ : Array Expr) (_ : Array Expr) (alt rhsᵢ : Expr) : TermElabM Expr := do
    let goal ← mkEq alt rhsᵢ
    match ← dischargeOne goal (depth - 1) with
    | some (p, _) => return p
    | none => throwError "proveByMatchCases: alternative not discharged"
  let attemptWith (rhsFn : Array Expr → MetaM Expr) : TermElabM (Option Expr) := do
    let s ← saveState
    let r ← attempt dischargeHeartbeats do
      try
        let p ← mkMatchCasesProof m (fun xs => rhsFn xs) altPf
        let p ← if symm then mkEqSymm p else pure p
        if ← isDefEq (← inferType p) type then return some p
        return none
      catch _ => return none
    if r.isNone then s.restore
    return r
  -- substitute the patterns for the discriminants in `rhs` first
  let abst? ← try some <$> abstractDiscrs app.discrs other catch _ => pure none
  if let some abst := abst? then
    if abst.hasLooseBVars then
      if let some p ← attemptWith (fun xs => pure (abst.instantiateRev xs)) then return some p
  attemptWith (fun _ => pure other)
end

/-- Return the type of a hole, i.e., `t` in `mdata {blaster.hole := _} (sorryAx t _)`. -/
def holeType? (e : Expr) : Option Expr := do
  let _ ← isHole? e
  match e.consumeMData with
  | .app (.app (.const ``sorryAx _) t) _ => some t
  | _ => none

/-- Generalize a discharged equation `prf : type` over the free variables it depends on, i.e., return
    `(∀ xs, type, fun xs => prf)`. Used to reuse equivalences of recursive functions as lemmas.
-/
def generalizeFact (type prf : Expr) : MetaM (Option (Expr × Expr)) := do
  let lctx ← getLCtx
  let fvars := (collectFVars {} (← instantiateMVars type)).fvarIds
  let fvars := fvars.filter lctx.contains
  let fvars := (lctx.getFVarIds.filter fvars.contains).map mkFVar
  let t ← mkForallFVars fvars type
  let p ← mkLambdaFVars fvars prf
  if t.hasFVar || p.hasFVar || t.hasMVar || p.hasMVar then return none
  return some (t, p)

/-- Try to discharge `type` with the induction strategy given the previously proved `facts`
    (i.e., closed equations between recursive functions) as additional hypotheses.
-/
def dischargeWithFacts (type : Expr) (facts : Array (Expr × Expr)) : TermElabM (Option Expr) := do
  if facts.isEmpty then return none
  let type' := facts.foldr (fun (t, _) acc => mkForall `blaster_fact .default t acc) type
  let tac ← `(tactic| (intro_facts; blaster_funind))
  let some prf ← proveWithTactic type' tac | return none
  return some (mkAppN prf (facts.map Prod.snd))

/-- Prove the equivalences `f = g` between recursive functions established by the optimizer (in order),
    each one using the previously proved ones as hypotheses. Return the proved equations.
-/
def proveEquivalences (equivs : Array (Expr × Expr)) : TermElabM (Array (Expr × Expr)) := do
  let mut facts := #[]
  for (f, g) in equivs do
    let r ← attempt (4 * dischargeHeartbeats) do
      let type ← mkEq f g
      if let some prf ← dischargeWithFacts type facts then return some (type, prf)
      if let some prf ← proveWithTactic type (← `(tactic| blaster_funind)) then return some (type, prf)
      return none
    if let some fact := r then facts := facts.push fact
  return facts

/-- Traverse `e` and replace each subterm `s` such that `f s = some r` with `r`.
    NOTE: Unlike `Meta.transform`, results are only shared within the same binder scope. Proof obligations
    are closed terms, but their proofs may depend on the hypotheses of the local context (e.g., `simp [*]`).
    Hence, the same obligation occurring under different binders must be discharged in each context.
-/
partial def transformScoped (e : Expr) (f : Expr → TermElabM (Option Expr)) : TermElabM Expr := do
  go (← IO.mkRef {}) e
where
  go (cache : IO.Ref (Std.HashMap ExprStructEq Expr)) (e : Expr) : TermElabM Expr := do
    if let some r := (← cache.get).get? e then return r
    let r ← match ← f e with
      | some r => pure r
      | none => visit cache e
    cache.modify (·.insert e r)
    return r

  visit (cache : IO.Ref (Std.HashMap ExprStructEq Expr)) (e : Expr) : TermElabM Expr := do
    match e with
    | .app fn a => return e.updateApp! (← go cache fn) (← go cache a)
    | .mdata _ b => return e.updateMData! (← go cache b)
    | .proj _ _ b => return e.updateProj! (← go cache b)
    | .lam n t b bi =>
        let t ← go cache t
        withLocalDecl n bi t fun x => do mkLambdaFVars #[x] (← go (← IO.mkRef {}) (b.instantiate1 x))
    | .forallE n t b bi =>
        let t ← go cache t
        withLocalDecl n bi t fun x => do mkForallFVars #[x] (← go (← IO.mkRef {}) (b.instantiate1 x))
    | .letE n t v b _ =>
        let t ← go cache t
        let v ← go cache v
        withLetDecl n t v fun x => do mkLetFVars #[x] (← go (← IO.mkRef {}) (b.instantiate1 x))
    | _ => return e

/-- Discharge all the proof obligations in `p`.
    Return the updated proof term and the discharge statistics. Proof obligations that cannot be
    discharged are left unchanged in the returned proof term.
    NOTE: A second pass is performed on the remaining obligations, using the equivalences between
    recursive functions proved during the first pass as hypotheses (nested equivalences).
    NOTE: A fallback region `r : lhs = rhs` (see `fallbackKey`) is replaced with a proof of `lhs = rhs`
    discharged as a whole when one of its proof obligations cannot be discharged.
-/
partial def dischargeHoles
  (p : Expr) (holes : Array HoleInfo := #[]) (equivs : Array (Expr × Expr) := #[]) :
  TermElabM (Expr × DischargeStats) := do
  let stats ← IO.mkRef ({} : DischargeStats)
  let facts ← IO.mkRef (← proveEquivalences equivs)
  let labelOf (e : Expr) : String :=
    match isHole? e with
    | some idx => if h : idx < holes.size then holes[idx].label else "top"
    | none => "top"
  -- first pass
  let p' ← transformScoped p fun e => do
    match holeType? e with
    | none => return none
    | some type =>
        let label := labelOf e
        stats.modify fun s => { s with total := s.total + 1 }
        match ← dischargeOne type with
        | some (prf, method) =>
            stats.modify (·.record method label)
            if label.startsWith "rule:recFunEquiv" then
              if let some f ← generalizeFact type prf then facts.modify (·.push f)
            return some prf
        | none => return some e
  -- second pass (with proved equivalences as hypotheses), fallback regions and failure reporting
  let (p', st) ← secondPass (← facts.get) labelOf p'
  return (p', (← stats.get).merge st)

  where
    secondPass (facts : Array (Expr × Expr)) (labelOf : Expr → String) (p : Expr) :
      TermElabM (Expr × DischargeStats) := do
      let stats ← IO.mkRef ({} : DischargeStats)
      let p' ← transformScoped p fun e => do
        if isFallback e then
          let inner := e.consumeMData
          let (inner', st) ← secondPass facts labelOf inner
          if st.failures.isEmpty && !hasHoles inner' then
            stats.modify (·.merge st)
            return some inner'
          -- discharge the region as a whole
          if let some type ← observing? (do instantiateMVars (← inferType inner)) then
            let label := s!"fallback:{headSymbol (type.eq?.map (·.2.1) |>.getD type)}"
            stats.modify fun s => { s with total := s.total + 1 }
            if let some (prf, method) ← dischargeOne type then
              stats.modify (·.record method label)
              return some prf
            if let some prf ← dischargeWithFacts type facts then
              stats.modify (·.record "induction+facts" label)
              return some prf
            stats.modify (·.record "failed" label)
          stats.modify (·.merge st)
          return some inner'
        match holeType? e with
        | none => return none
        | some type =>
            let label := labelOf e
            if let some prf ← dischargeWithFacts type facts then
              stats.modify (·.record "induction+facts" label)
              return some prf
            -- NOTE: unsound eliminations of unused binders are reported separately
            let unsound ← try isUnsoundBinderElim type catch _ => pure false
            stats.modify (·.record (if unsound then "refused:unsound" else "failed") label)
            if (← IO.getEnv "BLASTER_RECON_DEBUG").isSome then
              let g ← mkFreshExprMVar type
              logInfo m!"[{label}] unresolved proof obligation:\n{← Meta.ppGoal g.mvarId!}"
            let lctx ← getLCtx
            let dangling := (type.find? fun s => s.isFVar && !lctx.contains s.fvarId!).isSome
            let msg ← addMessageContext (if dangling then m!"{type} (out of scope variables)" else m!"{type}")
            stats.modify fun s => { s with failures := s.failures.push msg }
            return some e
      return (p', ← stats.get)

/-! ## Seeded quantifier instantiation

SMT solvers frequently prove goals by instantiating universally quantified hypotheses with terms
that do not occur in the goal (e.g., `(∀ n : Nat, 0 < n) → P` is valid as `0 < 0` is false).
E-matching based procedures (e.g., `grind`) fail on such goals. As a first approximation, we
specialize universally quantified hypotheses with a few seed values of the quantified type.
-/

/-- Return seed values for type `t`. -/
def seedsFor (t : Expr) : MetaM (Array Expr) := do
  match ← whnfR t with
  | .const ``Nat _ => return #[mkNatLit 0, mkNatLit 1]
  | .const ``Int _ => return #[toExpr (0 : Int), toExpr (1 : Int), toExpr (-1 : Int)]
  | .const ``Bool _ => return #[toExpr true, toExpr false]
  | .sort .zero => return #[mkConst ``False, mkConst ``True]
  | _ => return #[]

/-- Return the specializations of `p : ty` (up to `depth` quantifiers) w.r.t. seed values. -/
partial def specializeWithSeeds (p ty : Expr) (depth : Nat) : MetaM (Array (Expr × Expr)) := do
  if depth == 0 then return #[]
  let .forallE _ d b _ ← whnfR ty | return #[]
  let mut res := #[]
  for s in ← seedsFor d do
    let p' := mkApp p s
    let ty' := b.instantiate1 s
    res := res.push (p', ty')
    res := res ++ (← specializeWithSeeds p' ty' (depth - 1))
  return res

/-- Add the seeded specializations of all propositional hypotheses of `g` to its local context. -/
def instHypsWithSeeds (g : MVarId) : MetaM MVarId := g.withContext do
  let mut hs := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if !(← isProp ty) then continue
    for (p, pty) in ← specializeWithSeeds decl.toExpr ty 2 do
      hs := hs.push { userName := `h_seed, type := pty, value := p : Hypothesis }
  if hs.isEmpty then return g
  let (_, g) ← g.assertHypotheses hs
  return g

syntax (name := blasterInstHyps) "blaster_inst_hyps" : tactic

@[tactic blasterInstHyps] def evalBlasterInstHyps : Tactic := fun _ =>
  liftMetaTactic fun g => return [← instHypsWithSeeds g]

/-- Try to prove the residual goal `e` (i.e., an optimized expression proved valid by the
    backend SMT solver) using decision procedures available in Lean.
-/
def proveResidual (e : Expr) : TermElabM (Option (Expr × String)) := do
  if !(← isTypeCorrectObligation e) then return none
  let tacs : Array (String × TSyntax `tactic) := #[
    ("decide", ← `(tactic| decide)),
    ("simp", ← `(tactic| (blaster_denorm <;> simp <;> done))),
    ("omega", ← `(tactic| (intros <;> blaster_denorm <;> omega))),
    ("grind", ← `(tactic| (blaster_denorm <;> grind))),
    ("seeded instantiation", ← `(tactic| (intros <;> blaster_inst_hyps <;> blaster_denorm <;>
                                           first | omega | grind))),
    -- user definitions (e.g., derived `BEq` instances) with case analysis on inductive variables
    ("unfold + cases", ← `(tactic| (intros <;> blaster_denorm <;> blaster_cases_vars <;> blaster_unfold_user <;>
                                     (try simp_all) <;> (try blaster_unfold_user) <;>
                                     (try simp_all [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]) <;>
                                     (try decide) <;> first | done | ((repeat' split) <;> (try simp_all) <;> omega)))),
    -- `match` expressions over arithmetic: case analysis on the discriminants
    ("split", ← `(tactic| (intros <;> (try subst_vars) <;> blaster_denorm <;> (repeat' split) <;>
                          (try simp_all) <;> first | done | omega | grind))),
    -- existential goals: witness search
    ("exists", ← `(tactic| (intros <;> blaster_denorm <;> blaster_exists))),
    -- recursive functions: unfolding equation lemmas (e.g., `f (n + 1) = ...`)
    ("unfold", ← `(tactic| (intros <;> blaster_denorm <;>
        (try blaster_lit_add) <;>
        blaster_unfold_user <;> (try simp_all) <;> done))),
    -- division/modulo facts
    ("div/mod facts", ← `(tactic| (intros <;> blaster_denorm <;> blaster_divmod_facts <;> first
      | omega
      | (symm; apply Nat.div_eq_of_lt_le <;> grind)
      | (apply Nat.div_eq_of_lt_le <;> grind)
      | grind))),
    -- non-linear arithmetic with core lemmas
    ("nonlinear", ← `(tactic| (intros <;> blaster_denorm <;> first
      | (grind [Nat.div_lt_iff_lt_mul, Nat.le_div_iff_mul_le, Nat.mul_le_mul, Nat.eq_of_mul_eq_mul_left,
                Int.eq_of_mul_eq_mul_left, Nat.mod_lt, Nat.add_mul_div_right, Nat.div_eq_sub_div,
                Nat.mod_eq_sub_mod, Nat.mul_mod_mul_right, Nat.mod_add_div, Nat.sub_mul_div, Nat.div_mul_le_self])
      | (simp_all [Nat.div_eq, Nat.mod_eq]; done)
      | (simp_all [Nat.div_lt_iff_lt_mul, Nat.le_div_iff_mul_le, Nat.mul_le_mul, Nat.mul_mod_mul_right,
                   Nat.mul_comm]; done)
      | (simp_all [Nat.div_eq_sub_div, Nat.mod_eq_sub_mod, Nat.mul_left_cancel_iff, Nat.pos_iff_ne_zero,
                   Int.mul_eq_mul_left_iff]; done)
      | (rw [Nat.div_eq, Nat.mod_eq]; split <;> simp_all <;> omega)))),
    -- non-linear division/modulo identities
    ("arith simp", ← `(tactic| (intros <;> blaster_denorm <;>
        first
        | (simp_all [Nat.mod_add_div, Nat.div_add_mod, Nat.mul_div_mul_left, Nat.mul_div_cancel_left,
                     Nat.mul_mod_right, Nat.mul_mod_left, Nat.mod_mod, Nat.mod_self, Nat.div_self,
                     Nat.div_div_eq_div_mul, Nat.div_le_self, Nat.mod_le, Nat.mod_lt, Nat.mod_eq_of_lt,
                     Nat.add_mul_div_right, Nat.add_div_right, Nat.mul_self_inj, Nat.div_lt_iff_lt_mul,
                     Nat.le_div_iff_mul_le, Nat.div_lt_self, Nat.mod_def, Nat.mul_div_le, Nat.not_lt,
                     Int.emod_emod_of_dvd, Int.mul_emod_right, Int.mul_emod_left, Int.emod_add_mul_ediv,
                     Int.mul_ediv_add_emod, Int.fmod_add_mul_fdiv, Int.tmod_add_mul_tdiv, Nat.pos_iff_ne_zero]; done)
        | (simp_all [Nat.div_lt_iff_lt_mul, Nat.le_div_iff_mul_le, Nat.mod_def, Nat.mul_comm]; omega))))
  ]
  let large ← involvesLargeMatch e
  for (name, tac) in tacs do
    if large && name ∈ ["unfold + cases", "unfold", "split"] then continue
    if let some prf ← proveWithTactic e tac (budget := 4 * dischargeHeartbeats) then
      return some (prf, name)
  if !large then
    if let some prf ← proveWithTactic e (← deepCases) (budget := 8 * dischargeHeartbeats) then
      return some (prf, "unfold + cases")
  return none

end Blaster.Reconstruct
