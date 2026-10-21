import Lean
import Blaster.Reconstruct.Types
import Blaster.Reconstruct.Proof
import Blaster.Reconstruct.Lemmas
import Blaster.Reconstruct.Match
import Blaster.Reconstruct.Depth
import Blaster.Reconstruct.Profile

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

/-- Implementation of `dependsOnSorry`.
    NOTE: Each expression is traversed by the native `Expr.findExt?` (whose cache of visited shared subterms is
    much more efficient than the one of `Expr.getUsedConstants`, i.e., on large proofs), the constants of the
    current module being recorded on the fly.
-/
unsafe def dependsOnSorryImpl (env : Environment) (prf : Expr) (checked : Array (Name × Expr)) : BaseIO Bool := do
  let found ← IO.mkRef (#[] : Array Name)
  let step (s : Expr) : Expr.FindStep :=
    match s with
    | .const c _ =>
        if c == ``sorryAx then .found
        else if (env.getModuleIdxFor? c).isSome then .done
        else unsafeBaseIO do found.modify (·.push c); return .done
    | _ => .visit
  let mut visited : NameHashSet := {}
  let mut todo : Array Expr := #[prf]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if (e.findExt? step).isSome then return true
    for c in ← found.swap #[] do
      if visited.contains c then continue
      visited := visited.insert c
      let some info := env.find? c | continue
      let value? := info.value? (allowOpaque := true)
      if let some v := value? then
        if checked.any fun (n, v') => n == c && ptrEq v v' then continue
        todo := todo.push v
      todo := todo.push info.type
  return false

@[implemented_by dependsOnSorryImpl]
private opaque dependsOnSorryAux (env : Environment) (prf : Expr) (checked : Array (Name × Expr)) : BaseIO Bool

/-- Return `true` if `prf` depends on `sorryAx`, directly or through an auxiliary declaration of the current
    module (e.g., a matcher created by `nomatch` after an elaboration error). The declarations of `checked`
    (with their values) are known not to depend on `sorryAx` (see `Blaster.Reconstruct.checkedProof`).
    NOTE: Imported declarations are not traversed.
-/
def dependsOnSorry (prf : Expr) (checked : Array (Name × Expr) := #[]) : MetaM Bool := do
  dependsOnSorryAux (← getEnv) prf checked

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
  -- NOTE: an attempt logging an error (e.g., an elaboration error recovered with `sorry`) is rejected
  Core.setMessageLog {}
  let r ← try
      attempt budget do
        let mvar ← mkFreshExprMVar type
        -- NOTE: asynchronous elaboration is disabled such that kernel errors on auxiliary declarations
        -- created by tactics are reported as exceptions instead of messages.
        let gs ← withOptions (fun o => Elab.async.set o false) <|
                   withoutErrToSorry <| Tactic.run mvar.mvarId! (evalTactic tac)
        let prf ← instantiateMVars mvar
        if !gs.isEmpty || prf.hasMVar || prf.hasSorry then return none
        if ← dependsOnSorry prf then return none
        if (← Core.getMessageLog).hasErrors then return none
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
      return !([`Init, `Lean, `Std, `Lake, `Blaster].contains mod.getRoot)

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

syntax (name := blasterCloseProofs) "blaster_close_proofs" : tactic

/-- Replace the proofs occurring in the goal that depend on local hypotheses but whose type is a
    closed decidable proposition (e.g., `s.length ≤ 64` for a string literal `s`) with proofs by
    `decide`, which is a definitional change by proof irrelevance. This allows closed goals to be
    decided by kernel evaluation after a case analysis (see `blaster_wf_eval`).
-/
@[tactic blasterCloseProofs] def evalBlasterCloseProofs : Tactic := fun _ =>
  liftMetaTactic fun g => g.withContext do
    let t ← instantiateMVars (← g.getType)
    let changed ← IO.mkRef false
    let t' ← Meta.transform t (pre := fun e => do
      if !e.hasFVar || e.hasLooseBVars then return .continue
      if !(← isProof e) then return .continue
      let p ← instantiateMVars (← inferType e)
      if p.hasFVar || p.hasMVar then return .continue
      try
        let r ← withAtLeastTransparency .default <| whnf (← mkDecide p)
        if !r.isConstOf ``true then return .continue
        changed.set true
        return .done (← mkDecideProof p)
      catch _ => return .continue)
    if !(← changed.get) then throwError "blaster_close_proofs: no proof to close"
    return [← g.replaceTargetDefEq t']

syntax (name := blasterClosedContra) "blaster_closed_contra" : tactic

/-- Close the goal when one of the hypotheses is a closed decidable proposition evaluating to
    `false` (e.g., an infeasible branch condition `"abc".length < 2` after a case analysis).
-/
@[tactic blasterClosedContra] def evalBlasterClosedContra : Tactic := fun _ =>
  liftMetaTactic fun g => g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let p ← instantiateMVars d.type
      if p.hasFVar || p.hasMVar || !(← isProp p) then continue
      try
        let r ← withAtLeastTransparency .default <| whnf (← mkDecide (mkNot p))
        if !r.isConstOf ``true then continue
        let np ← mkDecideProof (mkNot p)
        g.assign (← mkAbsurd (← g.getType) d.toExpr np)
        return []
      catch _ => continue
    throwError "blaster_closed_contra: no contradiction"

syntax (name := blasterWfEval) "blaster_wf_eval" : tactic

/-- Return `true` if `f` is defined by well-founded recursion. -/
def isWellFoundedDef (env : Environment) (f : Name) : Bool := Id.run do
  if env.contains (f ++ `_unary) then return true
  let some info := env.find? f | return false
  let some v := info.value? | return false
  return v.getUsedConstants.contains ``WellFounded.fix

/-- Evaluation of closed applications of functions defined by well-founded recursion, which the
    kernel cannot reduce efficiently (i.e., `decide` gets stuck). For each closed application `f a`
    of such a function (or of a non-recursive user definition calling one), an equation `f a = v` is
    proved by unfolding the equation lemmas step by step, each `if` condition being decided.
    The equations are then used to rewrite the main goal (with a case analysis on dependent `match`
    discriminants), which is finally closed by `rfl` or `decide`.
-/
@[tactic blasterWfEval] def evalBlasterWfEval : Tactic := fun _ => withMainContext do
  let env ← getEnv
  let target ← instantiateMVars (← getMainTarget)
  -- well-founded definitions reachable from the goal through (up to 3 levels of) user definitions,
  -- and the non-recursive user definitions on the way (wrappers)
  let mut wfs : Array Name := #[]
  let mut wrappers0 : Array Name := #[]
  let mut frontier := target.getUsedConstants
  for _ in [0:3] do
    let mut next := #[]
    for n in frontier do
      if wfs.contains n || wrappers0.contains n then continue
      if isWellFoundedDef env n then wfs := wfs.push n
      else if isUserDefinition env n then
        let some v := (env.find? n).bind (·.value?) | continue
        wrappers0 := wrappers0.push n
        next := next ++ v.getUsedConstants
    frontier := next
  -- only keep the wrappers leading to a well-founded definition
  let allWrappers := wrappers0
  let wrappers := allWrappers.filter fun n =>
    ((env.find? n).bind (·.value?) |>.map (·.getUsedConstants.any fun m => wfs.contains m || allWrappers.contains m)).getD false
  if wfs.isEmpty then throwError "blaster_wf_eval: no well-founded definition"
  let mut step ← `(tactic| fail "no unfolding")
  for n in wfs do
    let e := mkIdent (n ++ `eq_1)
    step ← `(tactic| first
      | rewrite [$e:ident, if_pos (by decide)] | rewrite [$e:ident, if_neg (by decide)]
      | rewrite [$e:ident, dif_pos (by decide)] | rewrite [$e:ident, dif_neg (by decide)] | ($step:tactic))
  let unfoldTac ← `(tactic| repeat ($step:tactic))
  -- same as `unfoldTac` but on the hypotheses (e.g., after a case analysis on a `match` discriminant)
  let mut stepAt ← `(tactic| fail "no unfolding")
  for n in wfs do
    let e := mkIdent (n ++ `eq_1)
    stepAt ← `(tactic| first
      | rewrite [$e:ident, if_pos (by decide)] at * | rewrite [$e:ident, if_neg (by decide)] at *
      | rewrite [$e:ident, dif_pos (by decide)] at * | rewrite [$e:ident, dif_neg (by decide)] at *
      | ($stepAt:tactic))
  let unfoldAtTac ← `(tactic| repeat ($stepAt:tactic))
  let evalTac ← `(tactic| ($unfoldTac <;> exact rfl))
  -- unfold the wrappers
  let wrapperLemmas ← wrappers.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  if !wrappers.isEmpty then evalTactic (← `(tactic| try simp only [$wrapperLemmas,*] at *))
  let mut idx := 0
  let mut evalTerms : Array Term := #[]
  let mut done : Array Expr := #[]
  for _ in [0:6] do
    if (← getGoals).isEmpty then break
    let apps ← withMainContext do
      let mut ts := #[← instantiateMVars (← getMainTarget)]
      for d in ← getLCtx do
        if !d.isImplementationDetail then ts := ts.push (← instantiateMVars d.type)
      let apps := ts.foldl (fun acc t => collect env wfs t acc) #[]
      return apps.filter (!done.contains ·)
    if apps.isEmpty then break
    for app in apps.extract 0 4 do
      done := done.push app
      if (← getGoals).isEmpty then break
      -- prove `app = v` (with `v` assigned by `rfl` after unfolding)
      let eqn? ← withMainContext do
        let v ← mkFreshExprMVar (← inferType app)
        let eqGoal ← mkFreshExprMVar (← mkEq app v)
        try
          let gs ← withoutErrToSorry <| Term.withSynthesize <| Tactic.run eqGoal.mvarId! (evalTactic evalTac)
          let prf ← instantiateMVars eqGoal
          let v ← instantiateMVars v
          if !gs.isEmpty || prf.hasMVar || v.hasMVar || prf.hasSorry || v == app then return none
          return some (← mkEq app v, prf)
        catch _ => return none
      let some (eqTy, prf) := eqn? | continue
      let hName := Name.mkSimple s!"blaster_eval_{idx}"
      idx := idx + 1
      let g ← getMainGoal
      let (_, g') ← (← g.assert hName eqTy prf).intro1P
      replaceMainGoal [g']
      -- NOTE: the equation is used as a term, as `simp ... at *` also rewrites the hypothesis to `True`
      let eqTerm ← Term.exprToSyntax prf
      evalTerms := evalTerms.push eqTerm
      evalTactic (← `(tactic| try simp only [$eqTerm:term] at *))
  if idx == 0 then throwError "blaster_wf_eval: no evaluation"
  if (← getGoals).isEmpty then return
  -- the evaluation equations are applied again after case analysis (e.g., on a `match` whose
  -- discriminant is an evaluated application, which can't be rewritten before the case split)
  let evalLemmas ← evalTerms.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  evalTactic (← `(tactic| first
    | rfl
    | decide +kernel +revert
    | ((repeat' split) <;> (try simp only [$evalLemmas,*] at *) <;> (try $unfoldAtTac:tactic) <;>
        (try simp_all) <;> (try subst_vars) <;>
        first | done | rfl | blaster_closed_contra | (blaster_close_proofs; decide +kernel) |
                decide +kernel +revert)))
where
  arity (env : Environment) (n : Name) : Nat :=
    ((env.find? n).map fun info => info.type.getForallArity).getD 0
  collect (env : Environment) (fs : Array Name) (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := match e.getAppFn with
      | .const n _ =>
          if fs.contains n && !e.hasFVar && !e.hasMVar && !e.hasLooseBVars && !acc.contains e
             && e.getAppNumArgs ≥ arity env n
          then acc.push e else acc
      | _ => acc
    match e with
    | .app f a => collect env fs a (collect env fs f acc)
    | .lam _ t b _ | .forallE _ t b _ => collect env fs b (collect env fs t acc)
    | .letE _ t v b _ => collect env fs b (collect env fs v (collect env fs t acc))
    | .mdata _ e | .proj _ _ e => collect env fs e acc
    | _ => acc

syntax (name := blasterNlDiv) "blaster_nl_div" : tactic

/-- Non-linear `Nat` division goals: for each `a / b` in the main goal, add `0 < b`, the division
    facts, and for each hypothesis `a < b * c` (or `a < c * b`) the bound `a / b < c` multiplied by `b`.
    Then the goal (or the two bounds of `Nat.div_eq_of_lt_le` for `_ / b = _`) are closed by `omega`
    after distributing the multiplications.
-/
@[tactic blasterNlDiv] def evalBlasterNlDiv : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let pairs := evalBlasterDivModFacts.collect (← instantiateMVars (← g.getType)) #[]
  if pairs.isEmpty then throwError "blaster_nl_div: no division"
  let hyps ← g.withContext do
    let mut hs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      -- `a < p` with `p` a product
      if let some (_, _, a, p) := t.app4? ``LT.lt then
        if p.isAppOfArity ``HMul.hMul 6 then hs := hs.push (d.toExpr, a, p.getArg! 4, p.getArg! 5)
    return hs
  for (a, b) in pairs.extract 0 4 do
    withMainContext do
      let aS ← Term.exprToSyntax a
      let bS ← Term.exprToSyntax b
      evalTactic (← `(tactic| have blaster_pos : 0 < $bS := by
        first | omega | (apply Nat.pos_of_ne_zero; intro h0; simp_all)))
      evalTactic (← `(tactic| (have := Nat.div_add_mod $aS $bS; have := Nat.mod_lt $aS blaster_pos)))
      for (h, a', l, r) in hyps do
        if !(← isDefEq a a') then continue
        let c ← if ← isDefEq l b then pure r else if ← isDefEq r b then pure l else continue
        let hS ← Term.exprToSyntax h
        let cS ← Term.exprToSyntax c
        evalTactic (← `(tactic| try (
          have blaster_q : $aS / $bS + 1 ≤ $cS :=
            Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul blaster_pos).2 (by rw [Nat.mul_comm]; first | exact $hS | omega))
          have := Nat.mul_le_mul_left $bS blaster_q)))
  evalTactic (← `(tactic| first
    | omega
    | (apply Nat.div_eq_of_lt_le <;>
        simp only [Nat.sub_mul, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at * <;>
        simp only [Nat.mul_comm] at * <;> omega)))

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
          -- NOTE: single fields (e.g., `next (n : T)`) range over all the candidates of their type
          for o in opts.extract 0 (if fields.size == 1 then 256 else 8) do
            if next.size < 256 then next := next.push (a.push o)
        args := next
      return some args
    let some argss := fieldsOk | continue
    for args in argss do
      cs := cs.push (← `($(mkIdent ctor) $args*))
  return cs.extract 0 512

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

syntax (name := blasterInstHyps) "blaster_inst_hyps" : tactic

syntax (name := blasterGenDiscrs) "blaster_gen_discrs" : tactic

/-- Generalize the non-variable discriminants of the first `match` expression occurring in the goal
    (e.g., the symbolic `Int.negSucc` normalized by the optimizer), such that case analysis on the
    `match` expression can be performed.
-/
@[tactic blasterGenDiscrs] def evalBlasterGenDiscrs : Tactic := fun _ =>
  liftMetaTactic fun g => g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some m ← findMatcher t
      | throwError "blaster_gen_discrs: no match expression"
    -- NOTE: closed discriminants (e.g., `Int.ofNat 10`) are kept such that the `match` can be reduced
    let ds := m.discrs.filter fun d => !d.isFVar && !d.hasLooseBVars && d.hasFVar
    if ds.isEmpty then throwError "blaster_gen_discrs: no discriminant to generalize"
    let (_, g) ← g.generalize (ds.map fun d => { expr := d, xName? := `d : GeneralizeArg })
    return [g]
where
  findMatcher (t : Expr) : MetaM (Option MatcherApp) := do
    let r ← IO.mkRef none
    Meta.forEachExpr' t fun e => do
      if (← r.get).isSome then return false
      if let some m ← matchMatcherApp? e then
        r.set (some m); return false
      return true
    r.get

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

/-- Case analysis on a `match` expression with generalized discriminants (see `blaster_gen_discrs`). -/
def matchGeneralizeTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| (blaster_gen_discrs <;> blaster_denorm <;> split <;> (repeat' split) <;>
             (try simp_all [Int.negSucc_eq]) <;> (try norm_cast at *) <;> (try simp_all) <;>
             (try blaster_inst_hyps) <;> first | omega | (subst_vars; simp_all; done) | grind))

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
    ("split", ← `(tactic| (blaster_denorm <;> (repeat' split) <;>
        first | omega | (simp_all; done) | grind | (simp_all [String.ext_iff]; done) |
                -- infeasible branches whose condition is used by a dependent proof in the goal
                (exfalso; simp_all; done)))),
    -- case analysis on `Int.negSucc` patterns (symbolic `Int.negSucc` is normalized by the optimizer)
    ("split", ← `(tactic| (blaster_denorm <;>
        simp (disch := decide) only [Blaster.Reconstruct.neg_natCast_add_eq_negSucc, Nat.reduceSub, Nat.add_zero] at * <;>
        (repeat' split) <;> first | omega | (simp_all; done) | grind))),
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

/-! ## Case analysis driven by stuck `match` applications

The splitter of a matcher with many overlapping patterns may not be generated within Lean's
heartbeat budget (see `getEquationsFor?`), i.e., `split` cannot be used. Instead, `blaster_match_cases`
performs case analysis on the variables `match` applications are stuck on, until they reduce by iota.
-/

/-- Maximum number of goals produced by `blaster_match_cases`. -/
def maxMatchCaseGoals : Nat := 1024

/-- Return the free variable `e` is stuck on (after weak head normalization), if any.
    NOTE: stuck `match` applications are reduced to their `casesOn` decision tree. -/
partial def stuckFVar? (e : Expr) (fuel : Nat := 16) : MetaM (Option FVarId) := do
  if fuel == 0 then return none
  let e ← whnf e
  match e.getAppFn with
  | .fvar fv => return if e.isFVar then some fv else none
  | .proj _ _ s => stuckFVar? s (fuel - 1)
  | .const n _ =>
      let args := e.getAppArgs
      if let some r ← stuckMatch? n e then return r
      if let some projInfo ← getProjectionFnInfo? n then
        if h : projInfo.numParams < args.size then return ← stuckFVar? args[projInfo.numParams] (fuel - 1)
        return none
      match ← getConstInfo n with
      | .recInfo recVal =>
          if h : recVal.getMajorIdx < args.size then stuckFVar? args[recVal.getMajorIdx] (fuel - 1)
          else return none
      | _ =>
          if let some e' ← unfoldDefinition? e then return ← stuckFVar? e' (fuel - 1)
          -- e.g., `Nat.beq n 0` (decidable equality of literal patterns): case analysis on an argument
          for a in args do
            let a ← whnf a
            if let .fvar fv := a then
              let t ← whnfR (← fv.getType)
              if let .const tn _ := t.getAppFn then
                if (← getEnv).isConstructor tn then continue
                if let .inductInfo _ ← getConstInfo tn then return some fv
          return none
  | _ => return none
where
  /-- Same as `reduceMatcher?` but the stuck term is examined within the scope of the alternatives. -/
  stuckMatch? (n : Name) (e : Expr) : MetaM (Option (Option FVarId)) := do
    let some info ← getMatcherInfo? n | return none
    let args := e.getAppArgs
    let prefixSz := info.numParams + 1 + info.numDiscrs
    if args.size < prefixSz + info.numAlts then return none
    let .const _ us := e.getAppFn | return none
    let f ← instantiateValueLevelParams (← getConstInfo n) us
    let auxApp := mkAppN f (args.extract 0 prefixSz)
    forallBoundedTelescope (← inferType auxApp) info.numAlts fun hs _ => do
      let aux ← whnf (mkAppN auxApp hs)
      if hs.contains aux.getAppFn then return some none
      return some (← stuckFVar? aux (fuel - 1))

/-- Return the `match` applications of `e` without loose bound variables. -/
partial def collectMatchApps (env : Environment) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if !e.hasLooseBVars && e.isApp && (e.getAppFn.constName?.map (Meta.isMatcherCore env)).getD false
             then acc.push e else acc
  match e with
  | .app f a => collectMatchApps env a (collectMatchApps env f acc)
  | .mdata _ b | .proj _ _ b => collectMatchApps env b acc
  | .forallE _ t b _ | .lam _ t b _ => collectMatchApps env b (collectMatchApps env t acc)
  | .letE _ t v b _ => collectMatchApps env b (collectMatchApps env v (collectMatchApps env t acc))
  | _ => acc

/-- Return the first free variable a `match` application of `e` is stuck on. -/
def findMatchStuckFVar? (e : Expr) : MetaM (Option FVarId) := do
  let lctx ← getLCtx
  for m in collectMatchApps (← getEnv) e do
    if let some fv ← observing? (stuckFVar? m) then
      if let some fv := fv then
        if lctx.contains fv && !(← fv.isLetVar) then return some fv
  return none

syntax (name := blasterMatchCases) "blaster_match_cases" : tactic

/-- Perform case analysis on the variables `match` applications (in the goal or hypotheses) are stuck on
    (bounded by `maxMatchCaseGoals`). -/
@[tactic blasterMatchCases] def evalBlasterMatchCases : Tactic := fun _ => do
  let mut todo := [← getMainGoal]
  let mut done := #[]
  while !todo.isEmpty do
    let g :: rest := todo | break
    todo := rest
    let fv? ← g.withContext do
      if let some fv ← findMatchStuckFVar? (← instantiateMVars (← g.getType)) then return some fv
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if let some fv ← findMatchStuckFVar? (← instantiateMVars d.type) then return some fv
      return none
    match fv? with
    | none => done := done.push g
    | some fv =>
        let subgoals ← g.cases fv
        todo := subgoals.toList.map (·.mvarId) ++ todo
    if done.size + todo.length > maxMatchCaseGoals then throwError "blaster_match_cases: too many goals"
  replaceMainGoal done.toList

/-- Case analysis on the variables stuck `match` applications depend on (`blaster_match_cases`), then
    reduction by iota and arithmetic. -/
def matchCasesTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| (intros <;> (try subst_vars) <;> blaster_denorm <;> blaster_match_cases <;>
              (try dsimp only at *) <;>
              first | rfl | omega | (simp_all; done) | decide
                    | (simp only [Int.ofNat_eq_coe, Int.toNat_natCast, Nat.succ_eq_add_one,
                                  Nat.zero_add, Nat.add_sub_cancel] at * <;>
                       first | omega | grind)
                    | grind))

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
/-- Try to discharge proof obligation `type` (expected to be an equality) and return the proof together with
    the method used and, when the proof is given by a tactic of `dischargeTactics`, its index.
    The tactic of index `first?` (e.g., the one that discharged the previous obligation with the same origin,
    see `dischargeHoles`) is tried first.
-/
partial def dischargeOneAux (type : Expr) (depth := matchCasesDepth) (first? : Option Nat := none) :
    TermElabM (Option (Expr × String × Option Nat)) := do
  let type ← instantiateMVars type
  -- ill-typed proof obligations (e.g., due to ill-typed optimized expressions) can't be discharged
  if !(← isTypeCorrectObligation type) then
    if (← IO.getEnv "BLASTER_RECON_DEBUG").isSome then
      try Meta.check type catch ex => logInfo m!"ill-typed proof obligation: {ex.toMessageData}"
    if ← isProfiling then
      let msg ← try Meta.check type; pure "budget" catch ex => pure (← ex.toMessageData.toString)
      profileLog "obligation.illtyped" 0 fun _ => msg.take 2000
    return none
  -- NOTE: case analysis on (or unfolding of) large `match` expressions requires the generation of
  -- costly auxiliary lemmas (e.g., splitters), which are not subject to the discharge budget.
  let large ← involvesLargeMatch type
  let tacs ← dischargeTactics
  let skip (name : String) : Bool := large && name ∈ ["split", "cases", "induction"]
  let first := first?.filter fun i => i < tacs.size && !skip tacs[i]!.1
  if let some i := first then
    let (name, tac) := tacs[i]!
    if let some prf ← profileAttempt s!"{i}:{name}" (proveWithTactic type tac) then return some (prf, name, some i)
  if let some prf ← profileAttempt "rfl" (proveByDefEq type) then return some (prf, "rfl", none)
  -- closed obligations (e.g., concrete computations) are decided by kernel evaluation
  if !type.hasFVar && !type.hasMVar then
    if let some prf ← profileAttempt "decide" (proveWithTactic type (← `(tactic| decide +kernel))) then
      return some (prf, "decide", none)
    -- closed computations involving well-founded recursion
    if let some prf ← profileAttempt "wf_eval"
        (proveWithTactic type (← `(tactic| blaster_wf_eval)) (budget := 4 * dischargeHeartbeats)) then
      return some (prf, "decide", none)
  for h : i in [0:tacs.size] do
    let (name, tac) := tacs[i]
    if skip name || first == some i then continue
    if let some prf ← profileAttempt s!"{i}:{name}" (proveWithTactic type tac) then return some (prf, name, some i)
  -- deeper case analysis with a larger budget (e.g., equality of nested structures)
  if !large then
    if let some prf ← profileAttempt "deep cases"
        (proveWithTactic type (← deepCases) (budget := 8 * dischargeHeartbeats)) then
      return some (prf, "cases", none)
  if let some prf ← profileAttempt "match cases" (proveByMatchCases type depth) then
    return some (prf, "match cases", none)
  -- case analysis on `match` expressions with generalized discriminants (e.g., symbolic `Int.negSucc`
  -- normalized by the optimizer)
  if !large then
    if let some prf ← profileAttempt "match generalize"
        (proveWithTactic type (← matchGeneralizeTactic) (budget := 4 * dischargeHeartbeats)) then
      return some (prf, "match cases", none)
  -- case analysis on the variables stuck `match` applications depend on (no splitter needed)
  if depth == matchCasesDepth then
    if (collectMatchApps (← getEnv) type).size > 0 then
      if let some prf ← profileAttempt "match stuck cases"
          (proveWithTactic type (← matchCasesTactic) (budget := 4 * dischargeHeartbeats)) then
        return some (prf, "match cases", none)
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
    match ← dischargeOneAux goal (depth - 1) with
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

/-- Try to discharge proof obligation `type` (expected to be an equality) and return
    the proof together with the method used.
-/
def dischargeOne (type : Expr) (depth := matchCasesDepth) : TermElabM (Option (Expr × String)) := do
  return (← dischargeOneAux type depth).map fun (p, m, _) => (p, m)

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

namespace TransformScoped

/-- Return the subterms of `e` (by pointer) containing a proof obligation, i.e., the ones mapped to `true`.
    NOTE: The traversal is iterative, each shared subterm is visited once and bound variables are not
    instantiated, i.e., the terms rewritten by the optimizer (which do not contain proof obligations) are
    traversed once.
-/
unsafe def obligationNodes (e : Expr) : PtrMap Expr Bool := Id.run do
  let mut m : PtrMap Expr Bool := mkPtrMap
  let mut todo : Array (Expr × Bool) := #[(e, false)]
  while !todo.isEmpty do
    let (x, expanded) := todo.back!
    todo := todo.pop
    if m.contains x then continue
    if (isHole? x).isSome then
      m := m.insert x true
      continue
    let cs : Array Expr := match x with
      | .app .. => #[x.getAppFn] ++ x.getAppArgs
      | .lam _ t b _ | .forallE _ t b _ => #[t, b]
      | .letE _ t v b _ => #[t, v, b]
      | .mdata _ b | .proj _ _ b => #[b]
      | _ => #[]
    if !expanded && !cs.isEmpty then
      todo := todo.push (x, true)
      for c in cs do
        if !m.contains c then todo := todo.push (c, false)
      continue
    m := m.insert x (cs.any fun c => (m.find? c).getD false)
  return m

mutual
/-- Visit `e`, whose loose bound variables stand for the free variables `subst` (see `Expr.instantiateRev`).
    The results for the visited subterms are memoized in `openCache` (subterms with loose bound variables, i.e.,
    valid at the current binder depth) and `closedCache` (closed subterms).
-/
unsafe def go (obl : PtrMap Expr Bool) (f : Expr → TermElabM (Option Expr)) (subst : Array Expr)
    (openCache closedCache : IO.Ref (PtrMap Expr Expr)) (e : Expr) : TermElabM Expr := do
  if !(obl.find? e).getD false then return e
  let cache := if e.hasLooseBVars then openCache else closedCache
  if let some r := (← cache.get).find? e then return r
  let r ← visit obl f subst openCache closedCache e
  cache.modify (·.insert e r)
  return r

unsafe def visit (obl : PtrMap Expr Bool) (f : Expr → TermElabM (Option Expr)) (subst : Array Expr)
    (openCache closedCache : IO.Ref (PtrMap Expr Expr)) (e : Expr) : TermElabM Expr := do
  if (isHole? e).isSome || isFallback e then
    if let some r ← f (e.instantiateRev subst) then return r.abstract subst
  let go' := go obl f subst openCache closedCache
  match e with
  | .app .. =>
      -- NOTE: the arguments of an application are visited in a loop (instead of recursing over the spine)
      let fn := e.getAppFn
      let args := e.getAppArgs
      let fn' ← go' fn
      let args' ← args.mapM go'
      if ptrEq fn fn' && (args.zip args').all (fun (a, a') => ptrEq a a') then return e
      return mkAppN fn' args'
  | .mdata _ b => return e.updateMData! (← go' b)
  | .proj _ _ b => return e.updateProj! (← go' b)
  | .lam n t b bi | .forallE n t b bi =>
      let t' ← go' t
      withLocalDecl n bi (t'.instantiateRev subst) fun x => do
        let b' ← go obl f (subst.push x) (← IO.mkRef mkPtrMap) (← IO.mkRef mkPtrMap) b
        return if e.isLambda then e.updateLambdaE! t' b' else e.updateForallE! t' b'
  | .letE .. => visitLets obl f subst openCache closedCache e
  | _ => return e

/-- Visit a `let` telescope iteratively (e.g., the declarations introduced by `shareDeepProofs`).
    NOTE: The declarations introduced by `shareDeepProofs` only bind subproofs, i.e., proof obligations and
    their proofs never refer to them (see `withoutSharedProofs`): they stand for free variables that are not
    declared, such that their types and values are not instantiated. Fallback regions don't refer to them
    either (see `ShareDeep.scope`).
    NOTE: The results for closed subterms are kept across the declarations introduced by `shareDeepProofs`,
    i.e., the proof obligations are discharged in the same local context.
-/
unsafe def visitLets (obl : PtrMap Expr Bool) (f : Expr → TermElabM (Option Expr)) (subst : Array Expr)
    (openCache closedCache : IO.Ref (PtrMap Expr Expr)) (e : Expr) : TermElabM Expr := do
  let insts ← getLocalInstances
  let mut lctx ← getLCtx
  let mut subst := subst
  let mut openCache := openCache
  let mut closedCache := closedCache
  let mut decls : Array (Name × Expr × Expr × Bool) := #[]
  let mut cur := e
  while true do
    let .letE n t v b nondep := cur | break
    let t' ← withLCtx lctx insts (go obl f subst openCache closedCache t)
    let v' ← withLCtx lctx insts (go obl f subst openCache closedCache v)
    let fvarId ← mkFreshFVarId
    let shared := n == sharedProofName
    if !shared then
      lctx := lctx.mkLetDecl fvarId n (t'.instantiateRev subst) (v'.instantiateRev subst) nondep
      closedCache ← IO.mkRef mkPtrMap
    subst := subst.push (mkFVar fvarId)
    openCache ← IO.mkRef mkPtrMap
    decls := decls.push (n, t', v', nondep)
    cur := b
  let mut r ← withLCtx lctx insts (go obl f subst openCache closedCache cur)
  for (n, t, v, nondep) in decls.reverse do
    r := .letE n t v r nondep
  return r
end

unsafe def transformScopedImpl (e : Expr) (f : Expr → TermElabM (Option Expr)) : TermElabM Expr := do
  go (obligationNodes e) f #[] (← IO.mkRef mkPtrMap) (← IO.mkRef mkPtrMap) e

end TransformScoped

/-- Traverse `e` and replace each proof obligation or fallback region `s` containing proof obligations such that
    `f s = some r` with `r` (in the local context of the binders of `e` enclosing `s`). Fallback regions for which
    `f` returns `none` are traversed.
    NOTE: Unlike `Meta.transform`, results are only shared within the same binder scope. Proof obligations
    are closed terms, but their proofs may depend on the hypotheses of the local context (e.g., `simp [*]`).
    Hence, the same obligation occurring under different binders must be discharged in each context.
    NOTE: The traversal is linear in the size of the subterms containing proof obligations (as a DAG): bound
    variables are only instantiated in proof obligations and fallback regions (and in the types of the binders
    enclosing them), and the results of `f` are abstracted accordingly.
-/
@[implemented_by TransformScoped.transformScopedImpl]
opaque transformScoped (e : Expr) (f : Expr → TermElabM (Option Expr)) : TermElabM Expr

/-- Return the local context (and local instances) restricted to the declarations `type` depends on
    (transitively) and to the hypotheses only depending on them (e.g., the equalities of the match context of
    a proof obligation), or `none` when no declaration is removed.
-/
def relevantContext? (type : Expr) : MetaM (Option (LocalContext × LocalInstances)) := do
  let lctx ← getLCtx
  let mut keep : FVarIdSet := {}
  let mut todo := (collectFVars {} (← instantiateMVars type)).fvarIds
  while !todo.isEmpty do
    let y := todo.back!
    todo := todo.pop
    if keep.contains y then continue
    keep := keep.insert y
    let some d := lctx.find? y | continue
    todo := todo ++ (collectFVars {} d.type).fvarIds
    if let some v := d.value? then todo := todo ++ (collectFVars {} v).fvarIds
  let mut removed := false
  for d in lctx do
    if keep.contains d.fvarId then continue
    if !d.isImplementationDetail && !d.type.hasAnyFVar (!keep.contains ·) && (← try isProp d.type catch _ => pure false) then
      keep := keep.insert d.fvarId
    else
      removed := true
  if !removed then return none
  let lctx' := lctx.foldl (init := lctx) fun acc d => if keep.contains d.fvarId then acc else acc.erase d.fvarId
  return some (lctx', (← getLocalInstances).filter (keep.contains ·.fvar.fvarId!))

/-- Same as `dischargeOneAux` but the obligation is first discharged in its relevant local context (see
    `relevantContext?`), i.e., without the hypotheses on other variables.
    NOTE: The hypotheses of the goal (e.g., the evaluation of a validator) may be large, while proof
    obligations usually only depend on a few variables. Tactics using all the hypotheses (e.g., `grind`,
    `simp [*]`) are much faster without them. The obligation is discharged in the whole local context
    otherwise.
-/
def dischargeInContext (type : Expr) (first? : Option Nat := none) : TermElabM (Option (Expr × String × Option Nat)) := do
  let some (lctx, insts) ← relevantContext? type | dischargeOneAux type (first? := first?)
  if let some r ← withLCtx lctx insts (dischargeOneAux type (first? := first?)) then return some r
  dischargeOneAux type (first? := first?)

/-- Discharge all the proof obligations in `p`.
    Return the updated proof term and the discharge statistics. Proof obligations that cannot be
    discharged are left unchanged in the returned proof term.
    NOTE: A second pass is performed on the remaining obligations, using the equivalences between
    recursive functions proved during the first pass as hypotheses (nested equivalences).
    NOTE: A fallback region `r : lhs = rhs` (see `fallbackKey`) is replaced with a proof of `lhs = rhs`
    discharged as a whole when one of its proof obligations cannot be discharged.
-/
partial def dischargeHoles
  (p : Expr) (holes : Array HoleInfo := #[]) (equivs : Array (Expr × Expr) := #[])
  (fallback : Expr → TermElabM (Option (Expr × String)) := fun _ => pure none) :
  TermElabM (Expr × DischargeStats) := do
  let stats ← IO.mkRef ({} : DischargeStats)
  let facts ← IO.mkRef (← withProfile "dischargeHoles.equivalences" (proveEquivalences equivs))
  let labelOf (e : Expr) : String :=
    match isHole? e with
    | some idx => if h : idx < holes.size then holes[idx].label else "top"
    | none => "top"
  -- NOTE: the optimizer may yield many proof obligations of the same origin (e.g., the same rewrite applied
  -- in each step of a computation), possibly with the same type in different scopes. Hence, the proofs of
  -- the obligations discharged so far are reused when they are well-scoped (i.e., their free variables are
  -- in the local context), and the tactic that discharged the last obligation with the same label is tried
  -- first.
  let solved ← IO.mkRef ({} : Std.HashMap ExprStructEq (Expr × String))
  let preferred ← IO.mkRef ({} : Std.HashMap String Nat)
  -- first pass
  let p' ← withProfile "dischargeHoles.first" (info := fun p' => s!"dag={dagSize p'}") <| transformScoped p fun e => do
    match holeType? e with
    | none => return none
    | some type =>
        let label := labelOf e
        stats.modify fun s => { s with total := s.total + 1 }
        let type ← instantiateMVars type
        if let some (prf, method) := (← solved.get).get? type then
          let lctx ← getLCtx
          if !prf.hasAnyFVar (!lctx.contains ·) then
            stats.modify (·.record method label)
            return some prf
        let start ← IO.monoMsNow
        let r ← withoutSharedProofs (dischargeInContext type (first? := (← preferred.get).get? label))
        let ms := (← IO.monoMsNow) - start
        if ms ≥ 1000 then
          profileLog "obligation" ms fun _ => s!"{label} {(r.map (·.2.1)).getD "failed"} hash={type.hash}"
          if ← isProfiling then
            let fvs := (collectFVars {} type).fvarIds.size
            profileLog "obligation.type" 0 fun _ => s!"fvars={fvs} dag={dagSize type}"
            if !(← preferred.get).contains label then
              let (lctx, insts) := (← relevantContext? type).getD (← getLCtx, ← getLocalInstances)
              let pp := toString (← withLCtx lctx insts (Meta.ppGoal (← mkFreshExprMVar type).mvarId!))
              profileLog "obligation.goal" 0 fun _ => (pp.take 4000).replace "\n" "\n    "
        match r with
        | some (prf, method, i?) =>
            stats.modify (·.record method label)
            solved.modify (·.insert type (prf, method))
            if let some i := i? then preferred.modify (·.insert label i)
            if label.startsWith "rule:recFunEquiv" then
              if let some f ← generalizeFact type prf then facts.modify (·.push f)
            return some prf
        | none => return some e
  reportAttempts
  -- second pass (with proved equivalences as hypotheses), fallback regions and failure reporting
  let (p', st) ← withProfile "dischargeHoles.second" (secondPass (← facts.get) labelOf p')
  reportAttempts
  return (p', (← stats.get).merge st)

  where
    secondPass (facts : Array (Expr × Expr)) (labelOf : Expr → String) (p : Expr) :
      TermElabM (Expr × DischargeStats) := do
      let stats ← IO.mkRef ({} : DischargeStats)
      let p' ← transformScoped p fun e => do
        if !isFallback e && (holeType? e).isNone then return none
        -- NOTE: tactics do not see the declarations introduced by `shareDeepProofs`
        withoutSharedProofs do
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
              if let some (prf, method, _) ← dischargeInContext type then
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
              -- last resort given by the caller (e.g., the replay of a proof of an SMT solver)
              if let some (prf, method) ← fallback type then
                stats.modify (·.record method label)
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

/-- Maximum number of specializations of a hypothesis w.r.t. local variables. -/
def maxLocalSpecializations : Nat := 64

/-- Return the specializations of `p : ty` w.r.t. the (non-propositional) local variables `vars`,
    i.e., all the instantiations of the leading quantifiers of `ty` with variables of the
    expected type (e.g., `(∀ β (x : T β), P β x) → ∀ α (y : T α), Q` needs `β := α` and `x := y`).
    Only fully instantiated specializations are returned (up to `maxLocalSpecializations`).
-/
partial def specializeWithLocals (vars : Array Expr) (p ty : Expr) : MetaM (Array (Expr × Expr)) := do
  let res ← IO.mkRef #[]
  let rec go (p ty : Expr) (depth : Nat) : MetaM Unit := do
    if (← res.get).size ≥ maxLocalSpecializations then return
    let ty ← whnfR ty
    let .forallE _ d b bi := ty | if depth > 0 then res.modify (·.push (p, ty)) else pure ()
    if bi.isInstImplicit then
      -- instance arguments are synthesized
      match ← trySynthInstance d with
      | .some inst => go (mkApp p inst) (b.instantiate1 inst) (depth + 1)
      | _ =>
        for v in vars do
          if ← isDefEq (← inferType v) d then go (mkApp p v) (b.instantiate1 v) (depth + 1)
      return
    if (← isProp d) then
      -- stop at the first hypothesis
      if depth > 0 then res.modify (·.push (p, ty))
      return
    for v in vars do
      if ← isDefEq (← inferType v) d then go (mkApp p v) (b.instantiate1 v) (depth + 1)
  go p ty 0
  return ← res.get

/-- Given a hypothesis `h : ∀ (k : Nat), ¬ a = k + c` (e.g., produced by the case analysis of a
    `match` with pattern `k + c`), where `c` is a constant offset, return `h (a - c)`.
-/
def patternInstance? (h ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let .forallE _ d b _ := ty | return none
  if !d.isConstOf ``Nat then return none
  let some body := b.not? | return none
  let some (_, l, r) := body.eq? | return none
  let (a, r) := if l.hasLooseBVars then (r, l) else (l, r)
  if a.hasLooseBVars || !r.hasLooseBVars then return none
  let some c₀ ← evalNat (r.instantiate1 (mkNatLit 0)) |>.run | return none
  let some c₁ ← evalNat (r.instantiate1 (mkNatLit 1)) |>.run | return none
  if c₁ != c₀ + 1 then return none
  let v := mkNatSub a (mkNatLit c₀)
  return some (mkApp h v, ← instantiateForall ty #[v])

/-- Add the seeded specializations of all propositional hypotheses of `g` to its local context,
    including their specializations w.r.t. the local variables.
-/
def instHypsWithSeeds (g : MVarId) : MetaM MVarId := g.withContext do
  let mut hs := #[]
  let mut vars := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if !(← isProp decl.type) then vars := vars.push decl.toExpr
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if !(← isProp ty) then continue
    for (p, pty) in ← specializeWithSeeds decl.toExpr ty 2 do
      hs := hs.push { userName := `h_seed, type := pty, value := p : Hypothesis }
    let locals ← try withNewMCtxDepth (specializeWithLocals vars decl.toExpr ty) catch _ => pure #[]
    for (p, pty) in locals do
      let p ← instantiateMVars p
      let pty ← instantiateMVars pty
      if p.hasMVar || pty.hasMVar then continue
      hs := hs.push { userName := `h_inst, type := pty, value := p : Hypothesis }
    if let some (p, pty) ← try patternInstance? decl.toExpr ty catch _ => pure none then
      hs := hs.push { userName := `h_pat, type := pty, value := p : Hypothesis }
  if hs.isEmpty then return g
  let (_, g) ← g.assertHypotheses hs
  return g

syntax (name := blasterStructFacts) "blaster_struct_facts" : tactic

/-- Add the propositional fields of the local variables of structure types (e.g., invariants
    `s.inv : ∀ x y, x < y → s.f x < s.f y`) as hypotheses.
-/
@[tactic blasterStructFacts] def evalBlasterStructFacts : Tactic := fun _ =>
  liftMetaTactic fun g => g.withContext do
    let env ← getEnv
    let mut hs := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || (← isProp decl.type) then continue
      let t ← whnfR decl.type
      let .const n _ := t.getAppFn | continue
      let some info := getStructureInfo? env n | continue
      for fld in info.fieldNames do
        let some proj := env.getProjectionFnInfo? (n ++ fld) |>.map (fun _ => n ++ fld) | continue
        try
          let p ← mkAppM proj #[decl.toExpr]
          let pty ← inferType p
          if ← isProp pty then hs := hs.push { userName := fld, type := pty, value := p : Hypothesis }
        catch _ => pure ()
    if hs.isEmpty then throwError "blaster_struct_facts: no fact"
    let (_, g) ← g.assertHypotheses hs
    return [g]


@[tactic blasterInstHyps] def evalBlasterInstHyps : Tactic := fun _ =>
  liftMetaTactic fun g => return [← instHypsWithSeeds g]

syntax (name := blasterNoMatch) "blaster_nomatch" : tactic

/-- Close the goal by exhibiting an element of an empty type, i.e., `nomatch f default ... default`
    for a local variable or an axiom `f` occurring in the goal (e.g., `g : Nat → E` with `E` empty).
-/
@[tactic blasterNoMatch] def evalBlasterNoMatch : Tactic := fun _ => withMainContext do
  let env ← getEnv
  let mut cands : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || (← isProp d.type) then continue
    cands := cands.push d.toExpr
  for n in (← instantiateMVars (← getMainTarget)).getUsedConstants do
    if let some (.axiomInfo _) := env.find? n then cands := cands.push (← mkConstWithFreshMVarLevels n)
  let s ← saveState
  for c in cands.extract 0 16 do
    let arity ← forallTelescopeReducing (← inferType c) fun xs _ => pure xs.size
    for k in [0:min arity 3 + 1] do
      -- NOTE: created for each attempt, as the state is restored after a failed attempt
      let t ← Term.exprToSyntax c
      let args := Array.replicate k (← `(default))
      -- NOTE: `nomatch` reports missing cases as an error message (with a `sorry` proof)
      let msgs ← Core.getMessageLog
      Core.setMessageLog {}
      try
        evalTactic (← `(tactic| exact nomatch ($t $args*)))
        if (← getGoals).isEmpty && !(← Core.getMessageLog).hasErrors then
          Core.setMessageLog msgs
          return
      catch _ => pure ()
      s.restore
      Core.setMessageLog msgs
  throwError "blaster_nomatch: no element of an empty type"

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
    -- invariants of structures (e.g., `s.inv`) and instantiation with local variables
    ("instantiation", ← `(tactic| (intros <;> (try blaster_struct_facts) <;> blaster_inst_hyps <;>
                                    blaster_denorm <;> first | omega | (solve_by_elim (maxDepth := 8)) | grind |
                                    (simp_all; done)))),
    -- case analysis with unfolding of list accessors
    ("cases", ← `(tactic| (intros <;> blaster_denorm <;> blaster_cases_vars <;>
                          simp_all [List.head!, List.head?, List.headD, List.getLast!, List.tail!] <;> done))),
    -- user definitions (e.g., derived `BEq` instances) with case analysis on inductive variables
    ("unfold + cases", ← `(tactic| (intros <;> blaster_denorm <;> blaster_cases_vars <;> blaster_unfold_user <;>
                                     (try simp_all) <;> (try blaster_unfold_user) <;>
                                     (try simp_all [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]) <;>
                                     (try decide) <;> first | done | ((repeat' split) <;> (try simp_all) <;> omega)))),
    -- `match` expressions over arithmetic: case analysis on the discriminants
    ("split", ← `(tactic| (intros <;> (try subst_vars) <;> blaster_denorm <;> (repeat' split) <;>
                          (try simp_all) <;> first | done | omega | grind))),
    -- existential goals: witness search
    -- case analysis on the variables `match` applications are stuck on
    ("match cases", ← matchCasesTactic),
    ("exists", ← `(tactic| (intros <;> blaster_denorm <;> blaster_exists))),
    -- recursive functions: unfolding equation lemmas (e.g., `f (n + 1) = ...`)
    ("unfold", ← `(tactic| (intros <;> blaster_denorm <;>
        (try blaster_lit_add) <;>
        blaster_unfold_user <;> (try simp_all) <;> done))),
    -- equivalence of recursive functions (e.g., when the solver unfolds both definitions)
    ("induction", ← `(tactic| (intros <;> blaster_funind))),
    -- division/modulo facts
    ("div/mod facts", ← `(tactic| (intros <;> blaster_denorm <;> blaster_divmod_facts <;> first
      | omega
      | (symm; apply Nat.div_eq_of_lt_le <;> grind)
      | (apply Nat.div_eq_of_lt_le <;> grind)
      | grind))),
    -- non-linear division
    ("nonlinear", ← `(tactic| (intros <;> blaster_denorm <;> blaster_nl_div))),
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
        | (simp_all [Nat.div_lt_iff_lt_mul, Nat.le_div_iff_mul_le, Nat.mod_def, Nat.mul_comm]; omega)))),
    -- `Nat.log2` (opaque for the solver, defined with `Nat.rec` in core): one unfolding step
    ("unfold", ← `(tactic| (intros <;> blaster_denorm <;> rw [Nat.log2_def] <;> split <;> first | omega | grind))),
    -- existential goals over types (e.g., `∃ (α : Type) (x : α), α = Nat`)
    ("exists", ← `(tactic| (intros <;> first | exact ⟨_, rfl⟩ | exact ⟨_, default, rfl⟩ | exact ⟨_, _, rfl⟩))),
    -- goals valid due to an empty type (e.g., `g : Nat → E` with `E` empty)
    ("empty", ← `(tactic| (intros <;> blaster_nomatch))),
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
