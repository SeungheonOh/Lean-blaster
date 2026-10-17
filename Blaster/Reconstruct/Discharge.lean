import Lean
import Blaster.Reconstruct.Types
import Blaster.Reconstruct.Proof
import Blaster.Reconstruct.Lemmas

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
  (budget : Nat) (x : m (Option α)) : m (Option α) := do
  let st ← saveState
  tryCatchRuntimeEx
    (withHeartbeatBudget budget <|
       withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := dischargeMaxRecDepth }) x)
    (fun _ => do restoreState st; return none)

/-- Try to close goal `type` with tactic `tac`. The elaboration state is restored on failure. -/
def proveWithTactic (type : Expr) (tac : TSyntax `tactic) (budget := dischargeHeartbeats) : TermElabM (Option Expr) := do
  let s ← saveState
  let r ← attempt budget do
    let mvar ← mkFreshExprMVar type
    -- NOTE: asynchronous elaboration is disabled such that kernel errors on auxiliary declarations
    -- created by tactics are reported as exceptions instead of messages.
    let gs ← withOptions (fun o => Elab.async.set o false) <|
               withoutErrToSorry <| Tactic.run mvar.mvarId! (evalTactic tac)
    let prf ← instantiateMVars mvar
    if !gs.isEmpty || prf.hasMVar || prf.hasSorry then return none
    return some prf
  if r.isNone then s.restore
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

/-- The portfolio of tactics used to discharge proof obligations, in order of application. -/
def dischargeTactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("simp", ← `(tactic| (blaster_denorm <;> simp [*] <;> done))),
    ("omega", ← `(tactic| ((try apply propext) <;> blaster_denorm <;> omega))),
    ("grind", ← `(tactic| (blaster_denorm <;> grind))),
    -- case analysis (e.g., `match` expressions normalized to `Blaster.dite'`)
    ("split", ← `(tactic| (blaster_denorm <;> (repeat' split) <;> first | omega | (simp_all; done) | grind)))
  ]

/-- Try to discharge proof obligation `type` (expected to be an equality) and return
    the proof together with the method used.
-/
def dischargeOne (type : Expr) : TermElabM (Option (Expr × String)) := do
  let type ← instantiateMVars type
  -- ill-typed proof obligations (e.g., due to ill-typed optimized expressions) can't be discharged
  if !(← isTypeCorrectObligation type) then return none
  if let some prf ← proveByDefEq type then return some (prf, "rfl")
  for (name, tac) in (← dischargeTactics) do
    if let some prf ← proveWithTactic type tac then return some (prf, name)
  return none

/-- Return the type of a hole, i.e., `t` in `mdata {blaster.hole := _} (sorryAx t _)`. -/
def holeType? (e : Expr) : Option Expr := do
  let _ ← isHole? e
  match e.consumeMData with
  | .app (.app (.const ``sorryAx _) t) _ => some t
  | _ => none

/-- Return `true` if `e` contains at least one proof obligation. -/
def hasHoles (e : Expr) : Bool :=
  (e.find? fun s => (isHole? s).isSome).isSome

/-- Discharge all the proof obligations in `p`.
    Return the updated proof term and the discharge statistics. Proof obligations that cannot be
    discharged are left unchanged in the returned proof term.
-/
def dischargeHoles (p : Expr) (holes : Array HoleInfo := #[]) : TermElabM (Expr × DischargeStats) := do
  let stats ← IO.mkRef ({} : DischargeStats)
  let p' ← Meta.transform p (pre := fun e => do
    match holeType? e with
    | none => return .continue
    | some type =>
        let label := match isHole? e with
                     | some idx => if h : idx < holes.size then holes[idx].label else "top"
                     | none => "top"
        stats.modify fun s => { s with total := s.total + 1 }
        match ← dischargeOne type with
        | some (prf, method) =>
            stats.modify (·.record method label)
            return .done prf
        | none =>
            stats.modify (·.record "failed" label)
            let lctx ← getLCtx
            let dangling := (type.find? fun s => s.isFVar && !lctx.contains s.fvarId!).isSome
            let msg ← addMessageContext (if dangling then m!"{type} (out of scope variables)" else m!"{type}")
            stats.modify fun s => { s with failures := s.failures.push msg }
            return .done e)
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

/-- Unfold (up to 3 rounds) the user definitions occurring in the main goal and its hypotheses. -/
@[tactic blasterUnfoldUser] def evalBlasterUnfoldUser : Tactic := fun _ => do
  let env ← getEnv
  for _ in [0:3] do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let mut t ← instantiateMVars (← g.getType)
    for d in ← g.withContext getLCtx do
      if !d.isImplementationDetail then t := mkApp t (← instantiateMVars d.type)
    let consts := t.getUsedConstants.filter (isUserDefinition env)
    if consts.isEmpty then return
    let lemmas ← consts.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    try evalTactic (← `(tactic| simp only [$lemmas,*] at *)) catch _ => return

/-- Maximum number of goals produced by `blaster_cases_vars`. -/
def maxCaseGoals : Nat := 128

syntax (name := blasterCasesVars) "blaster_cases_vars" : tactic

/-- Perform case analysis on the variables of inductive types (bounded by `maxCaseGoals`). -/
@[tactic blasterCasesVars] def evalBlasterCasesVars : Tactic := fun _ => do
  let g ← getMainGoal
  let vars ← g.withContext do
    let mut vars := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← whnfR d.type
      let .const n _ := t.getAppFn | continue
      let .inductInfo info ← getConstInfo n | continue
      if info.numIndices != 0 || (← isProp d.type) then continue
      vars := vars.push (d.fvarId, info.ctors.length)
    return vars
  let mut goals := [g]
  let mut nbGoals := 1
  for (v, nbCtors) in vars do
    if nbGoals * nbCtors > maxCaseGoals then break
    let mut newGoals := []
    for g in goals do
      -- the variable may have been substituted in some goals
      if !(← g.withContext (return (← getLCtx).contains v)) then
        newGoals := newGoals ++ [g]
        continue
      let subgoals ← g.cases v
      newGoals := newGoals ++ subgoals.toList.map (·.mvarId)
    goals := newGoals
    nbGoals := goals.length
  replaceMainGoal goals

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
                                     (try simp_all) <;> (try decide) <;> done))),
    -- non-linear division/modulo identities
    ("arith simp", ← `(tactic| (intros <;> blaster_denorm <;>
        simp_all [Nat.mod_add_div, Nat.div_add_mod, Nat.mul_div_mul_left, Nat.mul_div_cancel_left,
                  Nat.mul_mod_right, Nat.mul_mod_left, Nat.mod_mod, Nat.mod_self, Nat.div_self,
                  Int.emod_emod_of_dvd, Int.mul_emod_right, Int.mul_emod_left, Int.emod_add_ediv,
                  Int.ediv_add_emod, Nat.pos_iff_ne_zero] <;> done)))
  ]
  for (name, tac) in tacs do
    if let some prf ← proveWithTactic e tac (budget := 4 * dischargeHeartbeats) then
      return some (prf, name)
  return none

end Blaster.Reconstruct
