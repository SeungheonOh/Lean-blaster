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

/-- Try to close goal `type` with tactic `tac`. The elaboration state is restored on failure. -/
def proveWithTactic (type : Expr) (tac : TSyntax `tactic) (budget := dischargeHeartbeats) : TermElabM (Option Expr) := do
  let s ← saveState
  try
    let mvar ← mkFreshExprMVar type
    -- NOTE: asynchronous elaboration is disabled such that kernel errors on auxiliary declarations
    -- created by tactics are reported as exceptions instead of messages.
    let gs ← withOptions (fun o => Elab.async.set o false) <|
               withHeartbeatBudget budget <| withoutErrToSorry <| Tactic.run mvar.mvarId! (evalTactic tac)
    let prf ← instantiateMVars mvar
    if !gs.isEmpty || prf.hasMVar || prf.hasSorry then
      s.restore
      return none
    return some prf
  catch _ =>
    s.restore
    return none

/-- Try to prove `lhs = rhs` by definitional unfolding. -/
def proveByDefEq (type : Expr) (budget := dischargeHeartbeats) : MetaM (Option Expr) := do
  let some (_, lhs, rhs) := type.eq? | return none
  try
    if ← withHeartbeatBudget budget <| withTransparency .default <| isDefEq lhs rhs then
      return some (← mkExpectedTypeHint (← mkEqRefl lhs) type)
    return none
  catch _ => return none

/-- Return `true` if `type` is type correct. -/
def isTypeCorrectObligation (type : Expr) : MetaM Bool := do
  try
    withHeartbeatBudget dischargeHeartbeats <| Meta.check type
    return true
  catch _ => return false

/-- The portfolio of tactics used to discharge proof obligations, in order of application. -/
def dischargeTactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("simp", ← `(tactic| (blaster_denorm <;> simp [*] <;> done))),
    ("omega", ← `(tactic| ((try apply propext) <;> blaster_denorm <;> omega))),
    ("grind", ← `(tactic| (blaster_denorm <;> grind)))
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

/-- Try to prove the residual goal `e` (i.e., an optimized expression proved valid by the
    backend SMT solver) using decision procedures available in Lean.
-/
def proveResidual (e : Expr) : TermElabM (Option (Expr × String)) := do
  if !(← isTypeCorrectObligation e) then return none
  let tacs : Array (String × TSyntax `tactic) := #[
    ("decide", ← `(tactic| decide)),
    ("simp", ← `(tactic| (blaster_denorm <;> simp <;> done))),
    ("omega", ← `(tactic| (intros <;> blaster_denorm <;> omega))),
    ("grind", ← `(tactic| (blaster_denorm <;> grind)))
  ]
  for (name, tac) in tacs do
    if let some prf ← proveWithTactic e tac (budget := 4 * dischargeHeartbeats) then
      return some (prf, name)
  return none

end Blaster.Reconstruct
