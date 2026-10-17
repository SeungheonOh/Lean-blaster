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
deriving Inhabited

def DischargeStats.record (s : DischargeStats) (method : String) : DischargeStats :=
  { s with byMethod := s.byMethod.insert method (s.byMethod.getD method 0 + 1) }

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
    let gs ← withHeartbeatBudget budget <| withoutErrToSorry <| Tactic.run mvar.mvarId! (evalTactic tac)
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

/-- The portfolio of tactics used to discharge proof obligations, in order of application. -/
def dischargeTactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("simp", ← `(tactic| ((try simp only [Blaster.Reconstruct.dite'_eq_dite, Blaster.Reconstruct.decide'_eq_decide] at *) <;> simp [*] <;> done))),
    ("omega", ← `(tactic| ((try apply propext) <;> (try simp only [Blaster.Reconstruct.dite'_eq_dite, Blaster.Reconstruct.decide'_eq_decide] at *) <;> omega))),
    ("grind", ← `(tactic| ((try simp only [Blaster.Reconstruct.dite'_eq_dite, Blaster.Reconstruct.decide'_eq_decide] at *) <;> grind)))
  ]

/-- Try to discharge proof obligation `type` (expected to be an equality) and return
    the proof together with the method used.
-/
def dischargeOne (type : Expr) : TermElabM (Option (Expr × String)) := do
  let type ← instantiateMVars type
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
def dischargeHoles (p : Expr) : TermElabM (Expr × DischargeStats) := do
  let stats ← IO.mkRef ({} : DischargeStats)
  let p' ← Meta.transform p (pre := fun e => do
    match holeType? e with
    | none => return .continue
    | some type =>
        stats.modify fun s => { s with total := s.total + 1 }
        match ← dischargeOne type with
        | some (prf, method) =>
            stats.modify (·.record method)
            return .done prf
        | none =>
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
  let tacs : Array (String × TSyntax `tactic) := #[
    ("decide", ← `(tactic| decide)),
    ("simp", ← `(tactic| ((try simp only [Blaster.Reconstruct.dite'_eq_dite, Blaster.Reconstruct.decide'_eq_decide]) <;> simp <;> done))),
    ("omega", ← `(tactic| (intros <;> (try simp only [Blaster.Reconstruct.dite'_eq_dite, Blaster.Reconstruct.decide'_eq_decide] at *) <;> omega))),
    ("grind", ← `(tactic| ((try simp only [Blaster.Reconstruct.dite'_eq_dite, Blaster.Reconstruct.decide'_eq_decide]) <;> grind)))
  ]
  for (name, tac) in tacs do
    if let some prf ← proveWithTactic e tac (budget := 4 * dischargeHeartbeats) then
      return some (prf, name)
  return none

end Blaster.Reconstruct
