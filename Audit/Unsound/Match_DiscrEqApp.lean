import Lean
import Blaster
open Lean Elab Command Term Meta

syntax (name := optShow) "#opt " term : command
@[command_elab optShow]
def optShowImp : CommandElab := fun stx => do
  runTermElabM fun _ => do
    let e ← elabTermAndSynthesize stx[1] none
    let r ← withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $
      Blaster.Optimize.command default e
    logInfo m!"{r.1}"
set_option pp.funBinderTypes true
def F (x : Nat) : Nat → Nat → Nat :=
  match _h : x with
  | _n+1 => fun y _ => y
  | _m => fun y _ => y
#check @F.match_1
example : F 3 5 7 = 5 := rfl
#opt ∀ x, F x 5 7 = F x 6 7
theorem t : ∀ x, F x 5 7 = F x 6 7 := by blaster
theorem f : False := by have := t 0; simp [F] at this
