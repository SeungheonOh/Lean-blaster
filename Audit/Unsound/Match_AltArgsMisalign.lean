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
def bad (x y : Nat) (h : x = y) (z : Nat) : Nat :=
  match _hx : x, y, h, z with
  | _a, _, rfl, k => k
#check @bad.match_1
#print bad
example : bad 1 1 rfl 7 = 7 := rfl
#opt ∀ x y (h : x = y) z, bad x y h z = x
theorem t : ∀ x y (h : x = y) z, bad x y h z = x := by blaster
theorem f : False := by have := t 1 1 rfl 7; simp [bad] at this
