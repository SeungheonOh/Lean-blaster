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
#opt ∀ o : Option Nat,
  (Option.casesOn (motive := fun _ => Nat → Nat → Nat) o (fun y z => y - z) (fun _ y z => y - z)) 5 =
   Option.casesOn (motive := fun _ => Nat → Nat) o (fun z => z - 5) (fun _ z => 5 - z)
theorem t : ∀ o : Option Nat,
  (Option.casesOn (motive := fun _ => Nat → Nat → Nat) o (fun y z => y - z) (fun _ y z => y - z)) 5 =
   Option.casesOn (motive := fun _ => Nat → Nat) o (fun z => z - 5) (fun _ z => 5 - z) := by blaster
theorem f : False := by
  have h := congrFun (t none) 0
  simp at h
