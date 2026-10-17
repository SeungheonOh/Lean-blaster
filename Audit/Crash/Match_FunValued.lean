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
def k (b : Bool) : Nat → Nat := match b with | true => fun y => y + 1 | false => fun y => y
#opt ∀ b, k b = fun y => y
#opt ∀ b, (k b) 3 = 3
#blaster [ ∀ b, k b = fun y => y ]
#blaster [ ∀ b, (k b) 3 = 3 ]
#opt ∀ b, List.map (k b) [3] = [3]
#blaster [ ∀ b, List.map (k b) [3] = [3] ]
def k2 (x : Nat) : Nat → Nat := match x with | 0 => fun y => y + 1 | _ => fun y => y
#opt ∀ x, List.map (k2 x) [3] = [3]
#blaster [ ∀ x, List.map (k2 x) [3] = [3] ]
#blaster [ ∀ x, k2 x = fun y => y ]
#blaster [ ∀ x, k2 x 3 = 3 ]
