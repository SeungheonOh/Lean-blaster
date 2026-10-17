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
-- casesOn basics
#blaster [ ∀ b : Bool, (Bool.casesOn (motive := fun _ => Nat) b 1 2) = if b then 2 else 1 ]  -- true
#blaster [ ∀ b : Bool, (Bool.casesOn (motive := fun _ => Nat) b 1 2) = if b then 1 else 2 ]  -- false
#blaster [ ∀ o : Option Nat, (Option.casesOn (motive := fun _ => Nat) o 0 (fun n => n + 1)) = o.getD 0 + (if o.isSome then 1 else 0) ] -- true
#blaster [ ∀ n : Nat, (Nat.casesOn (motive := fun _ => Nat) n 7 (fun m => m)) = n - 1 ] -- false (n=0)
-- function valued casesOn applied
#opt ∀ b : Bool, (Bool.casesOn (motive := fun _ => Nat → Nat → Nat) b (fun y z => y - z) (fun y z => y - z)) 5 = fun z => z - 5
#blaster [ ∀ b : Bool, (Bool.casesOn (motive := fun _ => Nat → Nat → Nat) b (fun y z => y - z) (fun y z => y - z)) 5 = fun z => z - 5 ]
#blaster [ ∀ b : Bool, (Bool.casesOn (motive := fun _ => Nat → Nat → Nat) b (fun y z => y - z) (fun y z => y - z)) 5 9 = 0 ] -- true
#blaster [ ∀ b : Bool, (Bool.casesOn (motive := fun _ => Nat → Nat → Nat) b (fun y z => y - z) (fun y z => y - z)) 9 5 = 0 ] -- false
#opt ∀ b : Bool, (Bool.casesOn (motive := fun _ => Nat → Nat) b (fun y => y) (fun y => y + 1)) 5 = 5
#blaster [ ∀ b : Bool, (Bool.casesOn (motive := fun _ => Nat → Nat) b (fun y => y) (fun y => y + 1)) 5 = 5 ] -- false
