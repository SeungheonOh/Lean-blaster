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
def k3 (b : Bool) : Bool → Bool := match b with | true => fun y => !y | false => fun y => y
#opt ∀ b, k3 b = fun y => y
#blaster (dump-smt-lib: 1) [ ∀ b, k3 b = fun y => y ]
#blaster [ ∀ b, k3 b = fun y => !y ]
#blaster [ ∀ b, List.map (k3 b) [true] = [true] ]
#blaster [ ∀ b, List.map (k3 b) [true] = [false] ]
def k4 (b : Bool) : Prop → Prop := match b with | true => fun y => ¬ y | false => fun y => y
#opt ∀ b, k4 b = fun y => y
#blaster [ ∀ b, k4 b = fun y => y ]
#blaster [ ∀ b, k4 b = fun y => ¬ y ]
#blaster [ ∀ b, k4 b True ]
