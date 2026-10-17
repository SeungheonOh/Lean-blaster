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
def f1 (x : Nat) : Nat := match _h : x with | 0 => 1 | n+1 => n + 2
#opt ∀ x, f1 x = x
def f1c (x : Option Nat) : Nat := match h : x with | some n => n + 1 | none => 0
#opt ∀ x, f1c x ≠ 4
