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
def o1 (x : Option Nat) : Prop → Prop := match x with | none => fun y => ¬ y | some _ => fun y => y
def o2 (x : Option Nat) : Prop → Prop := match x with | none => fun y => ¬ y | some _ => fun _ => True
#opt ∀ x, o1 x = o2 x
#blaster [ ∀ x, o1 x = o2 x ]

def mm (b : Bool) : Prop → Prop := match (generalizing := false) b with
  | true => (match b with | true => fun y => ¬ y | false => fun y => y)
  | false => fun y => y
#opt ∀ b, mm b = fun y => ¬ y
#opt ∀ b, mm b False
#blaster [ ∀ b, mm b False ]   -- false (b = false)

def cr (x : Nat) : Nat → Nat := match x with | 0 => fun _ => 7 | _+1 => fun _ => 7
#opt ∀ x, cr x = fun _ => 7
#blaster [ ∀ x, cr x = fun _ => 7 ]
