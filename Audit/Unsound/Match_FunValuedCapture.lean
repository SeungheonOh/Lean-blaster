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
def k4 (b : Bool) : Prop → Prop := match b with | true => fun y => ¬ y | false => fun y => y
def k6 (b : Bool) : Prop → Prop := match b with | true => fun y => ¬ y | false => fun _ => True
#opt ∀ b, k4 b = k6 b
theorem t1 : ∀ b, k4 b = k6 b := by blaster
theorem f1 : False := by
  have h := congrFun (t1 false) False
  simp [k4, k6] at h

def m1 (b : Bool) : Bool → Bool := match b with | true => fun y => !y | false => fun y => y
def m2 (b : Bool) : Bool → Bool := match b with | true => fun y => !y | false => fun _ => true
#opt ∀ b, m1 b = m2 b
theorem t2 : ∀ b, m1 b = m2 b := by blaster
theorem f2 : False := by
  have h := congrFun (t2 false) false
  simp [m1, m2] at h
