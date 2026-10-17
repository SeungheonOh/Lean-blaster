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
def f5 (x : Int) : Nat := match x with | .negSucc n => n | .ofNat 3 => 7 | .ofNat n => n
#opt ∀ x, f5 x = 0
#blaster [ ∀ x, f5 x ≠ 7 ]          -- false (x=3 or x=-8)
#blaster [ ∀ x : Int, x ≥ 0 → x ≠ 3 → f5 x = x.toNat ]   -- true
#blaster [ ∀ x : Int, x < 0 → f5 x = (-x - 1).toNat ]   -- true
#blaster [ f5 3 = 7 ∧ f5 (-1) = 0 ∧ f5 4 = 4 ∧ f5 (-5) = 4 ]   -- true
#blaster [ ∀ n : Nat, f5 (Int.negSucc n) = n ]   -- true
def f10 (x : Int) : Nat := match x with | -3 => 1 | 5 => 2 | _ => 3
#opt ∀ x, f10 x = 0
#blaster [ ∀ x, f10 x ≠ 1 ]   -- false
#blaster [ ∀ x, x ≠ -3 → x ≠ 5 → f10 x = 3 ]   -- true
#blaster [ f10 (-3) = 1 ]   -- true
def f6 (c : Char) : Nat := match c with | 'a' => 1 | _ => 2
#opt ∀ x, f6 x = 0
#blaster [ ∀ x, f6 x ≠ 1 ]   -- false
#blaster [ f6 'a' = 1 ∧ f6 'b' = 2 ]   -- true
def f7 (s : String) : Nat := match s with | "a" => 1 | _ => 2
#blaster [ ∀ x, f7 x ≠ 1 ]   -- false
#blaster [ ∀ x, x ≠ "a" → f7 x = 2 ]   -- true
def f8 (x : Fin 3) : Nat := match x with | 0 => 1 | 1 => 2 | _ => 3
#opt ∀ x, f8 x = 0
#blaster [ ∀ x, f8 x ≠ 2 ]   -- false
#blaster [ ∀ x, f8 x ≠ 0 ]   -- true
def f9 (x : UInt8) : Nat := match x with | 0 => 1 | _ => 3
#opt ∀ x, f9 x = 0
#blaster [ ∀ x, f9 x ≠ 1 ]   -- false
