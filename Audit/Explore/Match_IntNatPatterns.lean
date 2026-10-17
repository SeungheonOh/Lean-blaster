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
def i1 (x : Int) : Int := match x with | .ofNat (n+2) => n | .negSucc (n+1) => n + 100 | .ofNat 1 => 50 | _ => 77
example : i1 5 = 3 ∧ i1 (-3) = 101 ∧ i1 1 = 50 ∧ i1 0 = 77 ∧ i1 (-1) = 77 := by decide
#opt ∀ x, i1 x = 0
#blaster [ i1 5 = 3 ∧ i1 (-3) = 101 ∧ i1 1 = 50 ∧ i1 0 = 77 ∧ i1 (-1) = 77 ]
#blaster [ ∀ x, i1 x ≠ 101 ]  -- false
#blaster [ ∀ x, x ≥ 2 → i1 x = x - 2 ]  -- true
#blaster [ ∀ x, x ≤ -2 → i1 x = -x - 2 + 100 ]  -- true
#blaster [ ∀ x, i1 x ≠ 77 ]  -- false

def i2 (x : Option Int) : Int := match x with | some (.negSucc n) => n | some (.ofNat (n+1)) => n | some _ => 9 | none => 8
#blaster [ i2 (some (-4)) = 3 ∧ i2 (some 4) = 3 ∧ i2 (some 0) = 9 ∧ i2 none = 8 ]
#blaster [ ∀ x : Int, x < 0 → i2 (some x) = -x - 1 ]  -- true
#blaster [ ∀ x : Int, x > 0 → i2 (some x) = x - 1 ]  -- true
#blaster [ ∀ x, i2 x ≠ 9 ]  -- false

def n1 (x : Nat) : Nat := match x with | y@(z@(n+1)+1) => y + z * 10 + n * 100 | _ => 7
example : n1 5 = 5 + 40 + 300 := by decide
#opt ∀ x, n1 x = 0
#blaster [ n1 5 = 345 ∧ n1 1 = 7 ∧ n1 0 = 7 ]
#blaster [ ∀ x, x ≥ 2 → n1 x = x + (x-1)*10 + (x-2)*100 ]  -- true
#blaster [ ∀ x, x ≥ 2 → n1 x = x + (x-1)*10 + (x-1)*100 ]  -- false

def n2 (x : Nat) (y : Nat) : Nat := match x, y with | 3, _ => 1 | _, 3 => 2 | n+1, m+1 => n + m | _, _ => 0
#blaster [ ∀ x y, n2 x y = if x = 3 then 1 else if y = 3 then 2 else if x ≥ 1 ∧ y ≥ 1 then x + y - 2 else 0 ] -- true
#blaster [ ∀ x y, n2 x y ≠ 2 ] -- false
#blaster [ ∀ x y, y = 3 → n2 x y = 2 ] -- false (x = 3)
