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
def f3 (x y : Nat) (h : x = y) : Nat := match x, y, h with | a, _, rfl => a + 1
#opt ∀ x y (h : x = y), f3 x y h = x + 1
#blaster [ ∀ x y (h : x = y), f3 x y h = x + 1 ]
#blaster [ ∀ x y (h : x = y), f3 x y h = x ]
def f3f (x y : Nat) (h : x = y) : Nat → Nat := match x, y, h with | a, _, rfl => fun z => z + a
#opt ∀ x y (h : x = y), f3f x y h 10 = 10 + x
#blaster [ ∀ x y (h : x = y), f3f x y h 10 = 10 + x ]
#blaster [ ∀ x y (h : x = y), f3f x y h 10 = 2 * x ]

inductive Vec (α : Type) : Nat → Type | nil : Vec α 0 | cons : {n : Nat} → α → Vec α n → Vec α (n+1)
def f4 (n : Nat) (v : Vec Nat n) : Nat := match n, v with | _, .cons a _ => a | _, .nil => 0
#opt ∀ n (v : Vec Nat n), f4 n v = 0
#blaster [ ∀ n (v : Vec Nat n), f4 n v = 0 ]
#blaster [ ∀ (a : Nat), f4 1 (.cons a .nil) = a ]
#blaster [ ∀ (a : Nat), f4 1 (.cons a .nil) = 0 ]
