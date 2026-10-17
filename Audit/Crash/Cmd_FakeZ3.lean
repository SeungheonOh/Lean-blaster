import Blaster
example (x : Nat) (h : x * x = 4) : x = 2 := by blaster
example : ∀ (f : Nat → Nat), f (f 0) = f 0 → f 0 = 0 := by blaster
