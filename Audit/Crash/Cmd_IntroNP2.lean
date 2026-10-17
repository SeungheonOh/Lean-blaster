import Blaster

theorem i4 (x y z w : Nat) : x * x = 2 := by
  blaster (only-optimize: 1)
  sorry

theorem i5 (x y z w : Nat) : x * x * x = 2 := by
  blaster (timeout: 1)
  sorry
