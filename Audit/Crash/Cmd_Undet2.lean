import Blaster

theorem u2 (x y : Nat) (h : y = 2) : x + x = 2 * x := by
  blaster (only-optimize: 1)
  intro _
  show x + x = 2 * x
  omega

-- axiom present in file: replaced goal gets an extra hypothesis
axiom myAx : ∀ n : Nat, n + 0 = n
theorem u5 (x y : Nat) (h : y = 2) : x + x = 2 * x := by
  blaster (only-optimize: 1)
  trace_state
  sorry
