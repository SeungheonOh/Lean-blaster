import Blaster

theorem i1 (x y z : Nat) (h : x * x = y) : x * x * x = x * y := by
  blaster (only-optimize: 1)
  trace_state
  sorry

theorem i2 (f : Nat → Nat) (x : Nat) (hf : ∀ n, f n = n) : f x = x + 0 + 0 * x := by
  blaster (only-optimize: 1)
  trace_state
  sorry

axiom ax1 : ∀ n : Nat, n * 2 = n + n
theorem i3 (x : Nat) (y : Nat) : x * y = y * x := by
  blaster (only-optimize: 1)
  trace_state
  sorry
