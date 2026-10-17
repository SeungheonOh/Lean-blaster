import Blaster

theorem u1 (x y : Nat) (h : x < y) : x + 1 ≤ y := by
  blaster (only-optimize: 1)
  trace_state
  omega

theorem u2 (x y : Nat) (h : y = 2) : x + x = 2 * x := by
  blaster (only-optimize: 1)
  trace_state
  omega

theorem u3 (x y : Nat) : x * y = y * x := by
  blaster (only-optimize: 1)
  trace_state
  sorry

theorem u4 (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  blaster (only-optimize: 1)
  trace_state
  exact ⟨‹q›, ‹p›⟩
