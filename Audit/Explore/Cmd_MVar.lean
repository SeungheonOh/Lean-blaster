import Blaster

-- natural mvar from apply
theorem m1 (x : Nat) (h : x ≤ 3) : x ≤ 5 := by
  apply Nat.le_trans
  · blaster
  · blaster

theorem m2 : ∃ n : Nat, n = 1 ∧ n = 2 := by
  refine ⟨?n, ?_⟩
  blaster

theorem m3 : ∃ n : Nat, n + 0 = n ∧ n = 2 := by
  refine ⟨?n, ?_, ?_⟩
  · blaster
  · rfl

theorem m4 : ∃ n : Nat, n = n → n = 2 := by
  refine ⟨?n, ?_⟩
  blaster
  rfl
