import Blaster
noncomputable def d : Nat := Classical.choose (⟨5, rfl⟩ : ∃ n : Nat, n = 5)
theorem d_eq : d = 5 := Classical.choose_spec (⟨5, rfl⟩ : ∃ n : Nat, n = 5)
-- Hypothesis context (not a match): closed `if d = 6 ..` optimized under hyp `d = 6`
-- is cached globally and reused outside the implication.
theorem bad : (d = 6 → (if d = 6 then True else False)) ∧ (if d = 6 then True else False) := by blaster
theorem f : False := by have h := bad.2; rw [d_eq] at h; simp at h
