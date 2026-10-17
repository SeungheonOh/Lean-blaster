import Blaster

-- A closed (fvar-free) term that the optimizer cannot evaluate; provably equal to 0.
noncomputable def z : Nat := Classical.choose (⟨0, rfl⟩ : ∃ n : Nat, n = 0)
theorem z_eq : z = 0 := Classical.choose_spec (⟨0, rfl⟩ : ∃ n : Nat, n = 0)

-- `z / z` is rewritten to `1` under hypothesis `0 < z`; since `z / z` has no fvars,
-- the result is stored in the GLOBAL rewrite cache and reused outside the implication.
theorem bad : (0 < z → z / z = 1) ∧ (z / z = 1) := by blaster

theorem oops : False := by
  have h := bad.2
  rw [z_eq] at h
  exact absurd h (by decide)
