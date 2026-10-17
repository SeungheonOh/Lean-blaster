import Blaster

noncomputable def one : Nat := Classical.choose (⟨1, rfl⟩ : ∃ n : Nat, n = 1)
theorem one_eq : one = 1 := Classical.choose_spec (⟨1, rfl⟩ : ∃ n : Nat, n = 1)

-- ITE variant of the closed-term hypothesis leak
theorem bad_ite : (one = 0 → (if one = 0 then 1 else 2) = 1) ∧ (if one = 0 then 1 else 2) = 1 := by
  blaster

-- match-context variant
theorem bad_match : (match one with | 0 => ((match one with | 0 => 1 | _ => 2) = 1) | _ => True) ∧
                    (match one with | 0 => 1 | _ => 2) = 1 := by
  blaster

theorem oops1 : False := by
  have h := bad_ite.2; rw [one_eq] at h; exact absurd h (by decide)
theorem oops2 : False := by
  have h := bad_match.2; rw [one_eq] at h; exact absurd h (by decide)
