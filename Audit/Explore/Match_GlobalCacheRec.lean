import Blaster
noncomputable def d : Nat := Classical.choose (⟨5, rfl⟩ : ∃ n : Nat, n = 5)
theorem d_eq : d = 5 := Classical.choose_spec (⟨5, rfl⟩ : ∃ n : Nat, n = 5)

noncomputable def r : Nat → Nat
  | 0 => (match d with | 5 => 1 | _ => 2)
  | n+1 => r n

theorem bad : ∀ n, (match d with | 5 => True | _ => r n = 2) ∧ r 0 = 2 := by blaster
theorem f : False := by
  have h := (bad 0).2
  simp [r, d_eq] at h
