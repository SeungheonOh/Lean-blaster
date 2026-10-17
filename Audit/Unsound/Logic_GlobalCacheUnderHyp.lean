import Blaster
set_option trace.Translate.optExpr true
/-
  OptimizeStack.lean `isInOptimizeEnvCache`: `isGlobal := !a.hasFVar || isGlobalContext`.
  A closed sub-term optimized under a hypothesis (here `P ∧ Q` under hyp `P`, rewritten to `Q`
  by andPropReduction?) is stored in the GLOBAL rewrite cache and later reused outside the
  hypothesis scope.
-/
theorem bad : ((∃ n : Nat, n + n = 1) → ((∃ n : Nat, n + n = 1) ∧ (∃ n : Nat, n + n = 2))) →
              ((∃ n : Nat, n + n = 2) → ((∃ n : Nat, n + n = 1) ∧ (∃ n : Nat, n + n = 2))) := by
  blaster

theorem bad_false : ¬ (((∃ n : Nat, n + n = 1) → ((∃ n : Nat, n + n = 1) ∧ (∃ n : Nat, n + n = 2))) →
              ((∃ n : Nat, n + n = 2) → ((∃ n : Nat, n + n = 1) ∧ (∃ n : Nat, n + n = 2)))) := by
  intro h
  have hP : ¬ ∃ n : Nat, n + n = 1 := fun ⟨n, hn⟩ => by omega
  obtain ⟨⟨n, hn⟩, _⟩ := h (fun hp => absurd hp hP) ⟨1, rfl⟩
  omega

theorem contra : False := bad_false bad

-- same bug through the `dite'` then-branch hypothesis
open Classical in
theorem bad2 : (if (∃ n : Nat, n + n = 1) then ((∃ n : Nat, n + n = 1) ∧ (∃ n : Nat, n + n = 2)) else True) →
               ((∃ n : Nat, n + n = 2) → ((∃ n : Nat, n + n = 1) ∧ (∃ n : Nat, n + n = 2))) := by
  blaster

open Classical in
theorem bad2_false : ¬ ((if (∃ n : Nat, n + n = 1) then ((∃ n : Nat, n + n = 1) ∧ (∃ n : Nat, n + n = 2)) else True) →
               ((∃ n : Nat, n + n = 2) → ((∃ n : Nat, n + n = 1) ∧ (∃ n : Nat, n + n = 2)))) := by
  intro h
  have hP : ¬ ∃ n : Nat, n + n = 1 := fun ⟨n, hn⟩ => by omega
  obtain ⟨⟨n, hn⟩, _⟩ := h (by simp [hP]) ⟨1, rfl⟩
  omega

theorem contra2 : False := bad2_false bad2
