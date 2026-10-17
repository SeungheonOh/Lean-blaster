import Blaster

/-! `structEq?` (Optimize/Rewriting/OptimizeEq.lean) decides `C a₁… = C b₁…` by comparing the
constructor arguments, even when the equality is between *proofs* (the inductive lives in `Prop`).
Here the differing arguments are ordinary data (`Nat`), not Prop fields, so this is NOT covered
by the suggested fix for REPORT #8 ("skip Prop-typed args"): the whole equation is trivially true
by proof irrelevance because the type `Nonempty Nat` is a Prop. -/

set_option trace.Translate.optExpr true in
theorem bad : (⟨0⟩ : Nonempty Nat) ≠ ⟨1⟩ := by blaster

theorem bad_neg : ¬ ((⟨0⟩ : Nonempty Nat) ≠ ⟨1⟩) := fun h => h rfl

theorem oops : False := bad_neg bad

-- same with Exists and a user-defined Prop inductive
theorem bad2 : (⟨0, trivial⟩ : ∃ _ : Nat, True) ≠ ⟨1, trivial⟩ := by blaster
theorem oops2 : False := bad2 rfl

inductive Tok : Prop
  | mk : Nat → Tok

theorem bad3 : ∀ a b : Nat, Tok.mk a = Tok.mk b → a = b := by blaster
theorem oops3 : False := absurd (bad3 0 1 rfl) (by decide)

#print axioms oops
#print axioms oops3
