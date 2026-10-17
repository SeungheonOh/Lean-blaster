import Blaster

-- structEq? treats Prop-valued ctor fields (proofs) as discriminating
structure P where
  h : True ∨ True

theorem bad1 : ¬ (P.mk (Or.inl trivial) = P.mk (Or.inr trivial)) := by blaster
example : P.mk (Or.inl trivial) = P.mk (Or.inr trivial) := rfl

theorem bad2 : ¬ ((⟨3, Or.inl rfl⟩ : {n : Nat // n = 3 ∨ n = 3}) = ⟨3, Or.inr rfl⟩) := by blaster
example : ((⟨3, Or.inl rfl⟩ : {n : Nat // n = 3 ∨ n = 3}) = ⟨3, Or.inr rfl⟩) := rfl

-- proofs directly at Prop
theorem bad3 : ¬ ((Or.inl trivial : True ∨ True) = Or.inr trivial) := by blaster

theorem false1 : False := bad1 rfl
