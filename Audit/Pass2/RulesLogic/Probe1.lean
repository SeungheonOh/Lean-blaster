import Blaster

-- impliesToNeg? with non-Prop antecedent (type variable)
theorem p1 : ∀ (α : Type) (q : Prop), ¬ q → ∀ (_ : α), q := by blaster
-- with Prop-typed binder (Sort)
theorem p2 : ∀ (q : Prop), ¬ q → ∀ (_ : Prop), q := by blaster
-- with Bool
theorem p3 : ∀ (q : Prop), ¬ q → ∀ (_ : Bool), q := by blaster
