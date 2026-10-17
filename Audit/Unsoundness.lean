import Blaster

/-
  Reproductions for the staging audit. Each `False` theorem is accepted by Lean
  because `blaster` admits a goal after reporting a transformed goal as valid.
  The `by decide` witnesses check the actual arithmetic semantics independently.
-/

namespace BlasterAudit

theorem tdiv_wrong : Int.tdiv (-7) 3 = -3 := by
  blaster (only-optimize: 1)

theorem tdiv_false : False := by
  have actual : Int.tdiv (-7) 3 ≠ -3 := by decide
  exact actual tdiv_wrong

theorem tmod_wrong : Int.tmod (-7) 3 = 2 := by
  blaster (only-optimize: 1)

theorem tmod_false : False := by
  have actual : Int.tmod (-7) 3 ≠ 2 := by decide
  exact actual tmod_wrong

theorem fdiv_wrong : Int.fdiv 7 (-3) = -2 := by
  blaster (only-optimize: 1)

theorem fdiv_false : False := by
  have actual : Int.fdiv 7 (-3) ≠ -2 := by decide
  exact actual fdiv_wrong

theorem fmod_wrong : Int.fmod 7 (-3) = 1 := by
  blaster (only-optimize: 1)

theorem fmod_false : False := by
  have actual : Int.fmod 7 (-3) ≠ 1 := by decide
  exact actual fmod_wrong

class ImpossibleClass where
  n : Nat
  contradiction : False

theorem impossible_class_exists : ∃ (_ : ImpossibleClass), True := by
  blaster (only-optimize: 1)

theorem impossible_class_false : False := by
  obtain ⟨inst, _⟩ := impossible_class_exists
  exact inst.contradiction

inductive EmptyP : Prop
inductive EmptyQ : Prop

theorem leaked_context :
    (EmptyP → EmptyP ∨ EmptyQ) ∧ (EmptyP ∨ EmptyQ) := by
  blaster (only-optimize: 1)

theorem leaked_context_false : False := by
  cases leaked_context.2 with
  | inl h => cases h
  | inr h => cases h

end BlasterAudit
