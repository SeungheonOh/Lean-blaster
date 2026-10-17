import Blaster

namespace BlasterAudit

inductive OnlyZero : Nat → Type where
  | zero : OnlyZero 0

theorem indexed_exists : ∃ (_ : OnlyZero 1), True := by
  blaster (only-optimize: 1)

theorem indexed_exists_false : False := by
  obtain ⟨x, _⟩ := indexed_exists
  cases x

end BlasterAudit
