import Lean
import Blaster

namespace Test.SmtUninhabited

/-! ## Test objectives to validate that the smt translation does not assume that sort variables are inhabited.

  Sort variables (e.g., `α : Type`) are all mapped to the universal smt sort `@@Type`, which can never be empty.
  Each quantified sort variable `α` therefore has its own (uninterpreted) membership predicate characterizing
  the subset of `@@Type` denoted by `α`. This subset may be empty and its cardinality is independent from
  the one of any other sort variable.
-/

/-! Test cases to ensure that sort variables may be instantiated with an empty type. -/

-- Counterexample: `α := Empty`
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (α : Type), (∀ (_x : α), False) → False ]

-- Counterexample: `α := Empty`
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (α : Type), ¬ ∃ (_x : α), True ]

-- Counterexample: `α := Empty` (the only `List Empty` is `[]`)
#blaster (timeout: 5) (solve-result: 2) [ ∀ (α : Type), (∀ (xs : List α), xs = []) → False ]

-- Counterexample: `α := Empty`
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (α : Type) [Add α], (∀ (_x : α), False) → False ]

-- Counterexample: `α := Empty`, `f := Empty.elim`
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (α : Type) (_f : α → Empty), False ]

-- Counterexample: `α := Empty`, `β := Empty`, `f := Empty.elim`
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (α β : Type) (_f : α → β), (∀ (_y : β), False) → False ]

-- Counterexample: `α := Empty`, `γ := Bool`, `h := id`, `k := not`
-- Test case: functions over an empty domain must not collapse functions of other types sharing the same smt sort.
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (α γ : Type) (_f : α → α) (h k : γ → γ), (∀ (_x : α), False) → h = k ]

-- Counterexample: `α := Empty`, `γ := Bool`, `h := id`, `k := not`
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (α γ : Type) (_f : α → γ) (h k : γ → γ), (∀ (_x : α), False) → h = k ]

/-! Test cases to ensure that distinct sort variables do not have the same cardinality. -/

-- Counterexample: `α := Unit`, `β := Bool`
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (α β : Type), (∀ (a1 a2 : α), a1 = a2) → ∀ (b1 b2 : β), b1 = b2 ]

/-! Test cases to ensure that valid theorems over sort variables are still proved. -/

#blaster [ ∀ (α : Type) (a : α), (∀ (_x : α), False) → False ]

#blaster [ ∀ (α : Type), (∃ (_x : α), True) → ∃ (_y : α), True ]

#blaster [ ∀ (α : Type) (xs : List α), (∀ (ys : List α), ys = []) → xs = [] ]

#blaster [ ∀ (α β : Type) (f : α → β) (x : α) (p : β → Prop), (∀ (y : β), p y) → p (f x) ]

#blaster [ ∀ (α β : Type) (f : α → β), (∀ (_y : β), False) → ∀ (_x : α), False ]

#blaster [ ∀ (α : Type) (x y : α) (xs : List α), x :: xs = y :: xs → x = y ]

-- function extensionality on the domain of each function type instance
#blaster [ ∀ (α β : Type) (f g : α → β), (∀ (x : α), f x = g x) → f = g ]

-- lambda terms are members of their function type instance
#blaster [ ∀ (α : Type) (f : α → α), (∀ x, f x = x) → f = (fun x => x) ]

-- codomain constraint for each instantiation of a class function
class ToNat (α : Type) where
  toNat : α → Nat

#blaster [ ∀ (α β : Type) [ToNat α] [ToNat β] (x : α) (y : β),
             Int.ofNat (ToNat.toNat x) ≥ 0 ∧ Int.ofNat (ToNat.toNat y) ≥ 0 ]

-- polymorphic hypotheses are instantiated with the top level sort variables
#blaster [ (∀ (β : Type) (xs : List β) (f : List β → Nat), f xs > 10) →
           ∀ (α : Type) (xs : List α) (f : List α → Nat), f xs > 5 ]

end Test.SmtUninhabited
