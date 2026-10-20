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

-- codomain constraint for each instantiation of a class function
class ToNat (α : Type) where
  toNat : α → Nat

#blaster [ ∀ (α β : Type) [ToNat α] [ToNat β] (x : α) (y : β),
             Int.ofNat (ToNat.toNat x) ≥ 0 ∧ Int.ofNat (ToNat.toNat y) ≥ 0 ]

-- polymorphic hypotheses are instantiated with the top level sort variables
#blaster [ (∀ (β : Type) (xs : List β) (f : List β → Nat), f xs > 10) →
           ∀ (α : Type) (xs : List α) (f : List α → Nat), f xs > 5 ]

/-! Test cases to ensure that sort quantifiers that are not in the top level ∀ prefix of the goal
    are soundly translated w.r.t. their polarity. -/

-- Counterexample: `p := False`, `α := Empty`
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (p : Prop), p ∨ ∀ (α : Type), (∀ (_x : α), False) → False ]

-- Counterexample: `p := False`, `n := 0`, `α := Empty` (sort quantifier under a universal quantifier)
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (p : Prop), p ∨ ∀ (n : Nat) (α : Type), (∀ (_x : α), n > 5) → n > 5 ]

-- Counterexample: `p := False`, `α := Empty` (sort quantifier with mixed polarity)
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (p : Prop), (p ↔ ∀ (α : Type), (∀ (_x : α), False) → False) → p ]

-- Counterexample: `p := False`, `α := Empty`
-- Test case: same sort quantifier in negative and positive position (translation not memoized)
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (p : Prop), ((∀ (α : Type), (∀ (_x : α), False) → False) → p) →
                  p ∨ ∀ (α : Type), (∀ (_x : α), False) → False ]

-- Counterexample: `p := False`, `α := Empty` (∃ over sort in negative position)
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (p : Prop), p ∨ ¬ ∃ (α : Type), ∀ (_x : α), False ]

-- Counterexample: `p := False`, `α := Empty` (∃ over sort in negative position)
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (p : Prop), p ∨ ((∃ (α : Type), ∀ (_x : α), False) → False) ]

-- Not a theorem (for `b := true` take `α := Empty` and for `b := false` take `α := Unit`).
-- Sort quantifier depending on an existential variable: `unsat` is reported as `Undetermined`.
#blaster (solve-result: 2)
  [ ∃ (b : Bool), ∀ (α : Type), (b = true ↔ ∃ (_x : α), True) ]

-- Not a theorem (counterexample: `f := λ n => decide (n > 5)`).
-- Sort quantifier with mixed polarity depending on a quantified variable:
-- `unsat` is reported as `Undetermined`.
#blaster (solve-result: 2)
  [ ∀ (f : Nat → Bool), (∀ (n : Nat), f n = true ↔ ∀ (α : Type), (∀ (_x : α), n > 5) → n > 5) → f 0 = true ]

-- Theorem (`n := 6`) but sort quantifier depending on an existential variable.
#blaster (solve-result: 2)
  [ ∃ (n : Nat), ∀ (α : Type), (∀ (_x : α), n > 5) → n > 5 ]

#blaster [ ∀ (p : Prop), p ∨ ∀ (α : Type) (a : α), (∀ (_x : α), False) → False ]

#blaster [ ∀ (p : Prop), p ∨ ∀ (α : Type) (x y : α) (xs : List α), x :: xs = y :: xs → x = y ]

#blaster [ ∃ (α : Type), ∃ (_x : α), True ]

#blaster [ ∀ (p : Prop), p ∨ ((∃ (α : Type) (x y : α), x ≠ y) → ∃ (β : Type) (u v : β), u ≠ v) ]

end Test.SmtUninhabited
