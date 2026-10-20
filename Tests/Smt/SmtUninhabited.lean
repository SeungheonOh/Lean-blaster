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

#blaster [ ∀ (p : Prop), p ∨ ∀ (n : Nat) (α : Type) (_a : α), (∀ (_x : α), n > 5) → n > 5 ]

-- Not a theorem (for every `m` take `n := m`).
-- Sort quantifier depending on a universal variable in the scope of an existential one:
-- `unsat` is reported as `Undetermined`.
#blaster (solve-result: 2)
  [ ∃ (m : Nat), ∀ (n : Nat), n ≠ m ∨
      ∀ (α : Type), (n = 0 → ∀ (_x : α), False) ∧ (n ≠ 0 → ∃ (_x : α), True) ]

/-! Test cases to ensure that sort quantifiers in the propositions of ctor fields are soundly translated.
    The predicate qualifier of a datatype is defined once and expanded at each of its applications,
    whatever their polarity. -/

structure FunRel where
  f [LT α] : α → α
  inv : ∀ (x y : α), [LT α] → x < y → f x < f y

structure FunRelWrap where
  r : FunRel
  n : Nat

-- predicate qualifier in negative position (see `Tests/FixedIssues/Issue15.lean`)
#blaster [ ∀ (α : Type) (r : FunRel) (x y : α) [LT α], x < y → r.f x < r.f y ]

-- nested predicate qualifier in negative position
#blaster [ ∀ (α : Type) (w : FunRelWrap) (x y : α) [LT α], x < y → w.r.f x < w.r.f y ]

-- predicate qualifier as function co-domain in negative position
#blaster [ ∀ (α : Type) (g : Nat → FunRel) (x y : α) [LT α], x < y → (g 0).f x < (g 0).f y ]

structure Positive where
  n : Nat
  inv : ∀ (α : Type), (∀ (_x : α), n > 5) → n > 5

-- Not a theorem (`n > 5` for any `Positive`, take `α := Empty`).
-- Predicate qualifier with a sort quantifier in positive position: `unsat` is reported as `Undetermined`.
#blaster (solve-result: 2) [ ∃ (p : Positive), p.n = 0 ]

-- Not a theorem (the hypothesis holds as `n > 5` for any `Positive`).
-- Predicate qualifier with a sort quantifier in positive position: `unsat` is reported as `Undetermined`.
#blaster (solve-result: 2) [ (∀ (p : Positive), p.n ≠ 0) → False ]

structure MixedInv where
  n : Nat
  c : Bool
  inv : c = true ↔ ∀ (α : Type), (n = 0 → ∀ (_x : α), False) ∧ (n = 1 → ∃ (_x : α), True)

-- Not a theorem (`c = true ↔ n ≥ 2` for any `MixedInv`).
-- Sort quantifier with mixed polarity depending on the predicate qualifier parameter:
-- `unsat` is reported as `Undetermined`.
#blaster (solve-result: 2)
  [ ∀ (s t : MixedInv), s.n = 0 → t.n = 1 → s.c = true ∨ t.c = true ]

/-! Test cases to ensure that functions with a proposition domain are guarded by the truth of the proposition.
    An inductive proposition (e.g., a structure in `Prop`) is translated to an smt datatype, which is never empty.
    However, `P → β` is inhabited whenever `P` does not hold, even when `β` is empty. -/

structure FalseInv : Prop where
  inv : 1 > 2

structure TrueInv : Prop where
  inv : 1 < 2

structure SortInv : Prop where
  inv : ∀ (α : Type), ∃ (_x : α), True

inductive NoNeg : Prop
  | intro (n : Nat) (h : n < 0)

inductive SomeBig : Prop
  | intro (n : Nat) (h : n > 5)

structure FalseInvFun where
  f : FalseInv → Empty

class EmptyFrom (α : Type) where
  elim : FalseInv → α

-- Not a theorem (`FalseInv` does not hold, take `f := λ h => absurd h.inv (by decide)`).
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (_f : FalseInv → Empty), False ]

-- Not a theorem (`FalseInv → Empty` has exactly one function).
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (f g : FalseInv → Empty), f = g → False ]

-- Not a theorem (proposition domain after the first argument).
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (_f : Nat → FalseInv → Empty), False ]

-- Not a theorem (proposition domain before a non empty domain).
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (_f : FalseInv → Nat → Empty), False ]

-- Not a theorem (inductive proposition with a data field).
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (_f : NoNeg → Empty), False ]

-- Not a theorem (`TrueInv → FalseInv` does not hold).
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (_f : (TrueInv → FalseInv) → Empty), False ]

-- Not a theorem (ctor field with a proposition domain).
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (_w : FalseInvFun), False ]

-- Not a theorem (`α := Empty`, `elim := λ h => absurd h.inv (by decide)`, `g := elim`).
-- Test case: co-domain constraint of an undeclared class function.
#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (α : Type) [EmptyFrom α] (g : FalseInv → α), g = EmptyFrom.elim → (∀ (_x : α), False) → False ]

-- Not a theorem (`1 = 2` is reduced to `False`, which has no ctor).
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (_f : (1 = 2) → Empty), False ]

-- Not a theorem (`False` has no ctor).
#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (_f : False → Empty), False ]

-- Not a theorem (`SortInv` does not hold, take `α := Empty`).
-- The predicate qualifier of `SortInv` is a negative only predicate qualifier (see `withQualifierBody`),
-- which cannot guard a co-domain constraint: `unsat` is reported as `Undetermined`.
#blaster (gen-cex: 0) (solve-result: 2) [ ∀ (_f : SortInv → Empty), False ]

-- Not a theorem (`SortInv → Empty` has exactly one function).
#blaster (gen-cex: 0) (solve-result: 2) [ ∀ (f g : SortInv → Empty), f = g → False ]

#blaster [ ∃ (_f : FalseInv → Empty), True ]

#blaster [ ∀ (_f : TrueInv → Empty), False ]

#blaster [ ∀ (_f : True → Empty), False ]

#blaster [ ∀ (_f : Nat → TrueInv → Empty), False ]

#blaster [ ∀ (_f : SomeBig → Empty), False ]

#blaster [ ∀ (_f : (FalseInv → TrueInv) → Empty), False ]

end Test.SmtUninhabited
