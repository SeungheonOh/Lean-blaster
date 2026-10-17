import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.COIUninhabited
/-! ## Test objectives to validate that COI reduction on `∀` and `∃` is only applied on inhabited types.

  The following COI reduction rules are only sound when `t` is inhabited:
     - `∀ (n : t), e ===> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ fVarInExpr n.fvarId! e)`
     - `∃ (n : t), e ===> e (if isSortOrInhabited t ∧ ¬ e.hasLooseBVar e 0)`
  Indeed, `(∀ (_x : Empty), False) = True` and `(∃ (_x : Empty), True) = False`.
-/

/-! Test cases to ensure that the COI reduction rules are not applied on quantifiers over possibly empty types. -/

-- ∀ (α : Type), (∀ (_x : α), False) → False ===> ∀ (α : Type), ¬ ∀ (_x : α), False
-- Test case: COI reduction rule not applicable on type variables (e.g., `α := Empty`).
#testOptimize [ "ForallCOIUninhabited_1" ]
  ∀ (α : Type), (∀ (_x : α), False) → False ===>
  ∀ (α : Type), ¬ ∀ (_x : α), False

-- ∀ (α : Type), ∃ (_x : α), True ===> ∀ (α : Type), ∃ (_x : α), True
-- Test case: COI reduction rule not applicable on type variables (e.g., `α := Empty`).
#testOptimize [ "ExistsCOIUninhabited_1" ]
  ∀ (α : Type), ∃ (_x : α), True ===> ∀ (α : Type), ∃ (_x : α), True

-- ∀ (α : Type), (∀ [_i : Inhabited α], False) → False ===>
-- ∀ (α : Type), ¬ ∀ [_i : Inhabited α], False
-- Test case: COI reduction rule not applicable on class constraints that may not have any instance.
#testOptimize [ "ForallCOIUninhabited_2" ]
  ∀ (α : Type), (∀ [_i : Inhabited α], False) → False ===>
  ∀ (α : Type), ¬ ∀ [_i : Inhabited α], False

-- (∀ (_f : Nat → Empty), False) → False ===> ¬ ∀ (_f : Nat → Empty), False
-- Test case: COI reduction rule not applicable on arrow types with an empty codomain.
#testOptimize [ "ForallCOIUninhabited_3" ]
  (∀ (_f : Nat → Empty), False) → False ===> ¬ ∀ (_f : Nat → Empty), False

-- ∃ (_f : Nat → Empty), True ===> ∃ (_f : Nat → Empty), True
-- Test case: COI reduction rule not applicable on arrow types with an empty codomain.
#testOptimize [ "ExistsCOIUninhabited_2" ]
  ∃ (_f : Nat → Empty), True ===> ∃ (_f : Nat → Empty), True

inductive Ev : Nat → Type where
 | zero : Ev 0

-- (∀ (_x : Ev 1), False) → False ===> ¬ ∀ (_x : Ev 1), False
-- Test case: COI reduction rule not applicable on indexed inductive types,
-- for which a nullary constructor does not inhabit all indices.
#testOptimize [ "ForallCOIUninhabited_4" ] (norm-result: 1)
  (∀ (_x : Ev 1), False) → False ===> ¬ ∀ (_x : Ev 1), False

-- ∃ (_x : Ev 1), True ===> ∃ (_x : Ev 1), True
-- Test case: COI reduction rule not applicable on indexed inductive types,
-- for which a nullary constructor does not inhabit all indices.
#testOptimize [ "ExistsCOIUninhabited_3" ] (norm-result: 1) ∃ (_x : Ev 1), True ===> ∃ (_x : Ev 1), True

-- ∀ (α : Type) [Inhabited α], (∀ (_y : α), False) → False ===>
-- ∀ (α : Type) [Inhabited α], ¬ ∀ (_y : α), False
-- Test case: COI reduction rule does not rely on local instances.
-- NOTE: Local instances are ignored as optimized expressions may be cached globally
-- and retrieved outside the scope of the local instance.
#testOptimize [ "ForallCOIUninhabited_5" ]
  ∀ (α : Type) [Inhabited α], (∀ (_y : α), False) → False ===>
  ∀ (α : Type) [Inhabited α], ¬ ∀ (_y : α), False


/-! Test cases to ensure that the COI reduction rules are still applied on inhabited types. -/

-- ∀ (α : Type), (∀ (_x : List α), False) → False ===> True
-- Test case: COI reduction applies on parametric inductive types with a nullary constructor.
#testOptimize [ "ForallCOIInhabited_1" ] ∀ (α : Type), (∀ (_x : List α), False) → False ===> True

-- ∀ (α : Type), ∃ (_x : Option α), True ===> True
-- Test case: COI reduction applies on parametric inductive types with a nullary constructor.
#testOptimize [ "ExistsCOIInhabited_1" ] ∀ (α : Type), ∃ (_x : Option α), True ===> True

-- (∀ (_x : Nat × Bool), False) → False ===> True
-- Test case: COI reduction applies on types with a Nonempty instance.
#testOptimize [ "ForallCOIInhabited_2" ] (∀ (_x : Nat × Bool), False) → False ===> True

-- ∀ (α : Type), (∀ (_f : α → Nat), False) → False ===> True
-- Test case: COI reduction applies on arrow types with an inhabited codomain.
#testOptimize [ "ForallCOIInhabited_3" ] ∀ (α : Type), (∀ (_f : α → Nat), False) → False ===> True

-- ∀ (α : Type), (∀ (_f : α → Type), False) → False ===> True
-- Test case: COI reduction applies on arrow types with a sort codomain.
#testOptimize [ "ForallCOIInhabited_4" ] ∀ (α : Type), (∀ (_f : α → Type), False) → False ===> True

-- (∀ (_α : Type), False) → False ===> True
-- Test case: COI reduction applies on sort types.
#testOptimize [ "ForallCOIInhabited_5" ] (∀ (_α : Type), False) → False ===> True

-- ∀ (α : Type), (∀ [_i : BEq α] [_j : DecidableEq α] [_k : LT α], False) → False ===> True
-- Test case: COI reduction applies on class constraints that can always be instantiated.
#testOptimize [ "ForallCOIInhabited_6" ]
  ∀ (α : Type), (∀ [_i : BEq α] [_j : DecidableEq α] [_k : LT α], False) → False ===> True

-- (∀ [_i : Inhabited Nat], False) → False ===> True
-- Test case: COI reduction applies on class constraints for which an instance can be synthesized.
#testOptimize [ "ForallCOIInhabited_7" ] (∀ [_i : Inhabited Nat], False) → False ===> True


/-! Test cases to ensure that Blaster does not prove false statements over empty types. -/

-- `Nat → Empty` is empty.
#blaster (solve-result: 1) [(∀ (_f : Nat → Empty), False) → False]

-- `Nat → Empty` is empty.
#blaster (solve-result: 1) [∃ (_f : Nat → Empty), True]

-- `α := Empty` is a counterexample (optimization only, see note below).
#blaster (only-optimize: 1) (solve-result: 2) [∀ (α : Type), (∀ (_x : α), False) → False]

-- `α := Empty` is a counterexample (optimization only, see note below).
#blaster (only-optimize: 1) (solve-result: 2) [∀ (α : Type), ∃ (_x : α), True]

-- `α := Empty` is a counterexample (optimization only, see note below).
#blaster (only-optimize: 1) (solve-result: 2) [∀ (α : Type), (∀ [_i : Inhabited α], False) → False]

-- NOTE: The above statements over type variables are still reported as `Valid` once translated to Smt,
-- as each type variable is mapped to the universal Smt sort `@@Type`, which is assumed to be non-empty.

end Test.COIUninhabited
