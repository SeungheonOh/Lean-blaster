import Blaster
/- coiExists (OptimizeExists.lean:164) drops `∃ x : t, e` to `e` when `isSortOrInhabited t`
   (Rewriting/Utils.lean:60), which wrongly accepts type variables / function types (fallback `isTypeEnv`),
   indexed families with a nullary ctor at another index, and uninhabited class types. -/

-- ∃ over a type variable (may be empty)
theorem e1 : ∀ (α : Type), ∃ (_x : α), True := by blaster
theorem e1_false : ¬ (∀ (α : Type), ∃ (_x : α), True) := fun h => nomatch (h Empty)

-- ∃ over a function type into Empty
theorem e2 : ∃ (_f : Nat → Empty), True := by blaster
theorem e2_false : ¬ (∃ (_f : Nat → Empty), True) := fun ⟨f, _⟩ => nomatch f 0

-- ∃ over an indexed family with a nullary constructor at a different index
inductive Idx : Nat → Type where
  | z : Idx 0
theorem e3 : ∃ (_x : Idx 1), True := by blaster
theorem e3_false : ¬ (∃ (_x : Idx 1), True) := fun ⟨x, _⟩ => nomatch x


-- ∃ over an uninhabited class
class Foo (α : Type) where
  val : α
theorem e5 : ∃ (_x : Foo Empty), True := by blaster
theorem e5_false : ¬ (∃ (_x : Foo Empty), True) := fun ⟨x, _⟩ => nomatch x.val

theorem contra1 : False := e1_false e1
theorem contra2 : False := e2_false e2
theorem contra3 : False := e3_false e3
theorem contra5 : False := e5_false e5

-- same isSortOrInhabited flaw through optimizeForall (OptimizeForAll.lean:143), negative position
theorem f3 : ¬ ∀ (_x : Idx 1), False := by blaster
theorem f3_false : ¬ ¬ ∀ (_x : Idx 1), False := fun h => h (fun x => nomatch x)
theorem contraF3 : False := f3_false f3
