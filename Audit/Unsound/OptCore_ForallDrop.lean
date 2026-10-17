import Blaster

-- dropping `∀ x : α, e` to `e` when α is assumed inhabited (isSortOrInhabited) is only an implication,
-- not an equivalence; under negation it is unsound.
theorem bad1 : ∀ (α : Type), ¬ ∀ (_x : α), False := by blaster

theorem bad1_false : ¬ (∀ (α : Type), ¬ ∀ (_x : α), False) := by
  intro h; exact h Empty (fun x => nomatch x)

theorem f1 : False := bad1_false bad1

theorem bad2 : ¬ ∀ (_f : Nat → Empty), False := by blaster
theorem bad2_false : ¬ (¬ ∀ (_f : Nat → Empty), False) := fun h => h (fun f => nomatch f 0)

theorem bad3 : ¬ ∀ (_i : Inhabited Empty), False := by blaster
theorem bad3_false : ¬ (¬ ∀ (_i : Inhabited Empty), False) := fun h => h (fun i => nomatch i.default)

theorem f2 : False := bad2_false bad2
theorem f3 : False := bad3_false bad3
