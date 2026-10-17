import Blaster

-- (1) Uninterpreted SMT sorts are non-empty; Lean `α : Type` may be empty.
theorem bad_sort : ∀ (α : Type) (p : α → Bool), (∀ x, p x = true) → ∃ x, p x = true := by blaster
example : False := by
  have ⟨x, _⟩ := bad_sort Empty (fun _ => true) (fun x => x.elim)
  exact x.elim

-- (2) All type variables are aliased to the single SMT sort @@Type, so
-- facts about one type variable transfer to another.
theorem bad_alias : ∀ (α β : Type), (∀ x y : α, x = y) → (∀ x y : β, x = y) := by blaster
example : False := by
  have h := bad_alias Unit Bool (fun _ _ => rfl) true false
  cases h
