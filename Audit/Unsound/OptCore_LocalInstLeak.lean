import Blaster

-- Inside the scope of a local instance `Inhabited Empty`, the closed term
-- `∀ x : Empty, False` is rewritten to `False` (isSortOrInhabited finds the local
-- instance).  The result (and the synthesized-instance query) is cached globally
-- because the key has no fvars, and is reused outside that scope.
theorem bad : (∀ (_ : Inhabited Empty), (∀ (_x : Empty), False) = False) ∧ ¬ (∀ (_x : Empty), False) := by
  blaster

theorem bad_false : ¬ ((∀ (_ : Inhabited Empty), (∀ (_x : Empty), False) = False) ∧ ¬ (∀ (_x : Empty), False)) := by
  intro ⟨_, h⟩; exact h (fun x => nomatch x)

theorem oops : False := bad_false bad

-- control: without the instance scope blaster correctly reports Falsified
#blaster (solve-result: 1) [ ¬ (∀ (_x : Empty), False) ]
