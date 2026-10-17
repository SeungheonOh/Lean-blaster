import Blaster

-- FALSE in Lean: Empty is an empty type but Unit is inhabited.
theorem ts2 : (∃ α : Type, ∀ _a : α, False) → ∀ (β : Type) (_x : β), False := by blaster

theorem ts2_false : ¬ ((∃ α : Type, ∀ _a : α, False) → ∀ (β : Type) (_x : β), False) :=
  fun h => h ⟨Empty, fun a => nomatch a⟩ Unit ()

theorem bad : False := ts2_false ts2
#print axioms bad

-- same through a local axiom (true in Lean!)
axiom emptyTypeExists : ∃ α : Type, ∀ _a : α, False
theorem ts3 : ∀ (β : Type) (_x : β), False := by blaster
theorem bad2 : False := ts3 Unit ()
#print axioms bad2

-- variant: #blaster
