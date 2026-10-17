import Blaster

-- ∀ over an instance-implicit binder nested under ∃: binder is dropped and the
-- variable becomes a single top-level SMT constant (quantifier alternation lost).
theorem bad_instq : ∃ x : Nat, ∀ [j : Inhabited Nat], @default Nat j ≠ x := by blaster (dump-smt-lib: 1)
example : False := by
  obtain ⟨x, h⟩ := bad_instq
  exact @h ⟨x⟩ rfl
