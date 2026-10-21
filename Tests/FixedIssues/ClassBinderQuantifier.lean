import Lean
import Blaster

namespace Tests.ClassBinderQuantifier

-- Issue: Unexpected Valid for an instance binder nested under a quantifier, e.g.,
--        `∃ x : Nat, ∀ [j : Inhabited Nat], default ≠ x` was declared `Valid` although it is false.
--
-- Diagnosis: Instance binders (i.e., binders whose type is a class) are not quantified at the Smt level.
--            Each class function applied to an instance binder is declared as a global uninterpreted
--            function (see `translateAxiomOrUndeclFun?`), i.e., the instance binder is treated as a top-level
--            constant. This is sound for top-level instance binders and for quantified formulas that do not
--            depend on enclosing bound variables. Otherwise, the dependency is lost and the quantifier
--            alternation is broken: the above example was translated to `∃ x, @default ≠ x` for a global
--            `@default` (see `translateForAll` and `genExistsTerm`).
--
-- Modifications: When a used instance binder depends on a variable bound by an enclosing quantifier, lambda or
--                match pattern, the Smt query is flagged (see `flagHoistedInstBinders`) and an `unsat` result
--                is reported as `Undetermined`. A `sat` result is still reported as `Falsified`.

/-! ## Kernel-checked counterexamples (no Blaster) -/

theorem forall_inst_under_exists_counterexample :
    ¬ (∃ x : Nat, ∀ [j : Inhabited Nat], @default Nat j ≠ x) :=
  fun ⟨x, h⟩ => @h ⟨x⟩ rfl

theorem explicit_inst_under_exists_counterexample :
    ¬ (∃ x : Nat, ∀ (j : Inhabited Nat), @default Nat j ≠ x) :=
  fun ⟨x, h⟩ => h ⟨x⟩ rfl

theorem not_exists_inst_under_exists_counterexample :
    ¬ (∃ x : Nat, ¬ ∃ j : Inhabited Nat, @default Nat j = x) :=
  fun ⟨x, h⟩ => h ⟨⟨x⟩, rfl⟩

theorem inst_in_premise_under_exists_counterexample :
    ¬ (∃ x : Nat, ∀ [j : Inhabited Nat], @default Nat j = x → False) :=
  fun ⟨x, h⟩ => @h ⟨x⟩ rfl

theorem forall_exists_forall_inst_counterexample :
    ¬ (∀ y : Nat, ∃ x : Nat, x ≥ y ∧ ∀ [j : Inhabited Nat], @default Nat j ≠ x) :=
  fun h => let ⟨x, _, hx⟩ := h 0; @hx ⟨x⟩ rfl

theorem add_inst_under_exists_counterexample :
    ¬ (∃ x : Nat, ∀ [Add Nat], x + 0 ≠ x) :=
  fun ⟨_, h⟩ => @h ⟨Nat.add⟩ rfl

theorem beq_inst_under_exists_counterexample :
    ¬ (∃ x : Nat, ∀ [BEq Nat], (x == x) = false) :=
  fun ⟨_, h⟩ => Bool.noConfusion (@h ⟨fun _ _ => true⟩)

theorem closed_inst_under_exists_counterexample :
    ¬ (∃ x : Nat, x > 0 ∧ ∀ [j : Inhabited Nat], @default Nat j ≠ 5) :=
  fun ⟨_, _, h⟩ => @h ⟨5⟩ rfl

/-! ## Instance binder depending on an enclosing bound variable: `Valid` must not be reported -/

-- original example
#blaster (solve-result: 2) [∃ x : Nat, ∀ [j : Inhabited Nat], @default Nat j ≠ x]

-- explicit instance binder
#blaster (solve-result: 2) [∃ x : Nat, ∀ (j : Inhabited Nat), @default Nat j ≠ x]

-- existential instance binder in a negative position
#blaster (solve-result: 2) [∃ x : Nat, ¬ ∃ j : Inhabited Nat, @default Nat j = x]

-- instance binder only used in a premise
#blaster (solve-result: 2) [∃ x : Nat, ∀ [j : Inhabited Nat], @default Nat j = x → False]

-- enclosing existential under a top-level universal
#blaster (solve-result: 2) [∀ y : Nat, ∃ x : Nat, x ≥ y ∧ ∀ [j : Inhabited Nat], @default Nat j ≠ x]

-- a counterexample found for the flagged query is still reported
#blaster (gen-cex: 0) (solve-result: 1) [∃ x : Nat, ∀ [Add Nat], x + 0 ≠ x]
#blaster (gen-cex: 0) (solve-result: 1) [∃ x : Nat, ∀ [BEq Nat], (x == x) = false]

/-! ## Nested instance binder not depending on any enclosing bound variable -/

#blaster (gen-cex: 0) (solve-result: 1) [∃ x : Nat, x > 0 ∧ ∀ [j : Inhabited Nat], @default Nat j ≠ 5]

#blaster [(∀ (x : Nat) [j : Inhabited Nat], @default Nat j ≠ x) → False]

/-! ## Top-level instance binders remain `Valid` -/

#blaster [∀ [j : Inhabited Nat], ∃ x : Nat, @default Nat j = x]

#blaster [∀ [Add Nat] (x y : Nat), x = y → x + 0 = y + 0]

#blaster [∀ (α : Type) [BEq α] (x y : α), x == y → (x == y) = true]

#blaster [∀ [j : Inhabited Nat] (x : Nat), (∀ y : Nat, y = x → y = @default Nat j) → x = @default Nat j]

theorem top_level_inst (α : Type) [Inhabited α] (f : α → Nat) :
    ∀ x : α, x = default → f x = f default := by blaster

end Tests.ClassBinderQuantifier
