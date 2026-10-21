import Lean
import Blaster

namespace Tests.StructEqLevels

-- Issue: Unexpected Valid / bogus counterexample when the same constructor occurs with
--        equivalent but syntactically different universe levels (e.g., `max u v` and `max v u`).
--
-- Diagnosis: Constructor constants were compared with physical equality, universe levels included,
--            although levels are not normalized by the optimizer (see `normLevel`), i.e.:
--              - `structEq?` (Blaster/Optimize/Rewriting/OptimizeEq.lean) returned `some false` for
--                `Option.none.{max u v} = Option.none.{max v u}`, which `optimizeEq` rewrote to `False`;
--              - `isPatternMatch` (Blaster/Optimize/Rewriting/OptimizeMatch.lean) returned `NoMatch` for
--                pattern `Tag.a.{max u v}` and discriminator `Tag.a.{max v u}`, which selected a
--                later wildcard alternative.
--            Constructors with the same name are now compared on their levels with `Level.isEquiv`,
--            and no disequality (resp. `NoMatch`) is concluded when the levels cannot be shown equivalent.

universe u v

/-! ## Example 1: `structEq?` on constructors with permuted universe levels -/

-- Kernel-checked counterexamples. None uses Blaster or sorry.
theorem none_counterexample :
    ¬ (∀ (α : Type (max u v)), ¬ (@Option.none.{max u v} α = @Option.none.{max v u} α)) := by
  intro h
  exact h PUnit rfl

theorem some_counterexample :
    ¬ (∀ (α : Type (max u v)) (x : α), ¬ (@Option.some.{max u v} α x = @Option.some.{max v u} α x)) := by
  intro h
  exact h PUnit PUnit.unit rfl

theorem pair_counterexample :
    ¬ (∀ (x : Nat) (α : Type (max u v)),
         ¬ ((x, @Option.none.{max u v} α) = (x, @Option.none.{max v u} α))) := by
  intro h
  exact h 0 PUnit rfl

-- Statement of the original report: `PUnit.unit.{max u v + 1}` and `PUnit.unit.{max v u + 1}` are equal.
-- NOTE: Blaster no longer reports it Valid, but the Smt translation does not yet support two level instances
--       of a non-parametric inductive type (`@isPUnit` defined twice), hence no `#blaster` test for it.
theorem punit_counterexample :
    ¬ ¬ ((PUnit.unit.{max u v + 1} : PUnit.{max u v + 1}) = PUnit.unit.{max v u + 1}) := by
  intro h
  exact h rfl

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ (α : Type (max u v)), ¬ (@Option.none.{max u v} α = @Option.none.{max v u} α)]
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ (α : Type (max u v)) (x : α), ¬ (@Option.some.{max u v} α x = @Option.some.{max v u} α x)]
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ (x : Nat) (α : Type (max u v)), ¬ ((x, @Option.none.{max u v} α) = (x, @Option.none.{max v u} α))]

-- Valid expected (counterexample previously reported for the first one)
#blaster [∀ (α : Type (max u v)), @Option.none.{max u v} α = @Option.none.{max v u} α]
#blaster [∀ (α : Type (max u v)) (x y : α), @Option.some.{max u v} α x = @Option.some.{max v u} α y → x = y]
-- Sanity checks: distinct constructors are still distinct, and equal levels are unaffected.
#blaster [∀ (α : Type (max u v)) (x : α), @Option.some.{max u v} α x ≠ @Option.none.{max v u} α]
#blaster [∀ (α : Type (max u v)) (x y : α), @Option.some.{max u v} α x = @Option.some.{max u v} α y → x = y]


/-! ## Example 2: match reduction on constructors with permuted universe levels -/

inductive Tag : Type u where
  | a
  | b

def isA (t : Tag.{max u v}) : Bool :=
  match t with
  | .a => true
  | _ => false

def isSomeAlt {α : Type (max u v)} (o : Option.{max u v} α) : Bool :=
  match o with
  | some _ => true
  | _ => false

-- Kernel-checked counterexamples. None uses Blaster or sorry.
theorem isA_counterexample : ¬ (isA.{u, v} Tag.a.{max v u} = false) := by
  intro h
  cases h

theorem isA_swap_counterexample : ¬ (isA.{v, u} Tag.a.{max u v} = false) := by
  intro h
  cases h

theorem isSomeAlt_counterexample :
    ¬ (∀ (α : Type (max u v)) (x : α), isSomeAlt.{u, v} (@Option.some.{max v u} α x) = false) := by
  intro h
  cases h PUnit PUnit.unit

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [isA.{u, v} Tag.a.{max v u} = false]
#blaster (gen-cex: 0) (solve-result: 1) [isA.{v, u} Tag.a.{max u v} = false]
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ (α : Type (max u v)) (x : α), isSomeAlt.{u, v} (@Option.some.{max v u} α x) = false]

-- Valid expected (counterexample previously reported for both)
#blaster [∀ (α : Type (max u v)) (x : α), isSomeAlt.{u, v} (@Option.some.{max v u} α x) = true]
#blaster [isA.{u, v} Tag.a.{max v u} = true]
-- Sanity checks: distinct constructors still do not match, and equal levels are unaffected.
#blaster [isA.{u, v} Tag.b.{max v u} = false]
#blaster [∀ (α : Type (max u v)), isSomeAlt.{u, v} (@Option.none.{max v u} α) = false]
#blaster [isA.{u, v} Tag.a.{max u v} = true]

end Tests.StructEqLevels
