import Lean
import Blaster
import Tests.Utils

namespace Tests.ImplicitArgKeys

-- Issue: distinct instances of a function were identified because their implicit arguments
--        were dropped from the key identifying the instance:
--        - `getInstApp` returned the bare function name whenever only implicit arguments were
--          provided, e.g., `@subL Int weirdSub _` and `@subL Int instSubInt _` (partial
--          applications) or `@Pt.pt Nat i` and `@Pt.pt Nat j` (all parameters implicit) shared
--          the same instance cache entry and the same Smt function;
--        - `storeRecFunDef` replaced every tagged recursive call with `_recFun` while dropping its
--          non-generic implicit arguments, so `@f (!b) n` in the definition of `@f b n` became a
--          call to `@f b`, and `f` was identified with `g` below.
--        Blaster declared the false statements below `Valid`.
--
-- Diagnosis: the key of a function instance must contain every implicit argument that is not
--            abstracted as a generic parameter, and a recursive call can only be generalized to
--            `_recFun` when it is a call to the instance being defined.
-- Modifications:
--   - `getInstApp` keeps the implicit arguments that are not types when only implicit arguments are provided
--     (e.g., a partial application passed to a higher-order function): the key of `@f x₁ ... xₙ` is then the
--     one of the corresponding full application, i.e., `fun y => @f x₁ ... xₙ y` (abstracted over the generic
--     free variables, if any). Type arguments are still dropped (the instances of a parametric function share
--     the same Smt function).
--   - `storeRecFunDef` only replaces a tagged call with `_recFun` when the call is to the function
--     being defined with the same non-generic implicit arguments. Any other tagged call (e.g.,
--     `@f (!b) n`) is kept as a regular call to the corresponding instance.

set_option warn.sorry false

/-! ## Partially applied polymorphic recursive function (only implicit arguments provided) -/

def subL {α} [Sub α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x - subL xs

def weirdSub : Sub Int := ⟨fun a b => a + b⟩

-- Kernel-checked counterexamples. None uses Blaster or sorry.
theorem map_subL_counterexample :
    ¬ (∀ ys : List (List Int),
        List.map (@subL Int weirdSub _) ys = List.map (@subL Int (inferInstance : Sub Int) _) ys) := by
  intro h
  exact absurd (h [[0, 1]]) (by decide)

theorem map_subL_singleton_counterexample :
    ¬ (∀ y : List Int,
        List.map (@subL Int weirdSub _) [y] = List.map (@subL Int (inferInstance : Sub Int) _) [y]) := by
  intro h
  exact absurd (h [0, 1]) (by decide)

-- Falsified on a singleton list
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 10)
  [∀ y : List Int, List.map (@subL Int weirdSub _) [y] = List.map (@subL Int (inferInstance : Sub Int) _) [y]]

-- Original example: no counterexample found within the timeout, but no longer `Valid`
#blaster (gen-cex: 0) (solve-result: 2) (timeout: 5)
  [∀ ys : List (List Int), List.map (@subL Int weirdSub _) ys = List.map (@subL Int (inferInstance : Sub Int) _) ys]

-- Same instance used twice: the partial and full applications must be identified
theorem map_subL_same_inst :
    ∀ ys : List (List Int), List.map (@subL Int weirdSub _) ys = List.map (@subL Int weirdSub _) ys := by blaster

theorem map_subL_same_inst_singleton :
    ∀ y : List Int, List.map (@subL Int weirdSub _) [y] = [@subL Int weirdSub _ y] := by blaster

-- Canonical instances: `inferInstance` and `Int.instSub` are the same instance
theorem map_subL_canonical_inst :
    ∀ ys : List (List Int),
      List.map (@subL Int (inferInstance : Sub Int) _) ys = List.map (@subL Int Int.instSub _) ys := by blaster

theorem map_subL_canonical_inst_singleton :
    ∀ y : List Int,
      List.map (@subL Int (inferInstance : Sub Int) _) [y] = [@subL Int Int.instSub _ y] := by blaster

-- Two instances that differ syntactically but have the same semantics
def sameSub : Sub Int := ⟨Int.sub⟩

theorem map_subL_equiv_inst :
    ∀ y : List Int, List.map (@subL Int sameSub _) [y] = List.map (@subL Int Int.instSub _) [y] := by blaster

/-! ## Function with only implicit parameters (class method) -/

class Pt (α : Type) where
  pt : α

theorem pt_counterexample : ¬ (∀ (i j : Pt Nat), @Pt.pt Nat i = @Pt.pt Nat j) := by
  intro h
  exact absurd (h ⟨0⟩ ⟨1⟩) (by decide)

#blaster (gen-cex: 0) (solve-result: 1) (timeout: 10) [∀ (i j : Pt Nat), @Pt.pt Nat i = @Pt.pt Nat j]

def ptPlus {α : Type} [Pt α] [Add α] (n : α) : α := n + Pt.pt

theorem ptPlus_counterexample : ¬ (∀ (i j : Pt Nat) (n : Nat), @ptPlus Nat i _ n = @ptPlus Nat j _ n) := by
  intro h
  exact absurd (h ⟨0⟩ ⟨1⟩ 0) (by decide)

#blaster (gen-cex: 0) (solve-result: 1) (timeout: 10)
  [∀ (i j : Pt Nat) (n : Nat), @ptPlus Nat i _ n = @ptPlus Nat j _ n]

-- same instance used twice
theorem pt_same_inst : ∀ (i : Pt Nat), @Pt.pt Nat i = @Pt.pt Nat i := by blaster
-- KNOWN (incompleteness): instances that are quantified variables are distinct keys, i.e., distinct Smt symbols
-- (sound, as instances are no longer identified, but `i = j` does not relate `@Pt.pt Nat i` and `@Pt.pt Nat j`):
-- theorem pt_eq_inst : ∀ (i j : Pt Nat), i = j → @Pt.pt Nat i = @Pt.pt Nat j := by blaster

/-! ## Recursive call changing a (non-generic) implicit argument -/

def f {b : Bool} : Nat → Nat
  | 0 => if b then 1 else 0
  | n + 1 => @f (!b) n

def g {b : Bool} : Nat → Nat
  | 0 => if b then 1 else 0
  | n + 1 => @g b n

-- Kernel-checked counterexamples. None uses Blaster or sorry.
theorem f_g_counterexample : ¬ (∀ n : Nat, @f true n = @g true n) := by
  intro h
  exact absurd (h 1) (by decide)

theorem f_const_counterexample : ¬ (∀ n : Nat, @f true n = 1) := by
  intro h
  exact absurd (h 1) (by decide)

#blaster (gen-cex: 0) (solve-result: 1) (timeout: 10) [∀ n : Nat, @f true n = @g true n]
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 10) [∀ n : Nat, @f true n = 1]

-- `@f true` calls `@f false` that calls back `@f true`
theorem f_two_steps : ∀ n : Nat, @f true (n + 2) = @f true n := by blaster
theorem f_one_step : ∀ n : Nat, @f true (n + 1) = @f false n := by blaster

-- Recursive calls with identical implicit arguments: equivalent functions are still identified
def g' {b : Bool} : Nat → Nat
  | 0 => if b then 1 else 0
  | n + 1 => @g' b n

theorem g_g'_equiv : ∀ n : Nat, @g true n = @g' true n := by blaster
theorem g_g'_equiv_poly : ∀ (b : Bool) (n : Nat), @g b n = @g' b n := by blaster

def subL' {α} [Sub α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x - subL' xs

theorem subL_subL'_equiv : ∀ (xs : List Int), @subL Int weirdSub _ xs = @subL' Int weirdSub _ xs := by blaster

theorem map_subL_subL'_equiv :
    ∀ ys : List (List Int), List.map (@subL Int weirdSub _) ys = List.map (@subL' Int weirdSub _) ys := by blaster

end Tests.ImplicitArgKeys
