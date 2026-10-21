import Lean
import Blaster
import Tests.Utils

namespace Tests.RecBodyHypLeak

-- Issue: the definition of a recursive function instance was optimized under the hypotheses,
--        equalities and match patterns in scope at its first call site. However, the optimized
--        definition is cached in `recFunInstCache`/`recFunMap` for all contexts (and is also the one
--        used for the smt function definition). E.g., the definition of `@f x` below was optimized
--        under `0 < x`, rewriting `x / x` to `1` and making `@f x` structurally equivalent to `g`.
--        This equivalence was then reused outside the implication and `imp_hyp_cex` was wrongly
--        declared `Valid`.
--
-- Diagnosis: `normRecFun` optimized the recursive function definition in the current context.
-- Modifications: the recursive function definition is now optimized in the root context (i.e., without
--                any hypothesis, equality or match pattern in scope). The current context is restored
--                once the definition is optimized (see `enterRootCtx` and `restoreCtx`).
--
-- NOTE: `(h → a) ∧ a` is normalized to `a`.

def f {n : Nat} : List Nat → Nat
  | [] => n / n
  | _ :: xs => f (n := n) xs

def g : List Nat → Nat
  | [] => 1
  | _ :: xs => g xs

/-! ## Implicit argument instantiated with a quantified variable

  NOTE: The smt translation does not yet support a recursive function instance whose implicit
  arguments contain a quantified variable (e.g., `@f x`). `#testOptimize` is therefore used to
  check that `@f x` is not identified with `g` outside the scope of the hypothesis.
-/

def imp_hyp_cex := ∀ (x : Nat) (l : List Nat), (0 < x → @f x l = g l) ∧ @f x l = g l

-- Kernel-checked counterexample. Does not use Blaster or sorry.
theorem imp_hyp_cex_false : ¬ imp_hyp_cex := by
  intro h
  exact absurd (h 0 []).2 (by decide)

#testOptimize ["RecBodyImpHypNotInParent"] imp_hyp_cex ===> ∀ (x : Nat) (l : List Nat), g l = @f x l

-- hypothesis introduced by a `dite` branch
def dite_hyp_cex := ∀ (x : Nat) (l : List Nat), (if 0 < x then @f x l = g l else True) ∧ @f x l = g l

-- Kernel-checked counterexample. Does not use Blaster or sorry.
theorem dite_hyp_cex_false : ¬ dite_hyp_cex := by
  intro h
  exact absurd (h 0 []).2 (by decide)

#testOptimize ["RecBodyDiteHypNotInParent"] dite_hyp_cex ===> ∀ (x : Nat) (l : List Nat), g l = @f x l

-- hypothesis `¬ x = 0` used to reduce an `ite` in the recursive function definition
def f3 {n : Nat} : List Nat → Nat
  | [] => if n = 0 then 0 else 1
  | _ :: xs => f3 (n := n) xs

def neq_hyp_cex := ∀ (x : Nat) (l : List Nat), (¬ x = 0 → @f3 x l = g l) ∧ @f3 x l = g l

-- Kernel-checked counterexample. Does not use Blaster or sorry.
theorem neq_hyp_cex_false : ¬ neq_hyp_cex := by
  intro h
  exact absurd (h 0 []).2 (by decide)

#testOptimize ["RecBodyNeqHypNotInParent"] neq_hyp_cex ===> ∀ (x : Nat) (l : List Nat), g l = @f3 x l

-- non-matching pattern `x ≠ 0` introduced by a `match` alternative
def f2 {n : Nat} : List Nat → Nat
  | [] => match n with | 0 => 0 | _ => 1
  | _ :: xs => f2 (n := n) xs

def match_alt_cex :=
  ∀ (x : Nat) (l : List Nat), (match x with | 0 => True | _ => @f2 x l = g l) ∧ @f2 x l = g l

-- Kernel-checked counterexample. Does not use Blaster or sorry.
theorem match_alt_cex_false : ¬ match_alt_cex := by
  intro h
  exact absurd (h 0 []).2 (by decide)

#testOptimize ["RecBodyMatchAltNotInParent"] match_alt_cex ===> ∀ (x : Nat) (l : List Nat), g l = @f2 x l


/-! ## Implicit argument instantiated with a closed term -/

-- `OddEqEven` is false, but is not reduced by the optimizer
def OddEqEven : Prop := ∃ n m : Nat, n + n = m + m + 1

theorem not_oddEqEven : ¬ OddEqEven := by
  intro ⟨n, m, h⟩
  omega

open Classical in
noncomputable def fp {p : Prop} : List Nat → Nat
  | [] => if p then 1 else 0
  | _ :: xs => fp (p := p) xs

def closed_imp_hyp_cex :=
  ∀ (l : List Nat), (OddEqEven → @fp OddEqEven l = g l) ∧ @fp OddEqEven l = g l

-- Kernel-checked counterexample. Does not use Blaster or sorry.
theorem closed_imp_hyp_cex_false : ¬ closed_imp_hyp_cex := by
  intro h
  have h1 := (h []).2
  simp [fp, g, not_oddEqEven] at h1

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [closed_imp_hyp_cex]

open Classical in
def closed_dite_hyp_cex :=
  ∀ (l : List Nat), (if OddEqEven then @fp OddEqEven l = g l else True) ∧ @fp OddEqEven l = g l

-- Kernel-checked counterexample. Does not use Blaster or sorry.
theorem closed_dite_hyp_cex_false : ¬ closed_dite_hyp_cex := by
  intro h
  have h1 := (h []).2
  simp [fp, g, not_oddEqEven] at h1

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [closed_dite_hyp_cex]


/-! ## Hypotheses are still used in their scope -/

-- the hypothesis is still in scope once the definition of `@f x` is optimized
#testOptimize ["HypInScopeAfterRecBody"]
  ∀ (x : Nat) (l : List Nat), 0 < x → @f x l = x / x * @f x l ===> True

theorem hyp_in_scope_after_rec_body : ∀ (x : Nat) (l : List Nat), 0 < x → @f x l = x / x * @f x l := by
  blaster

-- the hypothesis is used on the unfolded recursive function application
#testOptimize ["HypOnUnfoldedRecApp"] ∀ (x : Nat), 0 < x → @f x [] = 1 ===> True

theorem hyp_on_unfolded_rec_app : ∀ (x : Nat), 0 < x → @f x [] = 1 := by blaster

theorem closed_hyp_on_unfolded_rec_app : OddEqEven → @fp OddEqEven [] = 1 := by blaster

-- hypotheses introduced in the recursive function definition are still used
def h1 : List Nat → Nat
  | [] => 0
  | x :: xs => if 0 < x then x / x + h1 xs else h1 xs

def h2 : List Nat → Nat
  | [] => 0
  | x :: xs => if 0 < x then 1 + h2 xs else h2 xs

#testOptimize ["HypInRecBody"] ∀ (l : List Nat), h1 l = h2 l ===> True

-- including when the recursive function definition is first optimized under a hypothesis
#testOptimize ["HypInRecBodyUnderHyp"] ∀ (x : Nat) (l : List Nat), 0 < x → h1 l = h2 l ===> True

theorem hyp_in_rec_body_under_hyp : ∀ (x : Nat) (l : List Nat), 0 < x → h1 l = h2 l := by blaster

end Tests.RecBodyHypLeak
