import Lean
import Blaster

namespace Tests.LambdaDefGuard

-- Issue: Unexpected Valid for falsifiable goals equating lambda terms.
-- Diagnosis: The definitions of lambda terms (`@lambda_n_def_cstr`, `@global_lambda_n_def_cstr`) constrained
--            their applications to all the values of the sorts of their parameters, i.e., the values of all
--            the types denoted by sort variables (sort `@Instance`), and the negative integers for `Nat`
--            parameters. Two lambda terms equal in Lean (on their domain) are then equal on all the values of
--            their sort, which is inconsistent when they differ outside their domain. The definitions are now
--            guarded by the membership predicates of the parameters.

-- `fun x : α => x` and `fun _ => c` are equal when `α` is a singleton, which says nothing on the values of `β`
-- (false for `α := Unit`, `β := Bool`)
theorem poly_lambda_eq_false :
  ¬ (∀ (α β : Type) (c : α) (b1 b2 : β), (∀ x : α, x = c) → (fun x : α => x) = (fun _ => c) → b1 ≠ b2 → False) :=
  fun h => h Unit Bool () true false (fun _ => rfl) rfl (by decide)

#blaster (gen-cex: 0) (solve-result: 1) (timeout: 10)
  [∀ (α β : Type) (c : α) (b1 b2 : β), (∀ x : α, x = c) → (fun x : α => x) = (fun _ => c) → b1 ≠ b2 → False]

-- the two functions are equal on `Nat` but their encodings differ on the negative integers
theorem nat_lambda_eq : (fun n : Nat => n - 1 + 1) = (fun n : Nat => if n = 0 then 1 else n) := by
  funext n; split <;> omega

#blaster (gen-cex: 0) (solve-result: 1) (timeout: 10)
  [∀ (b : Bool), (fun n : Nat => n - 1 + 1) = (fun n : Nat => if n = 0 then 1 else n) → b = true]

-- Valid expected: lambda terms are still unfolded on their domain
#blaster [∀ (x : Nat), (fun n : Nat => n - 1 + 1) x ≥ 1]
#blaster [∀ (x : Nat) (f : Nat → Nat), f = (fun n => n + 1) → f x > x]
#blaster [∀ (α : Type) (x : α) (f : α → α), f = (fun y => y) → f x = x]

end Tests.LambdaDefGuard
