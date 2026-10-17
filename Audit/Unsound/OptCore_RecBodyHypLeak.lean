import Blaster

def f {n : Nat} : List Nat → Nat
  | [] => n / n
  | _ :: xs => f (n := n) xs

def g : List Nat → Nat
  | [] => 1
  | _ :: xs => g xs

-- The body of `@f x` (goal fvar x substituted for the implicit param) is optimized
-- under hypothesis `0 < x`, rewriting `x / x` to `1`; it then becomes structurally equal
-- to `g`'s body. recFunInstCache / recFunMap are never scoped to the hypothesis context,
-- so `@f x ≡ g` is reused outside the implication.
theorem bad : ∀ (x : Nat) (l : List Nat), (0 < x → @f x l = g l) ∧ @f x l = g l := by
  blaster

theorem bad_false : ¬ (∀ (x : Nat) (l : List Nat), (0 < x → @f x l = g l) ∧ @f x l = g l) := by
  intro h
  exact absurd (h 0 []).2 (by decide)

theorem oops : False := bad_false bad
