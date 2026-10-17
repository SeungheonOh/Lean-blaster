import Lean
import Blaster

/-! # Proof reconstruction tests

Each goal below must be proved by Blaster AND come with a proof term checked by the Lean kernel
(i.e., `(reconstruct: 2)` reports an error when reconstruction fails).
-/

namespace Tests.Reconstruct

/-! ## Goals reduced to `True` by the optimizer -/

-- propositional logic
#blaster (reconstruct: 2) [∀ (a : Prop), a ∧ True → a]
#blaster (reconstruct: 2) [∀ (a b : Prop), a ∧ b → b ∧ a]
#blaster (reconstruct: 2) [∀ (a b : Prop), a ∨ b → b ∨ a]
#blaster (reconstruct: 2) [∀ (a : Prop), a ∨ ¬ a]
#blaster (reconstruct: 2) [∀ (a b : Prop), (a ↔ b) → (b ↔ a)]
#blaster (reconstruct: 2) [∀ (a b : Prop), ¬ (¬ a ∧ ¬ b) → a ∨ b]

-- Boolean operators
#blaster (reconstruct: 2) [∀ (b : Bool), (b && true) = b]
#blaster (reconstruct: 2) [∀ (a b : Bool), (a || b) = (b || a)]
#blaster (reconstruct: 2) [∀ (b : Bool), (b && !b) = false]
#blaster (reconstruct: 2) [∀ (b : Bool), !(!b) = b]

-- arithmetic
#blaster (reconstruct: 2) [∀ (x : Nat), x + 0 = x]
#blaster (reconstruct: 2) [∀ (x y : Nat), x + y = y + x]
#blaster (reconstruct: 2) [(2 : Nat) + 3 = 5]
#blaster (reconstruct: 2) [∀ (x : Int), x - x = 0]
#blaster (reconstruct: 2) [∀ (x y : Int), x * y = y * x]

-- if-then-else (dite' congruence when the condition is normalized)
#blaster (reconstruct: 2) (only-optimize: 1) [∀ (c : Bool) (a b : Nat), (if c then a else b) = (if c = true then a else b)]
#blaster (reconstruct: 2) [∀ (a b : Prop) [Decidable a], (if a then a ∧ b else b) → b]

/-! ## Goals proved by the SMT solver (residual goal re-proved in Lean) -/

#blaster (reconstruct: 2) [∀ (x y : Nat), x < y → x + 1 ≤ y]
#blaster (reconstruct: 2) [∀ (c : Bool) (x y : Nat), (if c = false then x else y) ≥ min x y]
#blaster (reconstruct: 2) [∀ (x y : Nat), (if x > y then x else y) ≥ x]
#blaster (reconstruct: 2) [∀ (x : Int), (if x < 0 then -x else x) ≥ 0]
#blaster (reconstruct: 2) [∀ (x : Nat) (xs : List Nat), !(List.isEmpty xs) → List.head! (List.map (Nat.add x) xs) ≥ x]

/-! ## Equivalence of recursive functions (justified by induction) -/

def addNat (a : Nat) (b : Nat) : Nat :=
  match a, b with
  | _, Nat.zero => a
  | _, Nat.succ b => Nat.succ (addNat a b)

#blaster (reconstruct: 2) [∀ (x y : Nat), addNat x y = x + y]

-- nested equivalences: `powerNat ≡ Nat.pow` relies on `mulNat ≡ Nat.mul`, which relies on `addNat ≡ Nat.add`
def mulNat (x : Nat) (y : Nat) : Nat :=
  match x, y with
  | _, Nat.zero => 0
  | _, Nat.succ b => addNat x (mulNat x b)

def powerNat (a : Nat) (n : Nat) : Nat :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => mulNat a (powerNat a n')

#blaster (reconstruct: 2) (only-optimize: 1) [∀ (x y : Nat), powerNat x y = Nat.pow x y]

/-! ## Residual goals with user definitions (unfolding + case analysis) -/

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | black : Color
  deriving BEq

#blaster (reconstruct: 2) [∀ (x y : Color), x == y → x == Color.transparent → y == Color.transparent]

/-! ## Tactic: the goal is closed with a kernel-checked proof instead of `admit` -/

theorem and_left_rec : ∀ (a b : Prop), a ∧ b → a := by blaster (reconstruct: 2)

theorem nat_lt_succ_le : ∀ (x y : Nat), x < y → x + 1 ≤ y := by blaster (reconstruct: 2)

/-- Check that a declaration does not depend on `sorryAx`, i.e., it has been checked by the kernel
    without any trusted assumption. -/
elab "#assert_kernel_checked " n:ident : command => do
  let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms n.getId)
  if axs.contains ``sorryAx then
    Lean.throwError m!"{n.getId} depends on sorryAx"

#assert_kernel_checked and_left_rec
#assert_kernel_checked nat_lt_succ_le

end Tests.Reconstruct
