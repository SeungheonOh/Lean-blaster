import Lean
import Blaster

/-! # Replay of SMT proofs

Goals proved by the SMT solver, with proofs reconstructed by replaying the proof produced by the SMT
backend only (`(smt-proof: 3)`, see `Blaster.Reconstruct.SmtProof`).
-/

namespace Tests.Reconstruct.SmtProof

-- arithmetic
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (x y : Nat), x < y → x + 1 ≤ y]
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (x y : Nat), x - y ≤ x]
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (x t : Int), x = 1 → (Int.toNat t) + 2 ≥ 2]
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (x y : Nat), x / (y + 1) ≤ x]

-- nonlinear arithmetic (see `blaster_nlarith`), Z3's division and modulo by zero (`div0`, `mod0`)
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (x y z : Int), x * z = y * x → x ≠ 0 → y = z]
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (w x y z : Nat), w ≤ x → y ≤ z → w * y ≤ x * z]
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (x y z : Nat), 0 < x → x * y / (x * z) = y / z]
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (x y : Nat), x % y ≤ x]

-- Bool encodings
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (x : Int) (f : Int → Bool), (f x && x == 0) = true → x = 0]

-- datatypes and matches
inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | black : Color
  deriving BEq

#blaster (reconstruct: 2) (smt-proof: 3) [∀ (x y : Color), x == y → x == Color.transparent → y == Color.transparent]

structure BS where
  data : String

inductive D where
  | Constr : Int → List D → D
  | Map : List (D × D) → D
  | I : Int → D
  | B : BS → D

def firstAmount (l : List (D × D)) : Bool :=
  match l with
  | (D.B { data := "" }, D.Map [(D.B { data := "" }, D.I n)]) :: _ => n == 0
  | _ => false

#blaster (reconstruct: 2) (smt-proof: 3) [∀ l, firstAmount l = true → l ≠ []]

def nested (d : D) : Bool :=
  match d with
  | D.Constr 0 [r, _] =>
    match r with
    | D.Constr 0 [_, b] =>
      match b with
      | D.Constr n [] => if 0 = n then true else false
      | _ => false
    | _ => false
  | _ => false

#blaster (reconstruct: 2) (smt-proof: 3) [∀ d, nested d = true → d ≠ D.I 0]

-- polymorphism (a single sort variable)
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (α : Type) (o : Option α), o.isSome = true → o ≠ none]

-- polymorphism: several sort variables, possibly empty sort variables (skolem constants of their sort),
-- quantified sort variables
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (α β : Type) (_f : α → β), (∀ (_y : β), False) → ∀ (_x : α), False]
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (α β : Type) (f g : α → β), (∀ (x : α), f x = g x) → f = g]
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (α : Type) (f : α → α), (∀ x, f x = x) → f = (fun x => x)]
#blaster (reconstruct: 2) (smt-proof: 3)
  [(∀ (β : Type) (xs : List β) (f : List β → Nat), f xs > 10) → ∀ (α : Type) (xs : List α) (f : List α → Nat), f xs > 5]

-- polymorphic functions at several sort variables (interpreted at the universe and related to the goal by naturality
-- lemmas), lambda terms guarded by the membership predicates of their parameters (e.g., constant functions)
#blaster (reconstruct: 2) (smt-proof: 3) [∀ (α β : Type) (xs : List α) (c : β), List.map (fun _ => c) xs = [] → xs = []]

theorem zipWith_map_left {l₁ : List α} {l₂ : List β} {f : α → α'} {g : α' → β → γ} :
    List.zipWith g (l₁.map f) l₂ = List.zipWith (fun a b => g (f a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> blaster (reconstruct: 2) (smt-proof: 3)

end Tests.Reconstruct.SmtProof
