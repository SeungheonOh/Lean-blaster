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

end Tests.Reconstruct.SmtProof
