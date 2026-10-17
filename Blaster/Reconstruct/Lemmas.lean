import Lean
import Blaster.Optimize.Decidable

/-! # Lemmas used to justify the rewriting rules applied by the optimizer

Each lemma is stated as an equality whose lhs/rhs match (up to definitional equality)
the expressions produced by the corresponding rewriting rule.
-/

namespace Blaster.Reconstruct

/-! ## Normalization of opaque constants (see `normConst`) -/

theorem nat_pred_eq : Nat.pred = fun n => Nat.sub n 1 := by
  funext n; cases n <;> rfl

theorem nat_succ_eq : Nat.succ = fun n => Nat.add 1 n := by
  funext n; exact (Nat.one_add n).symm

theorem nat_ble_eq : Nat.ble = fun x y => Blaster.decide' (x ≤ y) := by
  funext x y
  cases h : Nat.ble x y
  . have h1 : ¬ (x ≤ y) := fun h2 => by
      have := Nat.ble_eq_true_of_le h2
      rw [h] at this; contradiction
    exact ((Blaster.decide'_false _).mpr h1).symm
  . exact ((Blaster.decide'_true _).mpr (Nat.le_of_ble_eq_true h)).symm

theorem nat_beq_eq : Nat.beq = fun x y => x == y := by
  funext x y
  cases h : Nat.beq x y
  . have h1 := Nat.ne_of_beq_eq_false h
    simp [h1]
  . have h1 := Nat.eq_of_beq_eq_true h
    simp [h1]

theorem int_negSucc_eq : Int.negSucc = fun n => Int.neg (Int.ofNat (Nat.add 1 n)) := by
  funext n
  show Int.negSucc n = Int.neg (Int.ofNat (1 + n))
  rw [Nat.add_comm]; rfl

end Blaster.Reconstruct

namespace Blaster.Reconstruct

/-! ## Denormalization lemmas

The optimizer replaces `ite`, `dite` and `decide` with `Blaster.dite'` and `Blaster.decide'`, which
ignore decidable instances. The following lemmas rewrite them back to their standard counterparts
(with classical decidable instances) such that Lean decision procedures can reason about them.
-/

theorem dite'_eq_dite {α : Sort u} (c : Prop) (t : c → α) (e : ¬ c → α) :
    Blaster.dite' c t e = @dite α c (Classical.propDecidable c) t e := by
  simp only [Blaster.dite_equiv]

theorem decide'_eq_decide (c : Prop) :
    Blaster.decide' c = @decide c (Classical.propDecidable c) := by
  simp only [Blaster.decide'_equiv]

end Blaster.Reconstruct
