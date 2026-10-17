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

namespace Blaster.Reconstruct

/-! ## Primitive operators

The optimizer keeps primitive operators (e.g., `Nat.add`) instead of their notation counterparts
(e.g., `HAdd.hAdd`). The following lemmas rewrite them back to notation such that Lean
decision procedures (e.g., `simp`, `omega`) can reason about them.
-/

theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
theorem nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl
theorem nat_pow_eq (a b : Nat) : Nat.pow a b = a ^ b := rfl
theorem int_add_eq (a b : Int) : Int.add a b = a + b := rfl
theorem int_mul_eq (a b : Int) : Int.mul a b = a * b := rfl
theorem int_neg_eq (a : Int) : Int.neg a = -a := rfl
theorem int_ediv_eq (a b : Int) : Int.ediv a b = a / b := rfl
theorem int_emod_eq (a b : Int) : Int.emod a b = a % b := rfl
theorem int_pow_eq (a : Int) (b : Nat) : Int.pow a b = a ^ b := rfl

end Blaster.Reconstruct

/-- Rewrite Blaster's internal representation back to standard Lean notation in all hypotheses and the goal. -/
macro "blaster_denorm" : tactic =>
  `(tactic| (try simp only [Blaster.Reconstruct.dite'_eq_dite, Blaster.Reconstruct.decide'_eq_decide,
              Blaster.Reconstruct.nat_add_eq, Blaster.Reconstruct.nat_sub_eq, Blaster.Reconstruct.nat_mul_eq,
              Blaster.Reconstruct.nat_div_eq, Blaster.Reconstruct.nat_mod_eq, Blaster.Reconstruct.nat_pow_eq,
              Blaster.Reconstruct.int_add_eq, Blaster.Reconstruct.int_mul_eq, Blaster.Reconstruct.int_neg_eq,
              Blaster.Reconstruct.int_ediv_eq, Blaster.Reconstruct.int_emod_eq, Blaster.Reconstruct.int_pow_eq,
              Int.ofNat_eq_coe] at *))

namespace Blaster.Reconstruct

/-! ## Congruence lemmas -/

/-- Congruence for `Blaster.dite'` when the condition is rewritten. -/
theorem dite'_congr {α : Sort u} {c c' : Prop} {t : c → α} {e : ¬ c → α} {t' : c' → α} {e' : ¬ c' → α}
    (hc : c = c') (ht : ∀ h : c', t (hc.mpr h) = t' h) (he : ∀ h : ¬ c', e (fun h0 => h (hc.mp h0)) = e' h) :
    Blaster.dite' c t e = Blaster.dite' c' t' e' := by
  subst hc
  have h1 : t = t' := funext ht
  have h2 : e = e' := funext he
  rw [h1, h2]

end Blaster.Reconstruct
