/-
  Pass-2 machine-checked proof obligations for the arithmetic / relational / Eq rewrite rules.
  Run: lake env lean Audit/Pass2/RulesArith/Obligations.lean
  Each theorem states one rule exactly as the code implements it (side conditions = what the code checks).
  Rules whose literal folding uses a meta-level function `g` for an object-level operator `f` are stated as
  `f n1 n2 = g n1 n2` for all literals.  Disproven rules are stated negated (`¬ ∀ …`) with a witness.
-/
import Blaster

namespace Pass2.Arith

/-! ## OptimizeNat.lean -/

theorem N1_zero_add (n : Nat) : Nat.add 0 n = n := by simp
theorem N2_add_cst (a b : Nat) : Nat.add a b = a + b := rfl
theorem N3_add_assoc_cst (N1 N2 n : Nat) : Nat.add N1 (Nat.add N2 n) = Nat.add (N1 + N2) n := by
  show N1 + (N2 + n) = N1 + N2 + n; omega
theorem N4_sub_self (n : Nat) : Nat.sub n n = 0 := by show n - n = 0; omega
theorem N5_zero_sub (n : Nat) : Nat.sub 0 n = 0 := by show 0 - n = 0; omega
theorem N6_sub_zero (n : Nat) : Nat.sub n 0 = n := rfl
theorem N7_sub_cst (a b : Nat) : Nat.sub a b = Nat.sub a b := rfl   -- meta fn = object fn (`Nat.sub`)
theorem N8_cst_sub_add (N1 N2 n : Nat) : Nat.sub N1 (Nat.add N2 n) = Nat.sub (Nat.sub N1 N2) n := by
  show N1 - (N2 + n) = N1 - N2 - n; omega
theorem N9_cst_sub_sub (N1 N2 n : Nat) : Nat.sub (Nat.sub N1 n) N2 = Nat.sub (Nat.sub N1 N2) n := by
  show N1 - n - N2 = N1 - N2 - n; omega
theorem N10_sub_cst_sub (N1 N2 n : Nat) : Nat.sub (Nat.sub n N1) N2 = Nat.sub n (N1 + N2) := by
  show n - N1 - N2 = n - (N1 + N2); omega
theorem N11_add_cst_sub (N1 N2 n : Nat) (h : Nat.ble N2 N1 = true) :
    Nat.sub (Nat.add N1 n) N2 = Nat.add (Nat.sub N1 N2) n := by
  have := Nat.le_of_ble_eq_true h; show N1 + n - N2 = N1 - N2 + n; omega
theorem N12_pow_zero (n : Nat) : Nat.pow n 0 = 1 := rfl
theorem N13_pow_cst (a b : Nat) : Nat.pow a b = Nat.pow a b := rfl
theorem N14_zero_mul (n : Nat) : Nat.mul 0 n = 0 := by show 0 * n = 0; simp
theorem N15_one_mul (n : Nat) : Nat.mul 1 n = n := by show 1 * n = n; simp
theorem N16_mul_cst (a b : Nat) : Nat.mul a b = Nat.mul a b := rfl
theorem N17_mul_assoc_cst (N1 N2 n : Nat) : Nat.mul N1 (Nat.mul N2 n) = Nat.mul (Nat.mul N1 N2) n := by
  show N1 * (N2 * n) = N1 * N2 * n; rw [Nat.mul_assoc]
theorem N18_mul_pow (n m : Nat) : Nat.mul n (Nat.pow n m) = Nat.pow n (Nat.add 1 m) := by
  show n * n ^ m = n ^ (1 + m); rw [Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
-- nonZeroNatInHyps m  ≡  (m lit ≠ 0) ∨ hyp (0 < m) ∨ hyp ¬(0 = m)  — all imply m ≠ 0
theorem N19a_mul_div_cancel (m n : Nat) (h : 0 < m ∨ ¬ (0 = m)) : Nat.div (Nat.mul m n) m = n := by
  have : 0 < m := by omega
  show m * n / m = n; exact Nat.mul_div_cancel_left n this
theorem N19b_mul_div_cancel (m n : Nat) (h : 0 < m ∨ ¬ (0 = m)) : Nat.div (Nat.mul n m) m = n := by
  have : 0 < m := by omega
  show n * m / m = n; exact Nat.mul_div_cancel n this
theorem N20_div_self (n : Nat) (h : 0 < n ∨ ¬ (0 = n)) : Nat.div n n = 1 := by
  have : 0 < n := by omega
  show n / n = 1; exact Nat.div_self this
theorem N21_div_zero (n : Nat) : Nat.div n 0 = 0 := by show n / 0 = 0; simp
theorem N22_div_one (n : Nat) : Nat.div n 1 = n := by show n / 1 = n; simp
theorem N23_zero_div (n : Nat) : Nat.div 0 n = 0 := by show 0 / n = 0; simp
theorem N24_div_cst (a b : Nat) : Nat.div a b = Nat.div a b := rfl
theorem N25_div_div (n N1 N2 : Nat) : Nat.div (Nat.div n N1) N2 = Nat.div n (Nat.mul N1 N2) := by
  show n / N1 / N2 = n / (N1 * N2); exact Nat.div_div_eq_div_mul n N1 N2
-- code: gcd := if n1 < n2 then Nat.gcd n1 n2 else Nat.gcd n2 n1 ; guard gcd ≠ 1 ; N2 ≠ 0 by arm order
theorem N26_mul_div_gcd (N1 N2 n : Nat) (h2 : N2 ≠ 0) :
    let g := if N1 < N2 then Nat.gcd N1 N2 else Nat.gcd N2 N1
    Nat.div (Nat.mul N1 n) N2 = Nat.div (Nat.mul (Nat.div N1 g) n) (Nat.div N2 g) := by
  intro g
  have hg : g = Nat.gcd N1 N2 := by
    simp only [g]; split <;> simp [Nat.gcd_comm]
  rw [hg]
  have hpos : 0 < Nat.gcd N1 N2 := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero h2)
  have e1 : N1 / Nat.gcd N1 N2 * Nat.gcd N1 N2 = N1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have e2 : N2 / Nat.gcd N1 N2 * Nat.gcd N1 N2 = N2 := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  show N1 * n / N2 = N1 / Nat.gcd N1 N2 * n / (N2 / Nat.gcd N1 N2)
  conv => lhs; rw [← e1, ← e2]
  rw [Nat.mul_right_comm, Nat.mul_div_mul_right _ _ hpos]
theorem N27_mod_self (n : Nat) : Nat.mod n n = 0 := by show n % n = 0; simp
theorem N28a_mul_mod_left (m n : Nat) : Nat.mod (Nat.mul m n) m = 0 := by
  show m * n % m = 0; simp
theorem N28b_mul_mod_right (m n : Nat) : Nat.mod (Nat.mul n m) m = 0 := by
  show n * m % m = 0; simp
theorem N29_mod_zero (n : Nat) : Nat.mod n 0 = n := by show n % 0 = n; simp
theorem N30_mod_one (n : Nat) : Nat.mod n 1 = 0 := by show n % 1 = 0; simp
theorem N31_zero_mod (n : Nat) : Nat.mod 0 n = 0 := by show 0 % n = 0; simp
theorem N32_mod_cst (a b : Nat) : Nat.mod a b = Nat.mod a b := rfl
theorem N33_mul_mod_cst (N1 N2 n : Nat) (h : Nat.mod N1 N2 = 0) : Nat.mod (Nat.mul N1 n) N2 = 0 := by
  show N1 * n % N2 = 0
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h) (Nat.dvd_mul_right _ _))
theorem N34_beq (x y : Nat) : Nat.beq x y = @BEq.beq Nat instBEqOfDecidableEq x y := by
  by_cases h : x = y <;> simp [h, Nat.beq_eq, BEq.beq]
theorem N35_ble (x y : Nat) : Nat.ble x y = Blaster.decide' (x ≤ y) := by
  unfold Blaster.decide'
  split <;> rename_i hc _ <;> simp_all [Nat.ble_eq]

end Pass2.Arith
