import Blaster
-- Every statement below is FALSE: each must be rejected (Falsified / error), never ✅ Valid.
theorem f01 : ∀ (c : Prop) [Decidable c], (if c then 0 else (if c then 1 else 2)) ≠ 2 := by blaster
theorem f02 : ∀ (c : Prop) [Decidable c], (if h : c then 0 else (if c then 1 else 2)) ≠ 2 := by blaster
theorem f03 : ∀ b : Bool, (if b then 0 else (if b then 1 else 2)) ≠ 2 := by blaster
theorem f04 : ∀ b : Bool, (if b = false then (if b then 1 else 2) else 0) ≠ 2 := by blaster
theorem f05 : ∀ (c : Prop) [Decidable c], (if ¬ c then (if c then 1 else 2) else 0) ≠ 2 := by blaster
theorem f06 : ∀ p q : Prop, (p ∨ q) → q := by blaster
theorem f07 : ∀ a c : Prop, (a ∧ (a → c)) ↔ c := by blaster
theorem f08 : ∀ a c : Prop, (a ∨ (c → a)) → a := by blaster
theorem f09 : ∀ a c : Prop, ((a → c) ∧ (¬a → c)) → a := by blaster
theorem f10 : ∀ b1 b2 : Bool, (decide (b1 = true) && b2) = b1 := by blaster
theorem f11 : ∀ x y : Bool, (x = false ∧ y = false) → (x || y) = true := by blaster
theorem f12 : ∀ x y : Bool, (x = true ∨ y = false) → x = true := by blaster
theorem f13 : ∀ s : String, "a" ++ s = s ++ "a" := by blaster
theorem f14 : ∀ s : String, String.length ("ab" ++ s) = 2 := by blaster
theorem f15 : ∀ (c : Prop) [Decidable c] (p q : Nat × Nat), (if c then p else q).1 = p.1 := by blaster
theorem f16 : ∀ (b : Bool) (x : Nat), b = true → (if b then x else 0) = 0 := by blaster
theorem f17 : ∀ (b : Bool), (!b && b) = true ∨ b = false := by blaster
theorem f18 : ∀ (p : Prop) (b : Bool), (p → b = true) → b = true := by blaster
theorem f19 : ∀ (p q : Prop), (¬ p → q) → p := by blaster
theorem f20 : ∀ (x : Nat), (if x = 0 then x + 1 else x) = x := by blaster
theorem f21 : ∀ (c : Prop) [Decidable c] (x y : Nat), (if c then (if c then x else y) else (if c then y else x)) = x := by blaster
theorem f22 : ∀ (a c : Prop) [Decidable a] [Decidable c] (x y z : Nat), (if a then (if c then x else y) else (if c then x else z)) = (if c then x else y) := by blaster
theorem f23 : ∀ (a c : Prop) [Decidable a] [Decidable c] (x y z : Nat), (if a then (if c then x else z) else (if c then y else z)) = (if c then x else z) := by blaster
theorem f24 : ∀ (a c : Prop) [Decidable a] [Decidable c] (x y : Nat), (if a then (if c then x else y) else (if c then y else x)) = x := by blaster
theorem f25 : ∀ (p : Prop) [Decidable p], decide p = true ∨ decide (¬ p) = false := by blaster
theorem f26 : ∀ (b : Bool) (p : Prop), (b = true ∧ p) → ((!b) || decide p) = false := by blaster
