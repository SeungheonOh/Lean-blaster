import Blaster

theorem b1 (α : Type) [inst : BEq α] (a : α) : (a == a) = true := by blaster
theorem b2 (α : Type) [inst : DecidableEq α] (a : α) : (a == a) = true := by blaster
theorem b3 (inst : BEq Nat) (a : Nat) : (@BEq.beq Nat inst a a) = true := by blaster
theorem b4 (α : Type) [inst : LT α] [DecidableRel (α := α) (· < ·)] (a : α) : ¬ (a < a) := by blaster
theorem b5 (α : Type) [Add α] (a b : α) : a + b = b + a := by blaster
theorem b6 (inst : Add Nat) (a b : Nat) : @HAdd.hAdd Nat Nat Nat (@instHAdd Nat inst) a b = b + a := by blaster
theorem b7 (α : Type) [inst : Inhabited α] (a : α) (h : a = default) : (default : α) = a := by blaster
theorem b8 (inst : Decidable (1 = 2)) : @decide (1 = 2) inst = false := by blaster
