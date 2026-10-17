import Blaster
/- `@LT.lt Nat inst` is treated as Nat.lt whatever `inst` is (isOpaqueRelational only checks the
   type, Env.lean:1194-1197; lt? / notLTNumNorm? in OptimizePropNot.lean:39 never look at the instance). -/
def revLT : LT Nat := ⟨fun a b => b < a⟩

theorem bad1 : ¬ (@LT.lt Nat revLT 1 0) := by blaster
theorem bad1_false : ¬ ¬ (@LT.lt Nat revLT 1 0) := fun h => h (show 0 < 1 from Nat.zero_lt_one)

theorem bad2 : ∀ x : Nat, ¬ (@LT.lt Nat revLT 0 x) → 0 = x := by blaster
theorem bad2_false : ¬ (∀ x : Nat, ¬ (@LT.lt Nat revLT 0 x) → 0 = x) :=
  fun h => absurd (h 1 (fun (hx : 1 < 0) => absurd hx (by decide))) (by decide)

theorem c1 : False := bad1_false bad1
theorem c2 : False := bad2_false bad2


def revLE : LE Nat := ⟨fun a b => b ≤ a⟩
theorem bad3 : @LE.le Nat revLE 0 1 := by blaster
theorem bad3_false : ¬ (@LE.le Nat revLE 0 1) := fun (h : 1 ≤ 0) => absurd h (by decide)
theorem c3 : False := bad3_false bad3
