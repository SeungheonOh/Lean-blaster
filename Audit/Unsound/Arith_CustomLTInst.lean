import Blaster

-- LT.lt / LE.le on Nat/Int ignore the instance argument
def weirdLT : LT Nat := ⟨fun _ _ => True⟩
def weirdLE : LE Nat := ⟨fun _ _ => False⟩

theorem bad_lt : ¬ (@LT.lt Nat weirdLT 0 0) := by blaster
example : ¬ ¬ (@LT.lt Nat weirdLT 0 0) := fun h => h trivial

theorem bad_le : @LE.le Nat weirdLE 0 1 := by blaster
example : ¬ (@LE.le Nat weirdLE 0 1) := id

theorem bad_lt_smt : ∀ x : Nat, ¬ (@LT.lt Nat weirdLT x x) := by blaster
theorem bad_lt_smt2 : ∀ x y : Int, (@LT.lt Int ⟨fun _ _ => True⟩ x y) → x < y := by blaster
example : ¬ (∀ x y : Int, (@LT.lt Int ⟨fun _ _ => True⟩ x y) → x < y) := fun h => absurd (h 0 0 trivial) (by decide)

theorem false_le : False := bad_le
