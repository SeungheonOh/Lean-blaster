import Blaster
def sf : Nat := sorry
def sg : Nat := sorry
theorem t1 : sf = sg := by blaster
example : sf = sg := rfl
def sh (n : Nat) : Nat := sorry
theorem t2 : sh 0 = sh 1 := by blaster
