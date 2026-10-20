import Blaster
set_option pp.all true
def sf : Nat := sorry
def sg : Nat := sorry
#print sf
#print sg
def sh (n : Nat) : Nat := sorry
#print sh
example : sh 0 = sh 1 := rfl
set_option trace.Translate.optExpr true in
theorem t1 : sf = sg := by blaster
set_option trace.Translate.optExpr true in
theorem t3 : sf + 1 = sg + 1 := by blaster
set_option trace.Translate.optExpr true in
theorem t4 (x : Nat) : (sf = x) = (sg = x) := by blaster
