import Blaster

theorem t1 (x : Nat) (h : x = 0) : x + 1 = 1 := by blaster
#print axioms t1

-- let-bound
theorem t2 (x : Nat) (h : x = 0) : let y := x; y = 0 := by intro y; blaster
theorem t3 (x : Nat) : True := by
  let y := x + 1
  have hy : y = x + 1 := rfl
  have : y > x := by blaster
  trivial
theorem t4 (x : Nat) : x = 1 := by
  let y := 1
  have hy : x = y := sorry
  blaster
