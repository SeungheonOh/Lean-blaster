import Blaster

theorem l1 (x : Nat) : x = 0 := by
  let y := 0
  have hy : x = y + 1 := sorry
  blaster   -- should be Falsified (x = 1)

theorem l2 (x : Nat) : True := by
  let y := x + 1
  have : y = x := by blaster  -- should be falsified
  trivial

theorem l3 (n : Nat) (h : n = 3) : True := by
  let m := n
  have : ∀ v : Fin m, v.val < 3 := by blaster
  trivial

theorem l3' (n : Nat) (h : n = 4) : True := by
  let m := n
  have : ∀ v : Fin m, v.val < 3 := by blaster  -- falsified
  trivial

theorem l4 (α : Type) [inst : Inhabited α] (x : α) (h : x = default) : x = @default α inst := by blaster
theorem l5 (α : Type) [inst : Inhabited α] (x : α) : x = @default α inst := by blaster -- falsified

-- let with shadowing names
theorem l6 (x : Nat) : True := by
  let x := 5
  have : x = 5 := by blaster
  trivial
theorem l7 (x : Nat) (hx : x = 2) : True := by
  let x := 5
  have : x = 2 := by blaster -- false (inner x = 5)
  trivial
