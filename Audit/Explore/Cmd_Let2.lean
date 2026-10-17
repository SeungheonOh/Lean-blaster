import Blaster
theorem a1 : True := by
  let f := fun x : Nat => x + 1
  have : f 2 = 3 := by blaster
  have : f 2 = 4 := by blaster -- should be Falsified
  trivial

theorem a2 (n : Nat) : True := by
  let k := n * 2
  let j := k + 1
  have : j % 2 = 1 := by blaster
  have : j % 2 = 0 := by blaster -- should be Falsified
  trivial

-- hypothesis depending on let var, then clear the value via generalize?
theorem a3 (n : Nat) (h : n > 5) : True := by
  let k := n - 5
  have hk : k + 5 = n := by blaster
  have : k = 0 := by blaster -- falsified
  trivial
