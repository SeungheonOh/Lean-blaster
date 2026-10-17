import Blaster

theorem bad (n : Nat) : n = n + 1 := by
  have h := bad n
  blaster

theorem worse : False := by
  have := bad 0
  omega

#print axioms worse
