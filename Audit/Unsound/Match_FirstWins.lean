import Blaster

def g (x : Nat) : Nat :=
  match (generalizing := false) x with
  | _n+1 => (match x with | 1 => 10 | _m+1 => 20 | 0 => 30)
  | 0 => 0

#print g
example : g 1 = 10 := by decide

-- false: x = 1 gives 10
theorem bad1 : ∀ x : Nat, g x ≠ 10 := by blaster

#blaster (only-optimize: 1) [ ∀ x : Nat, g x ≠ 10 ]

def g2 (x : Option Nat) : Nat :=
  match (generalizing := false) x with
  | some _ => (match x with | some 1 => 10 | some _ => 20 | none => 30)
  | none => 0

theorem bad2 : ∀ x : Option Nat, g2 x ≠ 10 := by blaster
example : g2 (some 1) = 10 := by decide

theorem false1 : False := bad1 1 (by decide)
theorem false2 : False := bad2 (some 1) (by decide)
#print axioms false1
#blaster (only-optimize: 1) (verbose: 1) [ ∀ x : Option Nat, g2 x ≠ 10 ]
