import Blaster

def f1 (x : Nat) : Nat := match _h : x with | 0 => 1 | n+1 => n + 2

-- true statements
#blaster [ ∀ x, f1 x = x + 1 ]
#blaster [ f1 3 = 4 ]
-- false statements
#blaster [ ∀ x, f1 x = x ]
#blaster [ ∀ x, f1 x ≠ 4 ]

def f1b (x : Nat) : Nat := match h : x with | 0 => 1 | n+1 => (have : n < x := by omega; n + 2)
#blaster [ ∀ x, f1b x = x + 1 ]
#blaster [ ∀ x, f1b x ≠ 4 ]

def f1c (x : Option Nat) : Nat := match h : x with | some n => n + 1 | none => 0
#blaster [ ∀ x, f1c x ≠ 4 ]
#blaster [ ∀ n, f1c (some n) = n + 1 ]
