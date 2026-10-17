import Blaster
set_option maxHeartbeats 0
inductive T where
 | leaf : Nat → T
 | node : T → T → T

def dup (t : T) : T := .node t t
def d4 (t : T) : T := dup (dup (dup (dup t)))
def d16 (t : T) : T := d4 (d4 (d4 (d4 t)))
def d20 (t : T) : T := d4 (d16 t)
def d22 (t : T) : T := dup (dup (d20 t))

#blaster (only-optimize: 1) (verbose: 1) [ ∀ a b : Nat, d16 (.leaf a) = d16 (.leaf b) → True ]
#blaster (only-optimize: 1) (verbose: 1) [ ∀ a b : Nat, d20 (.leaf a) = d20 (.leaf b) → True ]
#blaster (only-optimize: 1) (verbose: 1) [ ∀ a b : Nat, d22 (.leaf a) = d22 (.leaf b) → True ]
