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

-- control: same terms, no Eq between them
#blaster (only-optimize: 1) (verbose: 1) [ ∀ (a b : Nat) (p : T → T → Prop), p (d22 (.leaf a)) (d22 (.leaf b)) → p (d22 (.leaf a)) (d22 (.leaf b)) ]
#blaster (only-optimize: 1) (verbose: 1) [ ∀ (a b : Nat), (d22 (.leaf a)) = (d22 (.leaf b)) → (d22 (.leaf a)) = (d22 (.leaf b)) ]
