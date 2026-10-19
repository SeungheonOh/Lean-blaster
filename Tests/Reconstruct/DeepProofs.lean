import Lean
import Blaster

/-! # Proof reconstruction on long evaluations

The goals below are proved by the optimizer alone, by evaluating recursive functions on concrete
arguments, i.e., the reconstructed proofs chain thousands of rewrite steps. Reconstruction must neither
overflow the stack (when checking the proof with the kernel or when traversing it to discharge proof
obligations) nor make the kernel evaluate the whole computation again (see `Blaster.Reconstruct.joinChains`,
`Blaster.Reconstruct.shareDeepProofs` and `Blaster.Reconstruct.bridgeEnds`).
-/

namespace Tests.Reconstruct.DeepProofs

/-! ## A small stack machine run with fuel (tail recursion) -/

structure St where
  pc : Nat
  stack : List Nat

def exec (i : Nat) (s : List Nat) : List Nat :=
  match i, s with
  | 0, s => 1 :: s
  | 1, a :: b :: s => (a + b) :: s
  | 2, a :: s => a :: a :: s
  | 3, a :: b :: s => b :: a :: s
  | 4, _ :: s => s
  | _, s => s

def prog : List Nat := [0, 2, 1, 3, 4, 0, 1]

def stepM (s : St) : St :=
  match prog[s.pc]? with
  | some i => { pc := (s.pc + 1) % prog.length, stack := exec i s.stack }
  | none => { pc := 0, stack := s.stack }

def runM : Nat → St → St
  | 0, s => s
  | n+1, s => runM n (stepM s)

-- 6000 explicit rewrite steps
#blaster (reconstruct: 2) (only-optimize: 1) [(runM 3000 ⟨0, [5, 7]⟩).pc = 4]

example : (runM 3000 ⟨0, [5, 7]⟩).stack = [3, 2, 7] := by blaster (reconstruct: 2) (only-optimize: 1)

-- the evaluation occurs under binders (see `Blaster.Reconstruct.alignEnds`)
#blaster (reconstruct: 2) (only-optimize: 1) [∀ x : Nat, x = 1 → (runM 3000 ⟨0, [5, 7]⟩).pc = 4]

/-! ## Recursive calls not in tail position -/

def sumTo : Nat → Nat
  | 0 => 0
  | n+1 => (n+1) + sumTo n

-- the evidence of each recursive call is nested in a congruence over the enclosing addition
#blaster (reconstruct: 2) (only-optimize: 1) [sumTo 3000 = 4501500]

end Tests.Reconstruct.DeepProofs
