import Blaster

partial def pf (n : Nat) : Nat := pf n + 1
theorem p1 : pf 0 = pf 0 + 1 := by blaster
theorem p2 : pf 0 = 0 := by blaster
theorem p3 (n : Nat) : pf n = default := by blaster

opaque o : Nat
opaque o5 : Nat := 5
theorem o1 : o = 0 := by blaster
theorem o2 : o5 = 5 := by blaster

def implA (n : Nat) : Nat := n + 2
@[implemented_by implA] def specA (n : Nat) : Nat := n + 1
theorem e1 : specA 1 = 3 := by blaster
theorem e2 : specA 1 = 2 := by blaster

@[extern "lean_foo"] def extF (n : Nat) : Nat := n * 2
theorem e3 : extF 3 = 6 := by blaster

noncomputable def nc : Nat := Classical.choice ⟨3⟩
theorem n1 : nc = 3 := by blaster
