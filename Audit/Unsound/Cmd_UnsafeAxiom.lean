import Blaster

unsafe axiom unsafeFalse : False

-- Lean refuses to use the unsafe axiom in a safe theorem:
-- theorem viaLean : False := unsafeFalse   -- error: (kernel) invalid declaration, it uses unsafe declaration

theorem viaBlaster : False := by blaster
#print axioms viaBlaster
