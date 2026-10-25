import Lean
import Blaster

namespace Tests.PropProofEq

-- Issue: Unexpected Valid for falsifiable goals distinguishing the proofs of a proposition.
-- Diagnosis: Any two proofs of a proposition are (definitionally) equal in Lean, e.g., the two constructors of
--            `TwoP` below. The optimizer reduced `TwoP.a = TwoP.b` to `False` (distinct constructors) and the
--            translation of an inductive proposition to an smt datatype distinguishes its values. An equality
--            between proofs is now reduced to `True`, and the proof arguments of constructor applications are
--            ignored when comparing them structurally.

inductive TwoP : Prop
  | a
  | b

inductive SomeBig : Prop
  | intro (n : Nat) (h : n > 5)

structure WithProof where
  n : Nat
  h : TwoP

theorem twoP_eq : TwoP.a = TwoP.b := rfl

theorem with_proof_eq : WithProof.mk 0 TwoP.a = WithProof.mk 0 TwoP.b := rfl

-- Falsified expected (false in Lean, see the theorems above)
#blaster (gen-cex: 0) (solve-result: 1) [TwoP.a ≠ TwoP.b]

#blaster (gen-cex: 0) (solve-result: 1) [∃ (x y : TwoP), x ≠ y]

#blaster (gen-cex: 0) (solve-result: 1) [∃ (x y : SomeBig), x ≠ y]

#blaster (gen-cex: 0) (solve-result: 1) [WithProof.mk 0 TwoP.a ≠ WithProof.mk 0 TwoP.b]

-- Valid expected
#blaster [TwoP.a = TwoP.b]

#blaster [∀ (x y : TwoP), x = y]

#blaster [∀ (x y : SomeBig), x = y]

#blaster [∀ (n : Nat), WithProof.mk n TwoP.a = WithProof.mk n TwoP.b]

end Tests.PropProofEq
