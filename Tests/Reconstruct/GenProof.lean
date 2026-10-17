import Lean
import Blaster

/-! # Proof generation

`blaster_theorem` and `blaster (gen-proof: 1)` produce theorems whose proofs are checked by the Lean
kernel and only depend on Lean's standard axioms (never on `sorryAx`).
-/

namespace Tests.Reconstruct.GenProof

open Lean Elab Command in
/-- Check that a declaration only depends on Lean's standard axioms. -/
elab "#assert_standard_axioms " n:ident : command => do
  let axs ← liftCoreM (collectAxioms n.getId)
  let bad := axs.filter fun a => ![``propext, ``Classical.choice, ``Quot.sound].contains a
  if !bad.isEmpty then throwError m!"{n.getId} depends on non-standard axioms: {bad.toList}"

blaster_theorem add_comm' : ∀ (x y : Nat), x + y = y + x
#assert_standard_axioms add_comm'

blaster_theorem lt_succ_le : ∀ (x y : Nat), x < y → x + 1 ≤ y
#assert_standard_axioms lt_succ_le

blaster_theorem abs_nonneg : ∀ (x : Int), (if x < 0 then -x else x) ≥ 0
#assert_standard_axioms abs_nonneg

-- generated theorems can be used like any other theorem
example (a b : Nat) : a + b = b + a := add_comm' a b

theorem and_right' (a b : Prop) : a ∧ b → b := by blaster (gen-proof: 1)
#assert_standard_axioms and_right'

end Tests.Reconstruct.GenProof
