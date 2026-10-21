import Lean
import Blaster

open Blaster.StateMachine

namespace Tests.UnsafeAxiom

-- Issue: Unexpected Valid when an `unsafe` axiom is declared in the current module.
--        After `unsafe axiom unsafe_false : False`, `theorem viaBlaster : False := by blaster`
--        was accepted, although the kernel rejects any safe declaration using `unsafe_false`
--        (i.e., `theorem viaLean : False := unsafe_false` fails with
--        "(kernel) invalid declaration, it uses unsafe declaration").
--
-- Diagnosis: `findLocalAxioms` returned every `Prop` axiom defined in the current module,
--            including the `unsafe` ones, which were then added as hypotheses to the goal
--            (for `#blaster` and the `blaster` tactic) or asserted to the solver (for `#bmc`/`#kind`).
-- Modifications: `findLocalAxioms` now skips `unsafe` axioms. Safe local axioms are still considered.

set_option warn.sorry false

/-! ## Unsafe local axioms must not be assumed -/

unsafe axiom unsafe_false : False

-- Counterexample expected by Blaster (was `Valid`)
#blaster (gen-cex: 0) (solve-result: 1) [False]

/--
error: ❌ Falsified
---
error: Tactic `blaster` failed: Goal was falsified (see counterexample above)

⊢ False
-/
#guard_msgs in
theorem viaBlaster : False := by blaster (gen-cex: 0)

axiom g : Nat → Nat
unsafe axiom unsafe_g_pos : ∀ (n : Nat), g n > 0

-- Counterexample expected by Blaster (was `Valid`)
#blaster (gen-cex: 0) (solve-result: 1) [∀ (n : Nat), g n > 0]

-- `s ≤ 2` is not an invariant (i.e., `s = 3` at depth 3)
instance counter : StateMachine Nat Nat where
  init _ := 0
  next _ s := s + 1
  assumptions _ _ := True
  invariants _ s := s ≤ 2

-- induction must not be established (was `Valid`)
#kind (gen-cex: 0) (max-depth: 1) (solve-result: 2) [counter]

/-! ## Safe local axioms are still assumed -/

axiom f : Nat → Nat
axiom f_pos : ∀ (n : Nat), f n > 0

theorem f_add_gt_one : ∀ (n m : Nat), f n + f m > 1 := by blaster
#blaster [f_add_gt_one]

-- the unsafe axioms are still not assumed when safe local axioms are present
#blaster (gen-cex: 0) (solve-result: 1) [False]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (n : Nat), g n > 0]

end Tests.UnsafeAxiom
