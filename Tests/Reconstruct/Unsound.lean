import Lean
import Blaster

/-! # Proof reconstruction detects unsound results

The following statement is false (instantiate `α := Empty`).

Blaster (staging) used to rewrite `∀ (x : α), False` to `False`, which is only correct when `α` is
inhabited (see `isSortOrInhabited`). Proof reconstruction refused to justify this rewrite. The
optimizer now keeps quantifiers over possibly empty types and no longer proves the statement.

However, the Smt translation maps each type variable to the universal Smt sort `@@Type`, which is
non-empty. Hence, the solver still reports the statement as `Valid`, and proof reconstruction
refuses to produce a proof for the residual goal.
-/

namespace Tests.Reconstruct.Unsound

-- The optimizer no longer proves the statement.
#guard_msgs (drop info) in
#blaster (only-optimize: 1) (solve-result: 2) [∀ (α : Type), (∀ (_x : α), False) → False]

/--
warning: ⚠️ Proof reconstruction failed: could not reconstruct a proof for the residual goal proved by the SMT solver
  ∀ (α : Type), ¬∀ (_x : α), False
The result relies on the trusted Blaster pipeline.
-/
#guard_msgs (warning, drop info) in
#blaster (reconstruct: 1) [∀ (α : Type), (∀ (_x : α), False) → False]

-- The statement is indeed false.
example : ¬ (∀ (α : Type), (∀ (_x : α), False) → False) :=
  fun h => h Empty (fun x => nomatch x)

end Tests.Reconstruct.Unsound
