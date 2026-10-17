import Lean
import Blaster

/-! # Proof reconstruction detects unsound results

The following statement is false (instantiate `α := Empty`).

Blaster (staging) used to rewrite `∀ (x : α), False` to `False`, which is only correct when `α` is
inhabited (see `isSortOrInhabited`). Proof reconstruction refused to justify this rewrite. The
optimizer now keeps quantifiers over possibly empty types and no longer proves the statement.

The Smt translation used to map each type variable to the universal Smt sort `@@Type`, which is
non-empty, such that the solver still reported the statement as `Valid` (and proof reconstruction
refused to produce a proof for the residual goal). Each type variable universally quantified at
the top level now has its own (possibly empty) membership predicate, and the solver finds the
counterexample `α := Empty`.
-/

namespace Tests.Reconstruct.Unsound

-- The optimizer no longer proves the statement.
#guard_msgs (drop info) in
#blaster (only-optimize: 1) (solve-result: 2) [∀ (α : Type), (∀ (_x : α), False) → False]

-- The Smt solver no longer proves the statement and reports a counterexample.
#guard_msgs (drop info) in
#blaster (reconstruct: 1) (gen-cex: 0) (solve-result: 1) [∀ (α : Type), (∀ (_x : α), False) → False]

-- The statement is indeed false.
example : ¬ (∀ (α : Type), (∀ (_x : α), False) → False) :=
  fun h => h Empty (fun x => nomatch x)

end Tests.Reconstruct.Unsound
