import Lean
import Blaster

/-! # Proof reconstruction detects unsound optimizations

Blaster (staging) reports the following statement as `Valid` although it is false
(instantiate `α := Empty`). The optimizer rewrites `∀ (x : α), False` to `False`, which is only
correct when `α` is inhabited (see `isSortOrInhabited`). Proof reconstruction refuses to produce
a proof and pinpoints the unjustified rewrite.
-/

namespace Tests.Reconstruct.Unsound

/--
warning: ⚠️ Proof reconstruction failed: 1 unresolved proof obligation(s) out of 1:
  • (∀ (_x : α), False) = False
The result relies on the trusted Blaster pipeline.
-/
#guard_msgs (warning, drop info) in
#blaster (reconstruct: 1) [∀ (α : Type), (∀ (_x : α), False) → False]

-- The statement is indeed false.
example : ¬ (∀ (α : Type), (∀ (_x : α), False) → False) :=
  fun h => h Empty (fun x => nomatch x)

end Tests.Reconstruct.Unsound
