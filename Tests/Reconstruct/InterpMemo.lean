import Blaster

/-! # Memoization of the interpretation of SMT terms on object addresses

The interpretation of the steps of a replay memoizes the closed terms on their object addresses (`InterpCtx.cache`).
Terms built during the replay (e.g., the conclusion of a `proof-bind` step as a quantifier, see `stepConcl`) are freed
after their interpretation, and a term built afterwards may be allocated at the same address: the memo keeps its terms
alive, otherwise it returns the interpretation of the freed term for the new one. In a replay of
`Tests/FixedIssues/Issue17.lean`, the conclusion of a `proof-bind` step was thus interpreted as the conclusion of an
earlier one, and the kernel rejected the proof of the step using it (an application to the proof of the premise).
-/

namespace Tests.Reconstruct.InterpMemo

open Lean Meta Blaster.Reconstruct.SmtProof

/-- `∀ x, i ≤ x`, a new object at each call. -/
def quant (i : Nat) : STerm := .quant .forall #[("x", .atom "Int")] (.app "<=" #[.num i, .sym "x"])

/-- The number of terms `quant i` (`i < n`), interpreted one after the other with the same memo and freed after their
    interpretation, whose interpretation differs from the one without memo. -/
def staleInterpretations (n : Nat) : MetaM Nat := do
  let memo ← IO.mkRef {}
  let mut stale := 0
  for i in [0:n] do
    let e ← (interpProp (quant i)).run { table := {}, cache := some memo }
    let e' ← (interpProp (quant i)).run { table := {} }
    if e != e' then stale := stale + 1
  return stale

/-- info: 0 -/
#guard_msgs in
#eval staleInterpretations 1000

end Tests.Reconstruct.InterpMemo
