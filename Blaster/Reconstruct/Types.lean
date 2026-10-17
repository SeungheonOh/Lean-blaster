import Lean

open Lean

namespace Blaster.Reconstruct

/-! # Proof reconstruction: core types

Proof reconstruction turns a `Valid` verdict produced by Blaster into a proof term
checked by the Lean kernel. The optimizer is instrumented so that every rewrite
`e ⟶ e'` carries an `EqPf`, i.e., evidence that `e = e'`.
-/

/-- Evidence that the expression a frame started with (the *lhs*) is equal to the
    expression it produced (the *rhs*).
-/
inductive EqPf where
  /-- `lhs` and `rhs` are definitionally equal: no proof term is needed as the
      kernel can check the equality by conversion (e.g., beta, delta, iota, zeta). -/
  | defeq
  /-- `p : lhs = rhs` (up to definitional equality on both sides). -/
  | proof (p : Expr)
  /-- No evidence has been tracked. An `unknown` evidence is turned into a proof
      obligation (a *hole*) as soon as both ends of the rewrite are known. -/
  | unknown
deriving Inhabited, Repr

/-- Key used to tag a proof obligation (i.e., hole) in a proof term.
    A hole is represented as `mdata {blaster.hole := id} (sorryAx (lhs = rhs) true)`.
-/
def holeKey : Name := `blaster.hole

/-- Origin of a proof obligation. Used to report reconstruction coverage. -/
inductive HoleKind where
  /-- A rewrite rule that does not (yet) provide an explicit proof. -/
  | rule
  /-- A construction for which no congruence proof is (yet) built (e.g., match alternatives). -/
  | frame
  /-- A cached rewrite whose proof is not available in the current context. -/
  | cache
  /-- A congruence over a dependent argument. -/
  | dependent
deriving Inhabited, Repr, BEq, Hashable

def HoleKind.toString : HoleKind → String
  | .rule => "rule"
  | .frame => "frame"
  | .cache => "cache"
  | .dependent => "dependent"

instance : ToString HoleKind := ⟨HoleKind.toString⟩

/-- Information kept for each proof obligation. -/
structure HoleInfo where
  kind : HoleKind
  /-- A short description of the rewrite that generated the hole (e.g., the function name). -/
  label : String
deriving Inhabited

/-- Environment used when reconstructing proofs. -/
structure ReconEnv where
  /-- Flag set to `true` only when proof terms are to be tracked during optimization. -/
  tracking : Bool := false

  /-- Rewrites recorded by rewriting rules together with their justification, i.e.,
      `(lhs, rhs, p)` with `p : lhs = rhs`. The log is cleared before each rule application
      and consumed right after (see `ruleStep`).
  -/
  stepLog : Array (Expr × Expr × EqPf) := #[]

  /-- Proof cache. An entry `a := (b, pf)` is added each time `a` is optimized to `b`.
      Entries are validated at lookup time (i.e., the optimized expression must match and the
      free variables in `pf` must be in the current local context).
  -/
  proofCache : Std.HashMap Expr (Expr × EqPf) := {}

  /-- Proof obligations generated so far. -/
  holes : Array HoleInfo := #[]

  /-- Number of rewrite steps justified by an explicit proof term. -/
  nbExplicit : Nat := 0

  /-- Number of rewrite steps justified by definitional equality. -/
  nbDefEq : Nat := 0

instance : Inhabited ReconEnv := ⟨{}⟩

/-- Information required to reconstruct a proof for a `Valid` result. -/
structure ReconTask where
  /-- The proposition to be proved. -/
  goal : Expr
  /-- Local axioms added as hypotheses to `goal` before optimization (see `Translate.main`). -/
  axioms : List Name
  /-- The expression given to the optimizer, i.e., `∀ (_ : axₙ), ... ∀ (_ : ax₁), goal`. -/
  fullGoal : Expr
  /-- The optimized expression. -/
  optExpr : Expr
  /-- Evidence that `fullGoal = optExpr`. -/
  optPf : EqPf
  /-- `true` when `optExpr` has been proved valid by the backend SMT solver. -/
  bySmt : Bool
deriving Inhabited

end Blaster.Reconstruct
