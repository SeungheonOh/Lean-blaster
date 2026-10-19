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
  /-- Evidence for a lambda `fun x : t => b` rewritten to `fun x : t' => b'` such that the binder
      type has changed (i.e., `t` and `t'` are not definitionally equal) and neither `b` nor `b'`
      depend on `x`. `p : ∀ x : t', b = b'`.
      This evidence can only be consumed by a congruence lemma over the enclosing application
      (e.g., `Blaster.Reconstruct.dite'_congr`), i.e., it is considered `unknown` otherwise.
  -/
  | lamBody (p : Expr)
  /-- Evidence for an application `f a₁ ... aₙ` in which some arguments with forward dependencies
      have been rewritten, i.e.:
        - `pre : lhs = f a₁ ... aₙ`
        - `args : #[(i, aᵢ, pfᵢ)]` with `pfᵢ` the evidence for the rewrite of argument `aᵢ`.
      This evidence is resolved via a dedicated congruence lemma once all the arguments have
      been optimized (see `resolveDepArgs`). It is considered `unknown` otherwise.
      Each entry `(i, aᵢ, pfᵢ)` keeps the argument `aᵢ` before rewriting.
  -/
  | depArgs (pre : EqPf) (args : Array (Nat × Expr × EqPf))
  /-- Evidence for a match alternative `alt` rewritten to `alt'` under the match context of the
      alternative, i.e., `p : ∀ args (h₁ : d₁ = p₁) ... (hₙ : dₙ = pₙ), alt args = alt' args` with
      `d₁ ... dₙ` the discriminants and `p₁ ... pₙ` the patterns of the alternative.
      This evidence can only be consumed by the congruence over the enclosing match application
      (see `Blaster.Reconstruct.mkMatchCongr`), i.e., it is considered `unknown` otherwise.
  -/
  | matchAlt (p : Expr)
deriving Inhabited, Repr

/-- Consider evidence that can only be consumed by dedicated congruence lemmas as `unknown`. -/
@[always_inline, inline]
def EqPf.simplify : EqPf → EqPf
  | .lamBody _ | .depArgs .. | .matchAlt _ => .unknown
  | pf => pf

/-- Key used to tag a proof obligation (i.e., hole) in a proof term.
    A hole is represented as `mdata {blaster.hole := id} (sorryAx (lhs = rhs) true)`.
-/
def holeKey : Name := `blaster.hole

/-- Key used to tag a *fallback region* in a proof term, i.e., a proof `p : lhs = rhs` built from finer
    grained proof obligations. When one of them cannot be discharged, the whole region is replaced by
    the proof obligation `lhs = rhs` (see `Blaster.Reconstruct.dischargeHoles`).
    A region is represented as `mdata {blaster.fallback := true} p`.
-/
def fallbackKey : Name := `blaster.fallback

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

  /-- Equivalences between recursive functions established by the optimizer (see `storeRecFunDef`),
      in the order they have been established, i.e., `(f, g)` with `f` replaced by `g`.
  -/
  recFunEquivs : Array (Expr × Expr) := #[]

  /-- Number of rewrite steps justified by an explicit proof term. -/
  nbExplicit : Nat := 0

  /-- Number of rewrite steps justified by definitional equality. -/
  nbDefEq : Nat := 0

  /-- Evidence for the last expression optimized at the top level of the optimizer's stack, i.e.,
      `e = optimize(e)` (see `stackContinuity`).
  -/
  resultPf : EqPf := .unknown

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
  /-- The reconstruction environment obtained when optimizing `fullGoal` while tracking proof terms. -/
  recon : ReconEnv := {}
  /-- When to replay a proof of the SMT backend (see `BlasterOptions.smtProof`). -/
  smtProof : Option String := none
  /-- Random seed and timeout (in seconds) of the backend SMT solver (also used to produce the proofs to replay). -/
  randomSeed : Option Nat := none
  timeout : Option Nat := none
deriving Inhabited

end Blaster.Reconstruct
