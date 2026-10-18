import Lean
import Blaster.Reconstruct.SmtProof.IR
import Blaster.Reconstruct.SmtProof.Interp

/-!
# Replay of SMT proofs

Each step of a proof (see `IR.lean`) is replayed as a Lean proof of the interpretation of its
conclusion (see `Interp.lean`), given the proofs of its premises:
 - structural rules (resolution, modus ponens, equality reasoning, quantifier instantiation,
   hypotheses and lemmas) are replayed with explicit proof terms;
 - theory and rewriting rules are replayed by proving the implication `premises → conclusion` with
   a portfolio of tactics. Since steps are small, tactics usually succeed quickly;
 - leaves (asserted formulas) and steps that can't be replayed otherwise are proved directly with
   the bridge tactics provided by the caller (e.g., from the negated goal).
-/

open Lean Meta Elab Term Tactic

namespace Blaster.Reconstruct.SmtProof

/-- Statistics on replayed steps. -/
structure ReplayStats where
  /-- per rule: number of steps replayed by each method -/
  byRule : Std.HashMap String (Std.HashMap String Nat) := {}
  failures : Array String := #[]
  deriving Inhabited

def ReplayStats.record (s : ReplayStats) (rule method : String) : ReplayStats :=
  let m := s.byRule.getD rule {}
  { s with byRule := s.byRule.insert rule (m.insert method (m.getD method 0 + 1)) }

structure ReplayConfig where
  /-- tactic proving a closed formula directly (used for asserted formulas and as fallback);
      returns `none` when the formula can't be proved. -/
  proveDirect : Expr → TermElabM (Option Expr)
  /-- tactic proving `p₁ → ... → pₙ → c` for a step of the given rule -/
  proveStep : String → Expr → TermElabM (Option (Expr × String))

structure ReplayCtx where
  proof : Proof
  interp : InterpCtx
  cfg : ReplayConfig
  /-- facts available in the current scope (e.g., hypotheses of a `lemma`): proposition and proof -/
  facts : Array (Expr × Expr) := #[]
  /-- nesting depth of scopes (hypotheses, bound variables) -/
  depth : Nat := 0

structure ReplayState where
  /-- proofs of steps replayed at depth 0 -/
  cache : Std.HashMap Nat Expr := {}
  /-- proofs of steps replayed in the current scope -/
  scopeCache : Std.HashMap Nat Expr := {}
  /-- interpretation of the conclusions of steps at depth 0 -/
  conclCache : Std.HashMap Nat Expr := {}
  /-- steps that could not be replayed at depth 0 -/
  failed : Std.HashSet Nat := {}
  /-- steps that could not be replayed in the current scope -/
  scopeFailed : Std.HashSet Nat := {}
  stats : ReplayStats := {}

abbrev ReplayM := ReaderT ReplayCtx (StateRefT ReplayState TermElabM)

def liftInterp (x : InterpM α) : ReplayM α := do
  let ctx ← read
  x.run ctx.interp

/-- Interpretation of the conclusion of step `i`. -/
def stepConcl (i : Nat) : ReplayM Expr := do
  let ctx ← read
  if ctx.depth == 0 then
    if let some e := (← get).conclCache.get? i then return e
  let step := ctx.proof.steps[i]!
  -- NOTE: the conclusion of `proof-bind` is a lambda over the conclusion of its premise, i.e.,
  -- the premise holds for all values of the bound variables
  let c := match step.rule, step.concl with
    | "proof-bind", .quant .lambda vars body => .quant .forall vars body
    | _, c => c
  let e ← liftInterp (interp c)
  if ctx.depth == 0 then modify fun s => { s with conclCache := s.conclCache.insert i e }
  return e

def record (rule method : String) : ReplayM Unit :=
  modify fun s => { s with stats := s.stats.record rule method }

def orArgs? (e : Expr) : Option (Expr × Expr) := e.app2? ``Or

/-- Decompose a right-nested disjunction `l₁ ∨ (l₂ ∨ ... ∨ lₙ)` into its literals, given the
    expected number of literals `n`. -/
def disjuncts (e : Expr) (n : Nat) : Array Expr := Id.run do
  let mut r := #[]
  let mut cur := e
  for _ in [0:n-1] do
    match orArgs? cur with
    | some (a, b) => r := r.push a; cur := b
    | none => break
  r.push cur

/-- Number of literals of a clause conclusion `(or l₁ ... lₙ)` (`false` has none). -/
def clauseSize (t : STerm) : Nat :=
  match t.stripAnnot with
  | .app "or" args => args.size
  | .sym "false" => 0
  | _ => 1

def clauseLits (t : STerm) : Array STerm :=
  match t.stripAnnot with
  | .app "or" args => args
  | .sym "false" => #[]
  | t => #[t]

/-- Syntactic equality of propositions (up to instantiation of metavariables). -/
def propEq (a b : Expr) : MetaM Bool := do
  if a == b then return true
  if ← withReducible <| isDefEq a b then return true
  -- e.g., `Int.toNat (↑n)` and `n`
  withDefault <| isDefEq a b

/-- Proof of the `i`-th injection into the right-nested disjunction `lits` (of size `n`). -/
def mkOrInj (lits : Array Expr) (i : Nat) (p : Expr) : MetaM Expr := do
  -- lits = [l₀, ..., lₙ₋₁], disjunction l₀ ∨ (l₁ ∨ ... ∨ lₙ₋₁)
  let n := lits.size
  if n == 1 then return p
  let rest (j : Nat) : Expr := Id.run do
    let mut r := lits[n-1]!
    for k in (List.range (n - 1 - j)).reverse do
      r := mkOr lits[j + k]! r
    r
  -- proof for position i: Or.inr^i (Or.inl p) (or just Or.inr^i p for the last one)
  let mut proof := if i == n - 1 then p else mkApp3 (Lean.mkConst ``Or.inl) lits[i]! (rest (i+1)) p
  let mut j := i
  while j > 0 do
    j := j - 1
    proof := mkApp3 (Lean.mkConst ``Or.inr) lits[j]! (rest (j+1)) proof
  return proof

/-- Case analysis on a proof `d` of the disjunction of `lits`: `k i hᵢ` builds a proof of `goal`
    from a proof `hᵢ` of the `i`-th literal. -/
partial def orElim (lits : Array Expr) (d : Expr) (goal : Expr) (k : Nat → Expr → MetaM Expr) (start := 0) : MetaM Expr := do
  if lits.size - start == 1 then return ← k start d
  let a := lits[start]!
  let b := (lits.extract (start+1) lits.size).pop.foldr mkOr lits.back!
  let left ← withLocalDeclD `h a fun h => do mkLambdaFVars #[h] (← k start h)
  let right ← withLocalDeclD `h b fun h => do mkLambdaFVars #[h] (← orElim lits h goal k (start+1))
  return mkApp6 (Lean.mkConst ``Or.elim) a b goal d left right

/-- Given a proof `d` of a clause with literals `lits`, refutations of some literals and the target
    clause `target`, build a proof of `target` (each literal is either refuted or occurs in `target`). -/
def weakenClause (lits : Array Expr) (d : Expr) (refute : Expr → MetaM (Option Expr)) (targetLits : Array Expr) : MetaM Expr := do
  let target := if targetLits.isEmpty then Lean.mkConst ``False else targetLits.pop.foldr mkOr targetLits.back!
  orElim lits d target fun i h => do
    let l := lits[i]!
    if let some r ← refute l then
      return mkApp2 (Lean.mkConst ``False.elim [levelZero]) target (mkApp r h)
    for j in [:targetLits.size] do
      if ← propEq targetLits[j]! l then return ← mkOrInj targetLits j h
    throwError "smt proof: literal {l} is neither refuted nor in the conclusion"

/-- Refutation of `l` by one of the unit proofs: `u : ¬ l` or `u : a` with `l = ¬ a`. -/
def refuteBy (units : Array (Expr × Expr)) (l : Expr) : MetaM (Option Expr) := do
  for (t, u) in units do
    if let some a := t.not? then
      if ← propEq a l then return some u
    if let some a := l.not? then
      if ← propEq a t then return some (← withLocalDeclD `h l fun h => mkLambdaFVars #[h] (mkApp h u))
  return none

mutual

/-- Proof of the interpretation of the conclusion of step `i`. -/
partial def replay (i : Nat) : ReplayM Expr := do
  let ctx ← read
  if let some p := (← get).cache.get? i then return p
  if (← get).failed.contains i then throwError "smt proof: step {i} already failed"
  if ctx.depth > 0 then
    if let some p := (← get).scopeCache.get? i then return p
    if (← get).scopeFailed.contains i then throwError "smt proof: step {i} already failed"
  let p ← try replayCore i
    catch ex =>
      if ctx.depth == 0 then modify fun s => { s with failed := s.failed.insert i }
      else modify fun s => { s with scopeFailed := s.scopeFailed.insert i }
      throw ex
  if ctx.depth == 0 then modify fun s => { s with cache := s.cache.insert i p }
  else modify fun s => { s with scopeCache := s.scopeCache.insert i p }
  return p

partial def replayCore (i : Nat) : ReplayM Expr := do
  let ctx ← read
  let step := ctx.proof.steps[i]!
  let concl ← stepConcl i
  let attempt : ReplayM (Option Expr) := do
    try some <$> replayRule i step concl
    catch ex =>
      if (← IO.getEnv "BLASTER_SMTPROOF_DEBUG").isSome then
        logInfo m!"step {i} ({step.rule}) failed: {ex.toMessageData}"
      return none
  if let some p ← attempt then return p
  -- fallback: tactics on `premises → conclusion` (e.g., when an explicit construction fails due to casts)
  if !(["asserted", "goal", "hypothesis", "lemma", "proof-bind"].contains step.rule) then
    try return ← replayByTactic step concl
    catch _ => pure ()
  -- fallback: direct proof of the conclusion
  if let some p ← ctx.cfg.proveDirect concl then
    record step.rule "direct"
    return p
  let msg := s!"step {i} ({step.rule}): {step.concl}"
  modify fun s => { s with stats := { s.stats with failures := s.stats.failures.push msg } }
  throwError "smt proof: could not replay {msg}"

/-- Premise proofs with their propositions. -/
partial def premises (step : Step) : ReplayM (Array (Expr × Expr)) :=
  step.premises.mapM fun j => do return (← stepConcl j, ← replay j)

partial def replayRule (i : Nat) (step : Step) (concl : Expr) : ReplayM Expr := do
  let ctx ← read
  match step.rule with
  | "asserted" | "goal" =>
      let some p ← ctx.cfg.proveDirect concl | throwError "asserted formula not proved"
      record step.rule "bridge"
      return p
  | "hypothesis" =>
      for (t, p) in ctx.facts do
        if ← propEq t concl then record step.rule "exact"; return p
      throwError "hypothesis not found"
  | "lemma" => replayLemma step concl
  | "true-axiom" => record step.rule "exact"; return Lean.mkConst ``True.intro
  | "mp" | "mp~" =>
      let ps ← premises step
      let #[(a, pa), (eq, peq)] := ps | throwError "mp: two premises expected"
      let r ← do
        if let some (_, l, r) := eq.eq? then
          if ← propEq l a then pure (some (← mkEqMP peq pa, r)) else pure none
        else if let some (l, r) := eq.iff? then
          if ← propEq l a then pure (some (mkApp3 (Lean.mkConst ``Iff.mp) l r peq |>.app pa, r)) else pure none
        else if eq.isArrow then
          pure (some (mkApp peq pa, eq.bindingBody!))
        else pure none
      let some (p, r) := r | throwError "mp: unexpected premises"
      if ← propEq r concl then record step.rule "exact"; return p
      throwError "mp: conclusion mismatch"
  | "refl" =>
      if let some (_, a, _) := concl.eq? then
        record step.rule "exact"; return ← mkEqRefl a
      if concl.isArrow then
        record step.rule "exact"
        return ← withLocalDeclD `h concl.bindingDomain! fun h => mkLambdaFVars #[h] h
      throwError "refl: unexpected conclusion"
  | "symm" =>
      let ps ← premises step
      let #[(_, p)] := ps | throwError "symm: one premise expected"
      let r ← mkEqSymm p
      if ← propEq (← inferType r) concl then record step.rule "exact"; return r
      throwError "symm: conclusion mismatch"
  | "trans" =>
      let ps ← premises step
      let #[(_, p), (_, q)] := ps | throwError "trans: two premises expected"
      let r ← mkEqTrans p q
      if ← propEq (← inferType r) concl then record step.rule "exact"; return r
      throwError "trans: conclusion mismatch"
  | "iff-true" =>
      let ps ← premises step
      let #[(_, p)] := ps | throwError "iff-true: one premise expected"
      let r ← mkAppM ``eq_true #[p]
      if ← propEq (← inferType r) concl then record step.rule "exact"; return r
      throwError "iff-true: conclusion mismatch"
  | "iff-false" =>
      let ps ← premises step
      let #[(_, p)] := ps | throwError "iff-false: one premise expected"
      let r ← mkAppM ``eq_false #[p]
      if ← propEq (← inferType r) concl then record step.rule "exact"; return r
      throwError "iff-false: conclusion mismatch"
  | "unit-resolution" =>
      let ps ← premises step
      let some (c, pc) := ps[0]? | throwError "unit-resolution: premises expected"
      let units := ps.extract 1 ps.size
      -- the clause premise is `(or l₁ ... lₙ)`
      let n := clauseSize ctx.proof.steps[step.premises[0]!]!.concl
      let lits := disjuncts c n
      -- NOTE: the conclusion may be a single literal of the clause which is a disjunction
      let single ← lits.anyM fun l => propEq l concl
      let targetLits :=
        if clauseSize step.concl == 0 then #[]
        else if single then #[concl]
        else disjuncts concl (clauseSize step.concl)
      let r ← weakenClause lits pc (refuteBy units) targetLits
      record step.rule "exact"
      return r
  | "quant-inst" =>
      -- `(or (not (forall xs. P)) P[ts])`
      let some (nq, inst) := orArgs? concl | throwError "quant-inst: disjunction expected"
      let some q := nq.not? | throwError "quant-inst: negated quantifier expected"
      let ts ← liftInterp (step.args.mapM interpInt?)
      let r ← withLocalDeclD `h q fun h => do
        let hi ← instantiateWithCoercion h ts
        if !(← propEq (← inferType hi) inst) then throwError "quant-inst: instance mismatch"
        mkLambdaFVars #[h] (mkApp3 (Lean.mkConst ``Or.inr) nq inst hi)
      let rn ← withLocalDeclD `h nq fun h => mkLambdaFVars #[h] (mkApp3 (Lean.mkConst ``Or.inl) nq inst h)
      record step.rule "exact"
      return mkApp6 (Lean.mkConst ``Or.elim) q nq concl (mkApp (Lean.mkConst ``Classical.em) q) r rn
  | "proof-bind" => replayBind step
  | _ => replayByTactic step concl

/-- `lemma`: the premise derives `false` under hypotheses; the conclusion is the disjunction of the
    negations of the hypotheses. -/
partial def replayLemma (step : Step) (concl : Expr) : ReplayM Expr := do
  let ctx ← read
  let some j := step.premises[0]? | throwError "lemma: premise expected"
  let n := clauseSize step.concl
  let lits := disjuncts concl n
  let r ← withLocalDeclD `hn (mkNot concl) fun hn => do
    -- facts derived from `¬ (l₁ ∨ ... ∨ lₙ)`: `¬ lᵢ`, and `a` when `lᵢ = ¬ a`
    let mut facts := ctx.facts
    for k in [:lits.size] do
      let l := lits[k]!
      let nl ← withLocalDeclD `h l fun h => do mkLambdaFVars #[h] (mkApp hn (← mkOrInj lits k h))
      facts := facts.push (mkNot l, nl)
      if let some a := l.not? then
        facts := facts.push (a, mkApp2 (Lean.mkConst ``Classical.byContradiction) a nl)
    let saved := ((← get).scopeCache, (← get).scopeFailed)
    modify fun s => { s with scopeCache := {}, scopeFailed := {} }
    let pf ← withReader (fun c => { c with facts, depth := c.depth + 1 }) (replay j)
    modify fun s => { s with scopeCache := saved.1, scopeFailed := saved.2 }
    mkLambdaFVars #[hn] pf
  record step.rule "exact"
  return mkApp2 (Lean.mkConst ``Classical.byContradiction) concl r

/-- `proof-bind`: proof of the body of a quantifier rewrite, under bound variables. The conclusion is
    interpreted as a universally quantified formula. -/
partial def replayBind (step : Step) : ReplayM Expr := do
  let .quant _ vars _ := step.concl | throwError "proof-bind: lambda expected"
  let some j := step.premises[0]? | throwError "proof-bind: premise expected"
  let types ← liftInterp (vars.mapM fun (_, s) => sortToType s)
  let rec go (k : Nat) (fvars : Array Expr) : ReplayM Expr := do
    if h : k < vars.size then
      withLocalDeclD (Name.mkSimple vars[k].1) types[k]! fun x =>
        withReader (fun c => { c with interp := { c.interp with locals := c.interp.locals.insert vars[k].1 x } })
          (go (k + 1) (fvars.push x))
    else
      let saved := ((← get).scopeCache, (← get).scopeFailed)
      modify fun s => { s with scopeCache := {}, scopeFailed := {} }
      let pf ← withReader (fun c => { c with depth := c.depth + 1 }) (replay j)
      modify fun s => { s with scopeCache := saved.1, scopeFailed := saved.2 }
      mkLambdaFVars fvars pf
  let r ← go 0 #[]
  record step.rule "exact"
  return r

/-- Prove `p₁ → ... → pₙ → c` with tactics and apply it to the premise proofs. -/
partial def replayByTactic (step : Step) (concl : Expr) : ReplayM Expr := do
  let ps ← premises step
  -- NOTE: premises with a bound-variable body (`proof-bind`) are universally quantified propositions
  let stmt := ps.foldr (fun (t, _) acc => mkForall `h .default t acc) concl
  let some (pf, method) ← (← read).cfg.proveStep step.rule stmt | throwError "tactics failed"
  record step.rule method
  return mkAppN pf (ps.map (·.2))

/-- Instantiate the universally quantified proof `h` with `ts`, coercing arguments when necessary. -/
partial def instantiateWithCoercion (h : Expr) (ts : Array Expr) : MetaM Expr := do
  let mut p := h
  for t in ts do
    let ty ← whnf (← inferType p)
    let .forallE _ d _ _ := ty | throwError "quant-inst: too many instantiations"
    p := mkApp p (← coerce t (← inferType t) d)
  return p

end

end Blaster.Reconstruct.SmtProof
