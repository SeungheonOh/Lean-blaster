import Lean
import Blaster.Reconstruct.SmtProof.IR
import Blaster.Reconstruct.SmtProof.Interp
import Blaster.Reconstruct.SmtProof.Prop

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
  /-- per rule: time (ms) spent in replay attempts, including failed ones -/
  msByRule : Std.HashMap String Nat := {}
  failures : Array String := #[]
  deriving Inhabited

def ReplayStats.record (s : ReplayStats) (rule method : String) : ReplayStats :=
  let m := s.byRule.getD rule {}
  { s with byRule := s.byRule.insert rule (m.insert method (m.getD method 0 + 1)) }

def ReplayStats.addTime (s : ReplayStats) (rule : String) (ms : Nat) : ReplayStats :=
  { s with msByRule := s.msByRule.insert rule (s.msByRule.getD rule 0 + ms) }

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
  /-- time (`IO.monoMsNow`) after which the replay is abandoned -/
  deadline : Nat := 0
  /-- maximal number of direct proof attempts (see `replayCore`) -/
  maxDirect : Nat := 32
  /-- set during `prepass` (no direct proof attempts) -/
  prepass : Bool := false

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
  directAttempts : Nat := 0
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
  let e ← instantiateMVars (← liftInterp (interpProp c))
  if e.hasExprMVar then throwError "smt proof: can't infer the types of {e}"
  if ctx.depth == 0 then modify fun s => { s with conclCache := s.conclCache.insert i e }
  return e

def record (rule method : String) : ReplayM Unit :=
  modify fun s => { s with stats := s.stats.record rule method }

def orArgs? (e : Expr) : Option (Expr × Expr) := e.app2? ``Or

/-- `fun (h : t) => k h`, abstracting `h` syntactically: unlike `mkLambdaFVars`, the metavariables of the body
    are not instantiated, such that the cost does not depend on the size of the proofs they stand for
    (see `replay`). The body must not contain metavariables depending on `h`. -/
def withLam {m : Type → Type} [Monad m] [MonadControlT MetaM m] (n : Name) (t : Expr) (k : Expr → m Expr) : m Expr :=
  withLocalDeclD n t fun h => do
    let b ← k h
    return mkLambda n .default t (b.abstract #[h])

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

/-- Number of literals of the conclusion of `s` (explicit clause literals take precedence). -/
def Step.clauseSize (s : Step) : Nat :=
  match s.clause? with
  | some lits => lits.size
  | none => SmtProof.clauseSize s.concl

/-- Syntactic equality of propositions (up to instantiation of metavariables). -/
def propEq (a b : Expr) (deep := false) : MetaM Bool := do
  if a == b then return true
  if ← withReducible <| isDefEq a b then return true
  -- e.g., `Int.toNat (↑n)` and `n`
  if deep then withDefault <| isDefEq a b else return false

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
  -- empty clause: `d : False`
  if start ≥ lits.size then return mkApp2 (Lean.mkConst ``False.elim [← getLevel goal]) goal d
  if lits.size - start == 1 then return ← k start d
  let a := lits[start]!
  let b := (lits.extract (start+1) lits.size).pop.foldr mkOr lits.back!
  let left ← withLam `h a fun h => k start h
  let right ← withLam `h b fun h => orElim lits h goal k (start+1)
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

/-- Propositional replay by unit propagation (RUP): given clauses (literals and proofs of their
    disjunction), prove the disjunction of `target` literals. The negation of the target is assumed,
    and unit propagation on the clauses must derive a conflict. This justifies resolution steps
    (e.g., Alethe's `resolution`, Z3's `unit-resolution`) independently of pivot annotations. -/
partial def rupProof (clauses : Array (Array Expr × Expr)) (target : Array Expr) : MetaM Expr := do
  let goal := if target.isEmpty then Lean.mkConst ``False else target.pop.foldr mkOr target.back!
  let r ← withLam `hn (mkNot goal) fun hn => do
    -- refuted propositions ↦ proof of their negation (refutations are computed once, when facts are added)
    let mut falses : Std.HashMap Expr Expr := {}
    let mut trues : Std.HashSet Expr := {}
    for k in [:target.size] do
      let l := target[k]!
      let nl ← withLam `h l fun h => return mkApp hn (← mkOrInj target k h)
      falses := falses.insert l nl
    let mut used := Array.replicate clauses.size false
    let mut changed := true
    let mut conflict : Option Expr := none
    while changed && conflict.isNone do
      changed := false
      for ci in [:clauses.size] do
        if used[ci]! then continue
        let (lits, pc) := clauses[ci]!
        let mut unknown : Option Nat := none
        let mut nbUnknown := 0
        for i in [:lits.size] do
          if !falses.contains lits[i]! then
            nbUnknown := nbUnknown + 1
            unknown := some i
            if nbUnknown > 1 then break
        if nbUnknown == 0 then
          -- conflict: all literals are refuted
          conflict := some (← orElim lits pc (Lean.mkConst ``False) fun i h => return mkApp falses[lits[i]!]! h)
          break
        if nbUnknown == 1 then
          let some k := unknown | continue
          let l := lits[k]!
          used := used.set! ci true
          if trues.contains l then continue
          let p ← orElim lits pc l fun i h => do
            if i == k then return h
            return mkApp2 (Lean.mkConst ``False.elim [levelZero]) l (mkApp falses[lits[i]!]! h)
          trues := trues.insert l
          -- `l` refutes `¬ l`, and `l = ¬ a` refutes `a`
          let nl := mkNot l
          if !falses.contains nl then
            falses := falses.insert nl (← withLam `h nl fun h => return mkApp h p)
          if let some a := l.not? then
            if !falses.contains a then falses := falses.insert a p
          changed := true
    let some pf := conflict | throwError "smt proof: unit propagation did not derive a conflict"
    return pf
  return mkApp2 (Lean.mkConst ``Classical.byContradiction) goal r

/-- Run `x` in a new scope (hypotheses or bound variables): the proofs (and failures) of the
    current scope are saved and restored, also when `x` fails. -/
def withScope (x : ReplayM α) : ReplayM α := do
  let saved := ((← get).scopeCache, (← get).scopeFailed)
  modify fun s => { s with scopeCache := {}, scopeFailed := {} }
  try x finally modify fun s => { s with scopeCache := saved.1, scopeFailed := saved.2 }

mutual

/-- Proof of the interpretation of the conclusion of step `i`. -/
partial def replay (i : Nat) : ReplayM Expr := do
  let ctx ← read
  if let some p := (← get).cache.get? i then return p
  if ctx.depth == 0 && (← get).failed.contains i then throwError "smt proof: step {i} already failed"
  if ctx.depth > 0 then
    if let some p := (← get).scopeCache.get? i then return p
    if (← get).scopeFailed.contains i then throwError "smt proof: step {i} already failed"
  let p ← try replayCore i
    catch ex =>
      if ctx.depth == 0 then modify fun s => { s with failed := s.failed.insert i }
      else modify fun s => { s with scopeFailed := s.scopeFailed.insert i }
      -- NOTE: premises are replayed before their consumers, i.e., the first failures are the deepest ones
      let step := ctx.proof.steps[i]!
      let msg := s!"step {i} ({step.rule}): {toString step.concl |>.take 300}: {(← ex.toMessageData.toString).take 300}"
      modify fun s => { s with stats := { s.stats with failures := s.stats.failures.push msg } }
      throw ex
  if ctx.depth == 0 then
    -- the proof is represented by an assigned metavariable, such that the proofs using it stay small
    -- (they are instantiated once, at the end of the replay)
    let p ← if p.isFVar || p.isMVar then pure p else do
      let m ← mkFreshExprMVar (← stepConcl i)
      m.mvarId!.assign p
      pure m
    modify fun s => { s with cache := s.cache.insert i p }
    return p
  else modify fun s => { s with scopeCache := s.scopeCache.insert i p }
  return p

partial def replayCore (i : Nat) : ReplayM Expr := do
  let ctx ← read
  let step := ctx.proof.steps[i]!
  -- premises are replayed first, such that the time of the step only accounts for the step itself
  -- NOTE: premises of `lemma` (resp. `proof-bind`) are replayed under hypotheses (resp. bound variables)
  if !(["lemma", "proof-bind", "subproof", "bind", "sko_ex", "sko_forall"].contains step.rule) then
    for j in step.premises do
      try discard <| replay j catch _ => pure ()
  if (← IO.monoMsNow) > ctx.deadline then throwError "smt proof: replay deadline exceeded"
  let start ← IO.monoMsNow
  try replayCore' i step
  finally
    let ms := (← IO.monoMsNow) - start
    modify fun s => { s with stats := s.stats.addTime step.rule ms }

partial def replayCore' (i : Nat) (step : Step) : ReplayM Expr := do
  let ctx ← read
  let concl ← stepConcl i
  let attempt : ReplayM (Option Expr) := do
    try some <$> replayRule step concl
    catch ex =>
      if (← IO.getEnv "BLASTER_SMTPROOF_DEBUG").isSome then
        logInfo m!"step {i} ({step.rule}) failed: {ex.toMessageData}"
      return none
  if let some p ← attempt then return p
  -- fallback: unit propagation (e.g., for clauses whose literals are disjunctions)
  if ["unit-resolution", "resolution", "th_resolution"].contains step.rule then
    try return ← replayRup step concl
    catch _ => pure ()
  -- fallback: tactics on `premises → conclusion` (e.g., when an explicit construction fails due to casts)
  if !(["asserted", "goal", "hypothesis", "lemma", "proof-bind"].contains step.rule) then
    try return ← replayByTactic step concl
    catch _ => pure ()
  -- fallback: direct proof of the conclusion (except for `False`, which amounts to proving the goal
  -- without the proof of the backend)
  if concl.isConstOf ``False then
    throwError "smt proof: could not replay step {i} ({step.rule}) concluding false"
  -- NOTE: direct proofs are costly; they are attempted a bounded number of times
  if !ctx.prepass && (← get).directAttempts < ctx.maxDirect then
    modify fun s => { s with directAttempts := s.directAttempts + 1 }
    if let some p ← ctx.cfg.proveDirect concl then
      record step.rule "direct"
      return p
  throwError "smt proof: could not replay step {i} ({step.rule})"

/-- Premise proofs with their propositions. -/
partial def premises (step : Step) : ReplayM (Array (Expr × Expr)) :=
  step.premises.mapM fun j => do return (← stepConcl j, ← replay j)

partial def replayRule (step : Step) (concl : Expr) : ReplayM Expr := do
  let ctx ← read
  match step.rule with
  | "asserted" | "goal" | "assume" =>
      let some p ← ctx.cfg.proveDirect concl | throwError "asserted formula not proved"
      record step.rule "bridge"
      return p
  | "hypothesis" =>
      for (t, p) in ctx.facts do
        if ← propEq t concl then record step.rule "exact"; return p
      throwError "hypothesis not found"
  | "lemma" | "subproof" => replayLemma step concl
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
      if ← propEq r concl (deep := true) then record step.rule "exact"; return p
      throwError "mp: conclusion mismatch"
  | "refl" | "intro-def" =>
      if let some (_, a, b) := concl.eq? then
        if !(← propEq a b (deep := true)) then throwError "refl: sides differ"
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
      let #[(tp, p), (tq, q)] := ps | throwError "trans: two premises expected"
      let some (_, _, m₁) := tp.eq? | throwError "trans: equality expected"
      let some (_, m₂, _) := tq.eq? | throwError "trans: equality expected"
      if !(← propEq m₁ m₂) then throwError "trans: middle terms differ"
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
  | "resolution" | "th_resolution" | "reordering" | "contraction" => replayRup step concl
  | "unit-resolution" =>
      let ps ← premises step
      let some (c, pc) := ps[0]? | throwError "unit-resolution: premises expected"
      let units := ps.extract 1 ps.size
      -- the clause premise is `(or l₁ ... lₙ)`
      let n := ctx.proof.steps[step.premises[0]!]!.clauseSize
      let lits := disjuncts c n
      -- NOTE: the conclusion may be a single literal of the clause which is a disjunction
      let single ← lits.anyM fun l => propEq l concl
      let targetLits :=
        if step.clauseSize == 0 then #[]
        else if single then #[concl]
        else disjuncts concl step.clauseSize
      let r ← weakenClause lits pc (refuteBy units) targetLits
      record step.rule "exact"
      return r
  | "quant-inst" | "forall_inst" =>
      -- `(or (not (forall xs. P)) P[ts])`
      let some (nq, inst) := orArgs? concl | throwError "quant-inst: disjunction expected"
      let some q := nq.not? | throwError "quant-inst: negated quantifier expected"
      let ts ← liftInterp (step.args.mapM interpInt?)
      let r ← withLocalDeclD `h q fun h => do
        let hi ← instantiateWithCoercion h ts
        if !(← propEq (← inferType hi) inst (deep := true)) then throwError "quant-inst: instance mismatch"
        mkLambdaFVars #[h] (mkApp3 (Lean.mkConst ``Or.inr) nq inst hi)
      let rn ← withLocalDeclD `h nq fun h => mkLambdaFVars #[h] (mkApp3 (Lean.mkConst ``Or.inl) nq inst h)
      record step.rule "exact"
      return mkApp6 (Lean.mkConst ``Or.elim) q nq concl (mkApp (Lean.mkConst ``Classical.em) q) r rn
  | "proof-bind" => replayBind step
  | "monotonicity" | "cong" => replayCongr step concl
  | "commutativity" => replayComm concl
  | "sk" =>
      -- `(¬ ∀ x, φ) → ¬ φ[ε]` or `(∃ x, φ) → φ[ε]` (see the interpretation of skolem constants)
      let some (a, b) := (if concl.isArrow then some (concl.bindingDomain!, concl.bindingBody!) else none)
        | throwError "sk: implication expected"
      let r ← withLocalDeclD `h a fun h => do
        let ex ← if let some q := a.not? then
            -- `¬ ∀ x, φ x` gives `∃ x, ¬ φ x`
            let .forallE n t body bi := q | throwError "sk: negated forall expected"
            let p := mkLambda n bi t body
            let iff := mkApp2 (Lean.mkConst ``Classical.not_forall [← getLevel t]) t p
            mkAppM ``Iff.mp #[iff, h]
          else pure h
        let spec ← mkAppM ``Classical.epsilon_spec #[ex]
        if !(← propEq (← inferType spec) b) then throwError "sk: skolem mismatch"
        mkLambdaFVars #[h] spec
      record step.rule "exact"
      return r
  | _ => replayByTactic step concl

/-- `lemma`: the premise derives `false` under hypotheses; the conclusion is the disjunction of the
    negations of the hypotheses. -/
partial def replayLemma (step : Step) (concl : Expr) : ReplayM Expr := do
  let ctx ← read
  let some j := step.premises[0]? | throwError "lemma: premise expected"
  let n := step.clauseSize
  let lits := disjuncts concl n
  let r ← withLam `hn (mkNot concl) fun hn => do
    -- facts derived from `¬ (l₁ ∨ ... ∨ lₙ)`: `¬ lᵢ`, and `a` when `lᵢ = ¬ a`
    let mut facts := ctx.facts.push (mkNot concl, hn)
    for k in [:lits.size] do
      let l := lits[k]!
      let nl ← withLam `h l fun h => return mkApp hn (← mkOrInj lits k h)
      facts := facts.push (mkNot l, nl)
      if let some a := l.not? then
        facts := facts.push (a, mkApp2 (Lean.mkConst ``Classical.byContradiction) a nl)
    let pf ← withScope (withReader (fun c => { c with facts, depth := c.depth + 1 }) do
      let pj ← replay j
      -- the premise derives `false` (Z3's `lemma`) or a literal of the conclusion (Alethe's `subproof`)
      let cj ← stepConcl j
      if cj.isConstOf ``False then return pj
      for (t, p) in facts do
        if let some a := t.not? then
          if ← propEq a cj then return mkApp p pj
      throwError "lemma: the premise is not refuted by the hypotheses")
    return pf
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
      let pf ← withScope (withReader (fun c => { c with depth := c.depth + 1 }) (replay j))
      mkLambdaFVars fvars pf
  let r ← go 0 #[]
  record step.rule "exact"
  return r

/-- Congruence (`monotonicity`): from premises `aᵢ = bᵢ`, prove `L = R` by abstracting the
    occurrences of each `aᵢ` in `L` and applying `congrArg` (premises not occurring are ignored). -/
partial def replayCongr (step : Step) (concl : Expr) : ReplayM Expr := do
  let some (ty, l, r) := concl.eq? | throwError "monotonicity: equality expected"
  let ps ← premises step
  let mut cur := l
  let mut pf ← mkEqRefl l
  for (t, p) in ps do
    let some (_, a, b) := t.eq? | throwError "monotonicity: equality premise expected"
    let abst ← kabstract cur a
    if !abst.hasLooseBVars then continue
    let motive := mkLambda `x .default (← inferType a) abst
    let next := abst.instantiate1 b
    let u ← getLevel ty
    let v ← getLevel (← inferType a)
    let c := mkApp6 (Lean.mkConst ``congrArg [v, u]) (← inferType a) ty a b motive p
    pf := mkApp6 (Lean.mkConst ``Eq.trans [u]) ty l cur next pf c
    cur := next
  if !(← propEq cur r) then throwError "monotonicity: congruence mismatch"
  record step.rule "exact"
  return pf

/-- `commutativity`: `f a b = f b a` for commutative operations (equality, `∧`, `∨`, `+`, `*` on `Int`). -/
partial def replayComm (concl : Expr) : ReplayM Expr := do
  let some (_, l, r) := concl.eq? | throwError "commutativity: equality expected"
  let swapped (op : Name) (n : Nat) : Option (Expr × Expr) :=
    if l.isAppOfArity op n && r.isAppOfArity op n then
      let la := l.getAppArgs; let ra := r.getAppArgs
      if la[n-2]! == ra[n-1]! && la[n-1]! == ra[n-2]! then some (la[n-2]!, la[n-1]!) else none
    else none
  let pf ← do
    if let some (a, b) := swapped ``Or 2 then mkAppM ``propext #[← mkAppOptM ``or_comm #[a, b]]
    else if let some (a, b) := swapped ``And 2 then mkAppM ``propext #[← mkAppOptM ``and_comm #[a, b]]
    else if let some (a, b) := swapped ``Eq 3 then mkAppM ``propext #[← mkAppOptM ``eq_comm #[none, a, b]]
    else if let some (a, b) := swapped ``HAdd.hAdd 6 then mkAppM ``Int.add_comm #[a, b]
    else if let some (a, b) := swapped ``HMul.hMul 6 then mkAppM ``Int.mul_comm #[a, b]
    else throwError "commutativity: unsupported operation"
  if !(← propEq (← inferType pf) concl) then throwError "commutativity: mismatch"
  record "commutativity" "exact"
  return pf

/-- Resolution steps: unit propagation on the premise clauses (see `rupProof`). -/
partial def replayRup (step : Step) (concl : Expr) : ReplayM Expr := do
  let ctx ← read
  let t0 ← IO.monoMsNow
  let mut clauses := #[]
  for j in step.premises do
    let c ← stepConcl j
    let n := ctx.proof.steps[j]!.clauseSize
    let lits := if n == 0 then #[] else disjuncts c n
    clauses := clauses.push (lits, ← replay j)
    -- NOTE: a clause whose single literal is a disjunction is also given as is
    if n > 1 then clauses := clauses.push (#[c], ← replay j)
  let t1 ← IO.monoMsNow
  modify fun s => { s with stats := s.stats.addTime "rup-premises" (t1 - t0) }
  let n := step.clauseSize
  let target := if n == 0 then #[] else disjuncts concl n
  let t0 ← IO.monoMsNow
  let r ← rupProof clauses target
  let t1 ← IO.monoMsNow
  modify fun s => { s with stats := s.stats.addTime "rup-core" (t1 - t0) }
  record step.rule "exact"
  return r

/-- Prove `p₁ → ... → pₙ → c` with tactics and apply it to the premise proofs. -/
partial def replayByTactic (step : Step) (concl : Expr) : ReplayM Expr := do
  -- identical sides (e.g., rewrites of Z3 normalizing the n-ary connectives folded by the interpretation)
  if let some (_, a, b) := concl.eq? then
    if a == b then
      record step.rule "refl"
      return ← mkEqRefl a
  let ps ← premises step
  -- propositional steps (e.g., `def-axiom`, `not-or-elim`, propositional rewrites): exact proof
  if let some p ← PropEngine.prove ps concl then
    record step.rule "prop"
    return p
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

/-- Steps that can only be replayed in a scope: steps depending on hypotheses (discharged by `lemma` or
    `subproof`), and steps below binders (premises of `proof-bind`, `bind`, `sko_ex`, `sko_forall`). -/
def scopedSteps (p : Proof) : Array Bool := Id.run do
  let n := p.steps.size
  let mut inScope := Array.replicate n false
  -- NOTE: `lemma`/`subproof` steps (and the steps using them) are also excluded, as they may be nested
  -- in the scope of another one
  for i in [:n] do
    let s := p.steps[i]!
    if ["hypothesis", "lemma", "subproof"].contains s.rule then inScope := inScope.set! i true
    else if s.premises.any (fun j => inScope[j]!) then inScope := inScope.set! i true
  -- subtrees below binders
  let mut todo : Array Nat := #[]
  for i in [:n] do
    let s := p.steps[i]!
    if ["proof-bind", "bind", "sko_ex", "sko_forall"].contains s.rule then todo := todo ++ s.premises
  while !todo.isEmpty do
    let j := todo.back!
    todo := todo.pop
    if inScope[j]! && p.steps[j]!.rule != "proof-bind" then continue
    inScope := inScope.set! j true
    todo := todo ++ p.steps[j]!.premises
  return inScope

/-- Replay the reachable steps that don't need a scope in increasing order (premises precede the steps
    using them), such that the recursion depth of `replay` stays bounded on deep proofs. Failures are
    recorded (and reported when replaying the root). -/
def prepass : ReplayM Unit := do
  let p := (← read).proof
  let reach := p.reachable
  let inScope := scopedSteps p
  withReader (fun c => { c with prepass := true }) do
    for i in [:p.root] do
      if reach[i]! && !inScope[i]! then
        try discard <| replay i catch _ => pure ()
  -- failures of the prepass are retried by the replay from the root (with direct fallbacks)
  modify fun s => { s with failed := {} }

end Blaster.Reconstruct.SmtProof
