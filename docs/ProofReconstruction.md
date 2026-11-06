# Proof reconstruction

## 1. Overview

Blaster decides a goal in two stages: its optimizer aggressively rewrites the Lean goal, and an SMT solver decides
whatever remains. Without reconstruction, a `Valid` verdict trusts both stages, and the `blaster` tactic closes the
goal with `admit`.

Proof reconstruction moves the trust back to the **Lean kernel**. For a `Valid` verdict, Blaster builds an ordinary
proof term for the original goal and has the kernel check it. The verdict is then reported as kernel-checked, and the
tactic closes the goal with that term instead of `admit`. Neither the optimizer nor the SMT solver is trusted.

```lean
#blaster (reconstruct: 1) [∀ (x y : Nat), x < y → x + 1 ≤ y]
-- ✅ Valid
-- 🔒 Kernel-checked proof reconstructed

theorem t : ∀ (a b : Prop), a ∧ b → a := by blaster (reconstruct: 2)
#print axioms t   -- 't' depends on axioms: [propext, Quot.sound]
```

Status on branch `feat/smt-proof-replay` (Z3 5.3.1):

- In the default mode, every reconstruction attempt of Blaster's test suite yields a kernel-checked proof:
  3959 of 3959 attempts, i.e., 420 goals closed by the optimizer, 409 goals closed by the SMT solver and 3130
  `#testOptimize` certificates.
- Replaying the SMT solver's own proofs, without any tactic for the goals the solver closed, proves 311 of the 323
  SMT goals of `Tests/Smt` and `Tests/FixedIssues`.
- The validators of [CardanoLedgerApiBlaster](https://github.com/input-output-hk/CardanoLedgerApiBlaster), whose
  goals are evaluations of UPLC programs by the CEK machine, are kernel-checked in seconds to half an hour per theorem
  (Section 6.2).
- Working on reconstruction surfaced several soundness bugs of Blaster's trusted pipeline (Section 7.1).

Sections 2 and 5 are for users; Sections 3 and 4 describe the design; Section 6 gives the measurements. Terms such as
*evidence*, *proof obligation* or *global step* are defined in the [glossary](#glossary).

## 2. Usage

### 2.1 Options

| option             | meaning                                                                                  |
|--------------------|------------------------------------------------------------------------------------------|
| `(reconstruct: 0)` | default; no reconstruction (previous behavior)                                           |
| `(reconstruct: 1)` | best effort: when reconstruction fails, a warning is reported and the verdict is trusted |
| `(reconstruct: 2)` | required: when reconstruction fails, an error is reported                                |
| `(gen-proof: 1)`   | proof generation: implies `(reconstruct: 2)` and checks the axioms of the proof (2.2)    |
| `(smt-proof: n)`   | when to replay the SMT solver's proof: 0 `off`, 1 `last`, 2 `first`, 3 `only` (4.1)      |
| `(verbose: 1)`     | also reports statistics for each reconstruction                                          |

`BLASTER_RECONSTRUCT=<n>` sets the default level for every `#blaster` command and `blaster` tactic, and
`BLASTER_SMT_PROOF` the default replay mode (`last` if unset). Options given explicitly take precedence. All
environment variables are listed in Section 5.

### 2.2 Generating proofs

`blaster_theorem` proves a statement with Blaster and adds it to the environment as an ordinary theorem whose proof
term was kernel-checked:

```lean
blaster_theorem lt_succ_le : ∀ (x y : Nat), x < y → x + 1 ≤ y
-- ✅ Valid
-- 📜 Theorem lt_succ_le generated (kernel-checked, axioms: [propext, Classical.choice, Quot.sound], ...)

#print axioms lt_succ_le   -- 'lt_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]

theorem foo : ∀ (a b : Prop), a ∧ b → a := by blaster (gen-proof: 1)
```

A generated proof never depends on `sorryAx` or `Lean.ofReduceBool` (`native_decide`). Proof generation fails if the
proof term depends on any axiom other than Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
and the local axioms of the module used as hypotheses by Blaster. `Classical.choice` comes from `Blaster.dite'`,
Blaster's classical encoding of `if-then-else`, and from Lean's decision procedures.

The generated theorems are stored in the module's `.olean` file like any other theorem, so they can be re-checked
independently of Blaster (e.g., with `lean4checker`). Blaster's own definitions (`Blaster.dite'`, `Blaster.decide'`,
the lemmas of `Blaster/Reconstruct/Lemmas.lean`) occur in the proof terms, but they are ordinary, kernel-checked
definitions and theorems.

## 3. How it works

```
 G  ──(local axioms)──▶  G'  ──optimizer──▶  G''  ──(True | SMT)──▶  Valid
                          │      pf : G' = G''      │
                          ▼                          ▼
              proof of G  ◀── Eq.mpr pf r ◀── r : G''   (kernel-checked)
```

The proof of the original goal `G` combines the optimizer's evidence `pf : G' = G''` (Sections 3.2 to 3.4) with a
proof `r` of the residual goal `G''` (Section 3.5, and Section 4 for goals closed by the SMT solver).

### 3.1 Verdict run and proof run

The verdict (`Valid`, `Falsified`, ...) always comes from Blaster's unchanged pipeline, the *verdict run*. With
reconstruction, the goal is optimized a second time while tracking proof terms, the *proof run*:

- **Concurrency.** The proof run is performed while the backend solver checks the query and, for the `blaster`
  tactic, the reconstruction itself right after it. Both are interrupted as soon as the solver answers that the goal is
  not valid (or when the elaboration is interrupted, e.g., by an edit of the file), and their results are discarded
  unless the goal is `Valid`: the verdict and its reporting (e.g., counterexamples) are unchanged. Their heartbeats
  are not counted in the heartbeat limit of the enclosing declaration.
- **Well-typed output.** The proof run differs from the verdict run where the optimizer's output is not a valid Lean
  term: universe levels are kept instead of being normalized, and some rewritten binder types are kept
  (Section 7.2). Reconstruction therefore never changes Blaster's verdicts.
- **Optimizer caches.** On the `beta-lambda-cache-optimization` lineage (hash-consing, context reuse, equality maps,
  shared beta reduction), the proof run disables context reuse, equality-map lookups and shared beta reduction, and
  hash-conses its input in a fresh environment. It keeps the match context (Section 3.2): the equalities between the
  discriminants and the patterns are removed from the scope when leaving their alternative, and cached proofs using
  them are not reused outside.

When reconstruction is off (`reconstruct: 0`), the proof run is skipped, so the optimizer's behavior and cost are
unchanged.

### 3.2 Proof-producing optimizer

The optimizer is a stack machine (`Optimize/Basic.lean`, `Optimize/OptimizeStack.lean`). Every frame that waits for
the optimized form `v` of an expression `e` also receives *evidence* (`EqPf`, `Reconstruct/Types.lean`) that `e = v`:

| evidence  | meaning                                                                                               |
|-----------|-------------------------------------------------------------------------------------------------------|
| `defeq`   | `e` and `v` are definitionally equal (beta, delta of non-recursive definitions, iota, zeta, eta, ...) |
| `proof p` | an explicit proof term `p : e = v`                                                                    |
| `unknown` | no evidence: a *proof obligation* (hole) `e = v`, created at the nearest frame boundary               |

Evidence is composed by transitivity and congruence: `congrArg`, `congrFun`, `funext`, `forall_congr`,
`implies_congr_ctx` and `implies_dep_congr_ctx`. Hypothesis-dependent rewrites inside an implication `a → b` stay
valid because the body's evidence is abstracted over the hypothesis. Arguments with forward dependencies, such as the
condition of `Blaster.dite'`, are handled by dedicated congruence lemmas (`dite'_congr`). Rewrites served from the
optimizer's cache reuse the cached evidence after a scope check. The proof run's own caches (proofs without proof
obligations, congruences of `match` applications) live in its state.

**`match` alternatives.** Alternatives are optimized under a *match context*: fvar patterns are replaced by their
discriminants, and nested matches on the same discriminants are eliminated. When tracking proof terms, the equalities
`h : dⱼ = pⱼ` between the discriminants and the patterns of the alternative are declared in the local context
(`optimizeMatchAlt`). The evidence for an alternative is then `p : ∀ args h₁ ... hₙ, alt args = alt' args`
(`EqPf.matchAlt`). Once all the alternatives are optimized, the evidence is combined:

- by a case split over the matcher's *splitter* (`Reconstruct/Match.lean`, `mkMatchCongr`). The splitter is applied
  to the motive `fun xs => (d = xs) → match xs with alts = match xs with alts'`, and each case is closed with the
  match equations (or by iota for `casesOn`). Unreachable alternatives (e.g., wildcard alternatives of a match over
  structures) are closed from the splitter's overlap hypotheses;
- without case split, by `congr` and `funext` (`mkMatchCongrByAlts?`), when the evidence of the alternatives has no
  proof obligation and does not use the pattern equalities. This halves the evidence of `MintingPolicy`.

`MatcherApp.transform` is used without its type check of the new motive (`transformMatcherApp`), which traversed the
alternatives of nested `match` applications again at each level, and the match equations are cached.

### 3.3 Rule certificates

Each rewriting rule can record the lemma that justifies it: `withThm lhs rhs thm args`, or `withHypThm` when the rule
relies on a hypothesis. The stack machine collects the recorded steps after each rule application and chains them
(`ruleStep`). Any gap becomes a typed proof obligation `lhs = rhs`, so rules can be instrumented one at a time. The
lemmas live in `Reconstruct/Lemmas.lean`.

| rule                                                                     | justification                       |
|--------------------------------------------------------------------------|-------------------------------------|
| propositional connectives, Boolean operators, `decide'`, `BEq`, equality | lemma (`withThm`)                   |
| quantifiers and implications, existentials, commutativity normalization  | lemma (`withThm`)                   |
| `dite'` propagation, opaque constants (`ite`, `decide`, `Nat.succ`, ...) | lemma (`withThm`)                   |
| cancellation under non-zero hypotheses                                   | lemma (`withHypThm`)                |
| equality between proofs                                                  | `eq_proof_irrel`                    |
| `Blaster.dite'` with constant branches                                   | `recordDITESimp`                    |
| connectives of `Blaster.decide'`                                         | `recordDecideOp`                    |
| `matchReduction` on constructor discriminants                            | iota (`proveMatchReduction`)        |
| `matchReduction` over `Blaster.dite'` (`constMatchPropagation?`)         | `apply_dite'`                       |
| case of case, function over a match, match applied to extra arguments    | match push (`mkMatchPushProof`)     |
| `elimMatch?` with a common right-hand side                               | splitter case split, `rfl` per case |
| `elimMatch?` by the negative match context (`lastPatternReduction?`)     | proof obligation                    |
| replacement of a matcher by an equivalent one (`structEqMatch`)          | `mkMatchEquivProof`                 |
| `match` to a chain of `Blaster.dite'` (`normMatchExpr?`)                 | proof obligation (`match cases`)    |
| arithmetic (`Nat`/`Int`) constant folding                                | proof obligation                    |

Notes on the `match` rules:

- **`matchReduction`.** The discriminants, resolved with the match context, are rewritten with the equalities of the
  enclosing alternatives; the match then reduces by iota.
- **Match push.** Case of case (`constMatchPropagation?`), a function over a match (`funPropagation?`) and a match
  applied to extra arguments (`normChoiceApplication?`) all rewrite `F[match d with alts]` to
  `match d with (F[·] ∘ alts)`. The proof is a case split over the alternatives of the resulting match, each case
  being justified by the match equation of the pushed match.
- **`normMatchExpr?`.** The optimizer instantiates the equations of the discriminants (`h : d = p` for
  `match h : d with`) with `Eq.refl d`, whose type is `d = p` only once `d` is rewritten to `p`. When tracking proofs,
  they are instead proved from the condition of their branch (e.g., `h.1 : x = 2` for the condition
  `x = 2 ∧ y = 1`), so that the branches are well-typed. The equality between the `match` and its `dite'` chain is a
  proof obligation, discharged by `match cases` (Section 3.4).

### 3.4 Discharging proof obligations

Proof obligations are discharged in `Reconstruct/Discharge.lean`. Each obligation is type-checked (an ill-typed
obligation fails), then attempted in its own local context, with every binder and hypothesis of the rewrite
available. Blaster's internal forms (`Nat.add`, `Blaster.dite'`, `Nat.beq`, ...) are first rewritten back to standard
notation (`blaster_denorm`). Each attempt has a heartbeat budget, and failed attempts leave no trace (state, messages
and info trees are restored). The portfolio, in order:

| step | strategy                                                                                                 |
|------|----------------------------------------------------------------------------------------------------------|
| 0    | the tactic that discharged the previous obligation of the same kind (e.g., all the `match` reductions)   |
| 1    | definitional equality (`rfl`); for closed obligations, `decide +kernel` and `blaster_wf_eval`            |
| 2    | `simp [*]`, `omega`, `grind`                                                                             |
| 3    | cancellation of non-zero divisors (`simp` with `omega` as discharger)                                    |
| 4    | case analysis: `split`, the conditions of applied `dite`s, cancellation of non-zero factors              |
| 5    | case analysis on variables of inductive types and their fields, unfolding user definitions and instances |
| 6    | induction for equivalences between recursive functions (`blaster_funind`)                                |
| 7    | SMT proof replay of the obligation (`obligationBySmtProof`, Section 4), unless the replay mode is `off`  |
| 8    | a deeper case analysis with a larger budget                                                              |
| 9    | `match cases` over the splitter, then case analysis on `match`es with generalized discriminants          |
| 10   | case analysis on the variables that stuck `match` applications depend on                                 |

- **Closed computations.** `blaster_wf_eval` evaluates well-founded recursion by unfolding its equation lemmas, since
  the kernel cannot reduce well-founded recursion efficiently.
- **Induction.** `blaster_funind` uses functional induction following one of the functions of the equation, or
  structural induction on one variable. Nested equivalences are proved bottom-up and reused.
- **SMT proof replay.** The obligation is closed over the variables it mentions and the hypotheses on them (e.g., the
  conditions under which the optimizer rewrote). It comes before the costly case analyses: on CEK evaluations, the
  replay proves in less than a second obligations on which the case analyses fail after a minute. It is not tried on
  obligations without variables, which are computations left to kernel evaluation, and it is only the last resort for
  the equivalences of recursive functions, which need induction: on both, the backends ran until their timeouts (40 s
  for the constant folding of `Nat.log2 (2 ^ 65536)`, and for `powerNat x y = Nat.pow x y`).
- **`match cases`.** For an obligation `match ds with alts = rhs`, a case split over the matcher's splitter, where the
  discriminants are replaced by the patterns in `rhs`. Each case is discharged recursively with the portfolio, with the
  pattern equalities and the overlap hypotheses in the local context.
- **Stuck matches.** When no splitter can be generated, the variables a match is stuck on are split instead. Matches
  stuck on literal patterns (e.g., `Int` literals, whose `Int.decEq` tests `whnf` does not unfold) are reduced with the
  matcher's equation theorems before any lemma normalizes the discriminants (e.g., `Int.ofNat (n + 4)` to `↑n + 4`,
  which no equation theorem matches). For the obligations of `normMatchExpr?`, this step comes right after step 2,
  before the costly case analyses.

Before the sequential portfolio runs, the obligations that are not definitional are discharged speculatively in
parallel (`startDischarges`, 6 tasks, `BLASTER_RECON_PARDISCHARGE`), closed over their relevant context and without
the costly case analyses.

**Scopes.** Obligations are closed terms, but their proofs may use the hypotheses of their local context (e.g.,
`simp [*]` with the pattern equalities). The same obligation can occur under different binders, for example when a
proof is reused through the proof cache. It is therefore discharged once per binder scope (`transformScoped`), not
once per term as `Meta.transform` would do.

**Fallback regions.** The congruence over a `match` application is a *fallback region*: if one of the obligations of
its alternatives cannot be discharged, the whole region is replaced by the coarse obligation
`match ds with alts = match ds with alts'`. Finer evidence therefore never loses a goal that the coarse obligation
could prove. This matters when an alternative contains ill-typed intermediate rewrites (Section 7.2).

### 3.5 Residual goal

If the optimizer reduced the goal to `True`, the residual proof is `True.intro`. If the SMT solver proved the residual
goal, it is proved again in Lean, with tactics (`proveResidual`) or by SMT proof replay (Section 4), depending on the
mode. The tactic strategies:

| strategy            | tactics                                                                                |
|---------------------|----------------------------------------------------------------------------------------|
| decision procedures | `decide`, `simp`, `omega`, `grind`                                                     |
| instantiation       | seeded (`blaster_inst_hyps`), with structure invariants (`blaster_struct_facts`)       |
| case analysis       | variables of inductive types (unfolding user definitions), `split`, `match cases`      |
| recursive functions | unfolding equation lemmas (after `blaster_lit_add`), induction (`blaster_funind`)      |
| existentials        | witness search (`blaster_exists`), including existentials over types                   |
| arithmetic          | `div`/`mod` facts (`blaster_divmod_facts`), nonlinear lemmas                           |
| empty types         | elements of empty types (`blaster_nomatch`), constructed arguments (`blaster_inhabit`) |

**Empty types.** The arguments of a function into an empty type, like the witnesses of existentials over function
types, are constructed from their types when they have no default element (`blaster_inhabit`). For example, for
`∀ (f : SomeBig → Empty), False` with `SomeBig.intro (n : Nat) (h : n > 5)`, the term `f ⟨6, _⟩` takes the witness 6
from the literals of the constructor type. Another example is `fun x => absurd x.inv _ : FalseInv → Empty`, where a
field of `x` is contradictory.

**Racing case analyses.** On residuals with `match` applications, the case analyses (`split`, `match cases`, unfolding
with case analysis) are attempted in parallel right after `omega` and `grind` (`raceTactics`), on the goal closed over
its local context, because the best one depends on the goal (e.g., 0.3 s for one of them on a goal where another one
exhausts its budget). Each attempt's heartbeat budget is measured inside its own task.

**When to replay.** In the default mode (`last`), the SMT proof replay is tried once, as soon as two attempts exhaust
their budget (`proveResidual` with `hard`), the attempts of a race counting individually. On the
residuals of CEK evaluations, every tactic runs out of its budget (7.5 s each, 13 s for the deeper case analysis), so
waiting for all of them delayed the replay by about 75 s. If every strategy fails, the equivalences between recursive
functions established by the optimizer are proved and used as facts, and the replay is tried last if it has not been
tried yet.

### 3.6 Kernel check

The proof of the original goal is `Eq.mpr pf r`, applied to the local axioms. Every proof is checked once by the
kernel, synchronously, as an auxiliary theorem (`checkedProof`, `Kernel.Environment.addDecl`). The declarations using
it (e.g., the theorem proved by `blaster`) refer to the auxiliary theorem, so the proof term is neither checked again
nor traversed by later phases.

- **Free variables.** Goals with free variables (e.g., the goals of the `blaster` tactic, with its hypotheses) are
  closed over the declarations of their local context they depend on, then checked as auxiliary theorems too.
  `Meta.check`, used before, ran out of recursion depth on deep proofs (7 of the 26 `Auction` theorems failed).
- **Fallbacks.** A proof depending on `let` variables of the local context is checked by the kernel without being
  added as an auxiliary theorem (`kernelCheck`), and one whose goal still has metavariables (e.g., in the
  declarations of its local context, such as the universe levels of the hypotheses introduced by `induction`) by the
  elaborator's type checker. A proof term with metavariables is refused.
- **No heartbeat limit.** The kernel checks of reconstructed proofs have no heartbeat limit (`kernelOptions`).
- **Large proofs.** Large SMT proofs are split into auxiliary theorems checked in parallel (Section 4.5).
- **`sorryAx`.** A proof that depends on `sorryAx` is refused, including through auxiliary declarations created by
  tactics. For example, `nomatch` reports missing cases as an error message and still produces a matcher whose body is
  `sorry`, which the kernel accepts.

Only kernel-accepted proofs are reported as reconstructed or used to close tactic goals.

### 3.7 Direct fallback

If the steps above fail, the strategies of Section 3.5 are tried on the original goal itself (e.g., `rfl` or
`decide +kernel` for closed computations), with the local axioms as `simp` lemmas.

## 4. SMT proof replay

Goals closed by the SMT solver can also be proved by replaying a proof produced by an SMT backend, instead of (or in
addition to) re-proving them with Lean tactics. The same replay serves the proof obligations of the optimizer that no
tactic discharges (Section 3.4). It is implemented in `Blaster/Reconstruct/SmtProof/` and works with several backends
through a common representation.

### 4.1 Modes

| `BLASTER_SMT_PROOF` | `(smt-proof: n)` | behavior for goals closed by the SMT solver                              |
|---------------------|------------------|--------------------------------------------------------------------------|
| `off`               | 0                | never replay                                                             |
| `last` (default)    | 1                | tactics first; replay once two attempts exhaust their budget or all fail |
| `first`             | 2                | replay first, then the tactics                                           |
| `only`              | 3                | replay only, no tactics (to measure the replay)                          |

In every mode but `off`, the proof obligations of the optimizer that the cheaper tactics don't discharge are also
replayed, before the costly case analyses (step 7 of Section 3.4).

### 4.2 Backends

| backend | solver and proof format | notes                                                                         |
|---------|-------------------------|-------------------------------------------------------------------------------|
| `z3`    | Z3, legacy proofs       | Blaster's simplifier commands are dropped (finer proofs)                      |
| `z3rec` | Z3, legacy proofs       | recursive functions as `define-funs-rec` (Section 4.3); only for such queries |
| `z3+`   | Z3, legacy proofs       | keeps Blaster's simplifiers (`recfun-finder`, `macro_finder`): coarser proofs |
| `cvc5`  | cvc5, Alethe            | optional, not in the default list                                             |

The backends are tried in order (`BLASTER_SMTPROOF_BACKENDS`, default `z3,z3rec,z3+`). Z3 runs with
`:produce-proofs true` and `pp.simplify_implies false`; cvc5 with `--parsing-mode=lenient`,
`--proof-format-mode=alethe` and `--proof-granularity=dsl-rewrite`. Z3 runs as a portfolio of random seeds (3 by
default), started a quarter of the timeout apart (at most 10 s) while no proof is found: on CEK evaluations, the time
Z3 takes to find a proof varies from 30 to 170 s with the seed. The Alethe parser (`Alethe.lean`) also reads veriT's
proofs, but no veriT backend is provided.

### 4.3 Pipeline

1. **Query** (`Driver.lean`). The residual goal is translated again with Blaster's translation, after introducing its
   leading variables as Lean free variables, so that the SMT constants `$k` can be mapped back to them. Definitional
   axioms of recursive functions over `Nat` (`∀ x, f x = f_LRec x`) are guarded with `0 ≤ x` (this only weakens the
   query).
2. **Proof** (`Z3.lean`, `Alethe.lean`, `IR.lean`). Each adapter translates the backend's proof into a DAG of steps:
   rule, premises, arguments (e.g., quantifier instantiations) and conclusion (clauses as disjunctions).
3. **Interpretation** (`Interp.lean`). SMT terms are interpreted as Lean terms:
   - `Int` arithmetic on Lean `Int`, with casts (`↑n`, `Int.toNat`) where Lean terms of type `Nat` occur (arguments
     and results of Lean functions, constructor fields);
   - `Bool` formulas as propositions;
   - datatype constructors, selectors and testers as Lean constructors and case analyses;
   - Blaster's function values (`@@ArrowT`, `@apply`) as Lean functions;
   - Blaster's type predicates (`@isNat`, ...) as `True` (Lean values always satisfy them);
   - skolem constants as `Classical.epsilon` terms;
   - the polymorphic encoding as described in Section 4.4.
4. **Sort inference** (`SortInfer.lean`). Z3 prints the nullary constructors of parametric datatypes without their
   sort (`List.nil` for all the instances of `@List`), and the occurrences of a term are one object only when Z3 binds
   it by a `let`. The instances of the constructor applications that their arguments don't determine are therefore
   inferred on the whole proof (one sort per term object, from the signatures of the query and the constraints of all
   the steps). Each occurrence is then interpreted in the same instance in all the steps where it occurs, and the
   parts that remain undetermined are defaulted identically in each step.
5. **Replay** (`Replay.lean`). Each step yields a Lean proof of the interpretation of its conclusion:
   - explicit proof terms for resolution (a unit propagation procedure building the proof), modus ponens, equality
     reasoning (`trans`, `symm`, `monotonicity`, `commutativity`), quantifier instantiation, skolemization,
     hypotheses and lemmas;
   - the propositional engine (`Prop.lean`) for `def-axiom`, `not-or-elim`, `and-elim`, propositional `rewrite`s and
     Alethe's Tseitin rules;
   - small tactic calls (`simp`, `omega`, `grind`, unfolding of user definitions) proving `premises → conclusion`
     for arithmetic (`th-lemma`, arithmetic `rewrite`s), with a portfolio ordered adaptively by success rate per time
     unit for each rule and goal shape, attempted in parallel on closed goals (`portfolioParMulti`).

   Large equalities (e.g., Z3 `rewrite`s inside big formulas) are related by congruence on their common structure,
   and only their *local differences* are given to tactics, with the subterms common to both sides generalized
   (`Local.lean`). Arithmetic lemmas over large atoms are generalized the same way, with facts on `div`/`mod` for
   `omega`. Nonlinear integer lemmas are proved by `blaster_nlarith` (`NlArith.lean`: case splits, products of
   hypotheses, polynomials normalized with the commutative ring lemmas of `grind`, then `omega` with the monomials as
   atoms). Tactics run on the statement of the step closed over the variables it mentions, in an empty local context:
   a step holds by itself (its premises are hypotheses of the statement), and the hypotheses of the context (e.g.,
   the negated goal of a CEK evaluation) slowed down `simp_all` and case analyses by one to two orders of magnitude.
6. **Bridge** (`Bridge.lean`, `BridgeMatch.lean`). The asserted formula is the translation of the negated goal,
   interpreted back. It is related to the negated goal by a simultaneous traversal of both terms: congruence on their
   common structure, and a lemma for each encoding of the translation where they differ:
   - `match` as `ite` chains over testers and selectors: an auxiliary theorem per matcher instance, stated for
     abstract discriminants and alternatives, and proved by evaluating the conditions with case analyses; named and
     normalized `Int` patterns are supported;
   - `Nat` terms as `Int` terms, and quantifiers over `Nat` as guarded quantifiers over `Int`;
   - `Bool` terms as formulas, `dite'`/`ite`, and Blaster's type predicates;
   - functions translated as SMT macros (e.g., `@Nat.sub`, `@Int.toNat`, expanded by the backends), with an auxiliary
     lemma per function relating it to its macro.

   The definitions of the other functions are bridged by tactics. The traversal is linear in the size of the shared
   terms, which matters for goals such as CEK evaluations.
7. **Recursive functions** (`RecFun.lean`, backend `z3rec`). Z3's `recfun-finder` simplifier, which turns the
   definitional axioms of recursive functions into recursive definitions, is a no-op under proof production, and Z3
   then times out on the CEK goals it proves without proofs. The `z3rec` backend rewrites the query into
   `define-funs-rec` at the SMT-LIB level, which yields a proof in seconds, and Z3's `recfun` lemmas are replayed with
   kernel-checked definitional equations. These equations are proved in parallel while the backend searches for a
   proof (`RecFun.preStartEqTasks`, `RecFun.startEqTasks`).

The proof of `False` is turned into a proof of the goal and kernel-checked like any other reconstructed proof.

### 4.4 Polymorphic encoding

Blaster encodes polymorphism with `@Type` (the types denoted by sort variables), `@Instance` (their values) and
membership predicates `@isInstance v t`. The replay interprets this encoding in one of two ways:

- **One sort variable `α` of an inhabited type:** `@Instance` is `α`, `@Type` is `Unit`, and membership predicates
  are `True`.
- **Otherwise** (several, possibly empty, or quantified sort variables; `Poly.lean`): `@Type` is `Sort u`, and
  `@Instance` is the always inhabited *universe* `Option (PSigma fun α : Sort u => α)`. Values are interpreted as their
  injections (lifted through lists, options, pairs and functions), and membership predicates as "lies in the image of
  the injection". The bridge relates the goal to the asserted formula with an additional *world* for these injections.
  - **User datatypes over sort variables** (e.g., `Term (List α)` for a nested or mutual datatype) are mapped to their
    instances at the universe by maps defined with their recursors: each constructor to itself, its fields by their
    worlds, its nested occurrences (e.g., `List (Term α)`) by the auxiliary recursors. Each instance comes with
    auxiliary definitions, proofs of their injectivity, and per constructor its equation in the world (nested
    occurrences as `List.map`) and its image (`Img W (C ys) = Img Ŵ₁ y₁ ∧ …`).
  - **`match` on such a datatype** (or on a list or an option of a sort variable), whose `ite` encoding would need
    default values of the selectors at the sort variables, is related to its interpretation by case analysis on its
    discriminant, generalized in both terms.
  - **Polymorphic Lean functions** instantiated at sort variables (e.g., `@List.zipWith α β γ`, whose SMT function is
    shared by all the instantiations of a universe) are interpreted at the universe (`@List.zipWith Univ Univ Univ`),
    so that their definitional axioms hold on all the values of the universe. The bridge relates their applications
    by *naturality lemmas*, e.g.,
    `List.zipWith (lift f) (List.map (inj α) xs) (List.map (inj β) ys) = List.map (inj γ) (List.zipWith f xs ys)`,
    proved once per function and instantiation by functional induction (`blaster_poly_nat`).
  - **Lambda terms** of the translation (`@lambda`, `@global_lambda`, with their definitional axioms) are interpreted
    as Lean lambdas, with their `Nat` parameters as Lean `Nat` variables. At the universe, they are guarded by the
    membership predicates of their parameters, as their definitions are (`fun x => if Img w x then b else dflt x`).
- **Not interpreted at the universe:** naturality only holds for parametric functions, so axioms and opaque functions
  at sort variables (e.g., `hash : α → String`) and functions with instance arguments that don't exist at the universe
  (e.g., `[BEq α]`) are only interpreted with `@Instance` as the sort variable.

### 4.5 Large proofs

The residual proofs of CEK evaluations have up to 150K steps. Several measures keep their replay and kernel check
tractable:

- **Linear construction.** The proofs of the top-level steps are held by metavariables, and binders are abstracted
  syntactically, so the construction of a step does not traverse the proofs of the previous ones. SMT terms are
  interpreted once (memoization on shared terms, by object address; the memo keeps its terms alive, since a term
  built during the replay and then freed, e.g., the conclusion of a `proof-bind` step as a quantifier, would leave
  its address to a later term, which then got its interpretation), and the steps that don't depend on a scope are
  replayed in increasing order (bounded recursion on deep proofs). The case analyses of unit resolutions and the facts derived by
  the propositional engine are built under their binders, with the premises of the step as bound variables.
- **Lifting global proofs** (`liftGlobalProofs`). The proofs of the global steps are held by unassigned metavariables
  during the replay and lifted at the end to closed lambda terms over the variables of the goal and the negated goal.
  They are shared by the nested `lemma` scopes at various binder depths, where abstracting the inlined proofs copied
  them once per depth: the second `MintingPolicy` proof (31.7K steps, 10.7M distinct subterms at binder depth 216)
  needed more than 36 GB to abstract; lifted, it takes 0.5 s and has 2.5M distinct subterms.
- **Auxiliary theorems.** The kernel's memory goes to its per-declaration caches (the types inferred for checked
  subterms, and the equivalences that `is_def_eq` records), not to binder depth: the first `SellNFT` proof (152,698
  steps, 10.1M distinct subterms) did not fit in 20 GB as a single declaration. Each lifted global proof is therefore
  checked as an auxiliary theorem `∀ xs, ¬ goal → φ` over the variables of the goal and the negated goal, and used as
  its constant applied to them (`liftGlobalProofs` with `aux?`). Proofs that are not closed (e.g., over variables of
  the polymorphic encoding bound by an enclosing context) stay inlined.
- **Parallel kernel checks.** With at least 1024 global proofs (`BLASTER_SMTPROOF_PARCHECK_MIN`), the auxiliary
  theorems are added without checking and checked by the kernel in parallel (`startKernelChecks`, 8 threads,
  `BLASTER_SMTPROOF_PARCHECK`), each against the environment before it, so that it only uses the auxiliary theorems
  before it. The proof is accepted once all the checks succeed (`awaitKernelChecks`). For the second `MintingPolicy`
  proof (6,928 global proofs), this takes 4 s at 2.3 GB, against 35 s at 3.7 GB for sequential auxiliary theorems and
  25 s at 6.2 GB as a single declaration.
- **Sequential split.** Without parallel checks (`BLASTER_SMTPROOF_PARCHECK=0`), the global proofs become sequentially
  checked auxiliary theorems when there are at least 4096 of them (`BLASTER_SMTPROOF_SPLIT`, 0: always) in a proof of
  at least 5M distinct subterms (`BLASTER_SMTPROOF_SPLIT_DAG`). With parallel checks, the threshold is
  `BLASTER_SMTPROOF_PARCHECK_MIN` alone.
- **Proof depth.** `shareDeepProofs` bounds the proof depth at 512.

With every global proof as an auxiliary theorem (`BLASTER_SMTPROOF_SPLIT=0`), the replay results on the test suite are
unchanged.

### 4.6 What the replay relies on

The interpretation is a *choice*: a step whose conclusion does not hold for it (e.g., an axiom of a `Nat` function
instantiated with a negative integer) simply fails to replay. Soundness only relies on the kernel.

## 5. Configuration reference

Options of the `#blaster` command and the `blaster` tactic are listed in Section 2.1. Environment variables:

**User-facing.**

| variable                    | meaning                                                   | default                 |
|-----------------------------|-----------------------------------------------------------|-------------------------|
| `BLASTER_RECONSTRUCT`       | default reconstruction level (`0`, `1`, `2`)              | `0`                     |
| `BLASTER_SMT_PROOF`         | replay mode: `off`, `last`, `first`, `only` (Section 4.1) | `last`                  |
| `BLASTER_SMTPROOF_BACKENDS` | comma-separated backends, tried in order (Section 4.2)    | `z3,z3rec,z3+`          |
| `BLASTER_SMTPROOF_Z3`       | Z3 executable                                             | `z3`                    |
| `BLASTER_SMTPROOF_CVC5`     | cvc5 executable                                           | `cvc5`                  |
| `BLASTER_SMTPROOF_TIMEOUT`  | timeout of each backend (s)                               | `(timeout: n)`, else 20 |
| `BLASTER_SMTPROOF_DEADLINE` | deadline of the replay of one proof (s)                   | 1800                    |

**Tuning.**

| variable                        | meaning                                                    | default             |
|---------------------------------|------------------------------------------------------------|---------------------|
| `BLASTER_SMTPROOF_SEEDS`        | Z3 random seeds raced per query                            | 3 (cvc5: 1)         |
| `BLASTER_SMTPROOF_SEED_DELAY`   | delay between the starts of two seeds (ms)                 | timeout / 4, ≤ 10 s |
| `BLASTER_SMTPROOF_LOCAL_MS`     | budget of tactics on local differences of large steps (ms) | 1000                |
| `BLASTER_SMTPROOF_PARPORTFOLIO` | parallel tactic attempts on closed goals (0: sequential)   | 6                   |
| `BLASTER_SMTPROOF_PARCHECK`     | threads for parallel kernel checks (0: none)               | 8                   |
| `BLASTER_SMTPROOF_PARCHECK_MIN` | minimum global proofs for parallel kernel checks           | 1024                |
| `BLASTER_SMTPROOF_SPLIT`        | minimum global proofs for a sequential split (0: always)   | 4096                |
| `BLASTER_SMTPROOF_SPLIT_DAG`    | minimum distinct subterms for a sequential split           | 5,000,000           |
| `BLASTER_RECON_PARDISCHARGE`    | tasks for speculative discharge of obligations (0: none)   | 6                   |

**Measurement and debugging hooks.** Variables taking a file append to it.

| variable                                  | effect                                                                   |
|-------------------------------------------|--------------------------------------------------------------------------|
| `BLASTER_RECON_STATS`                     | file: JSON lines per reconstruction attempt; `#testOptimize` audit       |
| `BLASTER_RECON_PROFILE`                   | file: durations of the reconstruction phases and attempts                |
| `BLASTER_SMTPROOF_LOG`                    | file: one JSON line per replay (`kind`: `residual` or `obligation`)      |
| `BLASTER_SMTPROOF_TRACE`                  | file: start and duration of the reconstruction and replay phases         |
| `BLASTER_SMTPROOF_ISTATS`                 | count the kernel's binder instantiations on the final proof (costly)     |
| `BLASTER_RECON_DEBUG`                     | full failure messages in the statistics; type-check failing obligations  |
| `BLASTER_SMTPROOF_DEBUG`                  | file: failures of steps and of the bridge                                |
| `BLASTER_BRIDGE_DEBUG`                    | file, or `1` for stderr: failures of the matcher lemmas of the bridge    |
| `BLASTER_RECEQN_DEBUG`                    | trace the case analyses of the equations of recursive functions          |
| `BLASTER_SMTPROOF_CURRENT`                | file: the steps being replayed (a stale mtime shows a stuck step)        |
| `BLASTER_SMTPROOF_CHECK`                  | check the proofs of steps for unknown free variables                     |
| `BLASTER_SMTPROOF_CHECKFINAL`             | report free variables escaping their scopes in the final proof           |
| `BLASTER_SMTPROOF_DUMP`                   | file: the query sent to the backend                                      |
| `BLASTER_SMTPROOF_PROOFDUMP`              | file, suffixed with the backend's name: the backend's proof output       |
| `BLASTER_SMTPROOF_PROOFFILE`              | file, suffixed likewise: proof read instead of running the backend       |
| `BLASTER_SMTPROOF_FAILDUMP`               | file: the failed steps with their conclusions                            |
| `BLASTER_SMTPROOF_GOALDUMP`               | file: closed statements of failed steps, as Lean examples                |
| `BLASTER_SMTPROOF_STEPDUMP`, `_STEPS`     | file and comma-separated step indices: their conclusions as Lean         |
| `BLASTER_SMTPROOF_BRIDGE_DUMP`, `_DUMP_N` | file and count (default 3): mismatching pairs of the bridge              |
| `BLASTER_SMTPROOF_SLOWGOALS`              | file: goals proved by tactics in 200 ms or more                          |
| `BLASTER_SMTPROOF_NOINHERIT`              | disable the reuse of step proofs across nested `lemma` scopes (ablation) |

`BLASTER_SMTPROOF_PROOFFILE` (e.g., `proof` for the file `proof.z3rec` written by `BLASTER_SMTPROOF_PROOFDUMP=proof`)
is read for every call of that backend, including the replays of proof obligations, so it is only meaningful for a
single replay.

## 6. Results

### 6.1 Test suite

Measured on branch `feat/smt-proof-replay` with Z3 5.3.1 (Section 9 describes the measurement):

| mode                 | scope                                            | kernel-checked               |
|----------------------|--------------------------------------------------|------------------------------|
| default (`last`)     | all reconstruction attempts                      | 3959 / 3959                  |
|                      | goals closed by the optimizer                    | 420 / 420                    |
|                      | goals closed by the SMT solver                   | 409 / 409                    |
|                      | `#testOptimize` certificates                     | 3130 / 3130                  |
| replay only (`only`) | SMT goals of `Tests/Smt` and `Tests/FixedIssues` | 311 / 323                    |

The twelve goals the replay alone does not prove are listed in Section 8; the tactic strategies prove all of them.

### 6.2 CardanoLedgerApiBlaster validators

The goals of [CardanoLedgerApiBlaster](https://github.com/input-output-hk/CardanoLedgerApiBlaster) evaluate UPLC
programs with the CEK machine. One theorem per run, 4 threads, low machine load; the `only` runs use the `z3rec`
backend. Measured at commit `3c64b27`, before the review commits that follow it.

| validator                     | theorems | mode            | time per theorem                | peak memory   |
|-------------------------------|----------|-----------------|---------------------------------|---------------|
| `HelloWorld`                  | 1        | `only` / `last` | 7 s / 16 s                      |               |
| `UnlockPIN`                   | 1 ¹      | `last`          | 14 s                            |               |
| `ParamFeed`                   | 1        | `last`          | 4 s                             |               |
| `Auction`                     | 26 ²     | `last`          | 3.5 min for all 26              |               |
| `Governance`                  | 20       | `only`          | 22–28 s (#14: 36 s in `last`)   |               |
| `MintingPolicy`               | 2        | `only`          | 31 s, 36 s (#2: 51 s in `last`) |               |
| `SellNFT`                     | 2        | `only`          | 33 min, 31 min ³                | 12.7, 13.3 GB |
| `Tests/Functions/Fibonacci` ⁴ | 4        | `last`          | 2 s for all 4                   |               |

¹ The file has three commands; the other two are expected-`Falsified` checks.

² Plus two expected-`Falsified` commands. Eight of the theorems are concrete evaluations closed by the optimizer,
whose evidence takes about 11 s of kernel check each (the type checker's caches).

³ Measured before the performance work of Section 6.4, with the global proofs checked as sequential auxiliary
theorems.

⁴ A test file of CardanoLedgerApiBlaster (not of this repository); its goals include the equivalence of two
implementations.

The `last` times of `Governance` #14 and `MintingPolicy` #2 were measured while other measurements were running.
In the `only` runs, the time goes mostly to Z3's check of the query (15 s for `Governance`, 10 s for
`MintingPolicy`, during which the proof run, 5 and 8 s, and the reconstruction are performed), Z3's search for a proof
of the residual (0.2 to 7 s, depending also on the fresh names of the query), the replay of the residual (11 to 20 s:
the arithmetic local differences of the rewrites for `Governance`, the lemmas of the recursive functions and of the
datatypes for `MintingPolicy`) and the kernel checks (1 to 4 s).

`SellNFT` #1 has a residual proof of 152,698 steps, replayed in 5 minutes; its 19,369 global proofs are checked as
auxiliary theorems in 6.5 minutes. Three of the 1,004 proof obligations of its optimizer evidence are proved by the
replay of their own Z3 proofs.

### 6.3 PlutusCoreBlaster

Measured on branch `feat/kernel-proof-reconstruction-beta` (proof reconstruction ported onto
`beta-lambda-cache-optimization`, before SMT proof replay), with a nightly Z3 providing `recfun-finder`.
[PlutusCoreBlaster](https://github.com/input-output-hk/PlutusCoreBlaster) (commit `c9dc0eb`) pins the
`beta-lambda-cache-optimization` branch of Blaster.

- **CBOR encoding.** All 31 `encode_example_i` goals of `PlutusCore/Cbor/Tests.lean` become kernel-checked theorems
  with `blaster_theorem` (see [`docs/examples/PlutusCoreCbor.lean`](examples/PlutusCoreCbor.lean)). They only depend
  on `propext`, `Classical.choice` and `Quot.sound`; upstream checks them with `native_decide` or with an unchecked
  `#blaster`. Running `PlutusCore/Cbor/Tests.lean` unchanged with `BLASTER_RECONSTRUCT=1` also reconstructs a
  kernel-checked proof for each of its 33 `#blaster` commands and `blaster` tactics (the 3 expected counterexamples
  need no proof). The examples splitting long strings evaluate the well-founded recursion `splitToChunksLoop` with
  `blaster_wf_eval`.
- **Lemmas.** 17 statements from `PlutusCore/{Integer,List,Bitwise,Cbor}` were restated with `blaster_theorem` (see
  [`docs/examples/PlutusCoreBlaster.lean`](examples/PlutusCoreBlaster.lean)). 14 become kernel-checked theorems,
  including `divide_add_mod`, `quotient_add_remainder`, the error cases of `integerToByteString` and
  `replicateByte_zero_l`. The other 3 (`integerToByteString_w_bounds_err`, `integerToByteString_neg_n`,
  `integerToByteString_n_bounds_err`) failed before reconstruction on that branch, because the SMT translation
  rejected `Nat.log2`, which core defines directly with `Nat.rec`. `Nat.log2` is now translated as an opaque recursive
  SMT function (`Tests/FixedIssues/NatLog2.lean`); these three lemmas have not been measured again.

### 6.4 Performance notes

The following changes brought the CEK validators from minutes to seconds in the `only` mode. Before them, the
fourteenth `Governance` theorem (#14 below) took 392 s, and the `MintingPolicy` theorems 348 and 382 s; they now take
22–28 s (every `Governance` theorem) and 31 and 36 s.

| change                                                                   | effect                                   |
|--------------------------------------------------------------------------|------------------------------------------|
| optimizer evidence for `dite'`, `decide'` and equivalent matchers (3.3)  | 467 of 672 obligations of #14 removed    |
| proof run while the solver checks the query (3.1)                        | #14: 42 s → 34 s                         |
| proof-run caches in its state instead of global references               | proof run 25 s → 9 s (`MintingPolicy`)   |
| `match` congruences without case split (`mkMatchCongrByAlts?`)           | evidence of `MintingPolicy` halved       |
| local differences: 1 s bound, refuted generalizations skipped            | no runaway tactic attempts               |
| syntactic abstraction before `kabstract` (`monotonicity`, `substProof?`) | fewer definitional checks                |
| recursive-function equations proved during the proof search (4.3)        | off the critical path                    |
| parallel tactic portfolios on closed goals (`portfolioParMulti`)         | rewrites of #14: 18 s → 11 s             |
| unit resolutions built under binders (`orElim`, `PropEngine.lam1`)       | rewrites of `MintingPolicy`: 3.6 s → 1 s |
| speculative parallel discharge of proof obligations (`startDischarges`)  | obligations of `HelloWorld`: 4.6 s → 2 s |
| proof depth bound 512 instead of 128 (`shareDeepProofs`)                 | 12 s of proof sharing removed            |
| in `last` mode, replay after two exhausted attempts (3.5)                | `HelloWorld` 83 → 16 s, #14 120 → 36 s   |

On the test suite (wall time per file, with the `#testOptimize` audit of `BLASTER_RECON_STATS`), skipping the replay
of the obligations without variables and of the equivalences of recursive functions (3.4) brought `NatLog2.lean` from
44 s to 8.5 s and `Tests/Reconstruct/Basic.lean` from 43 s to 2.5 s, and skipping the passes of `dischargeHoles` on
proofs without obligations brought `MatchToITE.lean` from 67 s to 59 s. The subterms containing obligations are
computed once for the two traversals of `dischargeHoles` (the speculative discharge and the first pass), at about
8 µs per distinct subterm: `dischargeHoles` on the four goals of `Tests/Reconstruct/DeepProofs.lean` 12.7 s → 7.3 s.

`orElim` was quadratic in the literals of large clauses (a third of the replay of `MintingPolicy`). The parallel
tactic tasks run without the replay's state, whose objects would otherwise be marked as multi-threaded; the auxiliary
lemmas created in a task are inlined in its proof and the reserved names it used (e.g., splitters) realized again
(`Local.inlineNewConstants`, `Local.realizeReservedNames`).

## 7. Findings

### 7.1 Soundness bugs

Reconstruction checks every individual rewrite, and the SMT proof replay checks the solver's reasoning step by step,
so they surface problems in the trusted pipeline. All the bugs below made false statements `Valid`.

| bug                                          | status on this branch | regression test                         |
|----------------------------------------------|-----------------------|-----------------------------------------|
| type variables assumed inhabited             | fixed                 | `Tests/Reconstruct/Unsound.lean`        |
| unguarded definitions of lambda terms        | fixed                 | `Tests/FixedIssues/LambdaDefGuard.lean` |
| non-canonical `LT`/`LE` instances            | fixed                 | `Tests/FixedIssues/InstanceArgs.lean`   |
| equality between proofs                      | fixed                 | `Tests/FixedIssues/PropProofEq.lean`    |
| sort quantifiers, `Prop` domains (`staging`) | not affected          | `Tests/Smt/SmtUninhabited.lean`         |

- **Type variables assumed inhabited (found by reconstruction).** The optimizer rewrote `∀ (x : α), e` to `e` (and
  `∃ (x : α), e` likewise) whenever `isSortOrInhabited α` held, which was the case for any type variable, and the SMT
  translation mapped every type variable to the non-empty sort `@@Type`. Blaster reported
  `∀ (α : Type), (∀ (_x : α), False) → False` as `Valid`, although `α := Empty` refutes it; reconstruction refused the
  goal and pinpointed the rewrite `(∀ (_x : α), False) = False`. The optimizer now keeps quantifiers over possibly
  empty types, and each type variable universally quantified at the top level of the goal gets its own, possibly
  empty, membership predicate; the solver now finds the counterexample.
- **Unguarded definitions of lambda terms (found by SMT proof replay).** The definitional axioms of lambda terms
  (`@lambda_n_def_cstr`, `@global_lambda_n_def_cstr`) constrained their applications on all the values of the sorts of
  their parameters: the values of all the types denoted by sort variables (`@Instance`), and the negative integers for
  `Nat` parameters. Function equality being translated as SMT equality, two lambda terms equal in Lean were equal on
  all the values of their sorts, which is inconsistent when they differ outside their domain. For example,
  `∀ (b : Bool), (fun n : Nat => n - 1 + 1) = (fun n : Nat => if n = 0 then 1 else n) → b = true` was `Valid`. The
  definitions are now guarded by the membership predicates of the parameters. The replay could not prove these goals
  (the axioms have no model in its interpretation), which is how the bug was found. Two induction steps of
  `Tests/FixedIssues/Issue26.lean` are no longer proved by Blaster.
- **Non-canonical instances (found by SMT proof replay).** `@LT.lt α inst` (resp. `LE.le`) was taken as the relation
  of the SMT theory for `α ∈ [Nat, Int, Bool, String]` whatever `inst`, and the instance arguments of function values
  (e.g., a structure field `f [LT α] : α → α`) were erased by the translation. With `lt1 := ⟨(· < ·)⟩` and
  `lt2 := ⟨fun a b => b < a⟩ : LT Nat` passed explicitly, `∀ x y, @g Nat lt1 _ x y = @g Nat lt2 _ x y` (with
  `g x y := decide (x < y)`) was `Valid`. Other instances of `LT`/`LE` are now unfolded, and applications of function
  values are only translated when their instance arguments are canonical or instance-implicit binders of the goal.
  Two instance-implicit binders of the same class are still not distinguished.
- **Equality between proofs.** Any two proofs of a proposition are definitionally equal in Lean, but the optimizer
  reduced `TwoP.a = TwoP.b` to `False` for the distinct constructors of `inductive TwoP : Prop | a | b`, and the SMT
  datatype of an inductive proposition distinguishes its values: `TwoP.a ≠ TwoP.b` and `∃ (x y : SomeBig), x ≠ y`
  were reported `Valid`. An equality `@Eq P a b` with `P : Prop` is now reduced to `True` (`eq_proof_irrel`), and
  `structEq?` ignores proof arguments, so constructor applications that differ only in proof arguments are equal. The
  fix is also on branches `fix/prop-proof-equality` (off `main`) and `fix/beta-prop-proof-equality` (off
  `beta-lambda-cache-optimization`), not merged.
- **Sort quantifiers outside the goal prefix and `Prop` domains (upstream `staging`).** On `staging`, sort quantifiers
  that are not in the leading `∀` prefix of the goal were instantiated with the non-empty sort `@@Type` (e.g.,
  `∀ p, p ∨ ∀ (α : Type), (∀ (_x : α), False) → False` was `Valid`), and the co-domain constraints of functions with a
  proposition domain (`P → β`, inhabited when `P` does not hold, even for an empty `β`) were not guarded (e.g.,
  `∀ (_f : Bad → Empty), False` for `structure Bad : Prop where inv : 1 > 2`). The fix for `staging` is on branch
  `sho/prop-domain-fun-guard`. This branch's translation is sound on all their regression tests, which are merged
  into `Tests/Smt/SmtUninhabited.lean`; four theorems of these tests get a spurious counterexample, as on
  `beta-lambda-cache-optimization`, and are kept commented out. Upstream `beta-lambda-cache-optimization` (c7e80b2)
  reports 18 of the false statements of these tests as `Valid`.

### 7.2 Ill-typed optimizer output

The proof run avoids the following issues; the verdict run is unchanged.

- The else branch of `Blaster.dite'` received the *normalized* type of `¬ c` (e.g., `false = c` instead of
  `¬ (true = c)`), so `dite'` applications were ill-typed. When tracking proofs, the branch binder keeps type `¬ c`,
  while the normalized form is still used as the hypothesis.
- `andBoolReduction?` returned the proposition `False` for a Boolean `&&` (fixed upstream, #177).
- `forallReduction?` substitutes `True.intro` for a hypothesis whose type was simplified to `True`. This yields
  ill-typed terms such as `Char.ofNatAux 84 True.intro`. When tracking proofs, proof arguments are not rewritten.
- Universe levels are normalized to `1` (`normLevel`), so goals over `Sort u` are rewritten to goals over `Type`, and
  `Blaster.dite'` is always built at level `1`. This includes unassigned *or uninstantiated* level metavariables; for
  example, `#testOptimize` passes terms with assigned but uninstantiated level metavariables. The proof run keeps the
  universe levels.
- The `dite'` branch-swap rule (`isITESwap?`) produced a then-branch of type `¬¬c → α` instead of `c → α`. When
  tracking proofs, the branches are retyped.
- Rewriting the domain of quantified *function* variables (e.g., `f : c = true → α` to `f : true = c → α`) leaves
  their dependent uses ill-typed. When tracking proofs, functions over proofs keep their original type.

## 8. Limitations and future work

**Optimizer evidence.**

- `match` rules relying on the *negative* match context (`lastPatternReduction?`, i.e., the discriminant does not
  match the patterns of the previous alternatives) leave a proof obligation. The overlap hypotheses of the splitter
  could be declared in the alternative's local context, like the pattern equalities.
- The normalization of matches to `Blaster.dite'` chains (`normMatchExpr?`) and arithmetic (`Nat`/`Int`) constant
  folding rely on tactic discharge rather than explicit lemmas.
- Match equations and splitters are generated by Lean on demand (`Match.getEquationsFor`). For matchers with many
  overlapping patterns, the generation can exceed Lean's fixed heartbeat budget; these matchers fall back to coarse
  obligations and to the case analysis on stuck variables.
- Equivalences between recursive functions that need a generalized induction hypothesis or mutual induction fail.
- The state machine commands (`#bmc`, `#kind`) are not reconstructed: their queries are checked incrementally on one
  solver session (base and induction cases selected by flags), not as Lean goals.

**SMT proof replay.** The twelve SMT goals of the test suite that the replay alone does not prove (Section 6.1):

| cause                                                                              | goals                                   |
|------------------------------------------------------------------------------------|-----------------------------------------|
| polymorphic structure fields with instance arguments                               | `Issue15` (3), `InstanceArgs`           |
| functions into empty types from inductive propositions (e.g., `SomeBig → Empty`)   | `SmtUninhabited` (3)                    |
| a sort quantifier depending on an existential variable                             | `SmtUninhabited`                        |
| nonlinear lemmas (products of conditionals, `(z * x) % (z * y) = z * (x % y)`)     | `SmtMatch`, `SmtNatMod`                 |
| proof-production timeouts of Z3                                                    | `Issue17`, `SmtNatMod`                  |

For inductive propositions, the selectors of Z3 proofs (e.g., `SomeBig.intro.0`) have no counterpart in Lean, as a
proof is not eliminated into data. Other limitations of the replay:

- Polymorphic goals with several sort variables over user datatypes without a world: indices, recursive fields of
  function types, proof fields whose propositions mention the sort variables (e.g., properties quantified over the
  instances of a class). Also constructor applications whose instance only the sort of a quantified variable
  determines (the undetermined type parameters of the conclusions of steps default to the universe), and axioms and
  non-parametric functions at sort variables (Section 4.4).
- `match` patterns on `Nat`/`Int` with variables (e.g., `n + 1`), whose translation needs the conditions of the
  branch.
- cvc5: the native CPC format (whose steps often leave their conclusion implicit) is not supported, and Alethe
  exports containing skolems (e.g., division by zero) fail.
- Proof production may time out where the verdict did not: `z3rec` and `z3+` make up for the missing
  `recfun-finder` on the CEK goals, but not in general.
- The kernel check of the largest proofs (`SellNFT`) takes about half an hour and 13 GB.

## 9. Measuring coverage

```sh
./scripts/recon_coverage.sh stats.jsonl 8
```

This runs every test file with `BLASTER_RECONSTRUCT=1` and `BLASTER_RECON_STATS=stats.jsonl`, which writes one JSON
line per reconstruction attempt. With `BLASTER_RECON_STATS` set, each `#testOptimize` case is also audited for a
kernel-checked proof of `e = optimize(e)`. The audit runs after the test's own check, and it optimizes with a dedicated
name-generator prefix, so that names created while building proof terms don't clash with those created during
reconstruction. `scripts/recon_report.py` summarizes the results: success rates per category, discharge methods,
failure reasons, and proof obligations per rewrite site. The rewrite-site breakdown is the to-do list for further rule
instrumentation.

The replay-only figure of Section 6.1 runs the test files of `Tests/Smt` and `Tests/FixedIssues` with
`BLASTER_SMT_PROOF=only` and `BLASTER_SMTPROOF_LOG=<file>`, and counts the logged replay attempts whose `kind` is not
`obligation`.

## Appendix A. Coverage history on `feat/kernel-proof-reconstruction`

Measured with `scripts/recon_coverage.sh` on the test suite of `feat/kernel-proof-reconstruction` (based on upstream
`staging`), before SMT proof replay. Percentages are the fraction of attempts producing a kernel-checked proof. The
last column excludes the 18 attempts refused because of the rewrite assuming type variables inhabited (Section 7.1,
since fixed).

| milestone | `#testOptimize` | goals closed by optimizer | goals closed by SMT | all   | all but refused |
|-----------|-----------------|---------------------------|---------------------|-------|-----------------|
| 1         | 85.7%           | 77.1%                     | 36.7%               | 82.4% |                 |
| 2         | 91.4%           | 84.4%                     | 33.3%¹              | 87.0% |                 |
| 3         | 90.9%¹          | 92.0%                     | 39.8%               | 87.4% |                 |
| 4         | 92.8%           | 92.0%                     | 39.8%               | 89.0% |                 |
| 5         | 92.9%           | 92.0%                     | 44.2%               | 89.5% |                 |
| 6         | 92.9%           | 92.0%                     | 65.5%               | 91.0% |                 |
| 7         | 95.1%           | 93.1%                     | 70.9%               | 93.3% |                 |
| 8         | 95.4%           | 93.2%                     | 70.9%               | 93.5% |                 |
| 9         | 98.3%           | 93.8%                     | 71.1%               | 96.1% | 96.6%           |
| 10        | 98.4%           | 93.8%                     | 78.5%               | 96.7% | 97.3%           |
| 11        | 98.4%           | 93.2%                     | 80.4%               | 96.8% | 97.3%           |
| 12        | 99.0%           | 97.9%                     | 89.6%               | 98.2% | 98.8%           |
| 13        | 99.1%           | 99.5%                     | 93.9%               | 98.7% | 99.3%           |
| 14        | 99.2%²          | 99.5%                     | 96.4%               | 99.0% | 99.6%           |

Milestones (each adds to the previous one):

1. proof-producing optimizer and tactic discharge;
2. `dite'` congruence, denormalization, synchronous kernel check, explicit Prop/Bool/`decide'` rules;
3. forall/Eq/arithmetic rule lemmas, seeded instantiation, validated steps;
4. robust discharge (runtime exceptions), relational lemmas, split strategy;
5. dependent `dite'` congruence, `dite'` propagation lemmas, arithmetic residuals;
6. residuals: user-definition unfolding with bounded case analysis;
7. nonlinear `div`/`mod` lemmas, induction for recursive-function equivalences;
8. nested recursive-function equivalences (proved bottom-up and reused);
9. well-typed tracking (casts for proof arguments and function binders), `BEq`/`decide'` lemmas;
10. existential witnesses, nonlinear residual strategies;
11. separate proof run (universe levels kept);
12. functional induction, case analysis of nested structures, `div`/`mod` facts;
13. existential elimination lemma, applied `dite` case analysis, direct fallback;
14. `match` alternatives (splitter congruence, `match cases`, fallback regions, stuck-match case analysis).

¹ More tests were measured in this run, as earlier runs aborted some test files.

² Measured against commit `deaf200` of that branch with the same harness; the row includes the match tests of
`Tests/Reconstruct/Basic.lean` and `Tests/Reconstruct/MatchEdge.lean`. On the tests of milestone 13 alone, the rates
go from 99.1% / 99.4% / 93.8% / 98.7% / 99.3% to 99.2% / 99.4% / 96.0% / 99.0% / 99.6% (3188 to 3197 of 3229
attempts), and no goal regresses. `Tests/Smt/SmtMatch.lean` goes from 69 to 74 of 74 goals, and
`Tests/Optimize/OptimizeMatch/*` from 62 to 65 of 68 certificates. Over all attempts, coarse obligations over whole
`match` applications (`frame::*match*`) go from 196 (7 unresolved) to 0, and `rule:matchReduction:*` obligations from
632 (63 unresolved) to 4. The `match`-to-`ite` normalization becomes visible as 99 `rule:normMatchExpr:*` obligations
(3 unresolved), previously hidden inside frame obligations.

Over milestones 1 to 13, the number of rewrite steps justified by an explicit lemma grew from about 1.1k to 16.6k,
and the proof obligations left to tactics dropped from 13.2k to 4.0k, the unresolved ones from 796 to 127.
Milestone 14 brought the unresolved obligations from 127 to 62.

## Appendix B. Port to `beta-lambda-cache-optimization`

Measured on branch `feat/kernel-proof-reconstruction-beta` (the port of Appendix A onto
`beta-lambda-cache-optimization`, before SMT proof replay), on that branch's test suite (3865 attempts) with a
nightly Z3:

| `#testOptimize`     | goals closed by optimizer | goals closed by SMT | all                     |
|---------------------|---------------------------|---------------------|-------------------------|
| 99.7% (3121 / 3130) | 100% (399 / 399)          | 98.8% (332 / 336)   | **99.7%** (3852 / 3865) |

Three of the SMT failures were *false* goals of `Tests/Smt/SmtUninhabited.lean` (e.g.,
`∀ (α : Type), (α → Empty) → False`), reported `Valid` because that branch did not include the fix for type variables
that may be empty yet; reconstruction correctly refused them. The remaining failures were 9 `match` normalizations
over `Int` patterns or dependent discriminants (`MatchToITE_9/10/15/20/21`, `MatchOverFun_3`, `MatchOverMatch_5`,
`MatchReduceUnchanged_6`, `NegLitSymOffset`) and one SMT residual (`Issue287`). All of them are proved on
`feat/smt-proof-replay` (Section 6.1).

## Appendix C. Earlier measurements on `feat/smt-proof-replay`

Superseded by Sections 6.1 and 6.2; kept to show the effect of individual changes.

- **Test suite, replay only.** 88.9% (248/279) of the goals closed by the SMT solver, then 99.1% (338/341) after the
  closed-statement tactics, the universe interpretation of polymorphic goals, the nonlinear lemmas and the bridge of
  normalized `match` patterns. Counting the replay attempts of `Tests/Smt` and `Tests/FixedIssues`: 283 of 297, then
  312 of 322 after the interpretation of empty types, of types used as values and of sort quantifiers under binders
  (with a nightly Z3; 311 of 323 with Z3 5.3.1, the same before and after the last review).
- **Test suite, default mode.** 99.8% (3917/3924) before the reduction of stuck matches by their equation theorems,
  the elements constructed for types without default element and the discriminant equations proved from the branch
  conditions.
- **Early replay.** A 245-step Z3 proof involving a recursive function replayed in about 6 s, and a 2458-step cvc5
  (Alethe) proof of the same goal in about 30 s.
- **First CEK replays** (`only`). The residual of `HelloWorld`, a 927-step Z3 proof, replayed in 1.8 s of step time
  (33 s before the tactics ran on closed statements), with about 26 s of reconstruction in total; `UnlockPIN` 917
  steps in 1.8 s; the `Auction` residuals 44 to 197 steps in at most 0.2 s each.
- **First `z3rec` runs.** All 20 `Governance` theorems kernel-checked in 7 to 9 minutes each (residual proofs of about
  4K steps replayed in 4.5 minutes); both `MintingPolicy` theorems in 6 minutes each (at most 7 GB); after lifting,
  `Governance` #14 in 392 s and `MintingPolicy` in 348 and 382 s.
- **`SellNFT`.** #2 kernel-checked in 53 minutes at 17.5 GB as a single declaration, before auxiliary theorems. The
  replay of #1 first failed on a `trans*` step about `(List.cons.0 List.nil)`, whose occurrences were interpreted in
  different instances by different steps; inferring the instances on the whole proof (`SortInfer.lean`: 195 hints on
  152,698 steps, in 0.15 s) fixed it. With the proofs of the replayed obligations split into auxiliary theorems too
  (`BLASTER_SMTPROOF_SPLIT=1`), #1 took 35 minutes at 11.0 GB instead of 33 minutes at 12.7 GB.

## Glossary

| term                   | meaning                                                                                 |
|------------------------|-----------------------------------------------------------------------------------------|
| binder depth           | the largest number of binders enclosing a subterm of a proof                            |
| bridge                 | the proof relating the negated goal to the SMT assertion interpreted back (Section 4.3) |
| CEK evaluation         | a goal of CardanoLedgerApiBlaster: a UPLC program evaluated by the CEK machine          |
| distinct subterms      | the size of a proof term as a DAG (shared subterms counted once)                        |
| evidence               | what the proof run records for a rewrite `e ⟶ v`: `defeq`, `proof p` or `unknown`       |
| fallback region        | a `match` congruence replaced by one coarse obligation when a finer one fails           |
| global step            | an SMT proof step whose proof does not depend on the hypotheses of an enclosing `lemma` |
| lifting                | turning global step proofs into closed terms over the goal's variables (Section 4.5)    |
| local differences      | the subterms where the two sides of a large equality differ, given to tactics           |
| match context          | the equalities between discriminants and patterns known inside a `match` alternative    |
| proof obligation       | an equality `lhs = rhs` the optimizer did not justify (a *hole*), proved afterwards     |
| proof run, verdict run | the optimization tracking proof terms; Blaster's unchanged optimization                 |
| propositional engine   | `Prop.lean`: derives propositional facts with explicit proof terms                      |
| residual goal          | the optimizer's output `G''`, closed as `True` or by the SMT solver                     |
| splitter               | Lean's case-analysis theorem for a matcher's alternatives, with overlap hypotheses      |
| universe, world        | the interpretation of `@Instance` (Section 4.4); a world injects a Lean type into it    |
