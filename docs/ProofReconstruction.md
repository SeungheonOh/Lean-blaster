# Proof reconstruction

Blaster decides goals by (1) aggressively rewriting the Lean goal with its optimizer and (2) sending
whatever remains to an SMT solver. Without reconstruction, a `Valid` verdict trusts both steps: the
`blaster` tactic closes the goal with `admit`.

Proof reconstruction moves proof checking back to the **Lean kernel**. For a `Valid` verdict, Blaster
builds an ordinary proof term for the original goal and checks it with the kernel. The verdict is
then reported as kernel-checked, and the tactic closes the goal with that term instead of `admit`.

```lean
#blaster (reconstruct: 1) [∀ (x y : Nat), x < y → x + 1 ≤ y]
-- ✅ Valid
-- 🔒 Kernel-checked proof reconstructed

theorem t : ∀ (a b : Prop), a ∧ b → a := by blaster (reconstruct: 2)
#print axioms t   -- 't' depends on axioms: [propext, Quot.sound]
```

## Options

| option             | meaning                                                                                 |
|--------------------|-----------------------------------------------------------------------------------------|
| `(reconstruct: 0)` | default; no reconstruction (previous behavior)                                          |
| `(reconstruct: 1)` | best effort; a warning is reported when reconstruction fails and the result is trusted  |
| `(reconstruct: 2)` | required; an error is reported when reconstruction fails                                |
| `(gen-proof: 1)`   | proof generation; implies `(reconstruct: 2)` and checks the axioms of the proof (below) |

The environment variable `BLASTER_RECONSTRUCT=<n>` sets the default level for every `#blaster`
command and `blaster` tactic. Options given explicitly take precedence. Use `(verbose: 1)` to see
statistics for each reconstruction.

## Generating proofs

`blaster_theorem` proves a statement with Blaster and adds it to the environment as an ordinary
theorem whose proof term was checked by the kernel:

```lean
blaster_theorem lt_succ_le : ∀ (x y : Nat), x < y → x + 1 ≤ y
-- ✅ Valid
-- 📜 Theorem lt_succ_le generated (kernel-checked, axioms: [propext, Classical.choice, Quot.sound], ...)

#print axioms lt_succ_le   -- 'lt_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]

theorem foo : ∀ (a b : Prop), a ∧ b → a := by blaster (gen-proof: 1)
```

A generated proof never depends on `sorryAx` or `Lean.ofReduceBool` (`native_decide`). Proof generation
fails if the proof term depends on any axiom other than Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and the local axioms of the module used as hypotheses by Blaster.
`Classical.choice` comes from `Blaster.dite'`, Blaster's classical encoding of `if-then-else`, and from
Lean's decision procedures.

The generated theorems are stored in the module's `.olean` file like any other theorem, so they can be
re-checked independently of Blaster (e.g., with `lean4checker`). Blaster's own definitions
(`Blaster.dite'`, `Blaster.decide'`, the lemmas of `Blaster/Reconstruct/Lemmas.lean`) occur in the proof
terms, but they are ordinary, kernel-checked definitions and theorems. Neither the optimizer nor the SMT
solver is trusted.

## Real-world examples: PlutusCoreBlaster

[PlutusCoreBlaster](https://github.com/input-output-hk/PlutusCoreBlaster) (commit `c9dc0eb`) pins the
`beta-lambda-cache-optimization` branch of Blaster. It was built against this port of proof
reconstruction onto that branch (with a nightly Z3 providing `recfun-finder`, as required by the branch).

- **CBOR encoding.** All 31 `encode_example_i` goals of `PlutusCore/Cbor/Tests.lean` become
  kernel-checked theorems with `blaster_theorem` (see
  [`docs/examples/PlutusCoreCbor.lean`](examples/PlutusCoreCbor.lean)). They only depend on `propext`,
  `Classical.choice` and `Quot.sound`; upstream checks them with `native_decide` or with an unchecked
  `#blaster`. Running `PlutusCore/Cbor/Tests.lean` unchanged with `BLASTER_RECONSTRUCT=1` also
  reconstructs a kernel-checked proof for each of its 33 `#blaster` commands and `blaster` tactics
  (the 3 expected counterexamples need no proof). The examples splitting long strings evaluate the
  well-founded recursion `splitToChunksLoop` by unfolding its equation lemmas (`blaster_wf_eval`),
  since the kernel can't reduce well-founded recursion efficiently.
- **Lemmas.** 17 statements from `PlutusCore/{Integer,List,Bitwise,Cbor}` were restated with
  `blaster_theorem` (see [`docs/examples/PlutusCoreBlaster.lean`](examples/PlutusCoreBlaster.lean)).
  14 become kernel-checked theorems, including `divide_add_mod`, `quotient_add_remainder`, the error
  cases of `integerToByteString` and `replicateByte_zero_l`. The other 3
  (`integerToByteString_w_bounds_err`, `integerToByteString_neg_n`,
  `integerToByteString_n_bounds_err`) fail before reconstruction: Blaster's SMT translation rejects
  `Nat.log2`, which core defines directly with `Nat.rec` (`translateApp: unexpected application`).

## How it works

```
 G  ──(local axioms)──▶  G'  ──optimizer──▶  G''  ──(True | SMT)──▶  Valid
                          │      pf : G' = G''      │
                          ▼                          ▼
              proof of G  ◀── Eq.mpr pf r ◀── r : G''   (kernel-checked)
```

0. **Verdict run and proof run.** The verdict (`Valid`, `Falsified`, ...) always comes from Blaster's
   unchanged pipeline. Only for a `Valid` verdict, the goal is optimized a second time while tracking
   proof terms (the *proof run*). The proof run differs from the verdict run in a few places where the
   optimizer's output is not a valid Lean term. Universe levels are kept instead of being normalized,
   and some rewritten binder types are kept (see Findings). As a result, reconstruction never changes
   Blaster's verdicts.

1. **Proof-producing optimizer.** The optimizer is a stack machine (`Optimize/Basic.lean`,
   `Optimize/OptimizeStack.lean`). Every frame that waits for the optimized form `v` of an
   expression `e` also receives *evidence* `EqPf` that `e = v` (`Reconstruct/Types.lean`):
   - `defeq`: `e` and `v` are definitionally equal (beta, delta of non-recursive definitions,
     iota, zeta, eta, mdata, projections). No proof term is needed.
   - `proof p`: an explicit proof term `p : e = v`.
   - `unknown`: no evidence. It is turned into a *proof obligation* (hole) at the nearest frame
     boundary, where both `e` and `v` are known.

   Evidence is composed by transitivity and congruence: `congrArg`, `congrFun`, `funext`,
   `forall_congr`, `implies_congr_ctx` and `implies_dep_congr_ctx`. Hypothesis-dependent rewrites
   inside an implication `a → b` stay valid because the body's evidence is abstracted over the
   hypothesis. Arguments with forward dependencies, such as the condition of `Blaster.dite'`, are
   handled by dedicated congruence lemmas (`dite'_congr`). Rewrites served from the optimizer's
   cache reuse the cached evidence after a scope check.

   `match` alternatives are optimized under a *match context*: fvar patterns are replaced by their
   discriminants, and nested matches on the same discriminants are eliminated. When tracking proof
   terms, the equalities `h : dⱼ = pⱼ` between the discriminants and the patterns of the alternative
   are declared in the local context (`optimizeMatchAlt`). The evidence for an alternative is then
   `p : ∀ args h₁ ... hₙ, alt args = alt' args` (`EqPf.matchAlt`). Once all the alternatives are
   optimized, the evidence is combined by a case split over the matcher's *splitter*
   (`Reconstruct/Match.lean`, `mkMatchCongr`). The splitter is applied to the motive
   `fun xs => (d = xs) → match xs with alts = match xs with alts'`, and each case is closed with
   the match equations (or by iota for `casesOn`). Unreachable alternatives (e.g., wildcard
   alternatives of a match over structures) are closed from the splitter's overlap hypotheses.

2. **Rule certificates.** Each rewriting rule can record the lemma that justifies it:
   `withThm lhs rhs thm args`, or `withHypThm` when the rule relies on a hypothesis. The stack machine
   collects the recorded steps after each rule application and chains them (`ruleStep`). Any gap
   becomes a typed proof obligation `lhs = rhs`, so rules can be instrumented one at a time.
   Rules currently instrumented: propositional connectives, Boolean operators, `decide'`, `BEq`,
   equality, quantifiers/implications, existentials, commutativity normalization, cancellation under
   non-zero hypotheses, `dite'` propagation, and opaque-constant normalization (`ite`, `dite`,
   `decide`, `Nat.succ`, ...). The lemmas live in `Reconstruct/Lemmas.lean`.
   The `match` rules are justified as follows:
   - `matchReduction` on constructor discriminants: definitional (iota);
   - `matchReduction` pushing a match over `Blaster.dite'` (`constMatchPropagation?`): `apply_dite'`;
   - `elimMatch` with a common rhs: a case split over the splitter with `rfl` in each case;
   - `elimMatch` with the match context (`matchInHyps?`): the discriminants are rewritten with the
     equalities `h : dⱼ = pⱼ` of the enclosing alternative, then the match is reduced.

3. **Discharging proof obligations** (`Reconstruct/Discharge.lean`). Each obligation is
   type-checked, then attempted in its own local context, with every binder and hypothesis of the
   rewrite available. The portfolio, in order:
   1. definitional equality (`rfl`), and `decide +kernel` for closed obligations;
   2. `simp [*]`, `omega`, `grind`;
   3. cancellation of non-zero divisors (`simp` with `omega` as discharger);
   4. case analysis: `split`, case analysis on the conditions of applied `dite`s, cancellation of
      non-zero factors;
   5. case analysis on the variables of inductive types and their constructor fields, unfolding
      user definitions and instances (e.g., derived `BEq` instances);
   6. induction for equivalences between recursive functions (`blaster_funind`): functional induction
      following one of the functions of the equation, or structural induction on one variable;
   7. a deeper case analysis with a larger budget.
   8. `match cases`: for an obligation `match ds with alts = rhs`, a case split over the
      matcher's splitter, where the discriminants are replaced by the patterns in `rhs`. Each case is
      discharged recursively with the portfolio, with the pattern equalities and the overlap
      hypotheses in the local context.

   Obligations are closed terms, but their proofs may use the hypotheses of their local context
   (e.g., `simp [*]` with the pattern equalities). The same obligation can occur under different
   binders, for example when a proof is reused through the proof cache. It is therefore discharged
   once per binder scope (`transformScoped`), not once per term as `Meta.transform` would do.

   The congruence over a `match` application is a *fallback region*. If one of the obligations of its
   alternatives cannot be discharged, the whole region is replaced by the coarse obligation
   `match ds with alts = match ds with alts'`. Finer evidence therefore never loses a goal that the
   coarse obligation could prove. This matters when an alternative contains ill-typed intermediate
   rewrites (see below).

   Each attempt has a heartbeat budget, and failed attempts leave no trace (state, messages and info
   trees are restored). Blaster's internal forms (`Nat.add`, `Blaster.dite'`, `Nat.beq`, ...) are first
   rewritten back to standard notation (`blaster_denorm`).

4. **Residual goal.** If the optimizer reduced the goal to `True`, the residual proof is
   `True.intro`. If the SMT solver proved the residual goal, Lean decision procedures re-prove it:
   `decide`, `simp`, `omega`, `grind`, seeded instantiation of quantified hypotheses
   (`blaster_inst_hyps`), unfolding of user definitions with case analysis, unfolding of recursive
   functions (`blaster_lit_add` first puts `k + n` in the form `n + k` expected by equation lemmas), case
   analysis on `match` expressions, witness search for existentials, and `div`/`mod` facts
   (`blaster_divmod_facts`) with non-linear lemmas. Replaying the solver's own proof certificate is
   future work.

5. **Kernel check.** The proof of the original goal is `Eq.mpr pf r`, applied to the local axioms.
   It is checked synchronously by the kernel (`Kernel.Environment.addDecl`). Only kernel-accepted
   proofs are reported as reconstructed or used to close tactic goals.

6. **Direct fallback.** If the steps above fail, the decision procedures of step 4 are tried on the
   original goal itself (e.g., `rfl` or `decide +kernel` for closed computations).

When tracking is off (`reconstruct: 0`), the proof run is skipped, so the optimizer's behavior and cost
are unchanged.

## Findings

Reconstruction checks every individual rewrite, so it surfaces problems in the trusted pipeline:

- **Unsound rewrite (soundness bug).** `∀ (x : α), e ⟶ e` is applied whenever `isSortOrInhabited α`
  holds. That check returns `true` for any type variable. As a result Blaster reports
  `∀ (α : Type), (∀ (_x : α), False) → False` as `Valid`, although `α := Empty` refutes it.
  Reconstruction refuses the goal and pinpoints `(∀ (_x : α), False) = False`; see
  `Tests/Reconstruct/Unsound.lean`. The same holds for `∃ (x : α), e ⟶ e`. These refusals are counted
  separately in the coverage measurements.
- **Ill-typed optimizer output.** The proof run avoids the following issues; the verdict run is unchanged.
  - The else branch of `Blaster.dite'` received the *normalized* type of `¬ c` (e.g. `false = c`
    instead of `¬ (true = c)`), so `dite'` applications were ill-typed. When tracking proofs, the
    branch binder now keeps type `¬ c` while the normalized form is still used as the hypothesis.
  - `andBoolReduction?` returned the proposition `False` for a Boolean `&&`; this is fixed.
  - `isCstImplies?` substitutes `True.intro` for a hypothesis whose type was simplified to `True`.
    This yields ill-typed terms such as `Char.ofNatAux 84 True.intro`. When tracking proofs, proof
    arguments are not rewritten.
  - Universe levels are normalized to `1` (`normLevel`), so goals over `Sort u` are rewritten to
    goals over `Type`, and `Blaster.dite'` is always built at level `1`. This includes unassigned *or
    uninstantiated* level metavariables; for example, `#testOptimize` passes terms with assigned but
    uninstantiated level metavariables. The proof run keeps the universe levels.
  - The `dite'` branch-swap rule (`isITESwap?`) produced a then-branch of type `¬¬c → α` instead of
    `c → α`. When tracking proofs, the branches are now retyped.
  - Rewriting the domain of quantified *function* variables (e.g. `f : c = true → α` to
    `f : true = c → α`) leaves their dependent uses ill-typed. When tracking proofs, functions over
    proofs keep their original type.

## Measuring coverage

```
./scripts/recon_coverage.sh stats.jsonl 8
```

This runs every test file with `BLASTER_RECONSTRUCT=1`. Each `#testOptimize` case is also audited
for a kernel-checked proof of `e = optimize(e)`. The audit runs after the test's own check, and it
optimizes with a dedicated name-generator prefix. Otherwise names created while building proof
terms could clash with those created during reconstruction. One JSON line per attempt is written, and
`scripts/recon_report.py` summarizes the results. The summary covers success rates per category,
discharge methods, failure reasons, and proof obligations per rewrite site. The rewrite-site
breakdown is the to-do list for further rule instrumentation.

## Coverage history

Measured with `scripts/recon_coverage.sh` on the full test suite. Each row adds one milestone; percentages
are the fraction of attempts producing a kernel-checked proof. The last column excludes the goals refused
because of the unsound rewrite above (18 attempts).

| milestone                                            | `#testOptimize` certificates | goals closed by optimizer | goals closed by SMT | all   | all except unsound |
|------------------------------------------------------|------------------------------|---------------------------|---------------------|-------|--------------------|
| proof-producing optimizer + tactic discharge         | 85.7%                        | 77.1%                     | 36.7%               | 82.4% |                    |
| + `dite'` congruence, denormalization, sync kernel check, explicit Prop/Bool/`decide'` rules | 91.4% | 84.4% | 33.3%¹ | 87.0% |  |
| + forall/Eq/arith rule lemmas, seeded instantiation, validated steps | 90.9%¹       | 92.0%                     | 39.8%               | 87.4% |                    |
| + robust discharge (runtime exceptions), relational lemmas, split strategy | 92.8%  | 92.0%                     | 39.8%               | 89.0% |                    |
| + dependent `dite'` congruence, `dite'` propagation lemmas, arithmetic residuals | 92.9% | 92.0%                | 44.2%               | 89.5% |                    |
| + residual: user-definition unfolding with bounded case analysis | 92.9%                  | 92.0%                     | 65.5%               | 91.0% |                    |
| + non-linear `div`/`mod` lemmas, induction for recursive-function equivalences | 95.1%  | 93.1%                     | 70.9%               | 93.3% |                    |
| + nested recursive-function equivalences (proved bottom-up and reused) | 95.4%           | 93.2%                     | 70.9%               | 93.5% |                    |
| + well-typed tracking (casts for proof arguments and function binders), `BEq`/`decide'` lemmas | 98.3% | 93.8%       | 71.1%               | 96.1% | 96.6%              |
| + existential witnesses, non-linear residual strategies | 98.4%                        | 93.8%                     | 78.5%               | 96.7% | 97.3%              |
| + separate proof run (universe levels kept)           | 98.4%                        | 93.2%                     | 80.4%               | 96.8% | 97.3%              |
| + functional induction, case analysis of nested structures, `div`/`mod` facts | 99.0%  | 97.9%                     | 89.6%               | 98.2% | 98.8%              |
| + existential elimination lemma, applied `dite` case analysis, direct fallback | 99.1% | 99.5%                     | 93.9%               | 98.7% | **99.3%**          |
| + `match` alternatives (splitter congruence, `match cases`, fallback regions, stuck-match case analysis) | 99.2%² | 99.5% | 96.4%        | 99.0% | **99.6%**          |

¹ more tests were measured in this run, as earlier runs aborted some test files.
² measured against `deaf200` with the same harness. The row includes the match tests of
`Tests/Reconstruct/Basic.lean` and `Tests/Reconstruct/MatchEdge.lean`. Excluding them, the rates go from
99.1% / 99.4% / 93.8% / 98.7% / 99.3% to 99.2% / 99.4% / 96.0% / 99.0% / 99.6% (3188 to 3197 of 3229 attempts),
and no goal regresses. `Tests/Smt/SmtMatch.lean` goes from 69 to 74 of 74 goals and
`Tests/Optimize/OptimizeMatch/*` from 62 to 65 of 68 certificates. Unresolved obligations drop from 127 to 62.
Over all attempts, `frame::*match*` obligations (coarse obligations over whole `match` applications) go
from 196 (7 unresolved) to 0, and `rule:matchReduction:*` obligations from 632 (63 unresolved) to 4.
`elimMatch` no longer leaves obligations. The `match`-to-`ite` normalization is now visible as
99 `rule:normMatchExpr:*` obligations (3 unresolved); these were previously hidden inside frame obligations.

Over the same milestones, the number of rewrite steps justified by an explicit lemma grew from about 1.1k
to 16.6k. Proof obligations left to tactics dropped from 13.2k to 4.0k, of which only 127 remain
unresolved (down from 796).

## Current limitations / next steps

- The remaining failures (14 of 3267 attempts, excluding refused unsound eliminations) fall into a few classes:
  - `match` expressions over `Int` literal patterns with many alternatives (`MatchToITE_9`, `_10`,
    `_15`): the `normMatchExpr` obligation (a 15-alternative match against its `dite'` chain) is
    beyond the budget of the case analysis on stuck matches, and the matcher's splitter cannot be
    generated;
  - residual goals of the SMT solver over polymorphic or uninterpreted functions with quantified
    hypotheses (`Issue15`, `Issue25`, `Issue32`, `SmtPredQualifier`), which need quantifier
    instantiations from the solver;
  - non-linear residuals (`SmtNatDiv`), and one kernel
    rejection (`DIteFalseEqCond_17`, a `dite` whose condition is rewritten without its
    `Decidable` instance).
- `match` rules that rely on the *negative* match context (`lastPatternReduction?`, i.e., the
  discriminant does not match the patterns of the previous alternatives) are not justified
  explicitly yet. The overlap hypotheses of the splitter could be declared in the alternative's local
  context, like the pattern equalities. Matches normalized to `ite` (`normMatchExpr?`) rely on the
  `match cases` discharge.
- Match equations and splitters are generated by Lean on demand (`Match.getEquationsFor`). For
  matchers with many overlapping patterns, the generation can exceed Lean's fixed heartbeat
  budget. These matchers fall back to coarse obligations.
- Goals proved by the SMT solver rely on Lean decision procedures. The next step is to replay Z3
  proofs, or at least use unsat cores and quantifier instantiations from Z3 as hints.
- Equivalences between recursive functions that need a generalized induction hypothesis or mutual
  induction still fail.
- Arithmetic (`Nat`/`Int`) constant folding and `match` normalization rules still rely on tactic
  discharge rather than explicit lemmas.
