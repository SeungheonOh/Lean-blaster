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

[PlutusCoreBlaster](https://github.com/input-output-hk/PlutusCoreBlaster) (commit `c9dc0eb`) was built
against this branch. The modules using Blaster's internals (`#prep_uplc`) were left out, since they
target another Blaster branch.

- **Lemmas.** 17 statements from `PlutusCore/{Integer,List,Bitwise,Cbor}` were restated with
  `blaster_theorem` (see [`docs/examples/PlutusCoreBlaster.lean`](examples/PlutusCoreBlaster.lean)).
  14 became kernel-checked theorems that depend only on `propext`, `Classical.choice` and
  `Quot.sound`. They include `divide_add_mod`, `quotient_add_remainder`, the error cases of
  `integerToByteString` and `replicateByte_zero_l`. The other 3 (`integerToByteString_w_bounds_err`,
  `integerToByteString_neg_n`, `integerToByteString_n_bounds_err`) fail before reconstruction: Blaster's
  SMT translation rejects the structural recursion of `Nat.log2` (`translateApp: unexpected
  application`), with or without reconstruction.
- **CBOR encoding.** The 31 `encode_example_i` goals of `PlutusCore/Cbor/Tests.lean` were run with
  `#blaster (only-optimize: 1) (gen-proof: 1)`. Blaster proves 24 of them; 2 are `Undetermined` and 5
  exceed 10 minutes, with or without reconstruction. 21 of the 24 come with a kernel-checked proof.
  The remaining 3 require evaluating a well-founded recursion (`splitToChunksLoop`) on 64-character
  strings under a dependent `match`. The kernel cannot reduce such definitions efficiently, and
  `native_decide` is excluded on purpose.

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
   - case of case (`constMatchPropagation?`), a function over a match (`funPropagation?`) and a match
     applied to extra arguments (`normChoiceApplication?`), i.e., `F[match d with alts] = match d with
     (F[·] ∘ alts)`: a case split over the alternatives of the resulting match, each case being justified
     by the match equation of the pushed match (`mkMatchPushProof`);
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

## Replaying SMT proofs

Goals left to the SMT solver can also be proved by replaying a proof produced by an SMT backend,
instead of (or in addition to) re-proving them with Lean tactics. This is implemented in
`Blaster/Reconstruct/SmtProof/` and works with several backends through a common representation:

1. **Query.** The residual goal is translated again with Blaster's translation, after introducing its
   leading variables as Lean free variables, such that the SMT constants `$k` can be mapped back to them.
   The recursive Lean functions, which this branch translates with `define-fun-rec`, are encoded for the
   backends as an uninterpreted function `f`, its definition `f_LRec` and the definitional axiom
   `∀ x, f x = f_LRec x`, such that their unfoldings are quantifier instantiations. The axioms over `Nat`
   are guarded with `0 ≤ x` (this only weakens the query).
2. **Backends** (`BLASTER_SMTPROOF_BACKENDS`, `z3,z3rec,z3+` by default, e.g., `z3,cvc5`): Z3 with legacy proof
   objects (`:produce-proofs true`, `pp.simplify_implies false`); `z3rec`, Z3 on the query with its recursive
   functions defined by a `define-funs-rec` block (`RecFun.lean`: Z3's `recfun-finder` simplifier, which does the
   same, is disabled under proof production, and Z3 may then get lost in the instantiations of the definitional
   axioms; skipped when the query has no recursive function), whose `recfun` theory lemmas are replayed with exact
   proofs (unfoldings of the definitional equations, proved once per function by case analysis in the normal
   forms of Z3's rewriter, `blaster_rec_eqn`; Z3's auxiliary `fold-rec-n` functions as auxiliary definitions); the
   same as `z3` with the simplifier options of the query kept (`z3+`, e.g., `smt.macro_finder`, which may be needed
   to find a proof but gives coarser proofs); and cvc5 with Alethe proofs (`--parsing-mode=lenient`,
   `--proof-granularity=dsl-rewrite`). Proofs are produced with the random seed and the timeout of the
   theorem's solver options.
   The timeout of a backend is `BLASTER_SMTPROOF_TIMEOUT` (seconds, 20 by default). Each adapter
   translates the proof into a DAG of steps (`IR.lean`): rule, premises, arguments (e.g., quantifier
   instantiations) and conclusion (clauses as disjunctions). The Alethe adapter also serves veriT.
3. **Interpretation** (`Interp.lean`). SMT terms are interpreted as Lean terms: `Int` arithmetic on Lean
   `Int`, with casts (`↑n`, `Int.toNat`) where Lean terms of type `Nat` occur (arguments and results of
   Lean functions, constructor fields); `Bool` formulas as propositions; datatype constructors, selectors and
   testers as Lean constructors and case analyses; Blaster's function values (`@@ArrowT`, `@apply`) as Lean
   functions; Blaster's type predicates (`@isNat`, ...) as `True` (Lean values always satisfy them);
   skolem constants as `Classical.epsilon` terms.
4. **Replay** (`Replay.lean`). Each step yields a Lean proof of the interpretation of its conclusion:
   explicit proof terms for resolution (a unit propagation procedure building the proof), modus ponens,
   equality reasoning, quantifier instantiation, skolemization, hypotheses and lemmas; and small tactic
   calls (`simp`, `omega`, `grind`, unfolding of user definitions) proving `premises → conclusion` for
   rewriting and theory lemmas. Large equalities (e.g., Z3 `rewrite`s inside big formulas) are related by
   congruence on their common structure, and only their differences are given to tactics, with the
   subterms common to both sides generalized (`Local.lean`); arithmetic lemmas over large atoms are
   generalized the same way, with facts on `div`/`mod` for `omega`; nonlinear integer lemmas are proved by
   `blaster_nlarith` (`NlArith.lean`: case splits, products of hypotheses, polynomials normalized with the
   commutative ring lemmas of `grind`, then `omega` with the monomials as atoms). Tactics run on the statement of
   the step closed over the variables it mentions, in an empty local context: a step holds by itself (its
   premises are hypotheses of the statement), and the hypotheses of the context (e.g., the negated goal of a CEK
   evaluation) only slowed down `simp_all` and case analyses, by one to two orders of magnitude. The proof of
   `False` is turned into a proof of the goal and checked by the kernel like any other reconstructed proof.
5. **Bridge** (`Bridge.lean`). The asserted formula is the translation of the negated goal, interpreted
   back. It is related to the negated goal by a simultaneous traversal of both terms: congruence on their
   common structure, and a lemma for each encoding of the translation where they differ: `match` as `ite`
   chains over testers and selectors (an auxiliary theorem per matcher instance, stated for abstract
   discriminants and alternatives, and proved by evaluating the conditions with case analyses), `Nat`
   terms as `Int` terms and quantifiers over `Nat` as guarded quantifiers over `Int`, `Bool` terms as
   formulas, `dite'`/`ite`, functions translated as SMT macros (e.g., `@Nat.sub`, `@Int.toNat`, expanded by
   the backends; an auxiliary lemma per function relating it to its macro), Blaster's type predicates. The
   definitions of the other functions are bridged by tactics. The traversal is linear in the size of the
   (shared) terms, which matters for goals such as the CEK evaluation of validators.

Blaster's polymorphic encoding is interpreted in two ways. On this branch, the values of the sort variables are
values of the universal sort `@@Type` (a sort variable is an alias `@α` of `@@Type`, with a membership predicate
`@is@α`; the sort variables quantified in hypotheses are instantiated with `@@Type`), and the membership
predicates of the types over sort variables are specific to each type (e.g., `@isList._uniq.n` for `List α`,
`Fun_uniq.n` for `α → β`). With a single sort variable `α` of an inhabited type, `@@Type` is interpreted as `α` and
the membership predicates as `True`. Otherwise (several, possibly empty, sort variables; `Poly.lean`), `@@Type` is
interpreted as the always inhabited universe `Univ.{u} := Option (PSigma fun α : Sort u => α)`, values as their
injections (lifted through lists, options, pairs, functions and the inductive types of the user, whose maps to
their instances at the universe are defined with their recursors), and each membership predicate as "lies in the
image of the injection" of its type; the bridge relates the goal to the asserted formula with an additional world
for these injections. Polymorphic Lean functions instantiated at sort variables (e.g., `@List.zipWith α β γ`,
whose SMT function is shared by all their instantiations) are interpreted at the universe, such that their
definitional axioms hold on all its values, and the bridge relates their applications in the goal to their
interpretations by *naturality* lemmas proved once per function and instantiation by functional induction
(`blaster_poly_nat`). A `match` on a datatype with fields of sort variables is related to its interpretation by
case analysis on its discriminant. Naturality only holds for parametric functions: axioms and opaque functions at
sort variables, and functions with instance arguments that don't exist at the universe (e.g., `[BEq α]`), are only
interpreted with `@@Type` as the sort variable. Lambda terms of the translation (`@lambda`, `@global_lambda` with
their definitional axioms) are interpreted as Lean lambdas, with their `Nat` parameters as Lean `Nat` variables;
with the universe, they are guarded by the membership predicates of their parameters as their definitions are
(`fun x => if Img w x then b else dflt x`). Differences with the `beta-lambda-cache-optimization` port, whose
encoding has a sort of types `@Type` per universe and membership predicates parametrized by sort values: the sort
variables of a goal must live in the same universe (they share `@@Type`), the arrow sorts of functions to `Prop`
have `Bool` codomains (interpreted with the `Prop` codomains of the Lean types of the goal's constants), and goals
with universe level parameters are re-optimized as by the proof run (the optimizer normalizes the universe levels
to `1` otherwise, such that the caches of the translation would not match the goal).

The interpretation is a *choice*: a step whose conclusion does not hold for it (e.g., an axiom of a
`Nat` function instantiated with a negative integer) simply fails to replay. Soundness only relies on the
kernel. The option `(smt-proof: n)` (or, by default, the environment variable `BLASTER_SMT_PROOF`) selects
when the replay is tried for SMT residuals: `1`/`last` (default, after the tactic strategies), `2`/`first`,
`3`/`only` (no tactic strategies, to measure the replay), or `0`/`off`. `Tests/Reconstruct/SmtProof.lean`
tests the replay alone (`(smt-proof: 3)`).

### Results

On this branch, after the sync with 85e883f of `feat/smt-proof-replay`, with `BLASTER_SMT_PROOF=only` (no tactic
strategy for SMT residuals) and Z3 5.3.1, counting each replay of the 52 files of `Tests/Smt` and
`Tests/FixedIssues` with SMT residuals (`covreplay`, optimizer obligations excluded): **245 of the 272 replays
succeed** (90.1%; 240 before the sync, on the same files). The gains come from the interpretation of the inductive
types without constructors declared as uninterpreted sorts (`(declare-sort Empty 0)`), `blaster_empty_elim`, the
skolem constants of several bound variables and `str.from_code` (`Tests/Smt/SmtUninhabited.lean` 8 → 12 of 21,
`Tests/FixedIssues/CharBitVec.lean` 17 → 18 of 21), and all the 3 new goals of `Tests/Reconstruct/SmtProof.lean`
are replayed (19 of its 25 replays). The remaining failures are those described below (universes of `Issue26`,
sort quantifiers in hypotheses, class methods at several sort variables, `Issue25`), the propositions with data
fields and the constructor testers on propositions of `SmtUninhabited`, its existential sort quantifier
`∃ (α : Type), ∃ (_x : α), True` (translated on this branch as a quantifier over `@@Type`, whose interpretation the
bridge does not relate to the goal), the `Char` literals and a bit-vector lemma of `CharBitVec`, and the nonlinear
lemma of `SmtMatch.lean` (the replay deadline being 30 minutes by default now, it exceeds the measurement's timeout
per file instead of the deadline). The types used as values (`@abstractType`, `@coerce`) of the source's
translation have no counterpart in this branch's translation.

At the sync with 53dc075, on the 42 files of `Tests/Smt` and `Tests/FixedIssues` with SMT residuals (except
`SmtNatMod`, `CharBitVec` and `Issue18`; the regression tests of `SmtUninhabited` were extended since):
**199 of the 220 replays succeeded** (90.5%), and all 5 of the new soundness tests (`LambdaDefGuard`,
`InstanceArgs`). The source branch replayed 212 of 223 on its versions of the same files. Per file (target /
source):

| file | this branch | `feat/smt-proof-replay` |
|------|-------------|-------------------------|
| `Tests/Smt/SmtMatch.lean` | 72/73 | 72/73 |
| `Tests/Smt/SmtNat/SmtNatSub.lean`, `SmtNatMul`, `SmtNatDiv`, `SmtNatAdd`, `SmtNatPow` | 68/68 | 67/67 |
| `Tests/Smt/SmtEqArith.lean`, `SmtLtArith`, `SmtRecFun` | 14/14 | 13/13 |
| `Tests/Smt/SmtUninhabited.lean` | 6/8 | 8/8 |
| `Tests/Smt/SmtPredQualifier.lean` | 5/7 | 7/7 |
| `Tests/FixedIssues/Issue26.lean` | 3/8 | 8/8 |
| other `Tests/FixedIssues` files | 31/42 | 37/47 |
| `Tests/Reconstruct/SmtProof.lean` | 16/22 | 22/22 |

The differences come from this branch's polymorphic encoding: sort variables of different universes (e.g., the
universe polymorphic theorems of `Issue26` and `zipWith_map_left`: they share `@@Type`, while the source has a
sort of types per universe), hypotheses quantifying over sorts (instantiated with `@@Type`: Z3 finds no proof with
proof production for `SmtPredQualifier`, `Issue32` and the four such goals of `SmtProof.lean`), class methods at
several sort variables (no instance at the universe, `Issue29` and `SmtUninhabited`), and two goals whose
re-translation fails on this branch (`Issue3`: `UInt32.toNat c.val`, `Issue25`: a sort variable of `Sort u`). The
`z3rec` backend behaves as on the source: with `BLASTER_SMTPROOF_BACKENDS=z3rec`, 44 of the 73 goals of
`SmtMatch.lean` are replayed on both branches (the others have no recursive function), with the same `recfun`
lemmas. The optimizer's evidence for pushing functions and matches into match alternatives replaces 16 of the 98
obligations of `Tests/Reconstruct/MatchEdge.lean` (reconstruction time 12.0 s → 9.2 s).

At the sync with 9b9a511, on the same files, 110 of the 220 replays succeeded with the system Z3 4.13.3 (82 before
that sync), and 149/219 with Z3 5.3.1, in line with the source branch on the same files with Z3 5.3.1 (143/220; the test
files of both branches differ slightly). Most of the failures with Z3 4.13.3 are in `Tests/Smt/SmtMatch.lean`
(13/73, 52/73 with Z3 5.3.1): Z3 4.13.3 rewrites the definitional axioms of the derived `BEq` instances under
their binders, and these large `rewrite` steps (proved by local differences and tactics) exceed the replay
deadline (`BLASTER_SMTPROOF_DEADLINE`, 300 s by default) when the goals of a file are replayed concurrently on a
loaded machine. `Tests/Reconstruct/SmtProof.lean` replays the proofs of its 7 goals closed by the SMT solver with
Z3 5.3.1. With Z3 4.13.3, 5 of them are replayed, and the other two are proved by the direct fallback: the proof
of `x / (y + 1) ≤ x` needs a non-linear `div` lemma, and the proof of the `Option α` goal a datatype lemma over a
selector of `Option α`, whose interpretation needs an inhabitant of `α`.

On the `beta-lambda-cache-optimization` port (`feat/smt-proof-replay`, nightly Z3), the replay proves 99.1% of the
goals closed by the SMT solver on the whole test suite (338/341, at 53dc075; 310 of the 320 replays of `covreplay`
at 85e883f), and scales to the validators of
[CardanoLedgerApiBlaster](https://github.com/input-output-hk/CardanoLedgerApiBlaster), whose goals are the
evaluation of UPLC programs by the CEK machine (Z3 proofs of ≈900 steps over formulas of tens of thousands of
nodes): `HelloWorld`, `UnlockPIN`, `ParamFeed` and `Auction` are fully reconstructed with the replay only, and with
the `z3rec` backend all the 20 `Governance` theorems and both `MintingPolicy` theorems are kernel checked (residual
proofs of 4K to 31.7K steps; the proofs of the steps that don't depend on a scope are held by unassigned
metavariables during the replay and lifted at the end to closed lambda terms over the variables of the goal and the
negated goal, `liftGlobalProofs`, instead of being abstracted once per binder depth of the nested `lemma` scopes).
`SellNFT` remains open. With the default mode (`last`), the replay complements the tactic strategies.

Most steps are replayed with explicit proof terms (`unit-resolution`, `mp`, `trans`, `symm`, `monotonicity`,
`commutativity`, `quant-inst`, `lemma`/`hypothesis`, resolution of Alethe proofs) or by the propositional
engine (`def-axiom`, `not-or-elim`, `and-elim`, propositional `rewrite`s, Alethe's Tseitin rules); tactics are
used for arithmetic (`th-lemma`, arithmetic `rewrite`s: `omega`, `simp`, `grind`), with a portfolio ordered
adaptively by success rate per time unit for each rule and goal shape. Performance notes:
 - proofs of the top-level steps are held by assigned metavariables and binders are abstracted syntactically,
   such that the construction of a step does not traverse the proofs of the previous ones (it was quadratic);
 - SMT terms are interpreted once (memoization on shared terms);
 - steps that don't depend on a scope are replayed in increasing order (bounded recursion on deep proofs).
For instance, on the `beta-lambda-cache-optimization` port, a 245-step Z3 proof involving a recursive function
replays in ~6 s, and a 2458-step cvc5 (Alethe) proof of the same goal in ~30 s.

Limitations: polymorphic goals whose sort variables live in different universes, or whose hypotheses quantify
over sorts (see above); class methods and other non-parametric functions at several sort variables; cvc5's
native CPC format (whose steps often leave their conclusion implicit) is not supported; the proofs depend on
the version of Z3 (see above), and proof production may time out where the verdict did not.

## Findings

Reconstruction checks every individual rewrite, so it surfaces problems in the trusted pipeline:

- **Unsound rewrite (soundness bug).** `∀ (x : α), e ⟶ e` is applied whenever `isSortOrInhabited α`
  holds. That check returns `true` for any type variable. As a result Blaster reports
  `∀ (α : Type), (∀ (_x : α), False) → False` as `Valid`, although `α := Empty` refutes it.
  Reconstruction refuses the goal and pinpoints `(∀ (_x : α), False) = False`; see
  `Tests/Reconstruct/Unsound.lean`. The same holds for `∃ (x : α), e ⟶ e`. These refusals are counted
  separately in the coverage measurements.
- **Unguarded definitions of lambda terms (soundness bug, fixed).** The definitional axioms of lambda terms
  (`@lambda_n_def_cstr`, `@global_lambda_n_def_cstr`) constrained their applications on all the values of the
  sorts of their parameters: on this branch, the values of the universal sort `@@Type` for the parameters of sort
  variables, and the negative integers for `Nat` parameters. Function equality being translated as SMT equality,
  two lambda terms equal in Lean were equal on all the values of their sorts, which is inconsistent when they
  differ outside their domain: `∀ (α β : Type) (c : α) (b1 b2 : β), (∀ x : α, x = c) → (fun x : α => x) =
  (fun _ => c) → b1 ≠ b2 → False` and `∀ (b : Bool), (fun n : Nat => n - 1 + 1) = (fun n : Nat => if n = 0 then 1
  else n) → b = true` were reported `Valid`. The definitions are now guarded by the membership predicates of the
  parameters (`Tests/FixedIssues/LambdaDefGuard.lean`). The replay of SMT proofs could not prove these goals (the
  axioms have no model in its interpretation), which is how the bug was found on the
  `beta-lambda-cache-optimization` port. Two induction steps of `Tests/FixedIssues/Issue26.lean` are no longer
  proved by Blaster.
- **Non-canonical instances (soundness bug, fixed).** `@LT.lt α inst` (resp. `LE.le`) was taken as the relation of
  the SMT theory for `α ∈ [Nat, Int, Bool, String]` whatever `inst`, and the instance arguments of function values
  (e.g., a structure field `f [LT Nat] : Nat → Nat`) are erased by the translation. With `lt1 := ⟨(· < ·)⟩` and
  `lt2 := ⟨fun a b => b < a⟩ : LT Nat` passed explicitly, `∀ x y, @g Nat lt1 _ x y = @g Nat lt2 _ x y` (with
  `g x y := decide (x < y)`) and `∀ r x, @FunRelNat.f r lt1 x = @FunRelNat.f r lt2 x` were reported `Valid`.
  Other instances of `LT`/`LE` are now unfolded, and applications of function values are only translated when
  their instance arguments are canonical or instance-implicit binders of the goal
  (`Tests/FixedIssues/InstanceArgs.lean`; two instance-implicit binders of the same class are still not
  distinguished).
- **Issues of this branch found while porting the fixes** (not fixed):
  - a structure field polymorphic in a sort variable and applied at a type (e.g., `f [LT α] : α → α` applied at
    `Nat`) is translated with an undeclared `@apply` function (`Unexpected smt error: unknown constant
    @apply_uniq.n (@@ArrowT2 Int)`);
  - when `blaster` leaves a goal it can't prove, the goal has its universe levels normalized to `1`, which the
    kernel rejects for universe polymorphic theorems (e.g., `blaster <;> sorry`); `first | (blaster; done) | sorry`
    closes the original goal instead.
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
| + soundness fix merged, WF evaluation, residual induction, `sorryAx` checks on auxiliary declarations³ | 99.9% | 100% | 100%      | **99.9%** |                |

¹ more tests were measured in this run, as earlier runs aborted some test files.
³ 3306 of 3309 attempts; the unsound rewrite was fixed (no refused goals). The 3 failures are
`MatchToITE_9`, `_10` and `_15`.
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
- Goals proved by the SMT solver are reconstructed with Lean decision procedures and by the replay of SMT
  proofs (see above); the replay fails on polymorphic goals whose sort variables live in different universes or
  whose hypotheses quantify over sorts (Z3 does not find proofs for this branch's encoding of such hypotheses,
  instantiated with the universal sort), and on cvc5 proofs whose Alethe export contains skolems.
- Equivalences between recursive functions that need a generalized induction hypothesis or mutual
  induction still fail.
- Arithmetic (`Nat`/`Int`) constant folding and `match` normalization rules still rely on tactic
  discharge rather than explicit lemmas.
