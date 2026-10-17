# Blaster soundness & efficiency audit — `staging` @ 844622b

Scope: every module under `Blaster/` (Optimize, Optimize/Rewriting, Optimize/Lemmas, Smt, Smt/Translate,
Command, StateMachine, Logging) plus `Z3Check.lean`, Lean v4.24.0, Z3 4.13.3.

Trust model reminder: on a `Valid` result the tactic calls `goal.admit` (`Command/Tactic.lean:44`) — there is
no proof reconstruction, so every optimizer rewrite and every SMT encoding step is trusted. A soundness bug is
anything that makes Blaster report `Valid` for a statement that is false in Lean.

## Summary

* **22 independent root causes of unsoundness**, every one reproduced. In 21 of them the repro file derives
  `theorem … : False` (or `example : False`) that compiles; `#print axioms` on those shows only `sorryAx`
  (blaster's admit) plus `propext` / `Classical.choice` / `Quot.sound`. #22 is a spec/implementation mismatch
  in the state-machine layer.
* **20 of the 22 still reproduce on current `main` (585c5fc)**; 2 of those 20 (#6, #17) are only partly fixed
  there. `main` has fully fixed #10 (Int `tdiv`/`fdiv` folding, #165) and #18 (string escaping, #175), and
  narrowed #6 and #17 (sort universes, #104). `staging` is missing all of those fixes, plus #177
  (`andBoolReduction?`) and the CRLF fix.
* The single most dangerous class is **context-dependent results escaping their context through caches**
  (#1–#5): any closed sub-term simplified under a hypothesis or match branch is cached globally.
* About 20 crash / incompleteness issues and about 20 inefficiencies (several exponential) are listed below.

Repro files live in `Audit/Unsound/`, `Audit/Crash/`, `Audit/Perf/`; `Audit/Explore/` holds probes that came
out correct (kept as regression material). To run one:

```bash
lake env lean Audit/Unsound/Match_FirstWins.lean
```

## A. Confirmed unsound

Column "main?": does the repro still give a false `Valid` on `origin/main` 585c5fc.

### A.1 Optimizer: caching / scoping

| # | Root cause | Where | Repro | main? |
|---|---|---|---|---|
| 1 | **Closed terms always go to the global rewrite cache**, even when their rewrite used the current hypotheses (`andPropReduction?`, Nat/Int div rules, ITE choice) or the match-alternative context (`matchInHyps?`). The result is reused outside that scope. `isGlobal := !a.hasFVar \|\| isGlobalContext`. | `Optimize/OptimizeStack.lean:316-321`, `Optimize/Env.lean:656-667` | `Logic_GlobalCacheUnderHyp`, `OptCore_ClosedHypLeak{,2}`, `Match_GlobalCache`, `Match_GlobalCacheHyp` | yes |
| 2 | **Local instances leak through `synthInstanceCache`.** Under `∀ (_ : Inhabited Empty)`, `∀ x : Empty, False` is rewritten to `False`. Both that result and the instance-synthesis result are cached under fvar-free keys and reused outside the binder. | `Optimize/Env.lean:1116-1124` + #1 | `OptCore_LocalInstLeak` | yes |
| 3 | **Recursive-function bodies are optimized under whatever hypotheses are active** and stored in the unscoped `recFunInstCache`/`recFunMap`. With `h : 0 < x` in scope, `n / n` in the body becomes `1` for good. | `Optimize/Rewriting/OptimizeApp.lean:178-200`, `Optimize/Env.lean:1654,1676-1684` | `OptCore_RecBodyHypLeak` | yes |
| 4 | **`getInstApp` drops the arguments when only implicit/instance args are supplied**, so `@subL Int weirdSub _` and `@subL Int instSubInt _` share one cache key and one SMT function. | `Optimize/Telescope.lean:380-382` | `OptCore_InstAppCollide` | yes |
| 5 | **`storeRecFunDef.replacePred` drops non-generic implicit args of recursive calls.** `@f (!b) n` and `@g b n` normalize to the same body, so `f` and `g` are identified. | `Optimize/Env.lean:1694-1705` | `OptCore_PolyRecCall` | yes |

### A.2 Optimizer: rewrite rules

| # | Root cause | Where | Repro | main? |
|---|---|---|---|---|
| 6 | **`isSortOrInhabited` over-approximates inhabitedness.** It returns true for any type variable, function type or non-inductive (fallback `isTypeEnv`), any class type, and any indexed family with a nullary ctor (`Idx 1` with only `Idx.z : Idx 0`). The `∀ x:t, e ⇒ e` and `∃ x:t, e ⇒ e` drops built on it are unsound, e.g. `∀ α : Type, ¬ ∀ _ : α, False` gives `Valid`. | `Optimize/Rewriting/Utils.lean:60-75`, `OptimizeForAll.lean:143,154`, `OptimizeExists.lean:164` | `OptCore_ForallDrop`, `Logic_Exists` | partly: ∃ over type var / fn type fixed; `Idx`, class, ∀ cases still unsound |
| 7 | **`LT`/`LE` instance argument is never checked.** Only the carrier type (Nat/Int/…) is inspected, so `@LT.lt Nat revLT` and `@LE.le Nat ⟨fun _ _ => False⟩` get Nat semantics. The SMT side ignores the instance too. | `Optimize/Env.lean:1189-1197` (`isOpaqueRelational`), `OptimizeRelational.lean:249-276,322-342`, `OptimizePropNot.lean:39`, `Smt/Translate/Application.lean:332-338` | `Arith_CustomLTInst`, `Logic_CustomLT` | yes |
| 8 | **`structEq?` treats proofs as distinguishing.** It walks ctor args and returns `False` on different ctor names, including inside Prop fields, so `P.mk (Or.inl _) = P.mk (Or.inr _)` becomes `False`, contradicting proof irrelevance. | `Optimize/Rewriting/OptimizeEq.lean:13-45` | `Arith_StructEqProofIrrel` | yes |
| 9 | **`structEq?` compares ctor constants by pointer, levels included.** `normLevel` does not normalize `max u v` vs `max v u`, so `PUnit.unit.{max u v+1} = PUnit.unit.{max v u+1}` becomes `False`. | `OptimizeEq.lean:17-19`, `OptimizeConst.lean:17` | `Arith_StructEqLevels` | yes |
| 10 | **`Int.tdiv`/`tmod`/`fdiv`/`fmod` literals are folded with `Int.ediv`/`Int.emod`**: `Int.tdiv (-7) 2 = -4` gives `Valid`. | `Optimize/Rewriting/OptimizeInt.lean:165,249` | `Arith_TDivConst` | **fixed (#165)** |

### A.3 Pattern matching

| # | Root cause | Where | Repro | main? |
|---|---|---|---|---|
| 11 | **`matchInHyps?` ignores first-match-wins.** Inside outer alternative `n+1`, an inner `match x with \| 1 => 10 \| m+1 => 20 \| 0 => 30` is reduced to `20`, which is wrong at `x = 1`. It never checks that the earlier inner alternatives fail; `lastPatternReduction?` does. | `Optimize/Rewriting/OptimizeMatch.lean:440-451` (context built at :323-333) | `Match_FirstWins` | yes |
| 12 | **The pattern-variable list is misaligned with the alternative's binders.** A variable repeated via an inaccessible pattern (`rfl`) is collected twice, and the discriminant equation `h : x = pat` is not collected at all. Values get substituted into the wrong parameters (`k := a`; extra args pushed into `h`). | `Optimize/Rewriting/NormalizeMatch.lean:106-136` (consumers: :26-29, :511, `OptimizeMatch.lean:322-336`, `FunPropagation.lean:70-73,191-193`, `Smt/Translate/Match.lean:201-202`) | `Match_AltArgsMisalign`, `Match_DiscrEqApp` | yes |
| 13 | **`getLambdaBody` strips the alternative's own lambdas**, not just the `Unit` thunk. `fun _ => fun y => ¬y` becomes `¬#0`, and the loose bvar is then captured by the `dite'` hypothesis binder. | `NormalizeMatch.lean:26-29,561-563`; same pattern at `OptimizeMatch.lean:410,415,449`, `Smt/Translate/Match.lean:202` | `Match_FunValuedCapture` | yes |
| 14 | **`mkAppInRhs` uses `max 1 nbParams`**, which assumes a `Unit` thunk. Direct `casesOn` minors for field-less ctors have none, so extra args land one binder too deep: `(fun y z => y - z) 5` becomes `fun y => y - 5`. | `Optimize/Rewriting/FunPropagation.lean:70-73,193` | `Match_CasesOnDepth` | yes |

### A.4 SMT translation

| # | Root cause | Where | Repro | main? |
|---|---|---|---|---|
| 15 | **Empty-domain function types.** `@isFun` for `D → C` is `∀ x:D. C-pred(f x)`; SMT sorts are non-empty, so for an empty Lean `D` it becomes `false` and every `∀ f : D → C, …` is vacuous. Opaque `Empty → Empty` constants get the same unguarded axiom globally, which makes the whole context inconsistent. | `Smt/Translate/Quantifier.lean:579-585`, `Smt/Translate/Application.lean:629-655` | `Smt_EmptyFun`, `Smt_EmptyFun2` | yes |
| 16 | **Lambda definitions are not restricted to the Lean domain.** `fun n : Nat => …` becomes `∀ x:Int. apply lam x = body` with no `@isNat` guard, so SMT function equality also compares behaviour at negative Ints. `(fun n => n-1+1) ≠ (fun n => if n=0 then 1 else n)` gives `Valid`. | `Smt/Translate/Application.lean:1044-1083` (+ congruence axioms `Quantifier.lean:586-602`) | `Smt_LambdaNegDomain` | yes |
| 17 | **All type variables share one non-empty sort `@@Type`** with `@isType := true`, so facts transfer between `α` and `β` and empty types are impossible. `(∃ α : Type, ∀ _ : α, False) → ∀ β (x : β), False` gives `Valid`. | `Smt/Translate/Quantifier.lean:173-181,1244-1246`, `Smt/Env.lean:312-314` | `Smt_SortNonEmpty`, `Cmd_TypeSort` | partly: `Smt_SortNonEmpty` fixed (#104); `Cmd_TypeSort` still unsound |
| 18 | **String literals are emitted unescaped** (`"\"{s}\""`). Z3 decodes `\u{..}`, reads `""` as `"`, and counts UTF-8 bytes of non-ASCII chars. | `Smt/Term.lean:414` | `Smt_StrLit`, `Logic_StringLit` | **fixed (#175)** |
| 19 | **Instance-implicit args of function-typed variables are dropped**, both from the arrow sort and from applications: `@f ⟨0⟩ 3 = @f ⟨1⟩ 3` gives `Valid`. | `Smt/Translate/Quantifier.lean:1185`, `Smt/Translate/Application.lean:353` | `Smt_ImplicitArgDrop` | yes |
| 20 | **Class-typed binders lose their quantifier.** A nested `∀ [j : Inhabited Nat]` is hoisted to one global `declare-fun`, breaking quantifier alternation: `∃ x, ∀ [j], default ≠ x` gives `Valid`. | `Smt/Translate/Quantifier.lean:1275`, `Smt/Translate/Application.lean:948-965` | `Smt_InstQuantDrop` | yes |

### A.5 Front-end / state machine

| # | Root cause | Where | Repro | main? |
|---|---|---|---|---|
| 21 | **`findLocalAxioms` assumes every Prop axiom of the current module, including `unsafe` ones.** `unsafe axiom u : False` then `theorem t : False := by blaster` is accepted, although the kernel rejects using `u` directly. Even for safe axioms, the dependency is hidden: `#print axioms` shows only `sorryAx`. | `Optimize/Env.lean:1726-1740`; used at `Smt/Translate.lean:47`, `StateMachine/StateMachine.lean:197` | `Cmd_UnsafeAxiom` | yes |
| 22 | **BMC / k-induction semantics differ from the documented ones.** The docs say `stᵢ₊₁ = next inᵢ stᵢ` with `assumptions inᵢ stᵢ`. The code uses `stₖ = next inₖ stₖ₋₁`, so `in₀` never feeds `next` and `assumptions` constrains the post-state. `#kind` reports `Valid` for an invariant the documented machine violates (checked in Lean with `simp`). Either the code or the docs must change. | `StateMachine/BMC.lean:52-60`, `StateMachine/KInduction.lean:203-208` vs docs `BMC.lean:13-16`, `KInduction.lean:122-133` | `Cmd_SMSem` | yes |

### Suggested fix directions

* **#1–#3:** decide global-vs-local caching by whether the rewrite *consulted* context (hypotheses, match
  context, local instances), not by `hasFVar`. Simplest safe version: when `hypothesisMap`, `matchInContext`
  or the local-instance set is non-empty, cache locally. Scope `recFunInstCache`/`recFunMap` and
  `synthInstanceCache` the same way, or optimize recursive bodies in an empty context.
* **#4, #5:** key instances and recursive calls on *all* non-erased args (implicit and inst-implicit included).
* **#6:** make `isSortOrInhabited` return true only when an `Inhabited`/`Nonempty` instance is actually
  synthesized in the empty local context, or for non-indexed inductives with a nullary ctor. Never fall back
  to `isTypeEnv`.
* **#7:** check the instance argument against the canonical instance (`instLTNat`, `Int.instLTInt`, …)
  before applying any Nat/Int rule, and translate non-canonical instances as uninterpreted.
* **#8, #9:** skip Prop-typed args in `structEq?`; compare levels with `Level.isEquiv` after normalization.
* **#11:** in `matchInHyps?`, require a "does not match" fact for every earlier alternative (as
  `lastPatternReduction?` does).
* **#12–#14:** derive alternative parameters from the alternative's type (`MatcherInfo.altNumParams` /
  `forallTelescope` on the minor premise), and strip exactly the Unit thunk (only when `altNumParams = 0`
  for matchers, never for `casesOn`).
* **#15–#17:** guard every definition and quantifier by the Lean-domain predicate (`@isNat`, `@isα`), declare
  one uninterpreted sort per type variable with an uninterpreted, possibly-empty membership predicate, and
  make `@isFun` vacuous only when the domain is provably inhabited.
* **#19, #20:** keep instance-implicit binders as real arguments and quantifiers, or reject such goals.
* **#21:** skip `unsafe`/`partial` axioms; better, add assumed axioms as explicit hypotheses of the admitted
  goal (or use a dedicated axiom per run) so `#print axioms` shows them.

## B. Suspected / latent unsoundness (not exploited)

* `andBoolReduction?` returns Prop `False` instead of `Bool.false`, producing ill-typed terms
  (`OptimizeBoolBinary.lean:72`). Fixed on main (#177), not on staging. `Audit/Explore/Logic_AndBoolPropFalse.lean`.
* `define-fun-rec` parameters are unguarded Ints, so `g n := if n = 0 then 0 else g (n/2) + 1` yields the
  inconsistent `g(-1) = g(-1) + 1` (`Smt/Translate/Application.lean:507-519`). Z3 looped rather than
  returning unsat in our tests, but this is an inconsistent axiom set.
* `natModSmt` swaps its operands (`emodSmt op2 op1`, `Smt/Term.lean:338-339`). Currently unused.
* SMT symbols are quoted as `|…|` without rejecting `|` or `\` (`Smt/Syntax.lean:152-153`). `«a|b»`
  breaks the query, so a crafted name can inject SMT commands.
* Non-function axioms/opaques get no `@` prefix (`Application.lean:776`), so a user constant named `true`
  shadows the SMT literal. `@is<Type>` predicates can collide with user functions named `is<Type>`.
* `intRelLeftReduce?` returns True for `N + e < e` when `N ≤ 0`, but `N = 0` should give False
  (`OptimizeRelational.lean:27-29`). It is currently masked because `0 + e` is simplified first.
* `isGenericParam` inspects only the last arg of an application (`Env.lean:1508-1528`). `normLevel` maps
  every level param to `1` (`OptimizeConst.lean:19`), losing the `Sort 0` case. `isMatcherCache` is keyed by
  name only (`Env.lean:1329`).
* The funext axiom (fixed in 175c35d) is now sound but over-strong: its premise ranges over all SMT values,
  not only Lean-domain ones.
* String alphabet mismatch remains even after escaping: Z3 chars go up to 0x2FFFF and include surrogates,
  while Lean chars go up to 0x10FFFF and exclude surrogates.

## C. Crashes / incompleteness (no false `Valid` observed)

Repros in `Audit/Crash/`.

* `String.replace` always errors: it checks `args.size != 2` but reads `args[3]!`
  (`OptimizeString.lean:106-112`).
* `Exists p` with a non-lambda `p` gives `coiExists: lambda expression expected` (`OptimizeExists.lean:166`).
* `impliesToNeg?` has no Prop guard on the antecedent: `∀ _ : Empty, b` becomes the ill-typed `¬Empty`
  (`OptimizeForAll.lean:56-65`). The same rule would also be semantically wrong.
* Tactic: `introNP (max currQuantifiers nbQuantifiers)` miscounts when the optimizer drops unused binders,
  giving `introN failed` or the wrong names (`Command/Tactic.lean:50-51`).
* Tactic Undetermined path: `replaceTargetDefEq optExpr` installs a non-defeq target, so any later proof
  fails with a kernel type mismatch (`Command/Tactic.lean:48`). The kernel catches it, but the residual goal
  is unusable.
* Z3 EOF handling: `getOutputEval` panics on `"".get! 0` (`Smt/Env.lean:174`), and `getOutputModel` loops
  forever on EOF (`Smt/Env.lean:147-154`). Repro with the fake solver:
  `PATH=Audit/Crash/fakez3:$PATH lake env lean Audit/Crash/Cmd_FakeZ3.lean`.
* Matches:
  * `match h : x with` on symbolic `x` leaves an ill-typed lambda in the else branch
    (`Inductive datatype … not supported: Eq`).
  * Repeated pattern vars cause an index OOB panic at `OptimizeMatch.lean:336`.
  * Char/Fin/UInt8 literal patterns fail with `mkCstLet: unexpected pattern expression`
    (`NormalizeMatch.lean:245`).
  * Matching on `Decidable` fails.
  * Function-valued matches yield ill-typed terms or Z3 sort errors.
  * `commonRhs?` returns `7` for an all-`fun _ => 7` match (`OptimizeMatch.lean:410-416`).
* SMT:
  * Empty user inductives fail ("does not have any constructors"), and so do non-well-founded ones.
  * `Fin`/`Subtype` are rejected.
  * Implicit Nat args of function variables crash `translateType`.
  * Recursive fns with an implicit arg instantiated by a goal fvar crash with
    `translateRecFun: function body expected`.
* Two `@apply_uniq.N` symbols get declared for the same arrow sort, so higher-order goals such as
  `List.foldl Nat.add 0 l = List.foldl (·+·) 0 l` are wrongly Falsified (`Crash/Arith_HOF*.lean`).
* A lambda such as `fun n : Nat => n+1` fails `@isFun` because it is evaluated at negative Ints, so it cannot
  instantiate `∀ f : Nat → Nat` hypotheses.
* Options and state machine:
  * The `unfold-depth` option is parsed but never read anywhere (`Command/Options.lean:29`).
  * The minimum Z3 version is never checked (`Smt/Env.lean:78-98`).
  * `solve-result` is ignored by `logNoCexAtDepth`/`logUndeterminedAtDepth` (`StateMachine.lean:110-116`).
  * `random-seed: 0` means "no seed".
  * `IO.setNumHeartbeats 0` resets the heartbeat budget of the surrounding declaration (`Tactic.lean:41`).

## D. Inefficiencies

Measured ones carry numbers; repros in `Audit/Perf/`.

| Where | Issue | Evidence |
|---|---|---|
| `Optimize/Env.lean:1728` `findLocalAxioms` | Converts the whole environment (~140k constants with core only) to a list on every call. Iterate `env.constants.map₂` (current module) instead. | 63 ms per call; about 70% of a trivial `blaster` call; grows with imports |
| `OptimizePropBinary.lean:271-276` `optimizeIff` | `p ↔ q` becomes `(p→q) ∧ (q→p)`, duplicating both sides | nested depth 8/12/16: 0.08 s / 0.54 s / 7.9 s |
| `OptimizeEq.lean:13-45` `structEq?` | Unmemoized recursion over shared ctor DAGs | depth 16/20/22: 0.7 s / 10.6 s / 41.7 s (control 0.05 s) |
| `FunPropagation.lean:127-215`, `OptimizeMatch.lean:189-265` | Each ite/match-valued arg copies the whole application into every branch (2ⁿ) | n=8/12/14/16: 1.2 s / 6 s / 22 s / 88 s |
| `StateMachine/BMC.lean:60`, `KInduction.lean:206` | States are inlined as growing terms instead of fresh SMT constants per step | query bytes at depth 2/4/6/8: 1.6K / 7.4K / 53K / 596K; time 1.1 s → 18.2 s |
| `Logging/Basic.lean:24-29` | `logSmtQuery` reprints every accumulated command at each depth (quadratic) | — |
| `Optimize/Env.lean:1489-1501` `getFVarsInExpr` | No visited set (exponential on DAGs); re-infers fvar types at every occurrence | — |
| `OptimizeStack.lean:72,86` | Local rewrite cache wiped per hypothesis scope / match alternative | — |
| `OptimizeMatch.lean:317-319,322,329,400-489` | O(m²) per match: `getMatchAlts`/`retrieveAltsArgs` recomputed per alternative; `elimMatch?` has no early exit on an empty context | — |
| `Optimize/Env.lean:1692-1693,1508,1560` | `replacePred` is quadratic; `isGenericParam` is not memoized; a `getFVarLocalDecl` result is discarded | — |
| `Rewriting/Utils.lean:623-633` `hasSorryTheorem` | Re-scans shared lemma proofs with no global visited set | suspected |
| `Smt/Translate/Quantifier.lean:586-602` | `congr_fun`/`congr_args` axioms restate built-in congruence and add instantiation load | — |
| `Smt/Env.lean:84,104-110,207-216,536-538,662` | `z3 -version` spawned per call; stderr piped but never read (deadlock risk); one round trip per command; 20 ms polling; `:produce-proofs true` though proofs are never requested | — |
| `Smt/Syntax.lean:159-300`, `getOutputModel` | Quadratic string building via repeated `++` | — |
| `Command/Tactic.lean:38-41`, `Telescope.lean:176` | `maxHeartbeats := 0` + heartbeat resets, so non-terminating optimizer loops cannot be interrupted | — |
| `Optimize/Basic.lean:197-205` | Dead duplicate of `hasUnOptMatchInfo?` | — |

## E. Checked and found correct

* All `Lemmas/**` and `Decidable.lean` are proven (no `sorry`/`axiom`).
* Nat add/sub/mul/div/mod/pow rules (truncated sub, `x/0`, `x%0`), Eq cancellations, Int neg/toNat/negSucc,
  relational normalizations, and operand reordering (no loops).
* Non-lawful `BEq` is handled, as are user `HAdd`/`OfNat`/`Neg`/`Max`/`Min` instances.
* Match patterns: overlapping Nat/Int/String/Option/Prod/List patterns, `n+k`, named patterns; ITE guards
  respect first-match-wins (the bug is only in `matchInHyps?`).
* Hypothesis reverting (let/have, instance-implicit, dependent, shadowed); mvars in the goal are rejected;
  `partial` defs are rejected; opaque constants stay uninterpreted.
* The k-induction encoding is otherwise correct (base cases, step case, contradiction check).
* Garbled or crashed Z3 output never turned into `Valid`.
