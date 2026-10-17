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

The environment variable `BLASTER_RECONSTRUCT=<n>` sets the default level for every `#blaster`
command and `blaster` tactic. Options given explicitly take precedence. Use `(verbose: 1)` to see
statistics for each reconstruction.

## How it works

```
 G  ──(local axioms)──▶  G'  ──optimizer──▶  G''  ──(True | SMT)──▶  Valid
                          │      pf : G' = G''      │
                          ▼                          ▼
              proof of G  ◀── Eq.mpr pf r ◀── r : G''   (kernel-checked)
```

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

2. **Rule certificates.** Each rewriting rule can record the lemma that justifies it:
   `withThm lhs rhs thm args`, or `withHypThm` when the rule relies on a hypothesis. The stack machine
   collects the recorded steps after each rule application and chains them (`ruleStep`). Any gap
   becomes a typed proof obligation `lhs = rhs`, so rules can be instrumented one at a time.
   Rules currently instrumented: propositional connectives, Boolean operators, `decide'`, equality,
   quantifiers/implications, commutativity normalization, and opaque-constant normalization
   (`ite`, `dite`, `decide`, `Nat.succ`, ...). The lemmas live in `Reconstruct/Lemmas.lean`.

3. **Discharging proof obligations** (`Reconstruct/Discharge.lean`). Each obligation is
   type-checked, then attempted in its own local context, with every binder and hypothesis of the
   rewrite available. The portfolio, in order:
   1. definitional equality (`rfl`);
   2. `simp [*]`;
   3. `omega`;
   4. `grind`.

   Each attempt has a heartbeat budget. Blaster's internal forms (`Nat.add`, `Blaster.dite'`, ...)
   are first rewritten back to standard notation (`blaster_denorm`).

4. **Residual goal.** If the optimizer reduced the goal to `True`, the residual proof is
   `True.intro`. If the SMT solver proved the residual goal, Lean decision procedures re-prove it:
   `decide`, `simp`, `omega`, `grind`, and seeded instantiation of quantified hypotheses
   (`blaster_inst_hyps`). Replaying the solver's own proof certificate is future work.

5. **Kernel check.** The proof of the original goal is `Eq.mpr pf r`, applied to the local axioms.
   It is checked synchronously by the kernel (`Kernel.Environment.addDecl`). Only kernel-accepted
   proofs are reported as reconstructed or used to close tactic goals.

When tracking is off (`reconstruct: 0`), all evidence is `unknown` and no proof terms are built, so
the optimizer's behavior and cost are unchanged.

## Findings

Reconstruction checks every individual rewrite, so it surfaces problems in the trusted pipeline:

- **Unsound rewrite (soundness bug).** `∀ (x : α), e ⟶ e` is applied whenever `isSortOrInhabited α`
  holds. That check returns `true` for any type variable. As a result Blaster reports
  `∀ (α : Type), (∀ (_x : α), False) → False` as `Valid`, although `α := Empty` refutes it.
  Reconstruction refuses the goal and pinpoints `(∀ (_x : α), False) = False`; see
  `Tests/Reconstruct/Unsound.lean`.
- **Ill-typed optimizer output.**
  - The else branch of `Blaster.dite'` received the *normalized* type of `¬ c` (e.g. `false = c`
    instead of `¬ (true = c)`), so `dite'` applications were ill-typed. When tracking proofs, the
    branch binder now keeps type `¬ c` while the normalized form is still used as the hypothesis.
  - `andBoolReduction?` returned the proposition `False` for a Boolean `&&`; this is fixed.
  - `isCstImplies?` substitutes `True.intro` for a hypothesis whose type was simplified to `True`.
    This yields ill-typed terms such as `Char.ofNatAux 84 True.intro`.
  - Universe levels are normalized to `1` (`normLevel`), so goals over `Sort u` are rewritten to
    goals over `Type`. This includes unassigned *or uninstantiated* level metavariables; for example,
    `#testOptimize` passes terms with assigned but uninstantiated level metavariables.
  - The `dite'` branch-swap rule (`isITESwap?`) produced a then-branch of type `¬¬c → α` instead of
    `c → α`. When tracking proofs, the branches are now retyped.
  - Rewriting the domain of quantified *function* variables (e.g. `f : c = true → α` to
    `f : true = c → α`) leaves their dependent uses ill-typed. Reconstruction currently fails on these.

## Measuring coverage

```
./scripts/recon_coverage.sh stats.jsonl 8
```

This runs every test file with `BLASTER_RECONSTRUCT=1`. Each `#testOptimize` case is also audited
for a kernel-checked proof of `e = optimize(e)`. One JSON line per attempt is written, and
`scripts/recon_report.py` summarizes the results. The summary covers success rates per category,
discharge methods, failure reasons, and proof obligations per rewrite site. The rewrite-site
breakdown is the to-do list for further rule instrumentation.

## Coverage history

Measured with `scripts/recon_coverage.sh` on the full test suite. Each row adds one milestone; percentages
are the fraction of attempts producing a kernel-checked proof.

| milestone                                            | `#testOptimize` certificates | goals closed by optimizer | goals closed by SMT | all   |
|------------------------------------------------------|------------------------------|---------------------------|---------------------|-------|
| proof-producing optimizer + tactic discharge         | 85.7%                        | 77.1%                     | 36.7%               | 82.4% |
| + `dite'` congruence, denormalization, sync kernel check, explicit Prop/Bool/`decide'` rules | 91.4% | 84.4% | 33.3%¹ | 87.0% |
| + forall/Eq/arith rule lemmas, seeded instantiation, validated steps | 90.9%¹       | 92.0%                     | 39.8%               | 87.4% |
| + robust discharge (runtime exceptions), relational lemmas, split strategy | 92.8%  | 92.0%                     | 39.8%               | 89.0% |
| + dependent `dite'` congruence, `dite'` propagation lemmas, arithmetic residuals | 92.9% | 92.0%                | 44.2%               | 89.5% |
| + residual: user-definition unfolding with bounded case analysis | 92.9%                  | 92.0%                     | 65.5%               | 91.0% |
| + non-linear `div`/`mod` lemmas, induction for recursive-function equivalences | 95.1%  | 93.1%                     | 70.9%               | 93.3% |
| + nested recursive-function equivalences (proved bottom-up and reused) | 95.4%           | 93.2%                     | 70.9%               | 93.5% |

¹ more tests were measured in this run, as earlier runs aborted some test files.

Over the same milestones, the number of rewrite steps justified by an explicit lemma grew from about 1.1k
to 16.0k. Proof obligations left to tactics dropped from 13.2k to 4.5k, of which only 419 remain
unresolved (down from 796; 410 after the nested-equivalence work). The extended `div`/`mod`
lemma set then raised the `Tests/Smt/SmtNat` goals further, from 95 to 107 of 132.

## Current limitations / next steps

- `match` alternatives optimized under a pattern context (`MatchAltWaitForExpr`) produce coarse
  obligations at the match level. The next step is to support them through the matcher's splitter
  and equation lemmas.
- Rewrites of recursive functions into structurally equivalent ones (`storeRecFunDef`) are justified
  by `blaster_funind`, which applies function extensionality and then induction on one argument.
  The optimizer records every equivalence it establishes, including those found while optimizing other
  function bodies. Reconstruction proves them bottom-up, each one using the previous ones as
  hypotheses. Equivalences that need a generalized induction hypothesis or mutual induction still fail.
- Quantified *functions* whose domain is a proposition (e.g. `∀ f : (c = true → α), …`) block
  reconstruction once the optimizer rewrites the domain non-definitionally. Original and optimized
  bodies then need differently typed variables, and relating them requires casts in the optimizer.
  This accounts for most of the remaining `frame::forall` failures.
- Goals proved by the SMT solver rely on Lean decision procedures. The next step is to replay Z3
  proofs, or at least use unsat cores and quantifier instantiations from Z3 as hints.
- Universe-polymorphic goals cannot be reconstructed while `normLevel` is applied.
- Arithmetic (`Nat`/`Int`) constant folding and `match`/`ite` normalization rules still rely on tactic
  discharge rather than explicit lemmas.
- Residual goals involving derived `BEq` instances or recursive functions need their definitions
  unfolded, as the SMT solver receives them as axioms.
