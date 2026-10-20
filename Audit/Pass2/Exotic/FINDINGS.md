# Pass 2 — exotic Lean features (running log)

## Confirmed unsound

### E1. Equality between proofs built with the same constructor and different *data* args (PropCtorDataArg)
- Repro: `Audit/Pass2/Exotic/Unsound_PropCtorDataArg.lean` (derives `False`; axioms: `sorryAx` only).
- `(⟨0⟩ : Nonempty Nat) ≠ ⟨1⟩`, `(⟨0, trivial⟩ : ∃ _ : Nat, True) ≠ ⟨1, trivial⟩` → ✅ Valid (optimized to `True`).
  `inductive Tok : Prop | mk : Nat → Tok`; `∀ a b, Tok.mk a = Tok.mk b → a = b` → ✅ Valid (via SMT).
- Two root causes:
  1. Optimizer: `optimizeEq` calls `structEq?` without checking that the carrier (`args[0]`) is a Prop
     (`Blaster/Optimize/Rewriting/OptimizeEq.lean:337`, same for BEq at :427; `structEq?` at :13-45).
     Related to REPORT #8 but NOT fixed by its suggested fix ("skip Prop-typed args"): the differing args here
     are `Nat`; it is the equation's type that is a Prop.
  2. SMT: a Prop-valued inductive (`Tok : Prop`) is declared as an SMT datatype with injective constructors
     (`translateNonOpaqueType`, `Blaster/Smt/Translate/Quantifier.lean:996-1010`; the inductive-predicate
     guard `isInductivePredicate` in `Smt/Translate/Application.lean:59-61,974-977` only fires when the type
     itself is applied, e.g. `Nonempty Nat`, not for the constant `Tok` reached through its constructor).
     Query: `(declare-datatype @Tok ((Tok.mk (Tok.mk.1 Nat))))` and `(= (Tok.mk $0) (Tok.mk $1))`.
- Fix: in `optimizeEq`, rewrite `@Eq p a b` to `True` when `p : Prop`; reject (or translate as a trivial
  one-element sort) Prop-valued inductives in the SMT translator.

## Checked — correct or unsupported (no false Valid)
- Float/Float32: every non-syntactic goal fails with `translateType: ... proj FloatSpec` (unsupported);
  `x == x` is NOT reflexively simplified. `#blaster [b]` with Bool `b` is rejected ("not a proposition").
- UInt8/16/64, Int8, USize, Char: closed terms are unfolded to `Fin`/`BitVec` structures and evaluated
  correctly (wrap-around, `Char.ofNat 0x110000 = '\0'`, Int8 overflow); symbolic ones fail with
  "Inductive datatype with instance parameters not supported: BitVec/Fin".
- Fin/BitVec/Subtype/Sigma/PSigma/Vector/PLift/Decidable/Inhabited-vars: unsupported (same error).
- Quot/Quotient/Squash: `Quot.mk` → "translateApp: unexpected application"; `Quot` type → "inductive info expected".
- cast / ▸ / type equalities `α = β`, `Nat = Int` as antecedent, HEq: all rejected with errors.
- Classical: `p ∨ ¬p`, `ite`/`decide` with `Classical.propDecidable` (agrees with the instance version),
  propext (`(p ↔ q) → p = q`, `True = (1 = 1)`, `f True = f (1=1)` for `f : Prop → Nat`), Bool↔Prop
  coercions: all correct. `Classical.choice/choose/epsilon`: unsupported (Nonempty error).
- `Nonempty`/`HEq` as predicates: "Inductive predicate not yet supported".
- `Array` literals, `size`, `[i]!` out-of-bounds default: correct.

## Crashes
- `#blaster [(2:Nat)^(2^70) % 2 = 0]` → `INTERNAL PANIC: Nat.pow exponent is too big` (aborts the whole Lean
  process; root cause TBD).
