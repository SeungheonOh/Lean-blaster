/-
Pass 2 – deep SMT datatypes/functions: incremental findings log (comment-only file).

[CONFIRMED] S1 TrueShadow — Unsound_TrueShadow.lean
  Where: Smt/Translate/Application.lean:776 (updateAxiomMap -> nameToSmtSymbol, no `@` prefix);
         Smt/Translate/Quantifier.lean:65-66; Smt/Syntax.lean:142-153 prints simple-char names unquoted.
  Cause: `axiom _root_.true : Bool` emitted as `(declare-const true Bool)`; Z3 4.13.3 lets it shadow the
         builtin literal for the rest of the script (@isInt body, guards). Consistent axiom `true = false`
         falsifies every later `true` -> negated goal unsat.
  Observed: `∀ x : Int, x = 0` -> ✅ Valid; `oops : False` compiles.
  Note: upgrades REPORT.md B "user constant named `true` shadows the SMT literal" to confirmed.
-/
