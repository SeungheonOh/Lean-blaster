import Lean
import Blaster

/-! # Proof reconstruction: goals of other test suites

Goals adapted from the test suites of Aesop, lean-auto and lean-smt (and from Blaster's own fixed issues, in tactic
form), on which the reconstruction failed. Each goal must be proved by Blaster with a kernel-checked proof depending
only on Lean's standard axioms (`gen-proof`).
-/

namespace Tests.Reconstruct.External

/-! ## Direct proofs of the goals

The optimized goal may be ill-typed, e.g., a proof depending on a condition the optimizer normalized (`a 0 = 42` as
`42 = a 0`): the goal itself is proved, closed over the variables of the tactic's local context. -/

theorem dependent_match {a : Nat → Nat} (ha : a 0 = 37) :
    (match h : a 0 with | 42 => by simp_all | n => n) = 37 := by
  blaster (gen-proof: 1)

theorem dependent_dite {c : Bool} {t : c → Prop} {e : ¬ c → Prop} :
    (dite c t e) → ∀ (h : c), t h ∧ ∀ (h : ¬ c), e h := by
  blaster (gen-proof: 1)

theorem dite_true {α : Sort u} {t : True → α} {e : ¬ True → α} : (dite True t e) = t True.intro := by
  blaster (gen-proof: 1)

theorem dite_false {α : Sort u} {t : False → α} {e : ¬ False → α} : (dite False t e) = e not_false := by
  blaster (gen-proof: 1)

/-! ## Bit vectors

Decided on the goal before its optimization (the optimizer encodes the bit vectors as natural numbers, e.g., the
rotations with `Nat.bitwise`), by `bv_omega` or bit by bit. -/

theorem bv_add_comm (a b : BitVec 10) : a + b = b + a := by blaster (gen-proof: 1)

theorem bv_add_lits {x y : BitVec 4} : ¬(x = 11#4 ∧ y = 11#4 ∧ x + y = 15#4) := by blaster (gen-proof: 1)

theorem bv_rotate (x : BitVec 15) : x.rotateLeft 3 = x.rotateRight 12 := by blaster (gen-proof: 1)

theorem bv_rotate_zero (x : BitVec 20) (y : BitVec 4) :
    (0#5).rotateLeft x.toNat = 0#5 ∧ (0#5).rotateRight y.toNat = 0#5 := by
  blaster (gen-proof: 1)

/-! ## Strings, as their lists of characters -/

theorem string_append_assoc (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by blaster (gen-proof: 1)

/-! ## Nested existentials (witnesses searched for each of them) -/

theorem nested_exists : ∃ n : Nat, n ^ 2 = 4 ∧ ∃ n : Nat, n ^ 2 = 9 ∧ True := by blaster (gen-proof: 1)

/-! ## Hypotheses on propositional variables

The proof obligation of the rewrite of `¬ p3` to `False` needs the hypotheses on `p1` and `p2`, which are relevant to
it (see `relevantContext?`). -/

theorem prop_vars [Nonempty U] {f : U → U → U} {a b c d : U} :
    (a = b) → (c = d) → p1 ∧ True → (¬ p1) ∨ (p2 ∧ p3) → (¬ p3) ∨ (¬ (f a c = f b d)) → False := by
  blaster (gen-proof: 1)

/-! ## Certificates of Z3's nonlinear theory lemmas

The indices of `th-lemma` (e.g., `(_ th-lemma arith nla (polynomial-refutation ...))` with Z3 5.3) are kept as printed
when they are not terms (e.g., the empty lists and the lists of numbers of the certificate). -/

open Blaster.Reconstruct.SmtProof in
/-- The attributes of the `th-lemma` step of a proof with a certificate of Z3's nonlinear arithmetic. -/
def nlaAttrs : Except String String := do
  let p ← Z3.parseProof "((proof
    (let ((@p1 ((_ th-lemma arith nla (polynomial-refutation (premises 1) (variables (0 Int ()) (1 Int ((1 0))))
                  (steps (0 0 4294967295 0 () ()))))
                (asserted (< (* x x) 0)) false)))
    @p1)))"
  let some step := p.steps.find? (·.rule == "th-lemma") | throw "no th-lemma step"
  return " ".intercalate (step.attrs.toList.map toString)

/-- info: Except.ok "arith nla (polynomial-refutation (premises 1) (variables (0 Int ()) (1 Int ((1 0)))) (steps (0 0 4294967295 0 () ())))" -/
#guard_msgs in
#eval nlaAttrs

end Tests.Reconstruct.External
