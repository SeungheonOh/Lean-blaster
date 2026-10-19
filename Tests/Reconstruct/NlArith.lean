import Blaster

/-! # Nonlinear integer arithmetic (`blaster_nlarith`)

Theory lemmas and rewrites of Z3's nonlinear arithmetic, as replayed by the SMT proof replay (see
`Blaster.Reconstruct.SmtProof.NlArith`): `Int` statements, the variables of sort `Nat` being casts.
-/

namespace Tests.Reconstruct.NlArith

-- factorization and no zero divisors
example : ∀ (x y z : Int), (x * y + -1 * (x * z) = 0) = (x = 0 ∨ z * -1 + y = 0) := by
  blaster_nlarith

-- signs of products
example : ∀ (x y : Nat), ((x : Int) * (y : Int) ≤ 0) = (¬(0 ≤ (x : Int)) = (0 ≤ (y : Int)) ∨ (x : Int) = 0 ∨ (y : Int) = 0) := by
  blaster_nlarith

-- squares
example : ∀ (x y : Int), 0 ≤ x + -1 * y ∨ x ≤ 0 ∨ ¬0 ≤ x * x + -1 * (y * y) := by
  blaster_nlarith

-- monotonicity of products (sign split on `y`)
example : ∀ (x y z w : Int), ¬0 ≤ x + -1 * y ∨ x ≤ 2 ∨ ¬0 ≤ z + -1 * w ∨ 0 ≤ x * z + -1 * (y * w) ∨ ¬1 ≤ w := by
  blaster_nlarith

-- divisions and modulos
example : ∀ (x y z : Nat), 0 < (z : Int) → ((x : Int) ≤ (y : Int) / (z : Int) ↔ (x : Int) * (z : Int) ≤ (y : Int)) := by
  blaster_nlarith

example : ∀ (x y : Nat), (x : Int) % (y : Int) ≤ (x : Int) := by
  blaster_nlarith

-- lemmas of `Tests/Smt/SmtNat/SmtNatDiv.lean` (`if-then-else` terms, divisions by products)
example : ∀ (x z : Nat),
  ¬(↑x : Int) + (↑z : Int) +
          (-1 : Int) *
            ((↑z : Int) * (((↑x : Int) + (↑z : Int)) / (↑z : Int)) + ((↑x : Int) + (↑z : Int)) % (↑z : Int)) ≤
        (0 : Int) ∨
    ¬(((↑x : Int) + (↑z : Int)) / (↑z : Int) +
            (-1 : Int) * if (↑z : Int) = (0 : Int) then (0 : Int) else ((↑x : Int) + (↑z : Int)) / (↑z : Int)) ≤
          (0 : Int) ∨
      ((if (↑z : Int) = (0 : Int) then (0 : Int) else (↑x : Int) / (↑z : Int)) +
            (-1 : Int) * if (↑z : Int) = (0 : Int) then (0 : Int) else ((↑x : Int) + (↑z : Int)) / (↑z : Int)) ≤
          (-1 : Int) ∨
        ¬((↑x : Int) + (↑z : Int)) % (↑z : Int) + (-1 : Int) * (↑z : Int) ≤ (-1 : Int) ∨
          ¬(0 : Int) ≤ (↑x : Int) + (-1 : Int) * ((↑z : Int) * ((↑x : Int) / (↑z : Int)) + (↑x : Int) % (↑z : Int)) ∨
            ¬(0 : Int) ≤ (↑x : Int) % (↑z : Int) ∨
              (↑z : Int) ≤ (0 : Int) ∨
                ¬(0 : Int) ≤
                    (↑x : Int) / (↑z : Int) +
                      (-1 : Int) * if (↑z : Int) = (0 : Int) then (0 : Int) else (↑x : Int) / (↑z : Int) := by
  blaster_nlarith

example : ∀ (x y z : Nat),
  (↑x : Int) * (↑y : Int) / ((↑x : Int) * (↑z : Int)) =
    if (0 : Int) = (↑x : Int) * (↑z : Int) then (↑x : Int) * (↑y : Int) / (0 : Int)
    else
      if (0 : Int) = (↑x : Int) then (0 / 0 : Int)
      else if (0 : Int) ≤ (↑x : Int) then (↑y : Int) / (↑z : Int) else -(↑y : Int) / -(↑z : Int) := by
  blaster_nlarith

example : ∀ (x y z : Nat),
  ¬(if (↑y : Int) = (0 : Int) then (0 : Int) else (↑x : Int) / (↑y : Int)) % (↑z : Int) + (-1 : Int) * (↑z : Int) ≤
        (-1 : Int) ∨
    (↑z : Int) ≤ (0 : Int) ∨
      ¬(if (↑y : Int) = (0 : Int) then (0 : Int) else (↑x : Int) / (↑y : Int)) / (↑z : Int) ≤ (0 : Int) ∨
        ¬((↑x : Int) / (↑y : Int) +
                (-1 : Int) * if (↑y : Int) = (0 : Int) then (0 : Int) else (↑x : Int) / (↑y : Int)) ≤
              (0 : Int) ∨
          ¬(↑x : Int) + (-1 : Int) * ((↑y : Int) * ((↑x : Int) / (↑y : Int)) + (↑x : Int) % (↑y : Int)) ≤ (0 : Int) ∨
            (↑x : Int) / ((↑y : Int) * (↑z : Int)) ≤ (0 : Int) ∨
              ¬(↑x : Int) % (↑y : Int) + (-1 : Int) * (↑y : Int) ≤ (-1 : Int) ∨
                ¬(if (↑y : Int) = (0 : Int) then (0 : Int) else (↑x : Int) / (↑y : Int)) +
                        (-1 : Int) *
                          ((↑z : Int) *
                              ((if (↑y : Int) = (0 : Int) then (0 : Int) else (↑x : Int) / (↑y : Int)) / (↑z : Int)) +
                            (if (↑y : Int) = (0 : Int) then (0 : Int) else (↑x : Int) / (↑y : Int)) % (↑z : Int)) ≤
                      (0 : Int) ∨
                  ¬(0 : Int) ≤
                        (↑x : Int) + (-1 : Int) * ((↑y : Int) * (↑z : Int) * ((↑x : Int) / ((↑y : Int) * (↑z : Int)))) ∨
                    (↑y : Int) ≤ (0 : Int) := by
  blaster_nlarith

example : ∀ (x y : Nat),
  (0 : Int) ≤ (↑x : Int) % (↑y : Int) + (-1 : Int) * (↑x : Int) ∨
    (↑x : Int) % (↑y : Int) + (-1 : Int) * (↑x : Int) + (↑y : Int) ≤ (0 : Int) ∨
      ¬(↑x : Int) + (-1 : Int) * ((↑y : Int) * ((↑x : Int) / (↑y : Int)) + (↑x : Int) % (↑y : Int)) ≤ (0 : Int) ∨
        ¬(0 : Int) ≤ (↑x : Int) + (-1 : Int) * ((↑y : Int) * ((↑x : Int) / (↑y : Int)) + (↑x : Int) % (↑y : Int)) ∨
          (↑y : Int) ≤ (0 : Int) := by
  blaster_nlarith

end Tests.Reconstruct.NlArith
