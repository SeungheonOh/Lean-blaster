import Blaster

-- (a) opaque function with empty domain: codomain axiom `∀ x : Empty, @isEmpty (e2e x)`
--     is asserted globally and is false in SMT (sorts non-empty) => inconsistent context.
opaque e2e : Empty → Empty := id

theorem bad2 : ∀ (g : (Empty → Empty) → Nat), g e2e = 1 := by blaster
example : False := absurd (bad2 (fun _ => 0)) (by decide)

-- (b) user structure with an unsatisfiable invariant (empty in Lean)
structure Imp where
  n : Nat
  h : n < 0

theorem bad7 : ∀ (f : Imp → Imp) (g : (Imp → Imp) → Nat), g f = 1 := by blaster
example : False := absurd (bad7 id (fun _ => 0)) (by decide)
