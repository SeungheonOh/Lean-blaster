import Blaster

-- A (consistent) axiom-declared Bool constant whose root name is `true`.
axiom _root_.true : Bool
axiom true_is_false : (_root_.true : Bool) = Bool.false

theorem bad : ∀ x : Int, x = 0 := by blaster (dump-smt-lib: 1)

theorem oops : False := absurd (bad 1) (by decide)
