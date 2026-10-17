import Blaster
universe u v

-- structEq? compares constructor constants with pointer equality including universe levels;
-- `max u v` and `max v u` are defeq levels but distinct Exprs, so `PUnit.unit = PUnit.unit` is declared False.
theorem bad1 : ¬ ((PUnit.unit.{max u v + 1} : PUnit.{max u v + 1}) = PUnit.unit.{max v u + 1}) := by blaster
example : ((PUnit.unit.{max u v + 1} : PUnit.{max u v + 1}) = PUnit.unit.{max v u + 1}) := rfl

theorem bad2 : ∀ (x : Nat), ¬ ((some x, PUnit.unit.{max u v + 1}) = (some x, PUnit.unit.{max v u + 1})) := by blaster

theorem f1 : False := bad1.{0,0} rfl
theorem f2 : False := bad2.{0,0} 0 rfl
