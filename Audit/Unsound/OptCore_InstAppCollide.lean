import Blaster

def subL {α} [Sub α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x - subL xs

def weirdSub : Sub Int := ⟨fun a b => a + b⟩

-- getInstApp returns the bare constant `subL` when only implicit args are supplied,
-- so both partial applications share one recFunInstCache entry.
theorem bad : ∀ ys : List (List Int),
    List.map (@subL Int weirdSub _) ys = List.map (@subL Int (inferInstance : Sub Int) _) ys := by
  blaster

theorem bad_false : ¬ (∀ ys : List (List Int),
    List.map (@subL Int weirdSub _) ys = List.map (@subL Int (inferInstance : Sub Int) _) ys) := by
  intro h
  exact absurd (h [[0, 1]]) (by decide)

theorem oops : False := bad_false bad
