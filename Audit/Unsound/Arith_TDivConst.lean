import Blaster

-- Int.tdiv / tmod / fdiv / fmod constant folding uses ediv/emod
theorem bad_tdiv : Int.tdiv (-7) 2 = -4 := by blaster
example : ¬ (Int.tdiv (-7) 2 = -4) := by decide

theorem bad_tmod : Int.tmod (-7) 2 = 1 := by blaster
example : ¬ (Int.tmod (-7) 2 = 1) := by decide

theorem bad_fdiv : Int.fdiv (-7) (-2) = 4 := by blaster
example : ¬ (Int.fdiv (-7) (-2) = 4) := by decide

theorem bad_fmod : Int.fmod 7 (-2) = 1 := by blaster
example : ¬ (Int.fmod 7 (-2) = 1) := by decide

theorem false_from_tdiv : False := by
  have h := bad_tdiv
  revert h; decide

#blaster (only-optimize: 1) [ Int.tdiv (-7) 2 = -4 ]
