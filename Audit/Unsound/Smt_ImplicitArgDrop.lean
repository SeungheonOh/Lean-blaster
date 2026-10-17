import Blaster

-- Implicit Nat argument of a HOF variable: crash in translateArrowType
theorem crash_impl : ∀ (f : {x : Nat} → Nat → Nat), @f 1 5 = @f 2 5 := by blaster

-- Instance-implicit arguments of HOF variables are dropped from the SMT encoding,
-- so `@f i₁ y` and `@f i₂ y` become the same SMT term.
theorem bad_inst : ∀ (f : [Inhabited Nat] → Nat → Nat), @f ⟨0⟩ 3 = @f ⟨1⟩ 3 := by blaster
example : False := absurd (bad_inst (fun [i : Inhabited Nat] _ => i.default)) (by decide)

theorem bad_inst2 : ∀ (f : [Inhabited Nat] → Nat → Bool), @f ⟨0⟩ 3 = @f ⟨1⟩ 3 := by blaster
example : False := absurd (bad_inst2 (fun [i : Inhabited Nat] _ => i.default == 0)) (by decide)
