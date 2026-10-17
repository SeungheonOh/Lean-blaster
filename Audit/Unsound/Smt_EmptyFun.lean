import Blaster

-- `@isFun f := ∀ x : Empty, @isEmpty (@apply f x)` is `false` in SMT because the SMT
-- sort `Empty` is non-empty, so every quantifier over `Empty → Empty` is vacuous.
theorem bad1 : ∀ (f : Empty → Empty) (g : (Empty → Empty) → Nat), g f = 1 := by blaster
example : False := absurd (bad1 id (fun _ => 0)) (by decide)
