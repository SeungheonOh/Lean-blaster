import Blaster
-- OptimizeString.lean:106 checks `args.size != 2` for the 3-ary String.replace (and reads args[3]!)
#blaster [("abc".replace "b" "x") = "axc"]
#blaster [∀ s : String, s.replace "a" "a" = s]
-- OptimizeExists.lean:166 throws when the Exists predicate is not a syntactic lambda
#blaster [∀ p : Nat → Prop, Exists p → ∃ x, p x]
-- OptimizeForAll.lean:56-65 impliesToNeg? has no `isPropEnv a` guard: `∀ _ : Empty, b` under hyp `¬b`
-- becomes the ill-typed `¬ Empty` (and is semantically wrong: ∀ over an empty type is True)
#blaster (only-optimize: 1) [∀ b : Bool, (b = false) → ∀ (_x : Empty), b = true]
#blaster [∀ b : Bool, (b = false) → ∀ (_x : Empty), b = true]
#blaster [∀ (b : Bool) (n : Nat), ((b = false) → ∀ (_x : Fin n), b = true) → n = 0]
