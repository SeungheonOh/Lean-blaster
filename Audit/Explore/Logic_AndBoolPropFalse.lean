import Blaster

-- andBoolReduction? returns Prop `False` instead of Bool `false` (OptimizeBoolBinary.lean:72)
#blaster (only-optimize: 1) [∀ (a b : Bool), b = false → (a && b) = false]
#blaster (only-optimize: 1) [∀ (a b : Bool), b = false → (a && b) = true]
#blaster [∀ (a b : Bool), b = false → (a && b) = false]
#blaster [∀ (a b : Bool), b = false → (a && b) = true]
#blaster [∀ (a b : Bool), b = false → (!(a && b)) = true]
#blaster [∀ (a b : Bool), b = false → (!(a && b)) = false]
#blaster [∀ (a b : Bool) (x : Nat), b = false → (if (a && b) then x else x + 1) = x]
#blaster [∀ (a b : Bool) (x : Nat), b = false → (if (a && b) then x else x + 1) = x + 1]
#blaster [∀ (a b c : Bool), b = false → (c && (a && b)) = c]
#blaster [∀ (a b c : Bool), b = false → (c || (a && b)) = c]
#blaster [∀ (a b c : Bool), b = false → (c || (a && b)) = true]
