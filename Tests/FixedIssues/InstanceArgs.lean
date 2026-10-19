import Lean
import Blaster

namespace Tests.InstanceArgs

-- Issue: Unexpected Valid for falsifiable goals with instances that are not the canonical ones.
-- Diagnosis: `@LT.lt α inst` (resp. `LE.le`) was taken as the relation of the SMT theory for `α ∈ [Nat, Int, Bool,
--            String]` whatever `inst`, and the instance arguments of function values (e.g., a structure field
--            `f [LT α] : α → α`) are erased by the translation. Other instances of `LT`/`LE` are now unfolded, and
--            applications of function values are only translated with canonical (or local) instances.

def lt1 : LT Nat := ⟨fun a b => a < b⟩
def lt2 : LT Nat := ⟨fun a b => b < a⟩

def g {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] (x y : α) : Bool := decide (x < y)

instance d1 : @DecidableRel Nat Nat (@LT.lt Nat lt1) := fun a b => Nat.decLt a b
instance d2 : @DecidableRel Nat Nat (@LT.lt Nat lt2) := fun a b => Nat.decLt b a

theorem g_differ : ¬ ∀ (x y : Nat), @g Nat lt1 d1 x y = @g Nat lt2 d2 x y :=
  fun h => absurd (h 1 2) (by decide)

#blaster (gen-cex: 0) (solve-result: 1) (timeout: 10) [∀ (x y : Nat), @g Nat lt1 d1 x y = @g Nat lt2 d2 x y]

-- Valid expected: the canonical instance and an equivalent definition
#blaster [∀ (x y : Nat), @g Nat lt1 d1 x y = decide (x < y)]

structure FunRel where
  f [LT α] : α → α

structure FunRelNat where
  f [LT Nat] : Nat → Nat

-- Valid expected: canonical and local instances
-- NOTE: `∀ (r : FunRel) (x y : Nat), x = y → r.f x = r.f y` is not translated correctly on this branch, independently
-- of the instance arguments (the `@apply` function of the field instantiated at `Nat` is not declared), hence the
-- monomorphic field
#blaster [∀ (r : FunRelNat) (x y : Nat), x = y → r.f x = r.f y]
#blaster [∀ (α : Type) [LT α] (r : FunRel) (x : α), r.f x = r.f x]

end Tests.InstanceArgs
