import Blaster

theorem u1.{u} (α : Sort u) (a b : α) : a = b := by blaster
theorem u2.{u} (α : Type u) (a b : α) : a = b := by blaster
theorem u3 (α : Prop) (a b : α) : a = b := by blaster

#blaster [∀ (α : Sort _) (a b : α), a = b]
#blaster [∀ (α : Type) (a b : α), a = b]
