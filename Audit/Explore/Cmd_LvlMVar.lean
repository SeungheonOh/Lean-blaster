import Blaster
theorem lv1 : False := by
  have h : ∀ (α : Sort _) (a b : α), a = b := by blaster
  exact absurd (h Nat 0 1) (by decide)

theorem lv2 : True := by
  have h : ∀ (α : Sort _) (a : α), a = a := by blaster
  have := h Nat 0
  trivial

theorem lv3 : False := by
  have h : ∀ (p : Sort _) (a b : p), (fun _ : Nat => a) = (fun _ => b) := by blaster
  have := congrFun (h Nat 0 1) 0
  exact absurd this (by decide)
