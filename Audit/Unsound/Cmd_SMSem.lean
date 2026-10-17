import Blaster.StateMachine
open Blaster.StateMachine
namespace Audit.SMSem

/- Documented semantics (BMC.lean:13-16, KInduction.lean:122-133):
     st₀ = init in₀,  stᵢ₊₁ = next inᵢ stᵢ,  assumptions inᵢ stᵢ
   Under it: in₀ = true is allowed (s₀ = 0), so s₁ = next true 0 = 1 violates `s = 0`. -/
instance m : StateMachine Bool Nat where
  init _ := 0
  next i s := if i then s + 1 else s
  assumptions i s := i = true → s = 0   -- "may only increment from 0"
  invariants _ s := s = 0

#bmc (max-depth: 3) [m]
#kind (max-depth: 3) [m]

-- the documented trace, checked in Lean: s₁ = next in₀ s₀ with in₀ = true, in₁ = false
example : m.assumptions true (m.init true) ∧
          m.assumptions false (m.next true (m.init true)) ∧
          ¬ m.invariants false (m.next true (m.init true)) := by
  simp [m]
end Audit.SMSem
