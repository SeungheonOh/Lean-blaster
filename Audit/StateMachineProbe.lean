import Blaster.StateMachine

open Blaster.StateMachine

namespace BlasterAudit

inductive Input where
  | stay
  | jump
  deriving DecidableEq

instance shiftedInput : StateMachine Input Nat where
  init _ := 0
  next i s := if i = .jump then 1 else s
  assumptions i s := s = 0 → i = .stay
  invariants _ s := s = 0

theorem actual_step_safe (i : Input) (s : Nat)
    (h : s = 0) (ha : (s = 0 → i = .stay)) :
    (StateMachine.next (α := Input) (β := Nat) i s) = 0 := by
  simp [h, ha h, StateMachine.next]

#bmc (max-depth: 1) (gen-cex: 0) (solve-result: 1) [shiftedInput]

#kind (max-depth: 1) (gen-cex: 0) (solve-result: 1) [shiftedInput]

instance missedInput : StateMachine Input Nat where
  init _ := 0
  next i s := if i = .jump then 1 else s
  assumptions i s := s = 0 ∨ i = .stay
  invariants _ s := s = 0

theorem actual_counterexample :
    @StateMachine.next Input Nat missedInput .jump 0 = 1 := by
  rfl

theorem actual_unsafe_trace :
    @StateMachine.init Input Nat missedInput .jump = 0 ∧
    @StateMachine.assumptions Input Nat missedInput .jump 0 ∧
    @StateMachine.next Input Nat missedInput .jump 0 = 1 ∧
    @StateMachine.assumptions Input Nat missedInput .stay 1 ∧
    ¬ @StateMachine.invariants Input Nat missedInput .stay 1 := by
  simp [StateMachine.init, StateMachine.assumptions, StateMachine.next,
    StateMachine.invariants]

#bmc (max-depth: 1) (gen-cex: 0) [missedInput]

#kind (max-depth: 1) (gen-cex: 0) [missedInput]

end BlasterAudit
