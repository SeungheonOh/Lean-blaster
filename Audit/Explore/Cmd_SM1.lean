import Blaster.StateMachine
open Blaster.StateMachine
namespace Audit.SM1

-- invariant true for depth < 5 only
instance cnt : StateMachine Unit Nat where
  init _ := 0
  next _ s := s + 1
  assumptions _ _ := True
  invariants _ s := s < 5

#kind (max-depth: 2) [cnt]
#kind (max-depth: 6) [cnt]
#bmc (max-depth: 3) [cnt]
#bmc (max-depth: 6) [cnt]
-- solve-result mismatches
#bmc (max-depth: 3) (solve-result: 1) [cnt]
#kind (max-depth: 2) (solve-result: 0) [cnt]

-- parity: s even is 1-inductive
instance par : StateMachine Unit Nat where
  init _ := 0
  next _ s := s + 2
  assumptions _ _ := True
  invariants _ s := s % 2 = 0
#kind (max-depth: 2) [par]

-- invariant false at init only via input
instance initInp : StateMachine Nat Nat where
  init i := i
  next _ s := s
  assumptions _ _ := True
  invariants _ s := s ≠ 7
#kind (max-depth: 2) [initInp]
#bmc (max-depth: 2) [initInp]

-- not inductive but true: s ∈ {0,1,2} cycles; inv s ≠ 3, next: s=0->1,1->2,2->0, 3->3,4->3
instance cyc : StateMachine Unit Nat where
  init _ := 0
  next _ s := if s = 0 then 1 else if s = 1 then 2 else if s = 2 then 0 else if s = 4 then 3 else s
  assumptions _ _ := True
  invariants _ s := s ≠ 3
#kind (max-depth: 3) [cyc]
end Audit.SM1
