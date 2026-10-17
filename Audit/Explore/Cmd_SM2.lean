import Blaster.StateMachine
open Blaster.StateMachine
namespace Audit.SM2

structure St where
  a : Nat
  b : Nat

instance m1 : StateMachine Bool St where
  init _ := ⟨0, 0⟩
  next i s := if i then ⟨s.a + 1, s.b⟩ else ⟨s.a, s.b + 1⟩
  assumptions _ _ := True
  invariants _ s := s.a + s.b < 4
#kind (max-depth: 6) [m1]

-- property depends on the input at the step: inv i s := i → s.a < 2
instance m2 : StateMachine Bool St where
  init _ := ⟨0, 0⟩
  next i s := if i then ⟨s.a + 1, s.b⟩ else s
  assumptions _ _ := True
  invariants i s := i = true → s.a < 2
#kind (max-depth: 4) [m2]
#bmc (max-depth: 4) [m2]

-- assumption at last step restricts: assumptions i _ := i = false
instance m3 : StateMachine Bool Nat where
  init _ := 0
  next i s := if i then s + 1 else s
  assumptions i _ := i = false
  invariants _ s := s = 0
#kind (max-depth: 3) [m3]

-- init depends on input; next depends on input at depth k-1
instance m4 : StateMachine Nat Nat where
  init i := i % 3
  next i s := if i = 5 then s + 1 else s
  assumptions _ _ := True
  invariants _ s := s < 4
#kind (max-depth: 5) [m4]
end Audit.SM2
