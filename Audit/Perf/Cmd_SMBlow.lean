import Blaster.StateMachine
open Blaster.StateMachine
namespace Audit.SMBlow
structure St where
  a : Int
  b : Int
instance m : StateMachine Int St where
  init _ := ⟨1, 2⟩
  next i s := if i > 0 then ⟨s.a - s.b + i, s.b + s.a⟩ else ⟨s.b + s.a, s.a + 1⟩
  assumptions i _ := i < 1000 ∧ i > -1000
  invariants _ s := s.a < 1000000000
#bmc (max-depth: 8) (dump-smt-lib: 1) [m]
end Audit.SMBlow
