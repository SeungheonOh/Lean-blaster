import Lean
import Blaster
open Lean Elab Command Term Meta

syntax (name := optShow) "#opt " term : command
@[command_elab optShow]
def optShowImp : CommandElab := fun stx => do
  runTermElabM fun _ => do
    let e ← elabTermAndSynthesize stx[1] none
    let r ← withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $
      Blaster.Optimize.command default e
    logInfo m!"{r.1}"
set_option pp.funBinderTypes true
def dd (x y : Nat) : Nat := match decEq x y with | isTrue _ => 1 | isFalse _ => 0
#opt ∀ x y, dd x y = 1
#blaster (timeout: 15) [ ∀ x y, dd x y = if x = y then 1 else 0 ]  -- true
#blaster (timeout: 15) [ ∀ x y, dd x y = 1 ]  -- false
def dp (p : Prop) [Decidable p] : Nat := match (inferInstance : Decidable p) with | isTrue _ => 1 | isFalse _ => 0
#blaster (timeout: 15) [ ∀ x : Nat, dp (x = 3) = if x = 3 then 1 else 0 ]  -- true
#blaster (timeout: 15) [ ∀ x : Nat, dp (x = 3) = 1 ]  -- false
-- Prod / structure patterns with overlap
def pr (p : Nat × Nat) : Nat := match p with | (0, _) => 1 | (_, 0) => 2 | (a+1, b+1) => a + b
#blaster (timeout: 15) [ ∀ p, pr p = if p.1 = 0 then 1 else if p.2 = 0 then 2 else p.1 + p.2 - 2 ]  -- true
#blaster (timeout: 15) [ ∀ p, pr p ≠ 2 ]  -- false
#blaster (timeout: 15) [ ∀ a, pr (0, a) = 1 ∧ pr (a+1, 0) = 2 ]  -- true
-- List patterns with overlap
def ll (l : List Nat) : Nat := match l with | [a] => a | _ :: b :: _ => b | [] => 0
#blaster (timeout: 15) [ ∀ l, ll l = if l.length = 1 then l.head! else if l.length ≥ 2 then l[1]! else 0 ]
#blaster (timeout: 15) [ ∀ a, ll [a] = a ]
#blaster (timeout: 15) [ ∀ l, l ≠ [] → ll l = l[1]! ]  -- false
