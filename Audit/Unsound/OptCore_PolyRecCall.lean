import Blaster

-- recursive call changes the (non-generic) implicit argument
def f {b : Bool} : Nat → Nat
  | 0 => if b then 1 else 0
  | n + 1 => @f (!b) n

def g {b : Bool} : Nat → Nat
  | 0 => if b then 1 else 0
  | n + 1 => @g b n

-- storeRecFunDef replaces tagged recursive calls by `_recFun` while dropping the
-- (non-generic) implicit arguments, so `@f true` and `@g true` get the same
-- normalized body and are identified.
theorem bad : ∀ n : Nat, @f true n = @g true n := by blaster

theorem bad_false : ¬ (∀ n : Nat, @f true n = @g true n) := by
  intro h; exact absurd (h 1) (by decide)

theorem oops : False := bad_false bad
