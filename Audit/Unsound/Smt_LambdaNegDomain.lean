import Blaster

-- The two lambdas agree on every Nat (so are equal by funext) but their SMT
-- encodings differ on negative Ints (Nat is encoded as unguarded Int in lambda defs).
theorem bad_lam : (fun n : Nat => n - 1 + 1) ≠ (fun n : Nat => if n = 0 then 1 else n) := by blaster

theorem lam_eq : (fun n : Nat => n - 1 + 1) = (fun n : Nat => if n = 0 then 1 else n) := by
  funext n; cases n <;> simp

example : False := bad_lam lam_eq
