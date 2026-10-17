import Blaster
def R : Nat → Nat → Prop := fun _ _ => True
#blaster [¬ (Quot.mk R 0 = Quot.mk R 1)]
#blaster [Quot.mk R 0 ≠ Quot.mk R 1]
#blaster [Quot.mk R 0 = Quot.mk R 1]
#blaster [Quot.mk (fun (_ _ : Nat) => True) 0 ≠ Quot.mk (fun _ _ => True) 1]
#blaster [∀ a b : Nat, Quot.mk R a = Quot.mk R b → a = b]
#blaster [Quot.lift (fun n : Nat => n + 1) (fun _ _ (h : n_eq) => rfl) (Quot.mk (@Eq Nat) 3) = 4]
#blaster [∀ x y : Quot R, x = y]
#blaster [∀ x y : Quot R, x ≠ y]
#blaster [Squash.mk 1 ≠ Squash.mk 2]
#blaster [∀ x y : Squash Nat, x = y]
#blaster [(Trunc.mk 1 : Trunc Nat) ≠ Trunc.mk 2]
instance S : Setoid Nat := ⟨fun a b => a % 2 = b % 2, sorry⟩
#blaster [(Quotient.mk S 0) ≠ Quotient.mk S 2]
#blaster [(Quotient.mk S 0) = Quotient.mk S 2]
#blaster [∀ a b : Nat, Quotient.mk S a = Quotient.mk S b → a = b]
