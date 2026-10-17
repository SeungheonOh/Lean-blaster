import Blaster

opaque c : Nat

def P1 : Prop :=
  (match c with | 5 => True | _ => (match c with | 5 => False | _ => True)) ∧
  (match c with | 5 => False | _ => True)

#blaster (only-optimize: 1) [ P1 ]
#blaster [ P1 ]

def P2 : Prop :=
  (match c with | 5 => False | _ => True) ∧
  (match c with | 5 => True | _ => (match c with | 5 => False | _ => True))
#blaster [ P2 ]

-- closed but Lean-evaluable discriminant
noncomputable def d : Nat := Classical.choose (⟨5, rfl⟩ : ∃ n : Nat, n = 5)
theorem d_eq : d = 5 := Classical.choose_spec (⟨5, rfl⟩ : ∃ n : Nat, n = 5)

def Q : Prop :=
  (match d with | 5 => True | _ => (match d with | 5 => False | _ => True)) ∧
  (match d with | 5 => False | _ => True)

theorem badQ : Q := by blaster
theorem notQ : ¬ Q := by
  unfold Q; rw [d_eq]; simp
theorem falseQ : False := notQ badQ
