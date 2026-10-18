import Lean
import Blaster

/-! # Proof reconstruction: `match` edge cases

Each goal below must be proved by Blaster AND come with a proof term checked by the Lean kernel
(i.e., `(reconstruct: 2)` reports an error when reconstruction fails).
-/

namespace Tests.ReconstructMatch

/-! ## `match` expressions -/

-- overlapping `Int` literal patterns
def classify (x : Int) : Nat :=
  match x with
  | 0 => 0
  | 1 => 1
  | -1 => 2
  | Int.ofNat (n + 2) => n + 3
  | Int.negSucc (n + 1) => n + 4

#blaster (reconstruct: 2) [∀ (x : Int), x > 1 → classify x = Int.toNat x + 1]
#blaster (reconstruct: 2) [∀ (x : Int), x < -1 → classify x = Int.toNat (-x) + 2]

-- named patterns
def namedPat (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | m@(k + 1) => m + k

#blaster (reconstruct: 2) [∀ (n : Nat), n > 0 → namedPat n = 2 * n - 1]

-- nested match on the same discriminant (eliminated with the match context)
def nestedSame (o : Option Nat) : Nat :=
  match o with
  | some x => match o with
              | some y => x + y
              | none => 0
  | none => 1

#blaster (reconstruct: 2) [∀ (x : Nat), nestedSame (some x) = 2 * x]
#blaster (reconstruct: 2) [∀ (o : Option Nat), o.isSome → nestedSame o % 2 = 0]

-- match returning a function (extra arguments)
def pick (b : Bool) : Nat → Nat :=
  match b with
  | true => fun n => n + 0
  | false => fun n => 0 + n

#blaster (reconstruct: 2) [∀ (b : Bool) (n : Nat), pick b n = n]

-- wildcard alternative over two lists
def bothNil (xs ys : List Nat) : Bool :=
  match xs, ys with
  | [], [] => true
  | _, _ => false

#blaster (reconstruct: 2) [∀ (xs ys : List Nat), bothNil xs ys = true → xs.length + ys.length = 0]

-- structures (the wildcard alternative is unreachable)
structure P where
  a : Nat
  b : Nat

def sumP (p q : P) : Nat :=
  match p, q with
  | ⟨a, b⟩, ⟨c, d⟩ => a + b + 0 + c + d

#blaster (reconstruct: 2) [∀ (p q : P), sumP p q = p.a + p.b + q.a + q.b]

-- enumerations with many constructors
inductive Day | mon | tue | wed | thu | fri | sat | sun

def isWeekend : Day → Bool
  | .sat | .sun => true
  | _ => false

#blaster (reconstruct: 2) [∀ (d : Day), isWeekend d = true → d = .sat ∨ d = .sun]

-- match in a hypothesis
#blaster (reconstruct: 2) [∀ (o : Option Nat), (match o with | some _ => True | none => False) → o ≠ none]

-- alternatives with several patterns
def xor' (a b : Bool) : Bool :=
  match a, b with
  | true, false | false, true => true
  | _, _ => false

#blaster (reconstruct: 2) [∀ (a b : Bool), xor' a b = (a != b)]

-- overlapping wildcards over `Option Bool`
def both (a b : Option Bool) : Bool :=
  match a, b with
  | some true, some true => true
  | some _, none => false
  | none, _ => false
  | _, _ => false

#blaster (reconstruct: 2) [∀ (a b : Option Bool), both a b = true → a = some true]

-- string literal patterns
def greet (s : String) : Nat :=
  match s with
  | "hi" => 1
  | "hello" => 2
  | _ => 0

#blaster (reconstruct: 2) [greet "hello" = 2]
#blaster (reconstruct: 2) [∀ (s : String), greet s ≤ 2]

-- tuples, `if let`, `Option` do-notation and sum types
def swapSum (p : Nat × Nat) : Nat := let (a, b) := p; b + a

#blaster (reconstruct: 2) [∀ (p : Nat × Nat), swapSum p = p.1 + p.2]

def firstOr (xs : List Nat) (d : Nat) : Nat :=
  if let x :: _ := xs then x else d

#blaster (reconstruct: 2) [∀ (x d : Nat) (xs : List Nat), firstOr (x :: xs) d = x]

def addOpt (a b : Option Nat) : Option Nat := do
  let x ← a
  let y ← b
  return x + y

#blaster (reconstruct: 2) [∀ (a b : Option Nat), addOpt a b = none → a = none ∨ b = none]
#blaster (reconstruct: 2) [∀ (x y : Nat), addOpt (some x) (some y) = some (y + x)]

def sumVal : Nat ⊕ Bool → Nat
  | .inl n => n
  | .inr b => if b then 1 else 0

#blaster (reconstruct: 2) [∀ (s : Nat ⊕ Bool), sumVal s = 0 → s ≠ Sum.inr true]

-- large literal patterns
def big (n : Nat) : Nat :=
  match n with
  | 1000 => 1
  | 2000 => 2
  | _ => 0

#blaster (reconstruct: 2) [∀ (n : Nat), big n = 2 → n = 2000]

-- match producing a proposition
def isPos (n : Int) : Prop :=
  match n with
  | Int.ofNat (_ + 1) => True
  | _ => False

#blaster (reconstruct: 2) [∀ (n : Int), isPos n → n > 0]

/-! ## Validator-like goals: matches on projections optimized under the match context, case of case,
    `· = true` pushed into the alternatives -/

inductive Purpose where
  | spending (n : Nat)
  | minting (s : String)
  | rewarding

structure Ctx where
  info : Nat
  purpose : Purpose

structure Input where
  datum : Option Nat
  redeemer : Nat
  ctx : Ctx

def validCtx (d : Option Nat) (r : Nat) (c : Ctx) : Bool :=
  match c.purpose, d with
  | .spending n, some x => n == x && r > 0
  | .minting _, none => true
  | _, _ => false

def validInput (i : Input) : Bool :=
  match i.ctx.purpose with
  | .spending _ => validCtx i.datum i.redeemer i.ctx
  | _ => false

def step (i : Input) : Option Nat :=
  match i.ctx.purpose with
  | .spending n =>
     match i.datum with
     | some d => if d = n then some (d + 1) else none
     | none => none
  | _ => none

def succeeds (o : Option Nat) : Prop :=
  match o with
  | some _ => True
  | none => False

#blaster (reconstruct: 2) [∀ (i : Input), succeeds (step i) → i.datum.isSome]
#blaster (reconstruct: 2) [∀ (i : Input), validInput i = true → i.redeemer > 0]
#blaster (reconstruct: 2) [∀ (i : Input), validInput i = true → succeeds (step i) → i.redeemer > 0]

end Tests.ReconstructMatch
