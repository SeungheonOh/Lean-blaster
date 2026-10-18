import Lean
import Blaster.Optimize.Decidable
import Blaster.Reconstruct.SmtProof.Interp
import Blaster.Reconstruct.Discharge

/-!
# Bridge between goals and the interpretation of their translation

The asserted formula of an SMT proof is Blaster's translation of the negated goal, which the replay
interprets back in Lean (see `Interp.lean`). The interpretation differs from the goal in the encodings
of the translation:
 - `match` expressions are translated to `ite` chains whose conditions are datatype testers and
   selectors (see `Blaster.Smt.Translate.Match`);
 - `Nat` terms are translated to `Int` terms, `Bool` terms to formulas;
 - `Blaster.dite'` (with non-dependent branches) and `ite` are translated to `ite`, etc.

This module proves the equality of a goal term `a` with the interpretation `b` of its translation by a
simultaneous traversal of both terms: congruence on their common structure, and lemmas for each
encoding at the points where they differ. The proven statement is `W(a) = b` where `W` is the
mapping to the SMT world: `(↑a : Int)` for `Nat` terms, `a = true` for `Bool` terms, `a` otherwise.

`match` expressions are related to their `ite` encoding by auxiliary theorems stated for abstract
discriminants and alternatives (i.e., small statements, proved once per matcher instance by `proveMatchIte`,
which splits the matcher and evaluates the conditions of the encoding with case analyses). Functions
translated as SMT macros (e.g., `Nat.sub` as `@Nat.sub`, expanded by the backends) are related to the
interpretation of their macros by auxiliary theorems proved once per function (by the tactics given by the
caller).
-/

open Lean Meta Elab

namespace Blaster.Reconstruct.SmtProof.Bridge

/-- Debugging output (environment variable `BLASTER_BRIDGE_DEBUG`). -/
def dbg (msg : MessageData) : MetaM Unit := do
  match ← IO.getEnv "BLASTER_BRIDGE_DEBUG" with
  | none => pure ()
  | some "1" => IO.eprintln (← msg.toString)
  | some f =>
      let h ← IO.FS.Handle.mk f .append
      h.putStrLn (← msg.toString)

/-! ## Lemmas -/

theorem ite_congr' {α : Sort u} {c c' : Prop} [h : Decidable c] {x x' y y' : α}
    (hc : c = c') (hx : x = x') (hy : y = y') :
    @ite α c h x y = @ite α c' (Classical.propDecidable c') x' y' := by
  subst hc hx hy; by_cases hc : c <;> simp [hc]

theorem ite_congr_dep {α : Sort u} {c c' : Prop} [h : Decidable c] {x x' y y' : α}
    (hc : c = c') (hx : c → x = x') (hy : ¬ c → y = y') :
    @ite α c h x y = @ite α c' (Classical.propDecidable c') x' y' := by
  subst hc; by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact hx hc
  · rw [if_neg hc, if_neg hc]; exact hy hc

theorem dite_congr_dep {α : Sort u} {c c' : Prop} [h : Decidable c] {x : c → α} {y : ¬ c → α} {x' y' : α}
    (hc : c = c') (hx : ∀ h, x h = x') (hy : ∀ h, y h = y') :
    @dite α c h x y = @ite α c' (Classical.propDecidable c') x' y' := by
  subst hc; by_cases hc : c
  · rw [dif_pos hc, if_pos hc]; exact hx hc
  · rw [dif_neg hc, if_neg hc]; exact hy hc

theorem natCast_dite_congr {c c' : Prop} [h : Decidable c] {x : c → Nat} {y : ¬ c → Nat} {x' y' : Int}
    (hc : c = c') (hx : ∀ h, ((x h : Nat) : Int) = x') (hy : ∀ h, ((y h : Nat) : Int) = y') :
    ((@dite Nat c h x y : Nat) : Int) = @ite Int c' (Classical.propDecidable c') x' y' := by
  subst hc; by_cases hc : c
  · rw [dif_pos hc, if_pos hc]; exact hx hc
  · rw [dif_neg hc, if_neg hc]; exact hy hc

theorem boolEq_dite_congr {c c' : Prop} [h : Decidable c] {x : c → Bool} {y : ¬ c → Bool} {x' y' : Prop}
    (hc : c = c') (hx : ∀ h, (x h = true) = x') (hy : ∀ h, (y h = true) = y') :
    ((@dite Bool c h x y) = true) = @ite Prop c' (Classical.propDecidable c') x' y' := by
  subst hc; by_cases hc : c
  · rw [dif_pos hc, if_pos hc]; exact hx hc
  · rw [dif_neg hc, if_neg hc]; exact hy hc

theorem nat_sub_bridge {x y : Nat} {x' y' : Int} (h : y ≤ x) (hx : (x : Int) = x') (hy : (y : Int) = y') :
    ((x - y : Nat) : Int) = x' - y' := by
  subst hx hy; omega

theorem toNat_bridge {x x' : Int} (h : 0 ≤ x) (hx : x = x') : ((Int.toNat x : Nat) : Int) = x' := by
  subst hx; omega

theorem dite'_ite {α : Sort u} (c : Prop) (x y : α) :
    Blaster.dite' c (fun _ => x) (fun _ => y) = @ite α c (Classical.propDecidable c) x y := by
  have h := congrFun (congrFun (congrFun (congrFun (congrFun Blaster.ite_to_dite'_equiv α) c)
    (Classical.propDecidable c)) x) y
  exact h.symm

theorem natCast_ite {c : Prop} [h : Decidable c] (x y : Nat) :
    ((@ite Nat c h x y : Nat) : Int) = @ite Int c h (x : Int) (y : Int) := by
  split <;> rfl

theorem boolEq_ite {c : Prop} [h : Decidable c] (x y : Bool) :
    ((@ite Bool c h x y) = true) = @ite Prop c h (x = true) (y = true) := by
  split <;> rfl

theorem nat_eq {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (x = y) = (x' = y') := by
  subst hx hy; exact propext Int.natCast_inj.symm

theorem nat_le {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (x ≤ y) = (x' ≤ y') := by
  subst hx hy; exact propext Int.ofNat_le.symm

theorem nat_lt {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (x < y) = (x' < y') := by
  subst hx hy; exact propext Int.ofNat_lt.symm

theorem bool_eq {x y : Bool} {x' y' : Prop} (hx : (x = true) = x') (hy : (y = true) = y') :
    (x = y) = (x' = y') := by
  subst hx hy; cases x <;> cases y <;> simp

theorem iff_eq {p q p' q' : Prop} (hp : p = p') (hq : q = q') : (p ↔ q) = (p' = q') := by
  subst hp hq; exact propext ⟨propext, fun h => h ▸ Iff.rfl⟩

theorem nat_add {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    ((x + y : Nat) : Int) = x' + y' := by
  subst hx hy; exact Int.natCast_add x y

theorem nat_mul {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    ((x * y : Nat) : Int) = x' * y' := by
  subst hx hy; exact Int.natCast_mul x y

theorem bool_and {x y : Bool} {x' y' : Prop} (hx : (x = true) = x') (hy : (y = true) = y') :
    ((x && y) = true) = (x' ∧ y') := by
  subst hx hy; simp

theorem bool_or {x y : Bool} {x' y' : Prop} (hx : (x = true) = x') (hy : (y = true) = y') :
    ((x || y) = true) = (x' ∨ y') := by
  subst hx hy; simp

theorem bool_not {x : Bool} {x' : Prop} (hx : (x = true) = x') : ((!x) = true) = ¬ x' := by
  subst hx; cases x <;> simp

theorem bool_decide {a : Bool} {p : Prop} (h : (a = true) = p) : a = @decide p (Classical.propDecidable p) := by
  subst h; cases a <;> simp

theorem nat_toNat {a : Nat} {b : Int} (h : (a : Int) = b) : a = Int.toNat b := by
  subst h; simp

theorem bool_true : (true = true) = True := by simp
theorem bool_false : (false = true) = False := by simp

theorem decide'_eq {p p' : Prop} (h : p = p') : (Blaster.decide' p = true) = p' := by
  subst h; exact propext (Blaster.decide'_true p)

theorem decide_eq {p p' : Prop} [Decidable p] (h : p = p') : (decide p = true) = p' := by
  subst h; simp

theorem beq_eq {α : Type u} [BEq α] [LawfulBEq α] {x y x' y' : α} (hx : x = x') (hy : y = y') :
    ((x == y) = true) = (x' = y') := by
  subst hx hy; simp

theorem nat_beq [BEq Nat] [LawfulBEq Nat] {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    ((x == y) = true) = (x' = y') := by
  subst hx hy; simp [Int.natCast_inj]

theorem true_eq {e : Bool} {p : Prop} (h : (e = true) = p) : (true = e) = p := by
  subst h; cases e <;> simp

theorem false_eq {e : Bool} {p : Prop} (h : (e = true) = p) : (false = e) = ¬ p := by
  subst h; cases e <;> simp

theorem eq_false' {e : Bool} {p : Prop} (h : (e = true) = p) : (e = false) = ¬ p := by
  subst h; cases e <;> simp

theorem nat_ble {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (Nat.ble x y = true) = (x' ≤ y') := by
  subst hx hy; simp [Nat.ble_eq, Int.ofNat_le]

theorem nat_beq' {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (Nat.beq x y = true) = (x' = y') := by
  subst hx hy; simp [Nat.beq_eq, Int.natCast_inj]

theorem nat_forall {p : Nat → Prop} {q : Int → Prop} (h : ∀ n : Nat, p n = q (n : Int)) :
    (∀ n, p n) = (∀ x : Int, 0 ≤ x → q x) := by
  apply propext; constructor
  · intro hp x hx
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    rw [← h]; exact hp n
  · intro hq n; rw [h]; exact hq n (Int.natCast_nonneg n)

theorem nat_exists {p : Nat → Prop} {q : Int → Prop} (h : ∀ n : Nat, p n = q (n : Int)) :
    (∃ n, p n) = (∃ x : Int, 0 ≤ x ∧ q x) := by
  apply propext; constructor
  · intro ⟨n, hn⟩; exact ⟨n, Int.natCast_nonneg n, h n ▸ hn⟩
  · intro ⟨x, hx, hq⟩
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    exact ⟨n, (h n).symm ▸ hq⟩

theorem true_imp {p p' : Prop} (h : p = p') : p = (True → p') := by
  subst h; exact propext ⟨fun h _ => h, fun h => h trivial⟩

/-! ## Worlds -/

/-- Relation between a goal term and the interpretation of its translation. -/
inductive World where
  /-- same type: `a = b` -/
  | same
  /-- `Nat` term interpreted as an `Int` term: `(↑a : Int) = b` -/
  | nat
  /-- `Bool` term interpreted as a proposition: `(a = true) = b` -/
  | bool
  deriving BEq, Inhabited

def natCast (a : Expr) : Expr :=
  mkApp3 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt) a

def boolTrue (a : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) a (mkConst ``Bool.true)

def World.lift : World → Expr → Expr
  | .same, a => a
  | .nat, a => natCast a
  | .bool, a => boolTrue a

def worldOf (ta tb : Expr) : MetaM (Option World) := do
  if ta == tb then return some .same
  -- NOTE: types may be given by aliases (e.g., `abbrev Integer := Int`)
  let ta' ← whnfD ta
  let tb' ← whnfD tb
  if ta'.isConstOf ``Nat && tb'.isConstOf ``Int then return some .nat
  if ta'.isConstOf ``Bool && tb'.isProp then return some .bool
  if ← isDefEq ta tb then return some .same
  return none

/-! ## Matchers -/

/-- Translation of a match alternative: the conditions on the discriminants (in the order of
    Blaster's translation) and the values of the pattern variables. -/
structure AltView where
  conds : Array Expr
  vals : Array Expr

def isLiteral (e : Expr) : Bool :=
  let natLit (n : Expr) : Bool := n.isRawNatLit || (n.isAppOfArity ``OfNat.ofNat 3 && (n.getArg! 1).isRawNatLit)
  e.isRawNatLit || e.isStringLit || e.isConstOf ``Bool.true || e.isConstOf ``Bool.false ||
  ((e.isAppOfArity ``Int.ofNat 1 || e.isAppOfArity ``Int.negSucc 1) && natLit e.appArg!) ||
  (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isRawNatLit)

/-- `N + q` patterns on `Nat` (Blaster's `Nat.add N q`, `q + N`, `Nat.succ q`): `(N, q)`. -/
partial def natOffset? (p : Expr) : Option (Nat × Expr) :=
  let lit? (e : Expr) : Option Nat :=
    match e with
    | .lit (.natVal n) => some n
    | _ => if e.isAppOfArity ``OfNat.ofNat 3 then (match e.getArg! 1 with | .lit (.natVal n) => some n | _ => none) else none
  let rec go (p : Expr) (acc : Nat) : Option (Nat × Expr) :=
    if p.isAppOfArity ``Nat.succ 1 then go p.appArg! (acc + 1)
    else if p.isAppOfArity ``Nat.add 2 then
      match lit? (p.getArg! 0) with
      | some n => go (p.getArg! 1) (acc + n)
      | none => (match lit? (p.getArg! 1) with
          | some n => go (p.getArg! 0) (acc + n)
          | none => if acc == 0 then none else some (acc, p))
    else if p.isAppOfArity ``HAdd.hAdd 6 then
      match lit? (p.getArg! 5) with
      | some n => go (p.getArg! 4) (acc + n)
      | none => if acc == 0 then none else some (acc, p)
    else if acc == 0 then none else some (acc, p)
  go p 0

def mkNatLe (a b : Expr) : Expr := mkApp4 (mkConst ``LE.le [levelZero]) (mkConst ``Nat) (mkConst ``instLENat) a b

/-- Conditions and values of the `Nat`/`Int` patterns with variables (see `mkCond` and `mkLet` in
    `Blaster.Smt.Translate.Match`): `N + n` (`N ≤ x`, `n := x - N`), `Int.ofNat n` (`0 ≤ x`, `n := x.toNat`),
    `Int.ofNat (N + n)` (`N ≤ x`, `n := (x - N).toNat`), `Int.negSucc n` (`x ≤ -1`, `n := (-x - 1).toNat`).
    Returns the condition and the pattern of the variable with its value. -/
def numPattern? (x p : Expr) : Option (Expr × Expr × Expr) := Id.run do
  let natLit (n : Nat) : Expr := mkRawNatLit n
  if let some (n, q) := natOffset? p then
    return some (mkNatLe (natLit n) x, q,
      mkApp6 (mkConst ``HSub.hSub [levelZero, levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat)
        (mkApp2 (mkConst ``instHSub [levelZero]) (mkConst ``Nat) (mkConst ``instSubNat)) x (natLit n))
  if p.isAppOfArity ``Int.ofNat 1 then
    let q := p.appArg!
    if let some (n, q') := natOffset? q then
      return some (mkIntLe (mkIntLit n) x, q', mkApp (mkConst ``Int.toNat) (mkIntSub x (mkIntLit n)))
    return some (mkIntLe (mkIntLit 0) x, q, mkApp (mkConst ``Int.toNat) x)
  if p.isAppOfArity ``Int.negSucc 1 then
    return some (mkIntLe x (mkIntNeg (mkIntLit 1)), p.appArg!, mkApp (mkConst ``Int.toNat) (mkIntSub (mkIntNeg x) (mkIntLit 1)))
  return none

/-- Conditions of pattern `p` on the discriminant `x` (see `mkCond` in `Blaster.Smt.Translate.Match`).
    Returns `none` for unsupported patterns. -/
partial def patCond (x p : Expr) (acc : Array Expr) : MetaM (Option (Array Expr)) := do
  let p := removeNamed p
  -- NOTE: the named patterns below the root are removed (see `removeNamedPatternExpr`)
  let p := p.replace fun e => if e.isAppOfArity ``namedPattern 4 then some (removeNamed e) else none
  -- literals
  if isLiteral p then return some (acc.push (← mkEq p x))
  if p.isFVar then return some acc
  if let some (c, q, _) := numPattern? x p then
    -- NOTE: the variable of the pattern has no condition
    if q.isFVar then return some (acc.push c)
    return none
  let .const c _ := p.getAppFn | return none
  let some (.ctorInfo info) := (← getEnv).find? c | return none
  let args := p.getAppArgs
  if args.size != info.numParams + info.numFields then return none
  -- `Nat`/`Int` patterns (e.g., `n + 1`) are not supported (their translation needs the conditions
  -- of the branch)
  if info.induct == ``Nat || info.induct == ``Int then return none
  let mut acc := acc.push (← mkTester c x)
  for i in [:info.numFields] do
    let s ← mkSelector c i x
    let some acc' ← patCond s args[info.numParams + i]! acc | return none
    acc := acc'
  return some acc
where
  removeNamed (p : Expr) : Expr :=
    if p.isAppOfArity ``namedPattern 4 then removeNamed p.getAppArgs[2]! else p

/-- Values of the variables of pattern `p` matched against `x` (see `mkLet` in
    `Blaster.Smt.Translate.Match`), as a substitution of the variables. -/
partial def patVals (x p : Expr) (acc : Std.HashMap FVarId Expr) : MetaM (Option (Std.HashMap FVarId Expr)) := do
  if p.isAppOfArity ``namedPattern 4 then
    let args := p.getAppArgs
    let .fvar n := args[1]! | return none
    return ← patVals x args[2]! (acc.insert n x)
  if let .fvar v := p then return some (acc.insert v x)
  if isLiteral p then return some acc
  if let some (_, q, v) := numPattern? x p then
    if let .fvar n := q then return some (acc.insert n v)
    -- named pattern below the numeric pattern (e.g., `Int.ofNat (n@0)`): `n` and the variables of its pattern
    if q.isAppOfArity ``namedPattern 4 then return ← patVals v q acc
    return none
  -- named literal below `Int.ofNat` (e.g., `Int.ofNat (n@0)`): `n := x.toNat`
  if p.isAppOfArity ``Int.ofNat 1 && p.appArg!.isAppOfArity ``namedPattern 4 then
    return ← patVals (mkApp (mkConst ``Int.toNat) x) p.appArg! acc
  let .const c _ := p.getAppFn | return none
  let some (.ctorInfo info) := (← getEnv).find? c | return none
  if info.induct == ``Nat || info.induct == ``Int then return none
  let args := p.getAppArgs
  let mut acc := acc
  for i in [:info.numFields] do
    let some acc' ← patVals (← mkSelector c i x) args[info.numParams + i]! acc | return none
    acc := acc'
  return some acc

/-- Types of the alternatives of matcher `m` (with level parameters `lvls`) for the parameters `params`,
    a motive given as a free variable, and discriminants `discrs`: the patterns are the arguments of the
    motive. `inst` is Blaster's optimized instance of the matcher (when known), whose alternative types
    are the patterns as translated. -/
def altTypes (m : Name) (lvls : List Level) (info : MatcherInfo) (inst? : Option Expr)
    (params : Array Expr) (motive : Expr) (discrs : Array Expr) : MetaM (Array Expr) := do
  let args := params ++ #[motive] ++ discrs
  match inst? with
  | some inst =>
      -- `fun params motive discrs alts => ...`
      let mut e := inst
      for a in args do
        let .lam _ _ b _ := e | throwError "bridge: unexpected matcher instance"
        e := b.instantiate1 a
      let mut ts := #[]
      for _ in [:info.numAlts] do
        let .lam _ t b _ := e | throwError "bridge: unexpected matcher instance"
        ts := ts.push t
        e := b
      if ts.any (·.hasLooseBVars) then throwError "bridge: dependent alternatives"
      return ts
  | none =>
      let ty ← instantiateForall (← inferType (mkConst m lvls)) args
      let mut e := ty
      let mut ts := #[]
      for _ in [:info.numAlts] do
        let .forallE _ t b _ := e | throwError "bridge: unexpected matcher type"
        ts := ts.push t
        e := b
      if ts.any (·.hasLooseBVars) then throwError "bridge: dependent alternatives"
      return ts

/-- `ite` chain of Blaster's translation of `M params motive discrs alts`, given the types of the
    alternatives (with motive `mv`, a free variable): `if c₁ then alt₁ v⃗₁ else ... altₙ v⃗ₙ` where the
    last alternative has no condition, and an alternative without conditions ends the chain. The
    applications of the alternatives are β-reduced when `beta` is set. -/
def iteOf (ty : Expr) (mv : Expr) (altTys : Array Expr) (discrs alts : Array Expr) (beta : Bool) :
    Term.TermElabM (Option Expr) := do
  let u ← getLevel ty
  -- per alternative: the condition and the application of the alternative given a proof of the condition
  -- (for the proof parameters of named patterns `x@h:p`, whose equations hold under the condition)
  let mut branches : Array (Option Expr × (Option Expr → Term.TermElabM (Option Expr)) × Bool) := #[]
  for j in [:altTys.size] do
    let r ← forallTelescope altTys[j]! fun ys concl => do
      -- patterns: the arguments of the motive
      if !concl.isApp || concl.getAppFn != mv then dbg m!"bridge: unexpected alternative type {altTys[j]!}"; return none
      let pats := concl.getAppArgs
      if pats.size != discrs.size then dbg m!"bridge: unexpected patterns {pats}"; return none
      let mut conds := #[]
      let mut vals : Std.HashMap FVarId Expr := {}
      for (d, p) in discrs.zip pats do
        let some cs ← patCond d p conds | dbg m!"bridge: unsupported pattern {p}"; return none
        conds := cs
        let some vs ← patVals d p vals | dbg m!"bridge: unsupported pattern {p}"; return none
        vals := vs
      -- arguments of the alternative: the values of the pattern variables (`()` for `Unit`), proofs of the
      -- equations of named patterns (`none`)
      let mut args : Array (Option Expr) := #[]
      for y in ys do
        if let some v := vals.get? y.fvarId! then args := args.push (some v)
        else if (← inferType y).isConstOf ``Unit then args := args.push (some (mkConst ``Unit.unit))
        else if ← isProp (← inferType y) then args := args.push none
        else dbg m!"bridge: no value for the pattern variable {y} of {altTys[j]!}"; return none
      let dependent := args.any (·.isNone)
      let alt := alts[j]!
      let mk (hc? : Option Expr) : Term.TermElabM (Option Expr) := do
        let mut app := alt
        for a? in args do
          match a? with
          | some v => app := mkApp app v
          | none =>
              let some _ := hc? | return none
              let .forallE _ dom _ _ ← whnf (← inferType app) | return none
              let some pf ← proveEquation dom | dbg m!"bridge: equation of a named pattern not proved: {dom}"; return none
              app := mkApp app pf
        return some (if beta then app.headBeta else app)
      let cond ← if conds.isEmpty then pure none else some <$> foldAnd conds
      return some (cond, mk, dependent)
    let some b := r | return none
    branches := branches.push b
    if b.1.isNone then break
  let some (_, mkLast, depLast) := branches.back? | return none
  if depLast then return none
  let some last ← mkLast none | return none
  let mut acc := last
  for (c?, mk, dependent) in branches.pop.reverse do
    let some c := c? | return none
    let inst := mkApp (mkConst ``Classical.propDecidable) c
    if dependent then
      let some t ← withLocalDeclD `hc c fun hc => do
          let some app ← mk (some hc) | return none
          return some (← mkLambdaFVars #[hc] app)
        | return none
      acc := mkApp5 (mkConst ``dite [u]) ty c inst t (mkLambda `hc .default (mkNot c) acc)
    else
      let some app ← mk none | return none
      acc := mkApp5 (mkConst ``ite [u]) ty c inst app acc
  return some acc
where
  foldAnd (cs : Array Expr) : MetaM Expr := do
    let mut acc := cs.back!
    for c in cs.pop.reverse do acc := mkAnd c acc
    return acc
  /-- Proof of the equation of a named pattern under the condition of its alternative (in the local context). -/
  proveEquation (p : Expr) : Term.TermElabM (Option Expr) := do
    for tac in [← `(tactic| (subst_vars; rfl)), ← `(tactic| omega), ← `(tactic| (simp_all; done)),
                ← `(tactic| (rename_i h; cases h; subst_vars; simp_all))] do
      if let some pf ← Blaster.Reconstruct.proveWithTactic p tac then return some pf
    return none

/-- β-reduction of the alternatives of an `ite`/`dite` chain (see `iteOf`). -/
partial def betaChain (e : Expr) : Expr :=
  if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, args[3]!.headBeta, betaChain args[4]!]
  else if e.isAppOfArity ``dite 5 then
    let args := e.getAppArgs
    let t := match args[3]! with
      | .lam n ty b bi => Expr.lam n ty b.headBeta bi
      | t => t
    let f := match args[4]! with
      | .lam n ty b bi => Expr.lam n ty (betaChain b) bi
      | f => f
    mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, t, f]
  else e.headBeta

/-! ## Proofs of the matcher equations -/

/-- Value of a condition of the `ite` encoding (a conjunction of testers and literal equalities), possibly
    after a case analysis. -/
inductive CondVal where
  | isTrue (pf : Expr)
  | isFalse (pf : Expr)
  /-- case analysis needed on a free variable -/
  | splitFVar (x : FVarId)
  /-- case analysis needed on a proposition (an equality between a variable and a literal) -/
  | splitProp (p : Expr)
  | unknown

/-- Free variable whose case analysis unblocks `e` (a stuck recursor application whose major premise is a
    free variable or a projection of a free variable). -/
def stuckMajor? (e : Expr) : MetaM (Option FVarId) := do
  let .const n _ := e.getAppFn | return none
  let env ← getEnv
  let idx? : Option Nat := match env.find? n with
    | some (.recInfo info) => some info.getMajorIdx
    | _ => none
  let some idx := idx? | return none
  let some m := e.getAppArgs[idx]? | return none
  match ← whnfD m with
  | .fvar f => return some f
  | .proj _ _ s =>
      let .fvar f ← whnfD s | return none
      return some f
  | _ => return none

partial def evalCond (c : Expr) : Term.TermElabM CondVal := do
  let c := c.consumeMData
  if c.isAppOfArity ``And 2 then
    let a := c.appFn!.appArg!
    let b := c.appArg!
    match ← evalCond a with
    | .isTrue pa =>
        match ← evalCond b with
        | .isTrue pb => return .isTrue (mkApp4 (mkConst ``And.intro) a b pa pb)
        | .isFalse nb => return .isFalse (mkLambda `h .default c (mkApp nb (mkApp3 (mkConst ``And.right) a b (.bvar 0))))
        | r => return r
    | .isFalse na => return .isFalse (mkLambda `h .default c (mkApp na (mkApp3 (mkConst ``And.left) a b (.bvar 0))))
    | r => return r
  let c' ← whnfD c
  if c'.isConstOf ``True then return .isTrue (← mkExpectedTypeHint (mkConst ``True.intro) c)
  if c'.isConstOf ``False then return .isFalse (mkLambda `h .default c (.bvar 0))
  if let some (_, l, r) := c'.eq? then
    let l ← whnfD l
    let r ← whnfD r
    if isLiteral l && isLiteral r then
      if ← isDefEq l r then return .isTrue (← mkEqRefl l)
      let pf ← mkDecideProof (mkNot (← mkEq l r))
      return .isFalse (← mkExpectedTypeHint pf (mkNot c))
    let (v, lit) := if isLiteral l then (r, l) else (l, r)
    if let some x ← stuckMajor? v then return .splitFVar x
    -- field of a structure variable
    if let .proj _ _ st := v then
      if let .fvar x ← whnfD st then return .splitFVar x
    if v.isFVar && isLiteral lit then
      -- hypothesis `¬ v = lit` (resp. `¬ lit = v`) of a previous case analysis
      for d in ← getLCtx do
        if let some p := d.type.not? then
          if let some (_, a, b) := p.eq? then
            -- NOTE: `c` is `l = r` up to reduction
            let ty ← inferType v
            let u ← getLevel ty
            if (a == l && b == r) then
              return .isFalse (mkLambda `h .default c (mkApp d.toExpr (.bvar 0)))
            if (a == r && b == l) then
              return .isFalse (mkLambda `h .default c (mkApp d.toExpr (mkApp4 (mkConst ``Eq.symm [u]) ty l r (.bvar 0))))
      return .splitProp (← mkEq v lit)
    return .unknown
  if let some x ← stuckMajor? c' then return .splitFVar x
  -- arithmetic conditions (e.g., of `n + 1` patterns): decided by `omega` in the context of the case analysis
  let arith := c'.isAppOfArity ``LE.le 4 || c'.isAppOfArity ``LT.lt 4
  if arith then
    if let some p ← Blaster.Reconstruct.proveWithTactic c (← `(tactic| omega)) then return .isTrue p
    if let some p ← Blaster.Reconstruct.proveWithTactic (mkNot c) (← `(tactic| omega)) then return .isFalse p
  dbg m!"bridge: unknown atom {c'}"
  return .unknown

/-- Close `g` with an overlap hypothesis of the splitter (`∀ ys, x = p → False`) whose equalities hold by
    unification. -/
def closeByOverlap (g : MVarId) (base : Nat) : MetaM Bool := g.withContext do
  for d in ← getLCtx do
    -- only the hypotheses of the proof (not the ones of the context)
    if d.index < base || d.isImplementationDetail || !d.type.isForall then continue
    let s ← saveState
    let ok ← try
        let (ms, _, body) ← forallMetaTelescopeReducing d.type
        if !body.isConstOf ``False then pure false
        else
          let mut ok := true
          for m in ms do
            let t ← instantiateMVars (← inferType m)
            if let some (_, a, b) := t.eq? then
              if ← isDefEq a b then m.mvarId!.assign (← mkEqRefl a) else ok := false; break
          if ok then
            let pf ← instantiateMVars (mkAppN d.toExpr ms)
            if pf.hasExprMVar then pure false
            else
              g.assign (← mkFalseElim (← g.getType) pf)
              pure true
          else pure false
      catch _ => pure false
    if ok then return true
    s.restore
  return false

/-- Prove `lhs = rhs`, where `rhs` is an `ite` chain over conditions decided by case analysis, by
    evaluating the conditions (with case analyses on the variables and literal equalities blocking them). -/
partial def solveIte (g : MVarId) (fuel : Nat) (base : Nat) : Term.TermElabM Bool := g.withContext do
  if fuel == 0 then return false
  if ← closeByOverlap g base then return true
  let tgt ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := tgt.eq? | return false
  if rhs.isAppOfArity ``ite 5 then
    let args := rhs.getAppArgs
    let (α, c, inst, t, e) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
    match ← evalCond c with
    | .isTrue pc =>
        let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs t)
        let h ← mkAppOptM ``if_pos #[c, inst, pc, α, t, e]
        g.assign (← mkEqTrans g' (← mkEqSymm h))
        solveIte g'.mvarId! (fuel - 1) base
    | .isFalse pnc =>
        let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs e)
        let h ← mkAppOptM ``if_neg #[c, inst, pnc, α, t, e]
        g.assign (← mkEqTrans g' (← mkEqSymm h))
        solveIte g'.mvarId! (fuel - 1) base
    | .splitFVar x =>
        let gs ← try g.cases x catch ex =>
          dbg m!"bridge: cases failed {ex.toMessageData} in {g}"
          return false
        gs.allM fun s => solveIte s.mvarId (fuel - 1) base
    | .splitProp p =>
        let (s₁, s₂) ← g.byCases p
        let g₁ : MVarId := (← subst? s₁.mvarId s₁.fvarId).getD s₁.mvarId
        if !(← solveIte g₁ (fuel - 1) base) then return false
        solveIte s₂.mvarId (fuel - 1) base
    | .unknown =>
        dbg m!"bridge: unknown condition {c} ⟶ {← whnfD c} in {g}"
        return false
  else if rhs.isAppOfArity ``dite 5 then
    let args := rhs.getAppArgs
    let (α, c, inst, t, e) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
    match ← evalCond c with
    | .isTrue pc =>
        let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs (mkApp t pc).headBeta)
        let h ← mkAppOptM ``dif_pos #[c, inst, pc, α, t, e]
        g.assign (← mkEqTrans g' (← mkEqSymm h))
        solveIte g'.mvarId! (fuel - 1) base
    | .isFalse pnc =>
        let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs (mkApp e pnc).headBeta)
        let h ← mkAppOptM ``dif_neg #[c, inst, pnc, α, t, e]
        g.assign (← mkEqTrans g' (← mkEqSymm h))
        solveIte g'.mvarId! (fuel - 1) base
    | .splitFVar x =>
        let gs ← try g.cases x catch _ => return false
        gs.allM fun s => solveIte s.mvarId (fuel - 1) base
    | .splitProp p =>
        let (s₁, s₂) ← g.byCases p
        let g₁ : MVarId := (← subst? s₁.mvarId s₁.fvarId).getD s₁.mvarId
        if !(← solveIte g₁ (fuel - 1) base) then return false
        solveIte s₂.mvarId (fuel - 1) base
    | .unknown => return false
  else
    try g.refl; return true
    catch _ =>
      dbg m!"bridge: leaf {g}"
      return false

/-- Prove a matcher equation `∀ xs alts, M params motive xs alts = ite ...` (see `iteOf`). -/
def proveMatchIte (stmt : Expr) (fuel := 256) : Term.TermElabM (Option Expr) := do
  let m ← mkFreshExprMVar stmt
  let base := (← getLCtx).decls.size
  let s ← saveState
  try
    let (_, g) ← m.mvarId!.intros
    let ok ← g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let some (_, lhs, _) := tgt.eq? | return false
      let gs ← try Split.splitMatch g lhs catch _ => pure [g]
      gs.allM (solveIte · fuel base)
    if !ok then s.restore; return none
    let pf ← instantiateMVars m
    if pf.hasExprMVar then s.restore; return none
    return some pf
  catch ex =>
    dbg m!"bridge: {ex.toMessageData}"
    s.restore; return none

/-! ## Traversal -/

structure Cfg where
  /-- Blaster's optimized instances of the matchers (whose alternative types are the patterns as
      translated) -/
  matchInst : Name → Option Expr := fun _ => none
  /-- maximal size of the terms compared by unification when they differ syntactically (e.g., literals) -/
  defeqSize : Nat := 64
  /-- SMT macros (`define-fun`) translating Lean functions (e.g., `Nat.sub`, `Int.toNat`): the
      interpretation of the body of the macro of a function for given arguments (in the SMT world) -/
  macroOf : Name → Option (Array Expr → MetaM Expr) := fun _ => none
  /-- prover of the auxiliary lemmas relating functions and their macros -/
  proveLemma : Expr → Term.TermElabM (Option Expr) := fun _ => pure none
  /-- hypotheses of the current branch (free variables), e.g., the conditions of the `ite` encoding of a
      `match` on `Nat`/`Int` patterns -/
  facts : Array Expr := #[]

structure State where
  cache : Std.HashMap (Expr × Expr) (Option Expr) := {}
  /-- matcher equations, per matcher instance (`M params motive`) -/
  lemmas : Std.HashMap Expr (Option Expr) := {}
  /-- macro equations, per function -/
  macroLemmas : Std.HashMap Name (Option Expr) := {}
  /-- pairs of terms that could not be related (for diagnostics) -/
  failures : Array (Expr × Expr) := #[]

abbrev BridgeM := ReaderT Cfg (StateRefT State Term.TermElabM)

/-- `∀ xs alts, M params motive xs alts = ite ...`, proved once per matcher instance (as an auxiliary
    theorem). -/
def matcherLemma (m : Name) (lvls : List Level) (info : MatcherInfo) (params : Array Expr) (motive resTy : Expr) :
    BridgeM (Option Expr) := do
  let head := mkAppN (mkConst m lvls) (params.push motive)
  if let some l := (← get).lemmas.get? head then return l
  let inst? := (← read).matchInst m
  let l ← try
      forallBoundedTelescope (← inferType head) (some (info.numDiscrs + info.numAlts)) fun xs _ => do
        let xd := xs.extract 0 info.numDiscrs
        let fs := xs.extract info.numDiscrs xs.size
        let some rhs ← withLocalDeclD `m (← inferType motive) fun mv => do
            let tys ← altTypes m lvls info inst? params mv xd
            iteOf resTy mv tys xd fs false
          | return none
        let stmt ← mkForallFVars xs (← mkEq (mkAppN head xs) rhs)
        let some pf ← proveMatchIte stmt | dbg m!"bridge: matcher equation not proved: {stmt}"; return none
        -- NOTE: the statement may refer to free variables of the goal (e.g., in the parameters of the
        -- matcher), but not the proof
        some <$> mkAuxTheorem stmt pf
    catch ex => dbg m!"bridge: matcher lemma {m}: {ex.toMessageData}"; pure none
  modify fun s => { s with lemmas := s.lemmas.insert head l }
  return l

/-- `(i, a = i)` where `i` is the `ite` encoding of the matcher application `a` (with β-reduced alternatives). -/
def matcherIte? (a : Expr) : BridgeM (Option (Expr × Expr)) := do
  let .const m lvls := a.getAppFn | return none
  let some info ← getMatcherInfo? m | return none
  let args := a.getAppArgs
  if args.size != info.arity then dbg m!"bridge: over-applied matcher {m}"; return none
  if info.discrInfos.any (·.hName?.isSome) then dbg m!"bridge: matcher with discriminant equations {m}"; return none
  let np := info.numParams
  let params := args.extract 0 np
  let motive := args[np]!
  let discrs := args.extract (np + 1) (np + 1 + info.numDiscrs)
  let alts := args.extract (np + 1 + info.numDiscrs) args.size
  -- non-dependent motive
  let some resTy ← lambdaTelescope motive fun xs b => do
      if xs.any (fun x => b.containsFVar x.fvarId!) then return none else return some b
    | dbg m!"bridge: dependent motive {motive}"; return none
  let some lem ← matcherLemma m lvls info params motive resTy | return none
  -- the encoding of `a`: the right-hand side of the instance of the lemma (with β-reduced alternatives)
  let pf := mkAppN lem (discrs ++ alts)
  let some (_, _, rhs) := (← instantiateMVars (← inferType pf)).eq? | return none
  let i := betaChain rhs
  return some (i, ← mkExpectedTypeHint pf (← mkEq a i))

/-- `ite`-like terms of goals: `(α, c, inst, x, y, a = @ite α c inst x y)` for `ite`, `dite` and
    `Blaster.dite'` with non-dependent branches. -/
def iteView? (a : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr × Expr)) := do
  if a.isAppOfArity ``ite 5 then
    let args := a.getAppArgs
    return some (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, ← mkEqRefl a)
  let branch (f : Expr) : Option Expr :=
    match f with
    | .lam _ _ b _ => if b.hasLooseBVars then none else some b
    | _ => none
  if a.isAppOfArity ``dite 5 then
    let args := a.getAppArgs
    let some x := branch args[3]! | return none
    let some y := branch args[4]! | return none
    let i := mkAppN a.getAppFn #[] |>.constLevels!
    let ite := mkApp5 (mkConst ``ite i) args[0]! args[1]! args[2]! x y
    -- `dite c (fun _ => x) (fun _ => y)` is `ite c x y` by definition
    return some (args[0]!, args[1]!, args[2]!, x, y, ← mkExpectedTypeHint (← mkEqRefl a) (← mkEq a ite))
  if a.isAppOfArity ``Blaster.dite' 4 then
    let args := a.getAppArgs
    let some x := branch args[2]! | return none
    let some y := branch args[3]! | return none
    let c := args[1]!
    let pf := mkApp4 (mkConst ``dite'_ite a.getAppFn.constLevels!) args[0]! c x y
    return some (args[0]!, c, mkApp (mkConst ``Classical.propDecidable) c, x, y,
      ← mkExpectedTypeHint pf (← mkEq a (mkApp5 (mkConst ``ite a.getAppFn.constLevels!) args[0]! c
          (mkApp (mkConst ``Classical.propDecidable) c) x y)))
  return none

/-- `@ite α' c' (Classical.propDecidable c') x' y'` -/
def classicalIte? (b : Expr) : Option (Expr × Expr × Expr × Expr) :=
  if b.isAppOfArity ``ite 5 then
    let args := b.getAppArgs
    if args[2]!.isAppOfArity ``Classical.propDecidable 1 then some (args[1]!, args[3]!, args[4]!, args[0]!) else none
  else none

/-- Heads of the interpretation that are definitionally equal to Blaster's normal forms (same explicit
    arguments), e.g., `x + y` (on `Int`) for `Int.add x y`. -/
def normalizeHead (fa : Expr) (b : Expr) : Expr :=
  match fa with
  | .const n _ =>
    let args := b.getAppArgs
    let int := mkConst ``Int
    let ok (op : Name) (arity : Nat) : Bool := b.isAppOfArity op arity && args[0]! == int
    if n == ``Int.add && ok ``HAdd.hAdd 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.mul && ok ``HMul.hMul 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.sub && ok ``HSub.hSub 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.neg && ok ``Neg.neg 3 then mkApp fa args[2]!
    else if n == ``Int.ediv && ok ``HDiv.hDiv 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.emod && ok ``HMod.hMod 6 then mkApp2 fa args[4]! args[5]!
    else if n == ``Int.le && ok ``LE.le 4 then mkApp2 fa args[2]! args[3]!
    else if n == ``Int.lt && ok ``LT.lt 4 then mkApp2 fa args[2]! args[3]!
    else b
  | _ => b

/-- Whether `e` has at most `n` nodes (as a tree), without traversing more than `n` nodes. -/
def sizeLe (e : Expr) (n : Nat) : Bool :=
  (go e n).isSome
where
  go (e : Expr) (fuel : Nat) : Option Nat :=
    if fuel == 0 then none else
    match e with
    | .app f a => go f (fuel - 1) >>= go a
    | .lam _ t b _ | .forallE _ t b _ => go t (fuel - 1) >>= go b
    | .letE _ t v b _ => go t (fuel - 1) >>= go v >>= go b
    | .mdata _ b | .proj _ _ b => go b (fuel - 1)
    | _ => some (fuel - 1)

/-- Standard notation of Blaster's normal forms (definitionally equal). -/
def standardForm (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  if args.size != 2 then return e
  let .const f _ := e.getAppFn | return e
  let op? : Option Name :=
    if f == ``Nat.div || f == ``Int.ediv then some ``HDiv.hDiv
    else if f == ``Nat.mod || f == ``Int.emod then some ``HMod.hMod
    else if f == ``Nat.sub || f == ``Int.sub then some ``HSub.hSub
    else if f == ``Nat.add || f == ``Int.add then some ``HAdd.hAdd
    else if f == ``Nat.mul || f == ``Int.mul then some ``HMul.hMul
    else none
  let some op := op? | return e
  try mkAppM op args catch _ => return e

mutual

/-- Proof of `W(a) = b` where `W` is given by the types of `a` and `b` (see `World`). -/
partial def walk (a b : Expr) : BridgeM (Option Expr) := do
  if let some r := (← get).cache.get? (a, b) then return r
  -- β-redexes of the interpretation (e.g., applications of the interpretations of auxiliary functions)
  if b.isHeadBetaTarget then
    let b' := b.headBeta
    let some p ← walk a b' | return none
    return some (← mkExpectedTypeHint p (← mkEq (← inferType p >>= fun t => pure (t.getArg! 1)) b))
  let r ← try walkCore a b catch _ => pure none
  if r.isNone then modify fun s => { s with failures := s.failures.push (a, b) }
  -- NOTE: proofs using the hypotheses of a branch are not cached (they are only valid in the branch)
  let facts := (← read).facts
  let local? := match r with
    | some p => !facts.isEmpty && p.hasAnyFVar (fun f => facts.any (·.fvarId! == f))
    | none => !facts.isEmpty
  if !local? then modify fun s => { s with cache := s.cache.insert (a, b) r }
  return r

/-- Proof of the proposition `p` from the hypotheses of the branch (`omega`). -/
partial def byFacts (p : Expr) : BridgeM (Option Expr) := do
  if (← read).facts.isEmpty then return none
  Blaster.Reconstruct.proveWithTactic p (← `(tactic| omega))

partial def walkCore (a b : Expr) : BridgeM (Option Expr) := do
  let ta ← inferType a
  let tb ← inferType b
  let some w ← worldOf ta tb | return none
  match w with
  | .same => walkSame a b
  | .nat => walkNat a b
  | .bool => walkBool a b

/-- Small terms: definitional equality (e.g., literals in different forms). -/
partial def byDefEq (lhs b : Expr) : BridgeM (Option Expr) := do
  let n := (← read).defeqSize
  if lhs.approxDepth.toNat > n || b.approxDepth.toNat > n then return none
  if lhs.hasFVar && b.hasFVar && !(sizeLe lhs n) then return none
  let ok ← try withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 2000 * 1000 }) <|
      withCurrHeartbeats <| isDefEq lhs b
    catch _ => pure false
  if ok then return some (← mkExpectedTypeHint (← mkEqRefl b) (← mkEq lhs b)) else return none

/-- `ite` on the goal side: `W(ite c x y) = ite c' x' y'`. -/
partial def walkIte (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  if a.isAppOfArity ``dite 5 then
    if let some p ← walkDite w a b then return some p
  let some (α, c, inst, x, y, pa) ← iteView? a | return none
  let some (c', x', y', _) := classicalIte? b | return none
  let some pc ← walk c c' | return none
  -- the branches are related under the condition (resp. its negation)
  let some px ← withLocalDeclD `hc c fun h => withReader (fun cfg => { cfg with facts := cfg.facts.push h }) do
      let some p ← walk x x' | return none
      some <$> mkLambdaFVars #[h] p
    | return none
  let some py ← withLocalDeclD `hc (mkNot c) fun h => withReader (fun cfg => { cfg with facts := cfg.facts.push h }) do
      let some p ← walk y y' | return none
      some <$> mkLambdaFVars #[h] p
    | return none
  -- `W(a) = W(ite c x y) = ite c W(x) W(y)`
  let pLift ← match w with
    | .same => mkEqRefl a
    | .nat =>
        mkEqTrans (← mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) pa)
          (mkApp4 (mkConst ``natCast_ite) c inst x y)
    | .bool =>
        mkEqTrans (← mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) pa)
          (mkApp4 (mkConst ``boolEq_ite) c inst x y)
  let (α', x₀, y₀) := match w with
    | .same => (α, x, y)
    | .nat => (mkConst ``Int, natCast x, natCast y)
    | .bool => (mkSort levelZero, boolTrue x, boolTrue y)
  let u ← getLevel α'
  let pIte := mkAppN (mkConst ``ite_congr_dep [u]) #[α', c, c', inst, x₀, x', y₀, y', pc, px, py]
  match w with
  | .same => return some (← mkEqTrans pa pIte)
  | _ => return some (← mkEqTrans pLift pIte)

/-- `dite c x y = ite c' x' y'` where the branches `x`, `y` depend on the condition (e.g., proofs of the equations
    of named patterns), related under the condition (resp. its negation). -/
partial def walkDite (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  let args := a.getAppArgs
  let (α, c, inst, x, y) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  let some (c', x', y', _) := classicalIte? b | return none
  let some pc ← walk c c' | return none
  let branch (cond f t : Expr) : BridgeM (Option Expr) :=
    withLocalDeclD `hc cond fun h => withReader (fun cfg => { cfg with facts := cfg.facts.push h }) do
      let some p ← walk (mkApp f h).headBeta t | return none
      some <$> mkLambdaFVars #[h] p
  let some px ← branch c x x' | return none
  let some py ← branch (mkNot c) y y' | return none
  match w with
  | .same =>
      let u ← getLevel α
      return some (mkAppN (mkConst ``dite_congr_dep [u]) #[α, c, c', inst, x, y, x', y', pc, px, py])
  | .nat => return some (mkAppN (mkConst ``natCast_dite_congr) #[c, c', inst, x, y, x', y', pc, px, py])
  | .bool => return some (mkAppN (mkConst ``boolEq_dite_congr) #[c, c', inst, x, y, x', y', pc, px, py])

/-- Matchers on the goal side: `W(a) = W(i)` where `i` is the `ite` encoding of `a`, then `W(i) = b`. -/
partial def walkMatcher (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  let some (i, pa) ← matcherIte? a | return none
  let some pi ← walk i b | return none
  let pa' ← match w with
    | .same => pure pa
    | .nat => mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) pa
    | .bool => mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) pa
  return some (← mkEqTrans pa' pi)

/-- Congruence: `f a₁ ... aₙ = f b₁ ... bₙ` from `aᵢ = bᵢ` (arguments without forward dependencies). -/
partial def walkApp (a b : Expr) : BridgeM (Option Expr) := do
  let fa := a.getAppFn
  let b := normalizeHead fa b
  let fb := b.getAppFn
  if fa != fb then return none
  let as := a.getAppArgs
  let bs := b.getAppArgs
  if as.size != bs.size then return none
  let info ← getFunInfoNArgs fa as.size
  let mut pf ← mkEqRefl a
  let mut cur := as
  for i in [:as.size] do
    if as[i]! == bs[i]! then continue
    if let some pi := info.paramInfo[i]? then
      if pi.hasFwdDeps then
        -- dependent argument: only definitionally equal arguments
        if ← isDefEq as[i]! bs[i]! then cur := cur.set! i bs[i]!; continue
        return none
    let ta ← inferType as[i]!
    let tb ← inferType bs[i]!
    if !(← isDefEq ta tb) then return none
    let some p ← walk as[i]! bs[i]! | return none
    -- `fun z => f cur[0..i) z as(i..n]`
    let ctx ← withLocalDeclD `z ta fun z => mkLambdaFVars #[z] (mkAppN fa (cur.set! i z))
    pf ← mkEqTrans pf (← mkCongrArg ctx p)
    cur := cur.set! i bs[i]!
  return some (← mkExpectedTypeHint pf (← mkEq a b))

/-- Applications of functions translated as SMT macros: `W(f xs) = M(W(xs))` (an auxiliary lemma proved once
    per function) where `b` is an instance of the interpretation of the body `M` of the macro. -/
partial def walkMacro (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  let .const f lvls := a.getAppFn | return none
  let some mk := (← read).macroOf f | return none
  let args := a.getAppArgs
  let fty ← inferType a.getAppFn
  -- non-dependent first-order functions only
  let (doms, _) ← forallTelescope fty fun xs body => do
    if (← xs.anyM fun x => do return !(← x.fvarId!.getBinderInfo).isExplicit) then return (#[], body)
    return (← xs.mapM fun x => inferType x, body)
  if doms.size != args.size || doms.any (·.hasLooseBVars) then return none
  let worldTy (t : Expr) : MetaM Expr := do
    let t' ← whnfR t
    if t'.isConstOf ``Nat then return mkConst ``Int
    if t'.isConstOf ``Bool then return mkSort levelZero
    return t
  let lift (t x : Expr) : MetaM Expr := do
    let t' ← whnfR t
    if t'.isConstOf ``Nat then return natCast x
    if t'.isConstOf ``Bool then return boolTrue x
    return x
  -- arguments of the macro in `b`, by matching
  let ms ← doms.mapM fun t => do mkFreshExprMVar (← worldTy t)
  let tmpl ← mk ms
  if !(← withReducible (isDefEq tmpl b)) then return none
  let bargs ← ms.mapM instantiateMVars
  if bargs.any (·.hasExprMVar) then return none
  -- lemma `∀ xs, W(f xs) = M(W(xs))` (stated with the standard notations of Blaster's normal forms, e.g.,
  -- `x / y` for `Nat.div x y`)
  let lem? ← match (← get).macroLemmas.get? f with
    | some l => pure l
    | none =>
        let l ← try
            let stmt ← forallTelescope fty fun xs _ => do
              let lhs := w.lift (← standardForm (mkAppN (mkConst f lvls) xs))
              let rhs ← mk (← (xs.zip doms).mapM fun (x, t) => lift t x)
              mkForallFVars xs (← mkEq lhs rhs)
            -- NOTE: proved in the empty local context, such that the proof does not refer to local hypotheses
            if stmt.hasFVar then pure none else
            let some pf ← withLCtx {} {} ((← read).proveLemma stmt) | pure none
            some <$> mkAuxTheorem stmt pf
          catch _ => pure none
        modify fun s => { s with macroLemmas := s.macroLemmas.insert f l }
        pure l
  let some lem := lem? | return none
  -- `W(f as) = M(W(as))`, then congruence with `W(aᵢ) = bᵢ`
  let mut pf := mkAppN lem args
  let liftedArgs ← (args.zip doms).mapM fun (x, t) => lift t x
  let mut cur := liftedArgs
  for i in [:args.size] do
    let some pi ← walk args[i]! bargs[i]! | return none
    if liftedArgs[i]! == bargs[i]! then continue
    let ctx ← withLocalDeclD `z (← worldTy doms[i]!) fun z => do mkLambdaFVars #[z] (← mk (cur.set! i z))
    pf ← mkEqTrans pf (← mkCongrArg ctx pi)
    cur := cur.set! i bargs[i]!
  return some (← mkExpectedTypeHint pf (← mkEq (w.lift a) b))

partial def walkSame (a b : Expr) : BridgeM (Option Expr) := do
  if a == b then return some (← mkEqRefl a)
  -- `Bool` terms interpreted as formulas, converted back with `decide`
  if b.isAppOfArity ``Decidable.decide 2 && (b.getArg! 1).isAppOfArity ``Classical.propDecidable 1 then
    if (← whnfR (← inferType a)).isConstOf ``Bool then
      let p := b.getArg! 0
      if let some h ← walk a p then return some (mkApp3 (mkConst ``bool_decide) a p h)
  -- `Int.ofNat x` is `↑x`
  if a.isAppOfArity ``Int.ofNat 1 && !a.appArg!.isRawNatLit then
    if let some p ← walk a.appArg! b then return some (← mkExpectedTypeHint p (← mkEq a b))
  if let some p ← walkMatcher .same a b then return some p
  if let some p ← walkIte .same a b then return some p
  -- `true = e` (resp. `false = e`, `e = false`) where `e` is translated as a formula
  if a.isAppOfArity ``Eq 3 && (a.getArg! 0).isConstOf ``Bool then
    let (l, r) := (a.getArg! 1, a.getArg! 2)
    -- same orientation: congruence
    let swapped := b.isAppOfArity ``Eq 3 && (b.getArg! 0).isConstOf ``Bool && (b.getArg! 2).isConstOf ``Bool.true &&
      l.isConstOf ``Bool.true
    let same := b.isAppOfArity ``Eq 3 && !swapped
    if !same then
      if l.isConstOf ``Bool.true then
        let some p ← walk r b | return none
        return some (mkApp3 (mkConst ``true_eq) r b p)
      if r.isConstOf ``Bool.true then return ← walk l b
      if b.isAppOfArity ``Not 1 then
        if l.isConstOf ``Bool.false then
          let some p ← walk r b.appArg! | return none
          return some (mkApp3 (mkConst ``false_eq) r b.appArg! p)
        if r.isConstOf ``Bool.false then
          let some p ← walk l b.appArg! | return none
          return some (mkApp3 (mkConst ``eq_false') l b.appArg! p)
  -- relations whose arguments are in different worlds
  if a.isAppOfArity ``Eq 3 && b.isAppOfArity ``Eq 3 then
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    if aa[0]! != ba[0]! then
      let some w ← worldOf aa[0]! ba[0]! | return none
      let some px ← walk aa[1]! ba[1]! | return none
      let some py ← walk aa[2]! ba[2]! | return none
      match w with
      | .nat => return some (mkApp6 (mkConst ``nat_eq) aa[1]! aa[2]! ba[1]! ba[2]! px py)
      | .bool => return some (mkApp6 (mkConst ``bool_eq) aa[1]! aa[2]! ba[1]! ba[2]! px py)
      | .same => pure ()
  for (op, lem) in [(``LE.le, ``nat_le), (``LT.lt, ``nat_lt)] do
    if a.isAppOfArity op 4 && b.isAppOfArity op 4 then
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if (← whnfD aa[0]!).isConstOf ``Nat && (← whnfD ba[0]!).isConstOf ``Int then
        let some px ← walk aa[2]! ba[2]! | return none
        let some py ← walk aa[3]! ba[3]! | return none
        return some (← mkExpectedTypeHint (mkApp6 (mkConst lem) aa[2]! aa[3]! ba[2]! ba[3]! px py) (← mkEq a b))
  if a.isAppOfArity ``Iff 2 && b.isAppOfArity ``Eq 3 then
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    let some pp ← walk aa[0]! ba[1]! | return none
    let some pq ← walk aa[1]! ba[2]! | return none
    return some (mkApp6 (mkConst ``iff_eq) aa[0]! aa[1]! ba[1]! ba[2]! pp pq)
  -- type predicates of Blaster's encoding (interpreted as `True`) as hypotheses
  if let .forallE _ t' body' _ := b then
    if t'.isConstOf ``True && !body'.hasLooseBVars && !(a.isForall && a.bindingDomain!.isConstOf ``True) then
      let some p ← walk a body' | return none
      return some (mkApp3 (mkConst ``true_imp) a body' p)
  -- quantifiers over `Nat`, translated as quantifiers over `Int` guarded by `0 ≤ x`
  if let some p ← walkNatBinder a b then return some p
  -- binders
  match a, b with
  | .forallE n t body bi, .forallE _ t' body' _ =>
      if !body.hasLooseBVars && !body'.hasLooseBVars then
        let some pt ← walk t t' | return none
        let some pb ← walk body body' | return none
        return some (← mkAppM ``implies_congr #[pt, pb])
      if t != t' then return none
      return ← withLocalDecl n bi t fun x => do
        let some pb ← walk (body.instantiate1 x) (body'.instantiate1 x) | return none
        return some (← mkAppM ``forall_congr #[← mkLambdaFVars #[x] pb])
  | .lam n t body bi, .lam _ t' body' _ =>
      if t != t' then return none
      return ← withLocalDecl n bi t fun x => do
        let some pb ← walk (body.instantiate1 x) (body'.instantiate1 x) | return none
        return some (← mkFunExt (← mkLambdaFVars #[x] pb))
  | .proj s i e, .proj s' i' e' =>
      if s != s' || i != i' then return none
      let some pe ← walk e e' | return none
      let ctx ← withLocalDeclD `z (← inferType e) fun z => mkLambdaFVars #[z] (.proj s i z)
      return some (← mkCongrArg ctx pe)
  | .mdata _ a', _ => return ← walk a' b
  | _, .mdata _ b' => return ← walk a b'
  | _, _ => pure ()
  if a.isApp && b.isApp then
    if let some p ← walkApp a b then return some p
  -- `Int` terms in `Nat` positions (`Int.toNat`)
  if b.isAppOfArity ``Int.toNat 1 then
    if (← whnfR (← inferType a)).isConstOf ``Nat then
      if let some p ← walk a b.appArg! then
        if (← inferType p).isAppOfArity ``Eq 3 && ((← inferType p).getArg! 0).isConstOf ``Int then
          return some (mkApp3 (mkConst ``nat_toNat) a b.appArg! p)
  if let some p ← walkMacro .same a b then return some p
  byDefEq a b

/-- `∀ n : Nat, p n` (resp. `∃ n : Nat, p n`) and `∀ x : Int, 0 ≤ x → q x` (resp. `∃ x : Int, 0 ≤ x ∧ q x`). -/
partial def walkNatBinder (a b : Expr) : BridgeM (Option Expr) := do
  let isGuard (g : Expr) : Bool := g.isAppOfArity ``LE.le 4 && g.appArg! == .bvar 0 && (g.getArg! 0).isConstOf ``Int
  -- (name, Nat body (one loose bvar), Int body without the guard (one loose bvar), lemma)
  let view? : Option (Name × Expr × Expr × Name) :=
    match a, b with
    | .forallE n t p _, .forallE _ t' g _ =>
        if t.isConstOf ``Nat && t'.isConstOf ``Int then
          match g with
          | .forallE _ guard q _ =>
              if isGuard guard && !(q.hasLooseBVarInExplicitDomain 0 false) && !q.hasLooseBVar 0 then
                some (n, p, q.lowerLooseBVars 1 1, ``nat_forall)
              else none
          | _ => none
        else none
    | _, _ =>
        if a.isAppOfArity ``Exists 2 && b.isAppOfArity ``Exists 2 && (a.getArg! 0).isConstOf ``Nat && (b.getArg! 0).isConstOf ``Int then
          match a.getArg! 1, b.getArg! 1 with
          | .lam n _ p _, .lam _ _ g _ =>
              if g.isAppOfArity ``And 2 && isGuard (g.getArg! 0) then some (n, p, g.getArg! 1, ``nat_exists) else none
          | _, _ => none
        else none
  let some (n, p, q, lem) := view? | return none
  withLocalDeclD n (mkConst ``Nat) fun x => do
    let some h ← walk (p.instantiate1 x) (q.instantiate1 (natCast x)) | return none
    let pl := mkLambda n .default (mkConst ``Nat) p
    let ql := mkLambda n .default (mkConst ``Int) q
    let pf := mkApp3 (mkConst lem) pl ql (← mkLambdaFVars #[x] h)
    return some (← mkExpectedTypeHint pf (← mkEq a b))

/-- `(↑a : Int) = b` -/
partial def walkNat (a b : Expr) : BridgeM (Option Expr) := do
  let la := natCast a
  if la == b then return some (← mkEqRefl b)
  if b.isAppOfArity ``Nat.cast 3 then
    let some p ← walk a b.appArg! | return none
    return some (← mkExpectedTypeHint (← mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) p) (← mkEq la b))
  if let some p ← walkMatcher .nat a b then return some p
  if let some p ← walkIte .nat a b then return some p
  let binop (lem : Name) : BridgeM (Option Expr) := do
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    let (x, y) := (aa[aa.size - 2]!, aa[aa.size - 1]!)
    let some px ← walk x ba[4]! | return none
    let some py ← walk y ba[5]! | return none
    return some (← mkExpectedTypeHint (mkApp6 (mkConst lem) x y ba[4]! ba[5]! px py) (← mkEq la b))
  if (a.isAppOfArity ``Nat.add 2 || a.isAppOfArity ``HAdd.hAdd 6) && b.isAppOfArity ``HAdd.hAdd 6 then
    if let some p ← binop ``nat_add then return some p
  if (a.isAppOfArity ``Nat.mul 2 || a.isAppOfArity ``HMul.hMul 6) && b.isAppOfArity ``HMul.hMul 6 then
    if let some p ← binop ``nat_mul then return some p
  -- subtraction (resp. `Int.toNat`) under the hypotheses of the branch (e.g., the variables of `n + 1` patterns)
  if (a.isAppOfArity ``Nat.sub 2 || a.isAppOfArity ``HSub.hSub 6) && b.isAppOfArity ``HSub.hSub 6 then
    let aa := a.getAppArgs
    let (x, y) := (aa[aa.size - 2]!, aa[aa.size - 1]!)
    if let some h ← byFacts (← mkAppM ``LE.le #[y, x]) then
      let ba := b.getAppArgs
      let some px ← walk x ba[4]! | return none
      let some py ← walk y ba[5]! | return none
      return some (← mkExpectedTypeHint (mkAppN (mkConst ``nat_sub_bridge) #[x, y, ba[4]!, ba[5]!, h, px, py]) (← mkEq la b))
  if a.isAppOfArity ``Int.toNat 1 && !(← read).facts.isEmpty then
    let x := a.appArg!
    if let some h ← byFacts (← mkAppM ``LE.le #[mkIntLit 0, x]) then
      if let some px ← walk x b then
        return some (← mkExpectedTypeHint (mkApp4 (mkConst ``toNat_bridge) x b h px) (← mkEq la b))
  if let some p ← walkMacro .nat a b then return some p
  byDefEq la b

/-- `(a = true) = b` -/
partial def walkBool (a b : Expr) : BridgeM (Option Expr) := do
  let la := boolTrue a
  if la == b then return some (← mkEqRefl b)
  if b.isAppOfArity ``Eq 3 && (b.getArg! 0).isConstOf ``Bool && (b.getArg! 2).isConstOf ``Bool.true then
    let some p ← walk a (b.getArg! 1) | return none
    return some (← mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) p)
  if a.isConstOf ``Bool.true && b.isConstOf ``True then return some (mkConst ``bool_true)
  if a.isConstOf ``Bool.false && b.isConstOf ``False then return some (mkConst ``bool_false)
  let bin (lem : Name) (op : Name) : BridgeM (Option Expr) := do
    if !b.isAppOfArity op 2 then return none
    let some px ← walk (a.getArg! 0) (b.getArg! 0) | return none
    let some py ← walk (a.getArg! 1) (b.getArg! 1) | return none
    return some (mkApp6 (mkConst lem) (a.getArg! 0) (a.getArg! 1) (b.getArg! 0) (b.getArg! 1) px py)
  if a.isAppOfArity ``and 2 then if let some p ← bin ``bool_and ``And then return some p
  if a.isAppOfArity ``or 2 then if let some p ← bin ``bool_or ``Or then return some p
  if a.isAppOfArity ``not 1 && b.isAppOfArity ``Not 1 then
    let some px ← walk a.appArg! b.appArg! | return none
    return some (mkApp3 (mkConst ``bool_not) a.appArg! b.appArg! px)
  if a.isAppOfArity ``Blaster.decide' 1 then
    let some p ← walk a.appArg! b | return none
    return some (mkApp3 (mkConst ``decide'_eq) a.appArg! b p)
  if a.isAppOfArity ``Decidable.decide 2 then
    let some p ← walk (a.getArg! 0) b | return none
    return some (mkApp4 (mkConst ``decide_eq) (a.getArg! 0) b (a.getArg! 1) p)
  if a.isAppOfArity ``BEq.beq 4 && b.isAppOfArity ``Eq 3 then
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    let some px ← walk aa[2]! ba[1]! | return none
    let some py ← walk aa[3]! ba[2]! | return none
    let ty ← whnfD aa[0]!
    if ty.isConstOf ``Nat && (← whnfD ba[0]!).isConstOf ``Int then
      let some lawful ← (try some <$> synthInstance (mkApp2 (mkConst ``LawfulBEq [levelZero]) aa[0]! aa[1]!) catch _ => pure none) | return none
      return some (mkAppN (mkConst ``nat_beq) #[aa[1]!, lawful, aa[2]!, aa[3]!, ba[1]!, ba[2]!, px, py])
    if ← isDefEq aa[0]! ba[0]! then
      let u ← getLevel aa[0]!
      let some lawful ← (try some <$> synthInstance (mkApp2 (mkConst ``LawfulBEq [u.dec.getD levelZero]) aa[0]! aa[1]!) catch _ => pure none) | return none
      return some (mkAppN (mkConst ``beq_eq [u.dec.getD levelZero]) #[aa[0]!, aa[1]!, lawful, aa[2]!, aa[3]!, ba[1]!, ba[2]!, px, py])
  if a.isAppOfArity ``Nat.ble 2 && b.isAppOfArity ``LE.le 4 then
    let some px ← walk (a.getArg! 0) (b.getArg! 2) | return none
    let some py ← walk (a.getArg! 1) (b.getArg! 3) | return none
    return some (← mkExpectedTypeHint (mkApp6 (mkConst ``nat_ble) (a.getArg! 0) (a.getArg! 1) (b.getArg! 2) (b.getArg! 3) px py) (← mkEq la b))
  if a.isAppOfArity ``Nat.beq 2 && b.isAppOfArity ``Eq 3 then
    let some px ← walk (a.getArg! 0) (b.getArg! 1) | return none
    let some py ← walk (a.getArg! 1) (b.getArg! 2) | return none
    return some (← mkExpectedTypeHint (mkApp6 (mkConst ``nat_beq') (a.getArg! 0) (a.getArg! 1) (b.getArg! 1) (b.getArg! 2) px py) (← mkEq la b))
  if let some p ← walkMatcher .bool a b then return some p
  if let some p ← walkIte .bool a b then return some p
  if let some p ← walkMacro .bool a b then return some p
  byDefEq la b

end

/-- Proof of `a = b` (resp. `a → b` when `imp`) for a goal term `a` and the interpretation `b` of its
    translation, with the failed pairs of subterms (deepest first) when it fails. -/
def prove (cfg : Cfg) (a b : Expr) : Term.TermElabM (Option Expr × Array (Expr × Expr)) := do
  let (r, s) ← (walk a b |>.run cfg).run {}
  return (r, s.failures)

end Blaster.Reconstruct.SmtProof.Bridge
