import Lean
import Blaster.Optimize.Decidable
import Blaster.Reconstruct.SmtProof.Interp
import Blaster.Reconstruct.Discharge
import Blaster.Reconstruct.SmtProof.Poly
import Blaster.Reconstruct.SmtProof.Local

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
mapping to the SMT world: `(↑a : Int)` for `Nat` terms, `a = true` for `Bool` terms, the world of the
type of `a` for the terms of the polymorphic encoding (e.g., `Poly.inj α a` for `a : α`, see `Poly.lean`),
`a` otherwise.

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
  /-- term of the polymorphic encoding: `w a = b` where `w` is the world of its type (e.g., `inj α a = b` for
      `a : α` with `α` a sort variable, see `Poly.mkWorld`), with a proof `inj` of the injectivity of `w` -/
  | poly (w inj : Expr)
  deriving BEq, Inhabited

def natCast (a : Expr) : Expr :=
  mkApp3 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt) a

def boolTrue (a : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) a (mkConst ``Bool.true)

def World.lift : World → Expr → Expr
  | .same, a => a
  | .nat, a => natCast a
  | .bool, a => boolTrue a
  | .poly w _, a => Poly.applyWorld w a

def worldOf (ta tb : Expr) : MetaM (Option World) := do
  if ta == tb then return some .same
  -- NOTE: types may be given by aliases (e.g., `abbrev Integer := Int`)
  let ta' ← whnfD ta
  let tb' ← whnfD tb
  if ta'.isConstOf ``Nat && tb'.isConstOf ``Int then return some .nat
  if ta'.isConstOf ``Bool && tb'.isProp then return some .bool
  if ← isDefEq ta tb then return some .same
  if let some (w, h) ← Poly.mkWorld ta tb then return some (.poly w h)
  return none

/-- `omega` on goals and hypotheses with the literals of Blaster's normal forms (e.g., `Int.ofNat 0`,
    `Int.negSucc 2`, which `omega` does not interpret). -/
def omegaTac : MetaM (TSyntax `tactic) :=
  `(tactic| ((try simp only [Int.ofNat_eq_coe, Int.negSucc_eq] at *) <;> omega))

/-- `Int.ofNat n` (resp. `Int.negSucc n`) in the notation of `omega`: `↑n` (resp. `-(↑n + 1)`), and raw `Nat`
    literals as `OfNat` literals (definitionally equal). -/
partial def omegaNotation (e : Expr) : Expr :=
  e.replace fun e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then some e
    else if let .lit (.natVal n) := e then some (mkNatLit n)
    else if e.isAppOfArity ``Int.ofNat 1 then
      match e.appArg! with
      | .lit (.natVal n) => some (mkIntLit n)
      | a => some (natCast (omegaNotation a))
    else if e.isAppOfArity ``Int.negSucc 1 then
      match e.appArg! with
      | .lit (.natVal n) => some (mkIntNeg (mkIntLit (n + 1)))
      | a => some (mkIntNeg (mkIntAdd (natCast (omegaNotation a)) (mkIntLit 1)))
    else none

/-- `e` with the case analyses on constructors reduced (e.g., the selectors of the interpretation applied to
    constructor applications in the cases of a matcher). -/
def reduceCases (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (post := fun e => do
    let .const n _ := e.getAppFn | return .done e
    if isCasesOnRecursor env n then return .done (← whnfCore e) else return .done e)

/-- Proof of `p` by `omega` from the hypotheses of the local context (in the notation of `omega`, see
    `omegaNotation`, with the case analyses on constructors reduced), without the tactic framework and the
    auxiliary theorems of the `omega` tactic. -/
def omegaProof? (p : Expr) : MetaM (Option Expr) :=
  Blaster.Reconstruct.attempt Blaster.Reconstruct.dischargeHeartbeats do
    let m ← mkFreshExprSyntheticOpaqueMVar (omegaNotation (← reduceCases p))
    let some g ← m.mvarId!.falseOrByContra | return none
    g.withContext do
      let hyps ← (← getLocalHyps).toList.mapM fun h => do
        let t ← inferType h
        let t' := omegaNotation (← reduceCases t)
        if t' == t then pure h else mkExpectedTypeHint h t'
      Lean.Elab.Tactic.Omega.omega hyps g
    let pf ← instantiateMVars m
    if pf.hasExprMVar then return none
    -- NOTE: as the `omega` tactic, the proof (typically large) is an auxiliary theorem
    return some (← mkAuxTheorem p (← mkExpectedTypeHint pf p) (zetaDelta := true))

/-- The free variables of `es` and, transitively, of their types and values, in the order of the local context. -/
def fvarClosure (es : Array Expr) : MetaM (Array Expr) := do
  let mut todo := es.foldl (fun acc e => (collectFVars {} e).fvarIds ++ acc) #[]
  let mut seen : FVarIdSet := {}
  while !todo.isEmpty do
    let f := todo.back!
    todo := todo.pop
    if seen.contains f then continue
    seen := seen.insert f
    let some d := (← getLCtx).find? f | continue
    let s := collectFVars {} d.type
    let s := match d.value? with | some v => collectFVars s v | none => s
    todo := todo ++ s.fvarIds
  let lctx ← getLCtx
  return lctx.foldl (init := #[]) fun acc d => if seen.contains d.fvarId then acc.push d.toExpr else acc

/-- Run `k` in the local context restricted to the free variables of `es` (see `fvarClosure`): tactics are not
    slowed down by the other hypotheses of the context (e.g., the negated goal, which `simp at *` would rewrite
    and `omega` would analyze). -/
def withRestrictedLCtx [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n] (es : Array Expr) (k : n α) : n α := do
  let keep ← liftM (m := MetaM) <| fvarClosure es
  let full ← liftM (m := MetaM) getLCtx
  let restricted := keep.foldl (init := ({} : LocalContext)) fun l x =>
    match full.find? x.fvarId! with
    | some d => l.addDecl d
    | none => l
  let insts := (← liftM (m := MetaM) getLocalInstances).filter fun li => keep.contains li.fvar
  withLCtx restricted insts k

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

/-- Raw `Nat` literal. -/
def rawNatLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | _ => none

/-- Blaster's normal form of the patterns in the conditions of the `ite` encoding (see
    `removeNamedPatternExpr` and `optimizePattern`): named patterns removed, and `Nat.add` (resp. `Int.neg`)
    applications on literals evaluated, e.g., `Int.neg (Int.ofNat (Nat.add 1 (p@(Nat.add 1 1))))` is `Int.negSucc 2`. -/
partial def normPattern (p : Expr) : Expr :=
  if p.isAppOfArity ``namedPattern 4 then normPattern p.getAppArgs[2]! else
  if !p.isApp then p else
  let f := p.getAppFn
  let args := p.getAppArgs.map normPattern
  if f.isConstOf ``Nat.add && args.size == 2 then
    match rawNatLit? args[0]!, rawNatLit? args[1]! with
    | some 0, _ => args[1]!
    | some a, some b => mkRawNatLit (a + b)
    | some a, none =>
        -- `N₁ + (N₂ + n)` is `(N₁ + N₂) + n`
        match (if args[1]!.isAppOfArity ``Nat.add 2 then rawNatLit? (args[1]!.getArg! 0) else none) with
        | some b => mkApp2 f (mkRawNatLit (a + b)) (args[1]!.getArg! 1)
        | none => mkAppN f args
    | _, _ => mkAppN f args
  else if f.isConstOf ``Int.neg && args.size == 1 then
    let a := args[0]!
    let lit? : Option Int :=
      if a.isAppOfArity ``Int.ofNat 1 then (rawNatLit? a.appArg!).map Int.ofNat
      else if a.isAppOfArity ``Int.negSucc 1 then (rawNatLit? a.appArg!).map Int.negSucc
      else none
    match lit? with
    | some i =>
        match -i with
        | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
        | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)
    | none => if a.isAppOfArity ``Int.neg 1 then a.appArg! else mkAppN f args
  else mkAppN f args

/-- Conditions and values of the `Nat`/`Int` patterns with variables (see `mkCond` and `mkLet` in
    `Blaster.Smt.Translate.Match`): `N + n` (`N ≤ x`, `n := x - N`), `Int.ofNat n` (`0 ≤ x`, `n := x.toNat`),
    `Int.ofNat (N + n)` (`N ≤ x`, `n := (x - N).toNat`), `Int.neg (Int.ofNat (N + n))` (`x ≤ -N`,
    `n := (-(x + N)).toNat`, Blaster's normal form of `Int.negSucc`), `Int.negSucc n` (`x ≤ -1`,
    `n := (-x - 1).toNat`). Returns the condition and the pattern of the variable with its value. -/
def numPattern? (x p : Expr) : Option (Expr × Expr × Expr) := Id.run do
  let natLit (n : Nat) : Expr := mkRawNatLit n
  if let some (n, q) := natOffset? p then
    return some (mkNatLe (natLit n) x, q,
      mkApp6 (mkConst ``HSub.hSub [levelZero, levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat)
        (mkApp2 (mkConst ``instHSub [levelZero]) (mkConst ``Nat) (mkConst ``instSubNat)) x (natLit n))
  if p.isAppOfArity ``Int.neg 1 && p.appArg!.isAppOfArity ``Int.ofNat 1 then
    if let some (n, q) := natOffset? p.appArg!.appArg! then
      return some (mkIntLe x (mkIntNeg (mkIntLit n)), q, mkApp (mkConst ``Int.toNat) (mkIntNeg (mkIntAdd x (mkIntLit n))))
  if p.isAppOfArity ``Int.ofNat 1 then
    let q := p.appArg!
    if let some (n, q') := natOffset? q then
      return some (mkIntLe (mkIntLit n) x, q', mkApp (mkConst ``Int.toNat) (mkIntSub x (mkIntLit n)))
    return some (mkIntLe (mkIntLit 0) x, q, mkApp (mkConst ``Int.toNat) x)
  if p.isAppOfArity ``Int.negSucc 1 then
    return some (mkIntLe x (mkIntNeg (mkIntLit 1)), p.appArg!, mkApp (mkConst ``Int.toNat) (mkIntSub (mkIntNeg x) (mkIntLit 1)))
  return none

/-- Literals of Blaster's normal forms in the notation of the interpretation (see `mkIntLit`). -/
def stdLit (e : Expr) : Expr :=
  match e with
  | .lit (.natVal n) => mkNatLit n
  | .app (.const ``Int.ofNat _) (.lit (.natVal n)) => mkIntLit n
  | .app (.const ``Int.negSucc _) (.lit (.natVal n)) => mkIntNeg (mkIntLit (n + 1))
  | e => e

/-- Conditions of pattern `p` on the discriminant `x` (see `mkCond` in `Blaster.Smt.Translate.Match`).
    Returns `none` for unsupported patterns. -/
partial def patCond (x p : Expr) (acc : Array Expr) : MetaM (Option (Array Expr)) := do
  -- NOTE: the named patterns are removed and the literals evaluated (see `removeNamedPatternExpr`)
  let p := normPattern p
  -- literals (in the notation of the interpretation, e.g., `-3` for `Int.negSucc 2`)
  if isLiteral p then return some (acc.push (← mkEq (stdLit p) x))
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
partial def iteOf (ty : Expr) (mv : Expr) (altTys : Array Expr) (discrs alts : Array Expr) (beta : Bool) :
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
        let some cs ← patCond d p conds | dbg m!"bridge: unsupported pattern {p} in {altTys[j]!}"; return none
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
    -- NOTE: the named patterns of the equations of the previous variables (reducible) are removed
    let some pf ← proveEquation' (stripNamed p) | return none
    return some (← mkExpectedTypeHint pf p)
  stripNamed (e : Expr) : Expr :=
    e.replace fun e => if e.isAppOfArity ``namedPattern 4 then some (stripNamed e.getAppArgs[2]!) else none
  proveEquation' (p : Expr) : Term.TermElabM (Option Expr) := do
    if let some pf ← omegaProof? p then return some pf
    for tac in [← `(tactic| (subst_vars; rfl)), ← `(tactic| (simp_all; done)),
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

/-- Value of a closed decidable condition (e.g., an equation between literals in different forms, such as
    `Int.ofNat 0 = Int.ofNat Nat.zero`), by evaluation of its decision procedure. -/
def evalClosed? (c : Expr) : MetaM (Option CondVal) := do
  if c.hasFVar || c.hasMVar then return none
  let some inst ← (try some <$> synthInstance (mkApp (mkConst ``Decidable) c) catch _ => pure none) | return none
  let r ← try withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 2000 * 1000 }) <|
      withCurrHeartbeats <| withDefault <| whnf (mkApp2 (mkConst ``Decidable.decide) c inst)
    catch _ => return none
  let refl (b : Name) := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst b)
  if r.isConstOf ``Bool.true then return some (.isTrue (mkApp3 (mkConst ``of_decide_eq_true) c inst (refl ``Bool.true)))
  if r.isConstOf ``Bool.false then return some (.isFalse (mkApp3 (mkConst ``of_decide_eq_false) c inst (refl ``Bool.false)))
  return none

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
  if let some v ← evalClosed? c then return v
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
  if let some x ← stuckMajor? c' then return .splitFVar x
  -- arithmetic conditions (e.g., of `n + 1` patterns, or literal patterns of `Int` against the patterns of
  -- the matcher's case analysis): decided by `omega` in the context of the case analysis
  -- NOTE: on the condition before reduction (e.g., `Int.le` unfolds to `Int.NonNeg`)
  let numEq ← match c.eq? with
    | some (t, _, _) => do let t ← whnfR t; pure (t.isConstOf ``Int || t.isConstOf ``Nat)
    | none => pure false
  let arith := c.isAppOfArity ``LE.le 4 || c.isAppOfArity ``LT.lt 4 || numEq
  if arith then
    -- NOTE: the conditions of the alternatives preceding the alternative of a case are false
    if let some p ← omegaProof? (mkNot c) then return .isFalse p
    if let some p ← omegaProof? c then return .isTrue p
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

/-- Variable of type `Nat` or `Int` of the condition `c` occurring in an overlap hypothesis of the splitter. -/
def overlapVar? (g : MVarId) (c : Expr) (base : Nat) : MetaM (Option FVarId) := g.withContext do
  let c ← instantiateMVars c
  let lctx ← getLCtx
  for d in lctx do
    if d.index < base || d.isImplementationDetail || !d.type.isForall then continue
    for x in (collectFVars {} c).fvarIds do
      if !d.type.containsFVar x then continue
      let some xd := lctx.find? x | continue
      let t ← whnfR xd.type
      if t.isConstOf ``Nat || t.isConstOf ``Int then return some x
  return none

/-- Prove `lhs = rhs`, where `rhs` is an `ite` chain over conditions decided by case analysis, by
    evaluating the conditions (with case analyses on the variables and literal equalities blocking them). -/
partial def solveIte (g : MVarId) (fuel : Nat) (base : Nat) : Term.TermElabM Bool := g.withContext do
  if fuel == 0 then dbg m!"bridge: no fuel left for {g}"; return false
  if ← closeByOverlap g base then return true
  let tgt ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := tgt.eq? | return false
  let dep := rhs.isAppOfArity ``dite 5
  if !dep && !rhs.isAppOfArity ``ite 5 then
    try g.refl; return true
    catch _ =>
      -- applications of the same alternative to arguments equal up to arithmetic (e.g., the values of the
      -- variables of `Int.ofNat (N + n)` patterns, `n` and `(Int.ofNat (n + N) - N).toNat`)
      if lhs.getAppFn.isFVar && lhs.getAppFn == rhs.getAppFn then
        let omega ← omegaTac
        let tac ← `(tactic| (congr 1 <;> first | rfl | $omega:tactic))
        if let some pf ← Blaster.Reconstruct.proveWithTactic tgt tac then
          g.assign pf; return true
      dbg m!"bridge: leaf {← ppGoal g}"
      return false
  let args := rhs.getAppArgs
  let (α, c, inst, t, e) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  -- `lhs = rhs` from `lhs = b` where `b` is the branch selected by `pc`
  let select (lem : Name) (b pc : Expr) : Term.TermElabM Bool := do
    let b := if dep then (mkApp b pc).headBeta else b
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs b)
    let h ← mkAppOptM lem #[c, inst, pc, α, t, e]
    g.assign (← mkEqTrans g' (← mkEqSymm h))
    solveIte g'.mvarId! (fuel - 1) base
  match ← evalCond c with
  | .isTrue pc => select (if dep then ``dif_pos else ``if_pos) t pc
  | .isFalse pnc => select (if dep then ``dif_neg else ``if_neg) e pnc
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
      -- a variable constrained by an overlap hypothesis of the splitter (e.g., `∀ n, x = n + 2 → False` for an
      -- arithmetic condition on `x`): case analysis
      if let some x ← overlapVar? g c base then
        if let some gs ← try some <$> g.cases x catch _ => pure none then
          return ← gs.allM fun s => solveIte s.mvarId (fuel - 1) base
      dbg m!"bridge: unknown condition {c} ⟶ {← whnfD c} in {← ppGoal g}"
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

/-- `∀ ys, G₁ → … → Gₙ → Q` where the guards `Gᵢ` (membership predicates of the polymorphic encoding, see `Poly`)
    follow all the binders (e.g., Blaster's translation of `∀ (xs : List β) (f : List β → Nat), P`): the equivalent
    proposition where each guard follows the last binder it mentions (i.e., the order of the goal), with a proof
    of their equality. -/
partial def interleaveGuards (b : Expr) : MetaM (Option (Expr × Expr)) := do
  -- only for quantifiers over the types of the encoding
  let rec univBinder (e : Expr) (fuel : Nat) : Bool :=
    match fuel, e with
    | fuel + 1, .forallE _ t body _ => Poly.hasUniv t || univBinder body fuel
    | _, _ => false
  let .forallE _ _ (.forallE ..) _ := b | return none
  if !univBinder b 8 then return none
  go b #[] #[]
where
  isGuard (t : Expr) : Bool := t.isAppOfArity ``Poly.Img 4 && t.appArg!.isFVar
  go (e : Expr) (ys gs : Array Expr) : MetaM (Option (Expr × Expr)) := do
    if let .forallE n t body bi := e then
      if gs.isEmpty && !(← isProp t) then
        return ← withLocalDecl n bi t fun y => go (body.instantiate1 y) (ys.push y) gs
      if isGuard t && !body.hasLooseBVars then
        return ← withLocalDecl n bi t fun g => go body ys (gs.push g)
    finish e ys gs
  finish (q : Expr) (ys gs : Array Expr) : MetaM (Option (Expr × Expr)) := do
    if gs.isEmpty || ys.size < 2 then return none
    -- each guard after the last binder it mentions
    let mut order := #[]
    let mut placed := Array.replicate gs.size false
    for y in ys do
      order := order.push y
      for i in [:gs.size] do
        if placed[i]! then continue
        let gt ← inferType gs[i]!
        if ys.all fun y' => !gt.containsFVar y'.fvarId! || order.contains y' then
          order := order.push gs[i]!
          placed := placed.set! i true
    if placed.any (!·) || order == ys ++ gs then return none
    let b' ← mkForallFVars order q
    let b ← mkForallFVars (ys ++ gs) q
    let mp ← withLocalDeclD `h b' fun h => do mkLambdaFVars #[h] (← mkLambdaFVars (ys ++ gs) (mkAppN h order))
    let mpr ← withLocalDeclD `h b fun h => do mkLambdaFVars #[h] (← mkLambdaFVars order (mkAppN h (ys ++ gs)))
    return some (b', mkApp3 (mkConst ``propext) b' b (mkApp4 (mkConst ``Iff.intro) b' b mp mpr))

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
  /-- maximal number of nested unfoldings of the functions inlined by Blaster's optimizer (see `walkUnfold`) -/
  unfoldDepth : Nat := 2

structure State where
  cache : Std.HashMap (Expr × Expr) (Option Expr) := {}
  /-- matcher equations, per matcher instance (`M params motive`) -/
  lemmas : Std.HashMap Expr (Option Expr) := {}
  /-- macro equations, per function -/
  macroLemmas : Std.HashMap Name (Option Expr) := {}
  /-- naturality lemmas of the polymorphic functions, per statement (see `walkPolyApp`) -/
  natLemmas : Std.HashMap Expr (Option Expr) := {}
  /-- pairs of terms that could not be related (for diagnostics) -/
  failures : Array (Expr × Expr) := #[]

abbrev BridgeM := ReaderT Cfg (StateRefT State Term.TermElabM)

/-- `(∀ xs alts, M params motive xs alts = ite ..., proof)` (see `iteOf` and `proveMatchIte`), where `inst?` is
    Blaster's optimized instance of the matcher. -/
def matcherEquation (m : Name) (lvls : List Level) (info : MatcherInfo) (inst? : Option Expr) (params : Array Expr)
    (motive resTy : Expr) : Term.TermElabM (Option (Expr × Expr)) := do
  let head := mkAppN (mkConst m lvls) (params.push motive)
  forallBoundedTelescope (← inferType head) (some (info.numDiscrs + info.numAlts)) fun xs _ => do
    let xd := xs.extract 0 info.numDiscrs
    let fs := xs.extract info.numDiscrs xs.size
    let some rhs ← withLocalDeclD `m (← inferType motive) fun mv => do
        let tys ← altTypes m lvls info inst? params mv xd
        iteOf resTy mv tys xd fs false
      | return none
    let stmt ← mkForallFVars xs (← mkEq (mkAppN head xs) rhs)
    let t0 ← IO.monoMsNow
    let pf? ← proveMatchIte stmt
    dbg m!"bridge: matcher equation of {m}: {(← IO.monoMsNow) - t0} ms"
    let some pf := pf? | dbg m!"bridge: matcher equation not proved: {stmt}"; return none
    return some (stmt, pf)

/-- An auxiliary theorem of the environment branch of a command (e.g., the `_proof_i` lemmas of tactics). -/
structure AuxThm where
  name : Name
  levelParams : List Name
  type : Expr
  value : Expr

/-- A closed matcher equation (statement and proof), with the auxiliary theorems of the environment branch it
    refers to (in dependency order). -/
structure SharedEquation where
  stmt : Expr
  proof : Expr
  aux : Array AuxThm

/-- The auxiliary theorems of the current module referenced by `es` (transitively), in dependency order. -/
partial def auxTheorems (es : Array Expr) : MetaM (Array AuxThm) := do
  let env ← getEnv
  let visited ← IO.mkRef ({} : NameSet)
  let out ← IO.mkRef (#[] : Array AuxThm)
  let rec visit (e : Expr) : MetaM Unit := do
    for n in e.getUsedConstants do
      if !n.isInternal || (env.getModuleIdxFor? n).isSome || (← visited.get).contains n then continue
      visited.modify (·.insert n)
      let some (.thmInfo info) := env.find? n | continue
      visit info.type
      visit info.value
      out.modify (·.push { name := n, levelParams := info.levelParams, type := info.type, value := info.value })
  for e in es do visit e
  out.get

/-- Add the auxiliary theorems `aux` of another environment branch to the environment (under new names, unless
    the current branch has a theorem of the same name and type), and rename the references to them in `es`. -/
def transplant (aux : Array AuxThm) (es : Array Expr) : MetaM (Array Expr) := do
  let mut ren : Std.HashMap Name Name := {}
  for a in aux do
    let rename (e : Expr) : Expr := if ren.isEmpty then e else
      e.replace fun e => match e with
        | .const n us => (ren.get? n).map (mkConst · us)
        | _ => none
    let ty := rename a.type
    if let some (.thmInfo info) := (← getEnv).find? a.name then
      if info.type == ty && info.levelParams == a.levelParams then continue
    let n ← mkAuxLemma a.levelParams ty (rename a.value)
    ren := ren.insert a.name n
  return es.map fun e => if ren.isEmpty then e else
    e.replace fun e => match e with
      | .const n us => (ren.get? n).map (mkConst · us)
      | _ => none

/-- Matcher equations shared by the commands (`#blaster` commands are elaborated concurrently, in their own
    environment branches): per matcher instance closed over its free variables (with Blaster's optimized
    instance), the task computing its equation (`none` when the computation was aborted). -/
initialize sharedEquations : IO.Ref (Std.HashMap (Expr × Option Expr) (Task (Option (Option SharedEquation)))) ←
  IO.mkRef {}

/-- `compute` once per `key` across the commands: the other commands wait for its result (and compute it
    themselves when the computation was aborted, e.g., by an exception). -/
def shareEquation (key : Expr × Option Expr) (compute : Term.TermElabM (Option SharedEquation)) :
    Term.TermElabM (Option SharedEquation) := do
  let p ← IO.Promise.new
  let existing? ← sharedEquations.modifyGet fun m => match m.get? key with
    | some t => (some t, m)
    | none => (none, m.insert key (p.resultD none))
  if let some t := existing? then
    if let some r ← IO.wait t then return r
    return ← compute
  try
    let r ← compute
    p.resolve (some r)
    return r
  finally
    if !(← p.isResolved) then
      p.resolve none
      sharedEquations.modify (·.erase key)

/-- `∀ xs alts, M params motive xs alts = ite ...`, proved once per matcher instance (as an auxiliary
    theorem). The equation is stated and proved in the local context of the free variables of the instance
    (e.g., in the parameters), and shared by the commands (see `shareEquation`). -/
def matcherLemma (m : Name) (lvls : List Level) (info : MatcherInfo) (params : Array Expr) (motive resTy : Expr) :
    BridgeM (Option Expr) := do
  let head := mkAppN (mkConst m lvls) (params.push motive)
  if let some l := (← get).lemmas.get? head then return l
  let inst? := (← read).matchInst m
  let l ← try
      let xs ← fvarClosure #[head]
      let compute : Term.TermElabM (Option SharedEquation) := withRestrictedLCtx xs do
        let some (stmt, pf) ← matcherEquation m lvls info inst? params motive resTy | return none
        let stmt ← mkForallFVars xs stmt
        let pf ← mkLambdaFVars xs pf
        if stmt.hasFVar || pf.hasFVar || stmt.hasMVar || pf.hasMVar then return none
        -- NOTE: the statement contains the proofs of the equations of named patterns
        return some { stmt, proof := pf, aux := ← auxTheorems #[stmt, pf] }
      let key := (← mkLambdaFVars xs head, inst?)
      let r ← if key.1.hasLevelParam || key.1.hasFVar then compute else shareEquation key compute
      let some eqn := r | pure none
      -- NOTE: the equation (computed by another command) is checked in the environment of this command, where
      -- the equations of the matcher (e.g., its splitter) are realized, and the auxiliary theorems are added
      let c ← try
          try discard <| Match.getEquationsFor m catch _ => pure ()
          let #[stmt, pf] ← transplant eqn.aux #[eqn.stmt, eqn.proof] | unreachable!
          mkAuxTheorem stmt pf
        catch ex => do
          dbg m!"bridge: shared equation of {m} rejected: {ex.toMessageData}"
          let some eqn ← compute | return none
          mkAuxTheorem eqn.stmt eqn.proof
      pure (some (mkAppN c xs))
    catch ex => dbg m!"bridge: matcher lemma {m}: {ex.toMessageData}"; pure none
  modify fun s => { s with lemmas := s.lemmas.insert head l }
  return l

/-- `(b, app = b)` where `b` is the right-hand side of the unfolding equation of the function `f` of `app`
    (`f.eq_def`, with the arguments of `app`). -/
def unfoldEqn? (app : Expr) : MetaM (Option (Expr × Expr)) := do
  let .const f us := app.getAppFn | return none
  let some eqDef ← (try getUnfoldEqnFor? f (nonRec := true) catch _ => pure none) | return none
  let some (_, app', b) := (← instantiateForall (← inferType (mkConst eqDef us)) app.getAppArgs).eq? | return none
  if app' != app then return none
  return some (b.headBeta, mkAppN (mkConst eqDef us) app.getAppArgs)

/-- `W(a) = W(b)` from `a = b`. -/
def World.liftEq (w : World) (p : Expr) : MetaM Expr :=
  match w with
  | .same => pure p
  | .nat => mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) p
  | .bool => mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) p
  | .poly w _ => mkCongrArg w p

/-- Whether `f` is a function of the user, which Blaster's optimizer may inline (not a definition of the
    libraries, which are translated by dedicated rules). -/
def isUserFunction (f : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo _) := env.find? f | return false
  if (← isMatcher f) || isInstanceCore env f || (env.getProjectionFnInfo? f).isSome then return false
  match env.getModuleIdxFor? f with
  | none => return true
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      return !(m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean || m.getRoot == `Blaster)

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

/-- Blaster's normal forms of the standard notations of the arithmetic operations on `Nat` and `Int`
    (definitionally equal, see `standardForm`). -/
def blasterForm (e : Expr) : Expr := Id.run do
  let ops := #[(``HAdd.hAdd, ``Nat.add, ``Int.add), (``HSub.hSub, ``Nat.sub, ``Int.sub),
    (``HMul.hMul, ``Nat.mul, ``Int.mul), (``HDiv.hDiv, ``Nat.div, ``Int.ediv), (``HMod.hMod, ``Nat.mod, ``Int.emod)]
  for (op, natOp, intOp) in ops do
    if e.isAppOfArity op 6 then
      let ty := e.getArg! 0
      if ty.isConstOf ``Nat && e.getArg! 1 == ty && e.getArg! 2 == ty then
        return mkApp2 (mkConst natOp) (e.getArg! 4) (e.getArg! 5)
      if ty.isConstOf ``Int && e.getArg! 1 == ty && e.getArg! 2 == ty then
        return mkApp2 (mkConst intOp) (e.getArg! 4) (e.getArg! 5)
  return e

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
  let facts := (← read).facts
  if facts.isEmpty then return none
  withRestrictedLCtx (facts.push p) do
    if let some pf ← omegaProof? p then return some pf
    -- hypotheses on datatype testers (e.g., the negated conditions of the previous alternatives of a matcher, in
    -- the last alternative): case analyses on the variables of non-recursive datatypes
    Blaster.Reconstruct.proveWithTactic p (← `(tactic| (blaster_cases_nonrec <;>
      (try simp only [and_true, true_and, not_true, not_false_eq_true, and_false, false_and] at *) <;>
      $(← omegaTac):tactic)))

partial def walkCore (a b : Expr) : BridgeM (Option Expr) := do
  let ta ← inferType a
  let tb ← inferType b
  let some w ← worldOf ta tb | return none
  -- applications of functions of the polymorphic encoding (e.g., `f x` with `f : α → β`)
  if a.isApp && b.isApp && !a.getAppFn.isConst then
    if let some p ← walkLiftedApp a b then return some (← mkExpectedTypeHint p (← mkEq (w.lift a) b))
  -- polymorphic functions at sort variables, interpreted at the universe (e.g., `List.zipWith`)
  if let .const f _ := a.getAppFn then
    if b.getAppFn.isConstOf f && a.getAppNumArgs == b.getAppNumArgs && a != b then
      if let some p ← walkPolyApp a b then return some (← mkExpectedTypeHint p (← mkEq (w.lift a) b))
  match w with
  | .same => walkSame a b
  | .nat => walkNat a b
  | .bool => walkBool a b
  | .poly w h => walkPoly w h a b

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
  -- NOTE: `ite` in the world of the polymorphic encoding is handled by `walkPoly`
  if let .poly .. := w then return none
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
    | .same | .poly .. => mkEqRefl a
    | .nat =>
        mkEqTrans (← mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) pa)
          (mkApp4 (mkConst ``natCast_ite) c inst x y)
    | .bool =>
        mkEqTrans (← mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) pa)
          (mkApp4 (mkConst ``boolEq_ite) c inst x y)
  let (α', x₀, y₀) := match w with
    | .same | .poly .. => (α, x, y)
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
  | .poly .. => return none

/-- Matchers on the goal side: `W(a) = W(i)` where `i` is the `ite` encoding of `a`, then `W(i) = b`. -/
partial def walkMatcher (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  let some (i, pa) ← matcherIte? a | return none
  let some pi ← walk i b | return none
  let pa' ← match w with
    | .same => pure pa
    | .nat => mkCongrArg (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt)) pa
    | .bool => mkCongrArg (mkLambda `z .default (mkConst ``Bool) (boolTrue (.bvar 0))) pa
    | .poly w _ => mkCongrArg w pa
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
  -- NOTE: the standard notations (e.g., `x - y` on `Nat`) as Blaster's normal forms (`Nat.sub x y`)
  let a₀ := a
  let a := blasterForm a
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
  return some (← mkExpectedTypeHint pf (← mkEq (w.lift a₀) b))

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
  -- NOTE: the sides of equations may be swapped by Blaster's normalization (e.g., `0 = x` for `x = 0`)
  if a.isAppOfArity ``Eq 3 && b.isAppOfArity ``Eq 3 then
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    if aa[0]! != ba[0]! then
      let some w ← worldOf aa[0]! ba[0]! | return none
      let eqOf (x y : Expr) : BridgeM (Option Expr) := do
        let some px ← walk aa[1]! x | return none
        let some py ← walk aa[2]! y | return none
        match w with
        | .nat => return some (mkApp6 (mkConst ``nat_eq) aa[1]! aa[2]! x y px py)
        | .bool => return some (mkApp6 (mkConst ``bool_eq) aa[1]! aa[2]! x y px py)
        | .poly _ h => return some (← mkAppM ``Poly.eq_world #[h, px, py])
        | .same => return none
      if let some p ← eqOf ba[1]! ba[2]! then return some p
      if let some p ← eqOf ba[2]! ba[1]! then
        return some (← mkEqTrans p (mkApp3 (mkConst ``Local.eq_comm_eq [← getLevel ba[0]!]) ba[0]! ba[2]! ba[1]!))
      if !(w matches .same) then return none
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
  -- quantifiers over the types of the polymorphic encoding, guarded by membership predicates
  if let some (b', h) ← interleaveGuards b then
    let some p ← walk a b' | return none
    return some (← mkEqTrans p h)
  if let some p ← walkPolyBinder a b then return some p
  -- quantifiers over `Nat`, translated as quantifiers over `Int` guarded by `0 ≤ x`
  if let some p ← walkNatBinder a b then return some p
  -- binders
  match a, b with
  | .forallE n t body bi, .forallE _ t' body' _ =>
      if !body.hasLooseBVars && !body'.hasLooseBVars then
        let some pt ← walk t t' | return none
        let some pb ← walk body body' | return none
        return some (← mkAppM ``implies_congr #[pt, pb])
      if t != t' && !(← isDefEq t t') then return none
      return ← withLocalDecl n bi t fun x => do
        let some pb ← walk (body.instantiate1 x) (body'.instantiate1 x) | return none
        return some (← mkAppM ``forall_congr #[← mkLambdaFVars #[x] pb])
  | .lam n t body bi, .lam _ t' body' _ =>
      if t != t' && !(← isDefEq t t') then return none
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
  -- equations of the same world with swapped sides
  if a.isAppOfArity ``Eq 3 && b.isAppOfArity ``Eq 3 && a.getArg! 0 == b.getArg! 0 then
    if let some px ← walk (a.getArg! 1) (b.getArg! 2) then
      if let some py ← walk (a.getArg! 2) (b.getArg! 1) then
        let u ← getLevel (a.getArg! 0)
        let p ← mkCongr (← mkCongrArg (mkApp (mkConst ``Eq [u]) (a.getArg! 0)) px) py
        return some (← mkEqTrans p (mkApp3 (mkConst ``Local.eq_comm_eq [u]) (b.getArg! 0) (b.getArg! 2) (b.getArg! 1)))
  -- `Int` terms in `Nat` positions (`Int.toNat`)
  if b.isAppOfArity ``Int.toNat 1 then
    if (← whnfR (← inferType a)).isConstOf ``Nat then
      if let some p ← walk a b.appArg! then
        if (← inferType p).isAppOfArity ``Eq 3 && ((← inferType p).getArg! 0).isConstOf ``Int then
          return some (mkApp3 (mkConst ``nat_toNat) a b.appArg! p)
  if let some p ← walkMacro .same a b then return some p
  if let some p ← walkUnfold .same a b then return some p
  if let some p ← walkArith .same a b then return some p
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

/-- `∀ x : T, P x` (resp. `∃ x : T, P x`) and `∀ y : D, Img w y → Q y` (resp. `∃ y : D, Img w y ∧ Q y`) where
    `w : T → D` is the world of `T` in the polymorphic encoding (see `Poly`). -/
partial def walkPolyBinder (a b : Expr) : BridgeM (Option Expr) := do
  -- (binder name, `T`, body of `P`, `D`, guard, body of `Q` (with one loose bound variable each), `∃`)
  let view? : Option (Name × Expr × Expr × Expr × Expr × Expr × Bool) :=
    match a, b with
    | .forallE n t p _, .forallE _ d (.forallE _ guard q _) _ =>
        if q.hasLooseBVar 0 then none else some (n, t, p, d, guard, q.lowerLooseBVars 1 1, false)
    | _, _ =>
        if a.isAppOfArity ``Exists 2 && b.isAppOfArity ``Exists 2 then
          match a.getArg! 1, b.getArg! 1 with
          | .lam n t p _, .lam _ d g _ =>
              if g.isAppOfArity ``And 2 then some (n, t, p, d, g.getArg! 0, g.getArg! 1, true) else none
          | _, _ => none
        else none
  let some (n, t, p, d, guard, q, ex) := view? | return none
  if t.hasLooseBVars || d.hasLooseBVars || !Poly.hasUniv d then return none
  let some (w, _) ← Poly.mkWorld t d | return none
  -- the guard is the membership predicate of the world
  let ok ← withLocalDeclD `y d fun y => do
    withReducible (isDefEq (guard.instantiate1 y) (← mkAppM ``Poly.Img #[w, y]))
  if !ok then return none
  withLocalDeclD n t fun x => do
    let some h ← walk (p.instantiate1 x) (q.instantiate1 (Poly.applyWorld w x)) | return none
    let pf ← mkAppOptM (if ex then ``Poly.exists_world else ``Poly.forall_world)
      (#[t, d, w, mkLambda n .default t p, mkLambda `y .default d q, ← mkLambdaFVars #[x] h].map some)
    return some (← mkExpectedTypeHint pf (← mkEq a b))

/-- `W(f x) = F X` where `f : A → B` is a function of the polymorphic encoding (e.g., `f : α → β` with `α`, `β` sort
    variables), whose world is `liftFun wa wb dflt`: from `liftFun wa wb dflt f = F` and `wa x = X`. The proof
    states `wb (f x) = F X`, i.e., `W(f x) = F X` up to definitional unfolding. -/
partial def walkLiftedApp (a b : Expr) : BridgeM (Option Expr) := do
  let .app fa xa := a | return none
  let .app fb xb := b | return none
  let tF ← inferType fb
  if !Poly.hasUniv tF then return none
  let some (wf, hf) ← Poly.mkWorld (← inferType fa) tF | return none
  if !(wf.isAppOfArity ``Poly.liftFun 7 && hf.isAppOfArity ``Poly.liftFun_injective 9) then return none
  let wa := wf.getArg! 4
  let some pf ← walk fa fb | return none
  let some px ← walk xa xb | return none
  let pf ← mkExpectedTypeHint pf (← mkEq (Poly.applyWorld wf fa) fb)
  let px ← mkExpectedTypeHint px (← mkEq (Poly.applyWorld wa xa) xb)
  return some (← mkAppM ``Poly.app_world #[hf.getArg! 5, pf, px])

/-- `W(f ts xs) = f ts' ys` where `f` is a polymorphic function at sort variables in the goal (type arguments `ts`)
    and at the universe in the interpretation (`ts'`, see `Poly.instantiateUniv`): from the naturality lemma
    `∀ αs xs, f ts' (W xs) = W (f ts xs)` (`αs` the sort variables of `ts`, proved once per statement by
    `blaster_poly_nat`) and `W(xᵢ) = yᵢ`. -/
partial def walkPolyApp (a b : Expr) : BridgeM (Option Expr) := do
  let fa := a.getAppFn
  let fb := b.getAppFn
  let .const f _ := fa | return none
  -- relations, `ite` and matchers have their own lemmas
  if [``Eq, ``Ne, ``HEq, ``ite, ``dite].contains f || (← isMatcher f) || isCasesOnRecursor (← getEnv) f then
    return none
  let as := a.getAppArgs
  let bs := b.getAppArgs
  let info ← getFunInfoNArgs fa as.size
  -- type and instance arguments
  let isType (i : Nat) : Bool := (info.paramInfo[i]?.map fun p => p.hasFwdDeps || p.isInstImplicit).getD false
  let tpos := (List.range as.size).filter isType
  if !(tpos.any fun i => Poly.hasUniv bs[i]!) || tpos.any (fun i => bs[i]!.hasFVar) then return none
  -- the sort variables of the instantiation in the goal
  let σ := (tpos.foldl (fun s i => collectFVars s as[i]!) {}).fvarIds.map mkFVar
  if ← σ.anyM fun α => do return !(← inferType α).isSort || (← isProp (← inferType α)) then return none
  -- domains of the value arguments (non-dependent)
  let mut tyA ← inferType fa
  let mut tyB ← inferType fb
  let mut doms : Array (Expr × Expr) := #[]
  for i in [:as.size] do
    let .forallE _ dA bA _ ← whnf tyA | return none
    let .forallE _ dB bB _ ← whnf tyB | return none
    if isType i then
      tyA := bA.instantiate1 as[i]!
      tyB := bB.instantiate1 bs[i]!
    else
      if bA.hasLooseBVars || bB.hasLooseBVars then return none
      doms := doms.push (dA, dB)
      tyA := bA
      tyB := bB
  let (rA, rB) := (tyA, tyB)
  let decls := doms.mapIdx fun k (dA, _) => (Name.mkSimple s!"x{k}", fun (_ : Array Expr) => pure dA)
  let stmt? ← withLocalDeclsD decls fun xs => do
    let mut argsA := #[]
    let mut argsB := #[]
    let mut k := 0
    for i in [:as.size] do
      if isType i then
        argsA := argsA.push as[i]!
        argsB := argsB.push bs[i]!
      else
        let (dA, dB) := doms[k]!
        let x := xs[k]!
        argsA := argsA.push x
        argsB := argsB.push (← match ← Poly.mkWorld dA dB with
          | some (w, _) => pure (Poly.applyWorld w x)
          | none => do if ← isDefEq dA dB then pure x else throwError "walkPolyApp: no world for {dA}")
        k := k + 1
    let rhs ← match ← Poly.mkWorld rA rB with
      | some (w, _) => pure (Poly.applyWorld w (mkAppN fa argsA))
      | none => do if ← isDefEq rA rB then pure (mkAppN fa argsA) else throwError "walkPolyApp: no world for {rA}"
    let stmt ← mkForallFVars (σ ++ xs) (← mkEq (mkAppN fb argsB) rhs)
    return if stmt.hasFVar then none else some stmt
  let some stmt := stmt? | return none
  let lem? ← match (← get).natLemmas.get? stmt with
    | some l => pure l
    | none =>
        let l ← try
            -- NOTE: proved in the empty local context (the statement is closed)
            let some pf ← withLCtx {} {} (Blaster.Reconstruct.proveWithTactic stmt (← `(tactic| blaster_poly_nat)))
              | pure none
            some <$> mkAuxTheorem stmt pf
          catch _ => pure none
        if l.isNone then dbg m!"bridge: naturality not proved: {stmt}"
        modify fun s => { s with natLemmas := s.natLemmas.insert stmt l }
        pure l
  let some lem := lem? | return none
  let vals := (List.range as.size).filter (!isType ·) |>.toArray.map (as[·]!)
  -- `W(f ts xs) = f ts' (W xs)`, then congruence with `W(xᵢ) = yᵢ`
  let mut pf ← mkEqSymm (mkAppN lem (σ ++ vals))
  let mut cur := (← inferType pf).appArg!.getAppArgs
  for i in [:as.size] do
    if isType i || cur[i]! == bs[i]! then continue
    let some p ← walk as[i]! bs[i]! | return none
    let ta ← inferType cur[i]!
    let ctx ← withLocalDeclD `z ta fun z => mkLambdaFVars #[z] (mkAppN fb (cur.set! i z))
    pf ← mkEqTrans pf (← mkCongrArg ctx (← mkExpectedTypeHint p (← mkEq cur[i]! bs[i]!)))
    cur := cur.set! i bs[i]!
  return some pf

/-- `w a = b` where `w` is the world of the type of `a` in the polymorphic encoding (see `Poly.mkWorld`), with
    `h` the proof of its injectivity. -/
partial def walkPoly (w h a b : Expr) : BridgeM (Option Expr) := do
  let la := Poly.applyWorld w a
  if la == b then return some (← mkEqRefl b)
  match a, b with
  | .mdata _ a', _ => return ← walk a' b
  | _, .mdata _ b' => return ← walk a b'
  | .lam n t body _, .lam _ d body' _ =>
      -- functions: `liftFun wa wb dflt (fun x => t) = fun y => t'` from `wb t = t'[y := wa x]` and `t'` being
      -- `dflt` outside of the domain (e.g., the identity)
      if !(w.isAppOfArity ``Poly.liftFun 7 && h.isAppOfArity ``Poly.liftFun_injective 9) then return none
      let (wa, wb, dflt) := (w.getArg! 4, w.getArg! 5, w.getArg! 6)
      let ts := #[w.getArg! 0, w.getArg! 1, w.getArg! 2, w.getArg! 3]
      -- lambda terms guarded by the membership predicates of their parameters (see `Driver.guardedLambda`):
      -- `liftFun wa wb dflt (fun x => t) = fun y => if Img wa y then t' else dflt y` from `wb t = t'[y := wa x]`
      if let some (c, x', y', _) := classicalIte? body' then
        if ← withLocalDeclD `y d fun y => do
            withReducible (isDefEq (c.instantiate1 y) (← mkAppM ``Poly.Img #[wa, y])) then
          let ok ← withLocalDeclD `y d fun y => do withReducible (isDefEq (y'.instantiate1 y) (Poly.applyWorld dflt y))
          if ok then
            let some hb ← withLocalDeclD n t fun x => do
                let some p ← walk (body.instantiate1 x) (x'.instantiate1 (Poly.applyWorld wa x)) | return none
                some <$> mkLambdaFVars #[x] p
              | return none
            let pf ← mkAppOptM ``Poly.lam_world_ite
              ((ts ++ #[wa, h.getArg! 5, wb, dflt, a, .lam `y d x' .default, hb]).map some)
            return some (← mkExpectedTypeHint pf (← mkEq la b))
      let some hb ← withLocalDeclD n t fun x => do
          let some p ← walk (body.instantiate1 x) (body'.instantiate1 (Poly.applyWorld wa x)) | return none
          some <$> mkLambdaFVars #[x] p
        | return none
      let some hout ← withLocalDeclD `y d fun y => do
          withLocalDeclD `hy (mkNot (← mkAppM ``Poly.Img #[wa, y])) fun hy => do
          let l := Poly.applyWorld dflt y
          let r := body'.instantiate1 y
          if !(← withReducible (isDefEq l r)) then return none
          some <$> mkLambdaFVars #[y, hy] (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq l r))
        | return none
      return some (← mkAppOptM ``Poly.lam_world ((ts ++ #[wa, h.getArg! 5, wb, dflt, a, b, hb, hout]).map some))
  | _, _ => pure ()
  -- `ite` on the goal side
  if let some (α, c, inst, x, y, pa) ← iteView? a then
    if let some (c', x', y', _) := classicalIte? b then
      let some pc ← walk c c' | return none
      let branch (cond v v' : Expr) : BridgeM (Option Expr) :=
        withLocalDeclD `hc cond fun hc => withReader (fun cfg => { cfg with facts := cfg.facts.push hc }) do
          let some p ← walk v v' | return none
          some <$> mkLambdaFVars #[hc] (← mkExpectedTypeHint p (← mkEq (Poly.applyWorld w v) v'))
      let some px ← branch c x x' | return none
      let some py ← branch (mkNot c) y y' | return none
      let pIte ← mkAppOptM ``Poly.ite_world (#[α, ← inferType b, w, c, c', inst, x, y, x', y', pc, px, py].map some)
      return some (← mkEqTrans (← mkCongrArg w pa) pIte)
  -- constructors of the functors (e.g., `List.map w (x :: xs)` is `w x :: List.map w xs`)
  let ctor (map ctor : Name) (mapArity ctorArity : Nat) (ws : Array Expr) : BridgeM (Option Expr) := do
    if !(w.isAppOfArity map mapArity && a.isAppOfArity ctor ctorArity && b.isAppOfArity ctor ctorArity) then
      return none
    let nps := ctorArity - ws.size
    let mut pf ← mkEqRefl (mkAppN b.getAppFn (b.getAppArgs.extract 0 nps))
    for i in [:ws.size] do
      let (x, x') := (a.getArg! (nps + i), b.getArg! (nps + i))
      let some p ← walk x x' | return none
      pf ← mkCongr pf (← mkExpectedTypeHint p (← mkEq (Poly.applyWorld ws[i]! x) x'))
    return some (← mkExpectedTypeHint pf (← mkEq la b))
  if w.isAppOfArity ``List.map 3 then
    if let some p ← ctor ``List.map ``List.cons 3 3 #[w.getArg! 2, w] then return some p
  if w.isAppOfArity ``Option.map 3 then
    if let some p ← ctor ``Option.map ``Option.some 3 2 #[w.getArg! 2] then return some p
  if w.isAppOfArity ``Prod.map 6 then
    if let some p ← ctor ``Prod.map ``Prod.mk 6 4 #[w.getArg! 4, w.getArg! 5] then return some p
  if let some p ← walkMatcher (.poly w h) a b then return some p
  byDefEq la b

/-- Functions of the user inlined by Blaster's optimizer: `W(f xs) = W(b)` by the unfolding equation of `f`,
    then `W(b) = b'` (at most `Cfg.unfoldDepth` nested unfoldings). -/
partial def walkUnfold (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  if (← read).unfoldDepth == 0 then return none
  let .const f _ := a.getAppFn | return none
  if b.getAppFn.isConstOf f || !(← isUserFunction f) then return none
  let some (u, eqn) ← unfoldEqn? a | return none
  let some p ← withReader (fun c => { c with unfoldDepth := c.unfoldDepth - 1 }) (walk u b) | return none
  return some (← mkEqTrans (← w.liftEq eqn) p)

/-- Arithmetic terms equal modulo the normalizations of Blaster's optimizer (e.g., the reordering of the operands
    of `+` in the definitions of functions): the arithmetic atoms of `a` are related to atoms of `b` (`walk`),
    then `W(a) = b` is proved by `omega` from these equations (and the hypotheses of the branch). -/
partial def walkArith (w : World) (a b : Expr) : BridgeM (Option Expr) := do
  if !(Local.isArithHead a && Local.isArithHead b) then return none
  if !(w == .nat || (w == .same && (← whnfR (← inferType a)).isConstOf ``Int)) then return none
  let as ← Local.arithAtoms a
  let bs ← Local.arithAtoms b
  if as.isEmpty || as.size > 8 || bs.size > 8 then return none
  let mut eqs : Array (Expr × Expr) := #[]
  for x in as do
    let mut found := false
    for y in bs do
      if let some p ← walk x y then
        eqs := eqs.push (← inferType p, p)
        found := true
        break
    if !found then return none
  let goal ← mkEq (w.lift a) b
  let decls := eqs.mapIdx fun i (t, _) => (Name.mkSimple s!"e{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun hs => do
    let some pf ← withRestrictedLCtx ((hs ++ (← read).facts).push goal) (omegaProof? goal) | return none
    return some (mkAppN (← mkLambdaFVars hs pf) (eqs.map (·.2)))

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
  if let some p ← walkUnfold .nat a b then return some p
  if let some p ← walkArith .nat a b then return some p
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
  if let some p ← walkUnfold .bool a b then return some p
  byDefEq la b

end

/-- Proof of the interpretation `c` of the definition of a Lean function `f` asserted by Blaster
    (`∀ xs, W(f xs) = b`, see `World`): the unfolding equation of `f` (`f.eq_def`), then the traversal of its
    right-hand side and `b` (e.g., the `ite` encoding of the `match` defining `f`). -/
def proveDefinition? (cfg : Cfg) (c : Expr) : Term.TermElabM (Option Expr) :=
  forallTelescope c fun xs body => do
    let some (_, lhs, rhs) := body.eq? | return none
    let (w, app) :=
      if lhs.isAppOfArity ``Nat.cast 3 then (World.nat, lhs.appArg!)
      else if lhs.isAppOfArity ``Eq 3 && (lhs.getArg! 2).isConstOf ``Bool.true then (World.bool, lhs.getArg! 1)
      else (World.same, lhs)
    if w.lift app != lhs then return none
    let .const f _ := app.getAppFn | return none
    let some (unfolded, eqn) ← unfoldEqn? app | dbg m!"bridge: no unfolding equation for {f}"; return none
    -- NOTE: the hypotheses of the definition (e.g., `0 ≤ x` for the `Int` variables of `Nat` arguments) are facts
    let facts ← xs.filterM fun x => do isProp (← inferType x)
    let (r, st) ← (walk unfolded rhs |>.run { cfg with facts := cfg.facts ++ facts }).run {}
    let some p := r | do
      for (a, b) in st.failures.extract (st.failures.size - 4) st.failures.size do dbg m!"bridge: definition of {f} not proved: {← ppExpr a}\n  ≠ {← ppExpr b}"
      return none
    mkLambdaFVars xs (← mkExpectedTypeHint (← mkEqTrans (← w.liftEq eqn) p) body)

/-- Proof of `a = b` (resp. `a → b` when `imp`) for a goal term `a` and the interpretation `b` of its
    translation, with the failed pairs of subterms (deepest first) when it fails. -/
def prove (cfg : Cfg) (a b : Expr) : Term.TermElabM (Option Expr × Array (Expr × Expr)) := do
  let t0 ← IO.monoMsNow
  let (r, s) ← (walk a b |>.run cfg).run {}
  dbg m!"bridge: {(← IO.monoMsNow) - t0} ms ({r.isSome})"
  return (r, s.failures)

end Blaster.Reconstruct.SmtProof.Bridge
