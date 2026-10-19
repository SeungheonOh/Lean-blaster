import Lean

/-!
# Interpretation of Blaster's polymorphic encoding

Blaster encodes the sort variables of a goal (e.g., `α β : Type`) as values of an SMT sort `@Type`, and the values of
all the types they denote as values of a single SMT sort `@Instance`, with membership predicates `@isInstance v α`
(see `Blaster.Smt.generateSortInstDecl`). SMT sorts being non-empty, `@Instance` can't be interpreted as one of the
sort variables when several of them occur, nor when the sort variable may denote an empty type (e.g., for the skolem
constants of sort `@Instance`). The general interpretation is:
 - `@Type` (for the sort variables of `Sort u`) is `Sort u`, and the sort variables are interpreted as themselves;
 - `@Instance` is `Univ.{u}`, the values of all the types of `Sort u` (and `none`, such that it is inhabited);
 - a Lean value `x : T` is related to its interpretation by a *world* `w : T → D` (where `D` is the interpretation of
   the SMT sort of `x`): `inj α` for the sort variables, `List.map w` for lists, `liftFun wa wb dflt` for functions
   (applied to their interpreted arguments, `dflt` outside of their domain), ... (see `mkWorld`);
 - Blaster's membership predicates (`@isInstance`, `@isFun`, `@isList`, ...) are the images of the worlds (`Img`),
   such that the extensionality axioms of the encoding hold: the functions of the encoding are determined by their
   values on their domain.

NOTE: the values of the datatypes of the user over sort variables (e.g., `Either α β`) have no world (no `map`
function), and the Lean functions of the goal applied to values of sort variables (e.g., `natCast : α → Nat` at
several sort variables) are only interpreted when `@Instance` is interpreted as the sort variable. The lambda terms of
the encoding are interpreted by their bodies on the whole universe, such that their membership predicates only hold
when their bodies are `dflt` outside of their domain (e.g., the identity).
-/

open Lean Meta Elab Tactic

namespace Blaster.Reconstruct.SmtProof.Poly

/-- Values of the types of `Sort u`: interpretation of the SMT sort `@Instance` of the sort variables of `Sort u`.
    Inhabited (`none`), also when all the types are empty. -/
def Univ : Type u := Option (PSigma fun (α : Sort u) => α)

instance : Inhabited Univ.{u} := ⟨(none : Option _)⟩

/-- The value `x : α` in the universe. -/
def inj (α : Sort u) (x : α) : Univ.{u} := some ⟨α, x⟩

theorem inj_injective (α : Sort u) : Function.Injective (inj α) := by
  intro x y h
  have h' : (⟨α, x⟩ : PSigma fun (α : Sort u) => α) = ⟨α, y⟩ := Option.some.inj h
  cases h'; rfl

/-- The values of `D` in the image of the world `w : T → D` (interpretation of Blaster's membership predicates,
    e.g., `@isInstance v α` is `Img (inj α) v`). -/
def Img {T : Sort u} {D : Sort v} (w : T → D) (d : D) : Prop := ∃ x, d = w x

theorem img_self {T : Sort u} {D : Sort v} (w : T → D) (x : T) : Img w (w x) := ⟨x, rfl⟩

/-- The function `f : A → B` on the interpretations `D` and `C` of its domain and codomain (worlds `wa : A → D`,
    `wb : B → C`), `dflt` outside of the image of `wa`. -/
noncomputable def liftFun {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    (wa : A → D) (wb : B → C) (dflt : D → C) (f : A → B) (x : D) : C :=
  @dite C (Img wa x) (Classical.propDecidable _) (fun h => wb (f (Classical.choose h))) (fun _ => dflt x)

theorem liftFun_apply {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) (wb : B → C) (dflt : D → C) (f : A → B) (x : A) :
    liftFun wa wb dflt f (wa x) = wb (f x) := by
  have h : Img wa (wa x) := ⟨x, rfl⟩
  unfold liftFun
  rw [dif_pos h]
  exact congrArg (fun y => wb (f y)) (hw (Classical.choose_spec h)).symm

theorem liftFun_out {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    (wa : A → D) (wb : B → C) (dflt : D → C) (f : A → B) {x : D} (h : ¬ Img wa x) :
    liftFun wa wb dflt f x = dflt x := by
  unfold liftFun; rw [dif_neg h]

theorem liftFun_injective {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hwa : Function.Injective wa) {wb : B → C} (hwb : Function.Injective wb) (dflt : D → C) :
    Function.Injective (liftFun wa wb dflt) := by
  intro f g h
  funext x
  apply hwb
  rw [← liftFun_apply hwa wb dflt f x, ← liftFun_apply hwa wb dflt g x, h]

theorem natCast_injective : Function.Injective (@Nat.cast Int instNatCastInt) :=
  fun _ _ h => Int.ofNat.inj h

theorem boolTrue_injective : Function.Injective (fun (b : Bool) => b = true) := by
  intro x y h
  cases x <;> cases y <;> simp_all

theorem id_injective (α : Sort u) : Function.Injective (@id α) := fun _ _ h => h

theorem listMap_injective {α : Type u} {β : Type v} {w : α → β} (hw : Function.Injective w) :
    Function.Injective (List.map w) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons => simp at h
  | cons x xs ih => cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hw h.1, ih h.2]

theorem optionMap_injective {α : Type u} {β : Type v} {w : α → β} (hw : Function.Injective w) :
    Function.Injective (Option.map w) := by
  intro x y h
  cases x <;> cases y <;> simp_all
  exact hw h

theorem prodMap_injective {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}
    {w₁ : α₁ → α₂} {w₂ : β₁ → β₂} (h₁ : Function.Injective w₁) (h₂ : Function.Injective w₂) :
    Function.Injective (Prod.map w₁ w₂) := by
  intro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.map, Prod.mk.injEq] at h
  rw [h₁ h.1, h₂ h.2]

/-! ## Bridge lemmas (see `Bridge.lean`) -/

theorem eq_world {T : Sort u} {D : Sort v} {w : T → D} (hw : Function.Injective w) {x y : T} {x' y' : D}
    (hx : w x = x') (hy : w y = y') : (x = y) = (x' = y') := by
  subst hx hy
  exact propext ⟨fun h => h ▸ rfl, fun h => hw h⟩

theorem forall_world {T : Sort u} {D : Sort v} (w : T → D) {P : T → Prop} {Q : D → Prop}
    (h : ∀ x, P x = Q (w x)) : (∀ x, P x) = (∀ y, Img w y → Q y) := by
  apply propext; constructor
  · intro hp y ⟨x, hx⟩; subst hx; rw [← h]; exact hp x
  · intro hq x; rw [h]; exact hq (w x) ⟨x, rfl⟩

theorem exists_world {T : Sort u} {D : Sort v} (w : T → D) {P : T → Prop} {Q : D → Prop}
    (h : ∀ x, P x = Q (w x)) : (∃ x, P x) = (∃ y, Img w y ∧ Q y) := by
  apply propext; constructor
  · intro ⟨x, hx⟩; exact ⟨w x, ⟨x, rfl⟩, h x ▸ hx⟩
  · intro ⟨y, ⟨x, hx⟩, hq⟩; subst hx; exact ⟨x, (h x).symm ▸ hq⟩

theorem app_world {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) {wb : B → C} {dflt : D → C} {f : A → B} {F : D → C} {x : A} {X : D}
    (hf : liftFun wa wb dflt f = F) (hx : wa x = X) : wb (f x) = F X := by
  subst hf hx; exact (liftFun_apply hw wb dflt f x).symm

theorem lam_world {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) {wb : B → C} {dflt : D → C} {f : A → B} {F : D → C}
    (h : ∀ x, wb (f x) = F (wa x)) (hout : ∀ y, ¬ Img wa y → dflt y = F y) : liftFun wa wb dflt f = F := by
  funext y
  by_cases hy : Img wa y
  · obtain ⟨x, rfl⟩ := hy; rw [liftFun_apply hw, h]
  · rw [liftFun_out _ _ _ _ hy, hout y hy]

/-- Lambda terms guarded by the membership predicates of their parameters (see `guardedLambda`). -/
theorem lam_world_ite {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) {wb : B → C} {dflt : D → C} {f : A → B} {F : D → C}
    (h : ∀ x, wb (f x) = F (wa x)) :
    liftFun wa wb dflt f = fun y => @ite C (Img wa y) (Classical.propDecidable _) (F y) (dflt y) := by
  funext y
  by_cases hy : Img wa y
  · rw [if_pos hy]; obtain ⟨x, rfl⟩ := hy; rw [liftFun_apply hw, h]
  · rw [if_neg hy, liftFun_out _ _ _ _ hy]

theorem ite_world {T : Sort u} {D : Sort v} (w : T → D) {c c' : Prop} [h : Decidable c] {x y : T} {x' y' : D}
    (hc : c = c') (hx : c → w x = x') (hy : ¬ c → w y = y') :
    w (@ite T c h x y) = @ite D c' (Classical.propDecidable c') x' y' := by
  subst hc
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact hx hc
  · rw [if_neg hc, if_neg hc]; exact hy hc

/-- Case analyses (testers and selectors, see `Bridge.walkPolyCasesOn`) on lists in the world `List.map w`, with the
    world `wr` of their results. -/
theorem list_casesOn_world {A : Type u} {B : Type v} {w : A → B} {C : Sort x} {C' : Sort y} (wr : C → C')
    {d : List A} {D : List B} (hd : List.map w d = D) {n : C} {n' : C'} {c : A → List A → C}
    {c' : B → List B → C'} (hn : d = [] → wr n = n') (hc : ∀ h t, d = h :: t → wr (c h t) = c' (w h) (List.map w t)) :
    wr (@List.casesOn A (fun _ => C) d n c) = @List.casesOn B (fun _ => C') D n' c' := by
  subst hd
  cases d with
  | nil => exact hn rfl
  | cons h t => exact hc h t rfl

theorem option_casesOn_world {A : Type u} {B : Type v} {w : A → B} {C : Sort x} {C' : Sort y} (wr : C → C')
    {d : Option A} {D : Option B} (hd : Option.map w d = D) {n : C} {n' : C'} {c : A → C} {c' : B → C'}
    (hn : d = none → wr n = n') (hc : ∀ v, d = some v → wr (c v) = c' (w v)) :
    wr (@Option.casesOn A (fun _ => C) d n c) = @Option.casesOn B (fun _ => C') D n' c' := by
  subst hd
  cases d with
  | none => exact hn rfl
  | some v => exact hc v rfl

/-! ## Axioms of the encoding -/

theorem img_liftFun {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) {wb : B → C} {dflt : D → C} {F : D → C} {y : D}
    (hF : Img (liftFun wa wb dflt) F) (hy : Img wa y) : Img wb (F y) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨x, rfl⟩ := hy
  rw [liftFun_apply hw]; exact ⟨f x, rfl⟩

theorem ext_liftFun {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} {wb : B → C} {dflt : D → C} {F G : D → C}
    (hF : Img (liftFun wa wb dflt) F) (hG : Img (liftFun wa wb dflt) G) (h : ∀ y, Img wa y → F y = G y) : F = G := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  funext y
  by_cases hy : Img wa y
  · exact h y hy
  · rw [liftFun_out _ _ _ _ hy, liftFun_out _ _ _ _ hy]

theorem ext_liftFun₂ {A₁ : Sort a₁} {A₂ : Sort a₂} {B : Sort b} {D₁ : Sort d₁} {D₂ : Sort d₂} {C : Sort c}
    {w₁ : A₁ → D₁} (hw₁ : Function.Injective w₁) {w₂ : A₂ → D₂} {wb : B → C} {dflt₁ : D₁ → D₂ → C}
    {dflt₂ : D₂ → C} {F G : D₁ → D₂ → C}
    (hF : Img (liftFun w₁ (liftFun w₂ wb dflt₂) dflt₁) F) (hG : Img (liftFun w₁ (liftFun w₂ wb dflt₂) dflt₁) G)
    (h : ∀ y₁ y₂, Img w₁ y₁ → Img w₂ y₂ → F y₁ y₂ = G y₁ y₂) : F = G := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  funext y₁
  by_cases hy₁ : Img w₁ y₁
  · obtain ⟨x₁, rfl⟩ := hy₁
    rw [liftFun_apply hw₁, liftFun_apply hw₁]
    funext y₂
    by_cases hy₂ : Img w₂ y₂
    · have := h (w₁ x₁) y₂ ⟨x₁, rfl⟩ hy₂
      rwa [liftFun_apply hw₁, liftFun_apply hw₁] at this
    · rw [liftFun_out _ _ _ _ hy₂, liftFun_out _ _ _ _ hy₂]
  · rw [liftFun_out _ _ _ _ hy₁, liftFun_out _ _ _ _ hy₁]

theorem img_liftFun₂ {A₁ : Sort a₁} {A₂ : Sort a₂} {B : Sort b} {D₁ : Sort d₁} {D₂ : Sort d₂} {C : Sort c}
    {w₁ : A₁ → D₁} (hw₁ : Function.Injective w₁) {w₂ : A₂ → D₂} (hw₂ : Function.Injective w₂) {wb : B → C}
    {dflt₁ : D₁ → D₂ → C} {dflt₂ : D₂ → C} {F : D₁ → D₂ → C} {y₁ : D₁} {y₂ : D₂}
    (hF : Img (liftFun w₁ (liftFun w₂ wb dflt₂) dflt₁) F) (hy₁ : Img w₁ y₁) (hy₂ : Img w₂ y₂) : Img wb (F y₁ y₂) :=
  img_liftFun hw₂ (img_liftFun hw₁ hF hy₁) hy₂

theorem img_id {T : Sort u} {D : Sort v} {w : T → D} (hw : Function.Injective w) :
    Img (liftFun w w (fun x => x)) (fun x => x) :=
  ⟨fun x => x, (lam_world hw (fun _ => rfl) (fun _ _ => rfl)).symm⟩

/-- Membership of the lambda terms guarded by the membership predicates of their parameters (see
    `guardedLambda`). -/
theorem img_lam_ite {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) {wb : B → C} {dflt : D → C} {F : D → C}
    (h : ∀ y, Img wa y → Img wb (F y)) :
    Img (liftFun wa wb dflt) (fun y => @ite C (Img wa y) (Classical.propDecidable _) (F y) (dflt y)) :=
  ⟨fun x => Classical.choose (h (wa x) ⟨x, rfl⟩),
    (lam_world_ite hw fun x => (Classical.choose_spec (h (wa x) ⟨x, rfl⟩)).symm).symm⟩

syntax (name := blasterPoly) "blaster_poly" : tactic

/-- Proofs of the axioms of the encoding on the interpretation (e.g., the co-domain constraints and the
    extensionality of the functions of the encoding, the membership of the declared constants). -/
@[tactic blasterPoly] def evalBlasterPoly : Tactic := fun _ => do
  evalTactic (← `(tactic| intros))
  let attempts : Array (TSyntax `tactic) := #[
    ← `(tactic| exact img_self _ _),
    ← `(tactic| exact img_id (inj_injective _)),
    ← `(tactic| (apply ext_liftFun <;> assumption)),
    ← `(tactic| (apply ext_liftFun₂ (inj_injective _) <;> assumption)),
    ← `(tactic| (subst_vars; rfl)),
    ← `(tactic| (apply img_liftFun₂ (inj_injective _) (inj_injective _) <;> assumption)),
    ← `(tactic| (apply img_liftFun (inj_injective _) <;> assumption))]
  for t in attempts do
    let s ← saveState
    try
      evalTactic t
      if (← getGoals).isEmpty then return
    catch _ => pure ()
    s.restore
  -- membership hypotheses on variables: the variables are substituted by their witnesses
  for _ in [0:16] do
    let h? ← withMainContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if t.isAppOfArity ``Img 4 && t.appArg!.isFVar && !t.appFn!.containsFVar t.appArg!.fvarId! then
          return some d.toExpr
      return none
    let some h := h? | break
    let hs ← withMainContext <| Term.exprToSyntax h
    -- NOTE: `rfl` patterns are not recognized in quotations (hygiene)
    evalTactic (← `(tactic| (obtain ⟨_, h⟩ := $hs; subst h)))
  evalTactic (← `(tactic| (simp only [liftFun_apply, inj_injective, listMap_injective, optionMap_injective,
    id_injective, natCast_injective, boolTrue_injective, img_self] <;> first | done | omega | rfl | simp_all | grind)))

/-! ## Worlds -/

/-- A default value of `t` (inhabited types and functions to inhabited types). -/
partial def mkDefault (t : Expr) : MetaM Expr := do
  let t ← whnfR t
  if let .forallE n d b bi := t then
    if !b.hasLooseBVars then
      return mkLambda n bi d (← mkDefault b)
  let u ← getLevel t
  try
    let inst ← synthInstance (mkApp (mkConst ``Inhabited [u]) t)
    return mkApp2 (mkConst ``Inhabited.default [u]) t inst
  catch _ =>
    let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) t)
    return mkApp2 (mkConst ``Classical.ofNonempty [u]) t inst

/-- The universe level `u` of `Univ.{u}`. -/
def univLevel? (t : Expr) : Option Level :=
  match t with
  | .const ``Univ [u] => some u
  | _ => none

/-- Whether `t` is (or contains) the universe of the interpretation. -/
def hasUniv (t : Expr) : Bool := (t.find? fun s => s.isConstOf ``Univ).isSome

/-- The world of the Lean values of type `t` interpreted with type `d`, with a proof of its injectivity: `none` when
    `t` and `d` are the same type (worlds `Nat → Int` and `Bool → Prop` only occur below the type constructors, as
    in `α → Nat`; they are handled by the bridge otherwise). The construction is syntactic, such that the worlds
    of the interpretation (e.g., of the membership predicates) and of the bridge coincide. -/
partial def mkWorld (t d : Expr) : MetaM (Option (Expr × Expr)) := do
  if !hasUniv d then return none
  go t d
where
  same (t d : Expr) : MetaM Bool := do
    if t == d then return true
    withReducible (isDefEq t d)
  /-- the world of `t`, `@id t` when `t` is interpreted as itself -/
  goId (t d : Expr) : MetaM (Option (Expr × Expr)) := do
    if ← same t d then
      let u ← getLevel t
      return some (mkApp (mkConst ``id [u]) t, mkApp (mkConst ``id_injective [u]) t)
    go t d
  go (t d : Expr) : MetaM (Option (Expr × Expr)) := do
    if ← same t d then return none
    if let some u := univLevel? d then
      if ← isDefEq (← inferType t) (mkSort u) then
        return some (mkApp (mkConst ``inj [u]) t, mkApp (mkConst ``inj_injective [u]) t)
      return none
    let t' ← whnfR t
    let d' ← whnfR d
    if t'.isConstOf ``Nat && d'.isConstOf ``Int then
      return some (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt),
                   mkConst ``natCast_injective)
    if t'.isConstOf ``Bool && d'.isProp then
      return some (mkLambda `b .default (mkConst ``Bool)
          (mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) (.bvar 0) (mkConst ``Bool.true)),
        mkConst ``boolTrue_injective)
    match t', d' with
    | .forallE _ a b _, .forallE _ da c _ =>
        if b.hasLooseBVars || c.hasLooseBVars then return none
        let some (wa, ha) ← goId a da | return none
        let some (wb, hb) ← goId b c | return none
        -- outside of the domain: the identity for the functions of a sort into itself (e.g., `fun x => x`
        -- for the lambda terms of the encoding), a default value otherwise
        let dflt ← if (← same da c) then pure (mkLambda `x .default da (.bvar 0))
          else pure (mkLambda `x .default da (← mkDefault c))
        let w ← mkAppM ``liftFun #[wa, wb, dflt]
        let h ← mkAppM ``liftFun_injective #[ha, hb, dflt]
        return some (w, h)
    | _, _ => pure ()
    let functor (n : Name) (map : Name) (lem : Name) : MetaM (Option (Expr × Expr)) := do
      if !(t'.isAppOfArity n 1 && d'.isAppOfArity n 1) then return none
      let some (w, h) ← go t'.appArg! d'.appArg! | return none
      return some (← mkAppM map #[w], ← mkAppM lem #[h])
    if let some r ← functor ``List ``List.map ``listMap_injective then return some r
    if let some r ← functor ``Option ``Option.map ``optionMap_injective then return some r
    if t'.isAppOfArity ``Prod 2 && d'.isAppOfArity ``Prod 2 then
      let some (w₁, h₁) ← goId (t'.getArg! 0) (d'.getArg! 0) | return none
      let some (w₂, h₂) ← goId (t'.getArg! 1) (d'.getArg! 1) | return none
      return some (← mkAppM ``Prod.map #[w₁, w₂], ← mkAppM ``prodMap_injective #[h₁, h₂])
    return none

/-- `w x`, β-reduced. -/
def applyWorld (w x : Expr) : Expr := (mkApp w x).headBeta

/-! ## Polymorphic functions

The Lean functions of the translation instantiated at sort variables (e.g., `@List.zipWith α β γ`) are translated as
SMT functions on `@Instance`, shared by all the instantiations at the sort variables of a universe. They are
interpreted at the universe (e.g., `@List.zipWith Univ Univ Univ`), such that their definitional axioms hold on all
the values of the universe (outside of the images of the worlds too). Their applications in the goal are related to
their interpretations by *naturality* lemmas proved once per function and instantiation (see `blaster_poly_nat` and
`Bridge.walkPolyApp`), e.g., `List.zipWith (liftFun (inj α) (liftFun (inj β) (inj γ) _) _ f) (List.map (inj α) xs)
(List.map (inj β) ys) = List.map (inj γ) (List.zipWith f xs ys)`.

NOTE: naturality only holds for parametric functions (e.g., not for axioms such as `hash : α → String`). -/

/-- Number of generic parameters of the Lean function `e` of the translation (abstracted over its generic parameters,
    see `Blaster.Optimize.getInstApp`), given the arity of its SMT function: the leading parameters that are not
    arguments of the SMT function. -/
def genericParams (e : Expr) (arity : Nat) : MetaM Nat :=
  lambdaTelescope e fun ps b => do
    let explicit ← forallTelescope (← inferType b) fun xs _ =>
      xs.filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    return ps.size + explicit.size - arity

/-- `e` with fresh universe level metavariables for the levels of its constants and of its sorts (except `Prop`),
    and the original levels. -/
def freshLevels (e : Expr) : StateT (Array (LMVarId × Level)) MetaM Expr :=
  Core.transform e (pre := fun s => do
    let fresh (l : Level) : StateT (Array (LMVarId × Level)) MetaM Level := do
      let m ← mkFreshLevelMVar
      modify (·.push (m.mvarId!, l))
      return m
    match s with
    | .const n ls => return .done (.const n (← ls.mapM fresh))
    | .sort l => if l.isZero then return .done s else return .done (.sort (← fresh l))
    | _ => return .continue)

/-- The Lean function `e` of the translation at the universe: its first `n` (generic) parameters are instantiated with
    `Univ.{u}` for the sort parameters of `Sort u`, and with synthesized instances for the instance parameters (`e`
    itself when an instance can't be synthesized, e.g., `BEq Univ`). The universe levels of the instance are inferred
    by type checking (e.g., `@List.zipWith.{u+1} Univ.{u+1}` for `@List.zipWith.{u} α` with `α : Type u`), the
    original levels otherwise. -/
def instantiateUniv (e : Expr) (n : Nat) : MetaM Expr := do
  let e := e.headBeta
  let mut binders := #[]
  let mut body := e
  for _ in [:n] do
    let .lam _ t b _ := body | break
    binders := binders.push t
    body := b
  if binders.isEmpty then return e
  try
    let (r, origs) ← (do
      let body ← freshLevels body
      let mut vals := #[]
      for t in binders do
        let t := t.instantiateRev vals
        if let .sort u := ← whnfR t then
          if u.isZero then throwError "instantiateUniv: proposition"
          vals := vals.push (mkConst ``Univ [u])
        else
          let t ← freshLevels t
          Meta.check t
          vals := vals.push (← synthInstance (← instantiateMVars t))
      let r := body.instantiateRev vals
      Meta.check r
      return r : StateT (Array (LMVarId × Level)) MetaM Expr).run #[]
    for (m, l) in origs do
      if !(← isLevelMVarAssigned m) then assignLevelMVar m l
    let r ← instantiateMVars r
    Meta.check r
    return r.headBeta
  catch _ => return e

/-- Simplification of the naturality statements (see `blaster_poly_nat`). -/
macro "blaster_poly_simp" : tactic => `(tactic| simp_all [liftFun_apply, inj_injective, liftFun_injective,
  listMap_injective, optionMap_injective, prodMap_injective, id_injective, natCast_injective, boolTrue_injective])

/-- One level of case analysis on the variables `fvs` of `g`. -/
partial def casesVars (g : MVarId) (fvs : List FVarId) : MetaM (List MVarId) := do
  match fvs with
  | [] => return [g]
  | fv :: rest =>
      if !(← g.withContext do return (← getLCtx).contains fv) then return ← casesVars g rest
      let sgs ← try g.cases fv catch _ => return ← casesVars g rest
      let mut acc := []
      for sg in sgs do
        let rest' := rest.map fun f => match sg.subst.get f with | .fvar f' => f' | _ => f
        acc := acc ++ (← casesVars sg.mvarId rest')
      return acc

syntax (name := blasterPolyCases) "blaster_poly_cases" : tactic

/-- One level of case analysis on the variables of datatypes (e.g., in the catch-all cases of a functional
    induction, whose hypotheses exclude the other patterns). -/
@[tactic blasterPolyCases] def evalBlasterPolyCases : Tactic := fun _ => do
  let g ← getMainGoal
  let fvs ← g.withContext do
    let mut acc := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR d.type
      let .const n _ := ty.getAppFn | continue
      if (← isProp ty) || (← isClass? ty).isSome then continue
      let some (.inductInfo info) := (← getEnv).find? n | continue
      if info.numIndices != 0 then continue
      acc := acc.push d.fvarId
    return acc
  replaceMainGoal (← casesVars g fvs.toList)

syntax (name := blasterPolyNat) "blaster_poly_nat" : tactic

/-- Proofs of the naturality statements `∀ αs xs, f Univ (W xs) = W (f αs xs)` (see `Bridge.walkPolyApp`): functional
    induction on `f αs xs` (the right-hand side), and simplification with the lemmas on the worlds. -/
@[tactic blasterPolyNat] def evalBlasterPolyNat : Tactic := fun _ => do
  evalTactic (← `(tactic| intros))
  let (app, f) ← withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let some (_, lhs, rhs) := t.eq? | throwError "blaster_poly_nat: equation expected"
    let some f := lhs.getAppFn.constName? | throwError "blaster_poly_nat: application expected"
    let some app := rhs.find? (·.isAppOf f) | throwError "blaster_poly_nat: application expected"
    return (app, f)
  let stx ← withMainContext (Term.exprToSyntax app)
  let fId := mkIdent f
  let attempts : Array (TSyntax `tactic) := #[
    ← `(tactic| (fun_induction $stx <;> blaster_poly_simp)),
    ← `(tactic| (fun_induction $stx <;> (try blaster_poly_simp) <;> blaster_poly_cases <;> blaster_poly_simp)),
    ← `(tactic| (fun_induction $stx <;> (try simp_all [$fId:ident]) <;> (try blaster_poly_cases) <;> blaster_poly_simp)),
    ← `(tactic| blaster_poly_simp)]
  for t in attempts do
    let s ← saveState
    try
      evalTactic t
      if (← getGoals).isEmpty then return
    catch _ => pure ()
    s.restore
  throwError "blaster_poly_nat: failed"

end Blaster.Reconstruct.SmtProof.Poly
