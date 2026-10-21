import Lean
import Blaster.Reconstruct.Discharge
import Blaster.Reconstruct.SmtProof.Interp
import Blaster.Reconstruct.SmtProof.NlArith
import Blaster.Reconstruct.SmtProof.Poly
-- NOTE: the identifiers of tactic quotations are resolved where they are elaborated (e.g., `Bridge.tdiv_macro`)
import Blaster.Reconstruct.SmtProof.Bridge

/-!
# Tactics of the replay of SMT proofs

The tactics proving the steps of SMT proofs that are not replayed by explicit constructions (theory lemmas, rewrites,
asserted formulas that the bridge does not relate to the goal), and the portfolio running them, ordered adaptively by
their success rate per time unit.
-/

open Lean Meta Elab Term Tactic Blaster.Smt Blaster.Optimize Blaster.Options

namespace Blaster.Reconstruct.SmtProof

/-! ## Bridge tactics -/

/-- Introduce the universally quantified variables of the goal, substituting `x := ↑n` for the
    `Int` variables guarded by `0 ≤ x`. -/
macro "blaster_nat_intros" : tactic =>
  `(tactic| repeat (first | (intro x hx; obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hx; subst hn) | intro _))

syntax (name := blasterDivMod) "blaster_divmod" : tactic

/-- Facts on the `Int` divisions and modulos by non-literal divisors of the goal (for `omega`, which treats
    them as atoms): `y * (x / y) + x % y = x`, `y ≠ 0 → 0 ≤ x % y`, `0 < y → x % y < y`, `y < 0 → x % y < -y`. -/
@[tactic blasterDivMod] def evalBlasterDivMod : Tactic := fun _ => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let mut pairs : Array (Expr × Expr) := #[]
  let mut todo := #[tgt]
  for d in ← getLCtx do
    if !d.isImplementationDetail then todo := todo.push (← instantiateMVars d.type)
  let found := todo.foldl (fun acc e => acc ++ (collect e)) #[]
  for s in found do
    let p := (s.getArg! 4, s.getArg! 5)
    if !(pairs.any fun q => q.1 == p.1 && q.2 == p.2) then pairs := pairs.push p
  if pairs.isEmpty then throwError "blaster_divmod: no division"
  for (x, y) in pairs do
    let xs ← Term.exprToSyntax x
    let ys ← Term.exprToSyntax y
    evalTactic (← `(tactic| have := Int.mul_ediv_add_emod $xs $ys))
    evalTactic (← `(tactic| have : $ys ≠ 0 → 0 ≤ $xs % $ys := fun h => Int.emod_nonneg $xs h))
    evalTactic (← `(tactic| have : 0 < $ys → $xs % $ys < $ys := fun h => Int.emod_lt_of_pos $xs h))
    evalTactic (← `(tactic| have : $ys < 0 → $xs % $ys < -$ys := fun h => by
      have := Int.emod_lt_of_pos $xs (Int.neg_pos.mpr h); rwa [Int.emod_neg] at this))
where
  collect (e : Expr) : Array Expr := Id.run do
    let mut acc := #[]
    let mut stack := #[e]
    let mut seen : Std.HashSet Expr := {}
    while !stack.isEmpty do
      let s := stack.back!
      stack := stack.pop
      if seen.contains s then continue
      seen := seen.insert s
      if (s.isAppOfArity ``HDiv.hDiv 6 || s.isAppOfArity ``HMod.hMod 6) && (s.getArg! 0).isConstOf ``Int &&
          !(s.getArg! 5).isAppOfArity ``OfNat.ofNat 3 && !s.hasLooseBVars then
        acc := acc.push s
      match s with
      | .app f a => stack := stack.push f |>.push a
      | .lam _ t b _ | .forallE _ t b _ => stack := stack.push t |>.push b
      | .mdata _ b | .proj _ _ b => stack := stack.push b
      | _ => pure ()
    return acc

theorem ediv_self_of_zero_ne {a : Int} (h : ¬0 = a) : a / a = 1 := Int.ediv_self (Ne.symm h)

syntax (name := blasterDivModSimp) "blaster_divmod_simp" : tactic

/-- The `Int` divisions and modulos by non-literal divisors of the goal normalized by case analyses on the
    conditionals and the signs (e.g., Z3's rewrites of `x % (-y)` into `x % y`, of `x / x` into
    `if x = 0 then 0 / 0 else 1`, of `x % (if c then a else b)` into `if c then x % a else x % b`). -/
@[tactic blasterDivModSimp] def evalBlasterDivModSimp : Tactic := fun _ => do
  evalTactic (← `(tactic| intros))
  withMainContext do
  if (evalBlasterDivMod.collect (← instantiateMVars (← getMainTarget))).isEmpty then
    throwError "blaster_divmod_simp: no division"
  -- NOTE: without case analyses first (e.g., `x % (-1 * y) = x % y` for large conditional terms `x` and `y`)
  evalTactic (← `(tactic| first
    | (simp only [Int.neg_one_mul, Int.emod_neg, Int.ediv_neg, Int.neg_neg]; done)
    | ((repeat' split) <;> (try subst_vars) <;>
        simp_all [Int.emod_neg, Int.ediv_neg, Int.neg_one_mul, Int.ediv_self, ediv_self_of_zero_ne, Int.emod_self] <;> done)))

theorem str_lt_total (a b : String) : a < b ∨ a = b ∨ b < a := by
  by_cases h : a < b
  · exact Or.inl h
  · by_cases h' : b < a
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl (String.le_antisymm h' h))

theorem str_not_lt_empty (a : String) : ¬a < "" := fun h => List.not_lt_nil _ (String.lt_iff.mp h)

syntax (name := blasterStringOrder) "blaster_string_order" : tactic

/-- The order of strings (e.g., Z3's lemmas of the lexicographic order: irreflexivity, transitivity, totality). -/
@[tactic blasterStringOrder] def evalBlasterStringOrder : Tactic := fun _ => withMainContext do
  let isStrLt (e : Expr) : Bool := e.isAppOfArity ``LT.lt 4 && (e.getArg! 0).isConstOf ``String
  if ((← instantiateMVars (← getMainTarget)).find? isStrLt).isNone then throwError "blaster_string_order: no string order"
  evalTactic (← `(tactic| (intros; grind [String.lt_irrefl, String.lt_trans, String.lt_asymm, str_lt_total,
    str_not_lt_empty])))

syntax (name := blasterEmptyElim) "blaster_empty_elim" : tactic

/-- Close the goal with a local function `f : A₁ → ... → Aₙ → T` into an inductive type `T` without constructors
    (e.g., `Empty`), whose arguments are proved by `trivial`, `decide` or a constructor of their types (e.g.,
    `f : True → Empty`): case analysis on `f a₁ ... aₙ`. Such functions are the values of the sorts
    `@@ArrowT .. Empty` (e.g., the axioms on `@isFun f` hold vacuously). -/
@[tactic blasterEmptyElim] def evalBlasterEmptyElim : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let r ← observing? do
      let (args, _, body) ← forallMetaTelescopeReducing d.type
      if args.isEmpty then throwError "not a function"
      let .const n _ := (← whnfD body).getAppFn | throwError "not an inductive type"
      let .inductInfo info ← getConstInfo n | throwError "not an inductive type"
      unless info.ctors.isEmpty do throwError "inhabited co-domain"
      for a in args do
        let ag := a.mvarId!
        if ← ag.isAssigned then continue
        let gs ← Tactic.run ag (evalTactic (← `(tactic| first | trivial | decide |
          (constructor <;> first | trivial | decide | omega))))
        unless gs.isEmpty do throwError "argument not proved"
      let e ← instantiateMVars (mkAppN d.toExpr args)
      if e.hasExprMVar then throwError "argument not inferred"
      let (h, g') ← (← g.assert `h (← inferType e) e).intro1
      unless (← g'.cases h).isEmpty do throwError "case analysis"
    if r.isSome then
      replaceMainGoal []
      return
  throwError "blaster_empty_elim: no function into an empty type"

syntax (name := blasterCasesNat) "blaster_cases_nat" : tactic

/-- Case analysis (`0` / `n + 1`) on the local variables of type `Nat`. -/
@[tactic blasterCasesNat] def evalBlasterCasesNat : Tactic := fun _ => do
  let vars ← withMainContext do
    let mut vs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← whnfR d.type).isConstOf ``Nat then vs := vs.push d.fvarId
    return vs
  if vars.isEmpty then throwError "blaster_cases_nat: no Nat variable"
  for v in vars do
    let gs ← getGoals
    let mut gs' := #[]
    for g in gs do
      if (← g.getDecl).lctx.contains v then
        let subgoals ← g.cases v
        gs' := gs' ++ subgoals.map (·.mvarId)
      else gs' := gs'.push g
    setGoals gs'.toList

syntax (name := blasterUnfoldLhs) "blaster_unfold_lhs" : tactic

/-- Unfold once the user function at the head of the left-hand side of the equality to prove (e.g., the
    definitional axiom `f x = body[x]` of a recursive function, whose recursive calls must not be unfolded). -/
@[tactic blasterUnfoldLhs] def evalBlasterUnfoldLhs : Tactic := fun _ => withMainContext do
  let some (_, lhs, _) := (← whnfR (← instantiateMVars (← getMainTarget))).eq?
    | throwError "blaster_unfold_lhs: equality expected"
  -- NOTE: through the casts of the interpretation (e.g., `↑(f x)` for a function `f` returning `Nat`)
  let lhs := if lhs.isAppOfArity ``Nat.cast 3 then lhs.appArg! else lhs
  let .const f _ := lhs.getAppFn | throwError "blaster_unfold_lhs: application of a constant expected"
  if !isUserDefinition (← getEnv) f then throwError "blaster_unfold_lhs: {f} is not a user definition"
  evalTactic (← `(tactic| rw [$(mkIdent f):ident]))

syntax (name := blasterUnfoldNonRec) "blaster_unfold_nonrec" : tactic

/-- Unfold the non-recursive user definitions occurring in the main goal and its hypotheses (e.g., the
    functions called by a recursive function whose definitional axiom is proved). -/
@[tactic blasterUnfoldNonRec] def evalBlasterUnfoldNonRec : Tactic := fun _ => withMainContext do
  let env ← getEnv
  let mut t ← instantiateMVars (← getMainTarget)
  for d in ← getLCtx do
    if !d.isImplementationDetail then t := mkApp t (← instantiateMVars d.type)
  let mut defs := #[]
  for n in t.getUsedConstants do
    if isUserDefinition env n && !(← isInstance n) && !(← isRecursiveDefinition n) then defs := defs.push n
  if defs.isEmpty then throwError "blaster_unfold_nonrec: no definition to unfold"
  let lemmas ← defs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  evalTactic (← `(tactic| simp only [$lemmas,*] at *))

/-- Tactics proving the interpretation of asserted formulas (and conclusions of steps that can't be
    replayed) from the negated goal and the definitions of user functions. -/
def bridgeTactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("assumption", ← `(tactic| assumption)),
    -- definitions of lambda terms (β-reduction)
    ("rfl", ← `(tactic| (intros; rfl))),
    -- definitions of functions over `Nat` (see `guardNatQuantifiers`)
    ("nat def", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                              blaster_cases_nat <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_unfold_user) <;> grind))),
    -- definitions by case analysis on datatype arguments
    ("nat def cases", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_cases_nat) <;> blaster_cases_vars <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_unfold_user) <;> (try simp_all) <;> first | done | grind))),
    ("omega", ← `(tactic| (intros; omega))),
    -- Blaster's normal forms (e.g., `Nat.add x y`, `Nat.mod x y`) in the negated goal
    ("denorm+omega", ← `(tactic| (intros; blaster_denorm; omega))),
    ("simp", ← `(tactic| (intros; simp_all [Int.toNat_natCast] <;> done))),
    ("simp+omega", ← `(tactic| (intros; blaster_denorm; simp_all [Int.toNat_natCast] <;> omega))),
    -- casts of `Nat` division and modulo (Blaster's encoding: `ite (0 = y) 0 (div x y)`)
    ("casts", ← `(tactic| (intros; blaster_denorm; simp only [Int.natCast_ediv, Int.natCast_emod, Int.natCast_add, Int.natCast_mul,
                            Int.toNat_natCast, Int.ediv_zero, Int.emod_zero] at * <;> (try split) <;> (try split) <;>
                            first | omega | (simp_all; done) | grind))),
    ("grind", ← `(tactic| (intros; grind))),
    -- axioms on the values of sorts of functions into empty types (e.g., `@@ArrowT2 @True Empty`)
    ("empty elim", ← `(tactic| (intros; blaster_empty_elim))),
    -- definitional axioms of recursive functions (e.g., by well-founded recursion): one unfolding
    ("unfold lhs", ← `(tactic| (intros; blaster_unfold_lhs <;> first | rfl | grind | ((repeat' split) <;> omega)))),
    ("nat unfold lhs", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;> blaster_unfold_lhs <;>
                                   first | rfl | grind | ((repeat' split) <;> (try simp_all) <;> first | done | omega | grind)))),
    -- definitional axioms by case analysis on datatype arguments (with the non-recursive callees unfolded)
    ("nat cases unfold lhs", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                                   (try blaster_cases_vars) <;> blaster_unfold_lhs <;> (try blaster_unfold_nonrec) <;>
                                   (try simp_all) <;> (try split) <;> first | done | omega | grind))),
    ("unfold", ← `(tactic| (intros; blaster_unfold_user <;> (try simp_all [Int.toNat_natCast]) <;>
                            (try split) <;> (try split) <;> first | done | omega | grind))),
    ("cases", ← `(tactic| (intros; blaster_cases_vars <;> blaster_unfold_user <;>
                            (try simp_all [Int.toNat_natCast]) <;> first | done | omega | grind)))
  ]

/-- Tactics proving the equations of the SMT macros of Lean functions (e.g., `↑(x - y) = if x < y then 0 else x - y`). -/
def macroTactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("rfl", ← `(tactic| (intros; rfl))),
    ("split+omega", ← `(tactic| (intros; (repeat' split) <;> omega))),
    ("simp+omega", ← `(tactic| (intros; (repeat' split) <;> simp_all [Int.natCast_ediv, Int.natCast_emod] <;> omega))),
    ("simp", ← `(tactic| (intros; simp [Int.natCast_ediv, Int.natCast_emod]; done))),
    ("grind", ← `(tactic| (intros; grind))),
    -- the divisions and modulos of `Int` (see `Bridge.tdiv_macro`)
    ("int div", ← `(tactic| first | exact Bridge.tdiv_macro | exact Bridge.tmod_macro | exact Bridge.fdiv_macro |
                                      exact Bridge.fmod_macro | exact Bridge.ediv_macro | exact Bridge.emod_macro))]

theorem toNat_ediv_two (y : Int) : (y / 2).toNat = y.toNat / 2 := by omega

def stepTactics (rule : String) : TermElabM (Array (String × TSyntax `tactic)) := do
  let arith := #[
    ("omega", ← `(tactic| (intros; omega))),
    ("divmod+omega", ← `(tactic| (intros; blaster_divmod; omega))),
    ("divmod simp", ← `(tactic| blaster_divmod_simp)),
    ("propext+omega", ← `(tactic| (intros; apply propext; constructor <;> intro <;> omega))),
    ("split+omega", ← `(tactic| (intros; (repeat' split) <;> omega))),
    -- nonlinear arithmetic (fails quickly on goals without nonlinear terms)
    ("nlarith", ← `(tactic| blaster_nlarith))]
  let simp := #[
    ("rfl", ← `(tactic| (intros; rfl))),
    ("simp", ← `(tactic| (intros; simp_all <;> done))),
    -- associativity of the connectives (e.g., the flattening of n-ary connectives by Z3's rewriter)
    ("simp ac", ← `(tactic| (intros; simp_all [and_assoc, or_assoc] <;> done))),
    ("simp only", ← `(tactic| (intros; simp only [*] <;> done)))]
  let grind := #[("grind", ← `(tactic| (intros; grind))), ("string order", ← `(tactic| blaster_string_order))]
  let quant := #[
    ("forall_congr", ← `(tactic| (intro h; exact forall_congr h))),
    ("forall_imp", ← `(tactic| (intro h h' x; exact h x (h' x))))]
  let unfold := #[
    ("nat def", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_cases_nat) <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_unfold_user) <;> grind))),
    -- definitional axioms of recursive functions (e.g., by well-founded recursion): one unfolding
    ("unfold lhs", ← `(tactic| (intros; blaster_unfold_lhs <;> first | rfl | grind | ((repeat' split) <;> omega)))),
    ("nat unfold lhs", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;> blaster_unfold_lhs <;>
                                   first | rfl | grind | ((repeat' split) <;> (try simp_all) <;> first | done | omega | grind)))),
    -- definitional axioms by case analysis on datatype arguments (with the non-recursive callees unfolded)
    ("nat cases unfold lhs", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                                   (try blaster_cases_vars) <;> blaster_unfold_lhs <;> (try blaster_unfold_nonrec) <;>
                                   (try simp_all) <;> (try split) <;> first | done | omega | grind))),
    ("unfold", ← `(tactic| (intros; blaster_unfold_user <;> (try simp_all [Int.toNat_natCast]) <;> grind))),
    -- `@Nat.log2` (see `auxiliaryInterp`): one unfolding step
    ("log2", ← `(tactic| (intros; rw [Nat.log2_def] <;> (try simp only [toNat_ediv_two] at *) <;> split <;> omega)))]
  match rule with
  | "th-lemma" => return arith ++ simp ++ grind ++ unfold
  -- datatype lemmas over generalized terms (e.g., `x = C (C.0 x) ∨ ¬ is-C x`)
  | "datatype" => return #[("cases", ← `(tactic| (intros; blaster_cases_vars <;> simp_all <;> done)))] ++ simp ++ grind
  | "quant-intro" => return quant ++ simp ++ grind
  | "def-axiom" | "not-or-elim" | "and-elim" | "iff~" | "nnf-pos" | "nnf-neg" => return simp ++ grind
  | _ => return simp ++ arith ++ grind

/-- Per rule and tactic: number of successes and time spent (ms, including failed attempts), used to
    order the tactic portfolios by efficiency (adaptive, per process). -/
initialize tacticStats : IO.Ref (Std.HashMap (String × String) (Nat × Nat)) ← IO.mkRef {}

/-- Coarse shape of a goal, refining the statistics of the adaptive ordering: `arith` for (in)equalities
    and propositional combinations of linear arithmetic atoms, `nat` for universally quantified formulas
    guarded by `0 ≤ x` (definitions of `Nat` functions), `data` for formulas with constructors or case
    analyses, `other` otherwise. -/
partial def goalShape (e : Expr) : MetaM String := do
  let some kind ← go e 0 | return "other"
  return kind
where
  go (e : Expr) (depth : Nat) : MetaM (Option String) := do
    if depth > 64 then return none
    if e.isForall then
      if let .forallE _ t b _ := e then
        if (← whnfR t).isConstOf ``Int then
          if let .forallE _ g _ _ := b then
            if g.isAppOfArity ``LE.le 4 then return some "nat"
      return none
    let env ← getEnv
    let isData (s : Expr) : Bool := match s with
      | .const n _ =>
          (n.isStr && n.getString!.endsWith "casesOn") ||
          (isCtorName env n && n != ``Int.ofNat && n != ``True && n != ``False && n != ``Int.negSucc)
      | _ => false
    if (e.find? isData).isSome then return some "data"
    let arith := e.find? (fun s => s.isAppOfArity ``LE.le 4 || s.isAppOfArity ``LT.lt 4 || s.isAppOfArity ``HAdd.hAdd 6 || s.isAppOfArity ``HMul.hMul 6) |>.isSome
    return some (if arith then "arith" else "other")
  isCtorName (env : Environment) (n : Name) : Bool := (env.find? n).any (·.isCtor)

def portfolio (tacs : Array (String × TSyntax `tactic)) (goal : Expr) (rule := "") : TermElabM (Option (Expr × String)) := do
  let rule := s!"{rule}/{← goalShape goal}"
  let stats ← tacticStats.get
  -- most efficient tactics first, i.e., highest number of successes per time unit (with a prior
  -- favoring the given order)
  let score (n : String) (i : Nat) : Float :=
    let (succ, ms) := stats.getD (rule, n) (0, 0)
    (succ.toFloat + 1.0 / (i.toFloat + 1.0)) / (ms.toFloat + 50.0)
  let tacs := (tacs.zipIdx.qsort fun ((n₁, _), i₁) ((n₂, _), i₂) => score n₁ i₁ > score n₂ i₂).map (·.1)
  for (name, tac) in tacs do
    let start ← IO.monoMsNow
    let r ← proveWithTactic goal tac
    let ms := (← IO.monoMsNow) - start
    let succ := if r.isSome then 1 else 0
    tacticStats.modify fun m => let (a, b) := m.getD (rule, name) (0, 0); m.insert (rule, name) (a + succ, b + ms)
    if let some p := r then return some (p, name)
  return none

end Blaster.Reconstruct.SmtProof
