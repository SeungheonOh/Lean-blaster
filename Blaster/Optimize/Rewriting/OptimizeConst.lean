import Lean
import Blaster.Optimize.Rewriting.OptimizeApp

open Lean Meta Elab Blaster.Reconstruct

namespace Blaster.Optimize

/-- Perform the following normalization on `l`
    - When `l := .param .. ∨ l := .mvar ..`
       - return `.succ .zero`
    - When `l := .succ l'`
        - return .succ (normLevel l')
    - Otherwise
        - return `l`
-/
@[always_inline, inline]
partial def normLevel (l : Level) : Level :=
 match l with
 | .param ..
 | .mvar .. => .succ .zero
 | .succ l' => .succ (normLevel l')
 | _ => l

/-- Given `e := Expr.const n l, apply the following normalization rule:
     - When `n := Nat.zero` return `Expr.lit (Literal.natVal 0)`

     - When `n := Nat.pred`
         - return `λ n => n - 1`

     - When `n := Nat.succ`
         - return `λ n => 1 + n`

     - When `n := Nat.le`
         - return `mkNatLeOp`

     - When `n := Nat.ble` ∧ (← isOptimizeRecCall):
         - return `λ x y => decide' (x ≤ y)`

     - When `n := Nat.beq` ∧ (← isOptimizeRecCall):
         - return `λ x y => x == y`

     - When `n := Int.negSucc ∧ ¬ (← isInFunApp)`
         - return `λ n => Int.neg (Int.ofNat (1 + n))`

     - When `n := Int.le`
         - return `mkIntLeOp`

     - When `n := ite`
         - return `λ (α : Sort u) (p : Prop) [h : Decidable p] (t e : α) =>
                     Blaster.dite' α p (fun _ => t) (fun _ => e)`

     - When `n := dite`
         - return `λ (α : Sort u) (p : Prop) [h : Decidable p] (t : p → α) (e : ¬ p → α) =>
                     Blaster.dite' α p t e`

     - When `n := Decidable.decide`
         - return `λ (p : Prop) [h : Decidable p] => Blaster.decide' p`

     - When `¬ (← isInFunApp):
         - When `¬ hasImplicitArgs e`:
             - When `isRecursiveFun n` (i.e., a recursive function passed as argument):
                 - return `(← normOpaqueAndRecFun e #[] optimizer)`
             - When `(← getFunBody e).isSome ∧ ¬ isRecursiveFun n ∧ ¬ isNotFoldable e`:
                 - return `optimizer (← getFunBody e)`

     - When `(← isInFunApp) ∧ ¬ isNotFoldable e ∧ ¬ hasImplicitArgs e ∧ (← getFunBody e).isSome`:
          - return `← getFunBody e`

     - Otherwise:
         - When `isResolvebleType e` :
             - return `mkExpr (← resolveTypeAbbrev e)`
         - Otherwise
             - return `mkExpr e`
-/
def normConst (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
  match e with
  | Expr.const n l =>
       withLocalContext $ do
         match n with
         | ``Nat.zero => stackContinuity stack (← mkNatLitExpr 0) (← defEqStep)
         | _ =>
           if (← isPartialDef n) then throwEnvError "normConst: partial function not supported {n} !!!"
           if (← isUnsafeDef n) then throwEnvError "normConst: unsafe definition not supported {n} !!!"
           if let some r ← isToNormOpaqueFun n then return r
           -- NOTE: universe levels are not normalized when tracking proof terms (see `Expr.sort` case)
           let e' := if (← isTracking) then e else normConstLevel n l
           -- NOTE: level normalization is not an equivalence preserving rewrite when `l` contains level parameters.
           let pf ← normLevelStep e'
           if let some r ← isHOF n e' pf then return r
           if (← isResolvableType e')
           then
             -- NOTE: type abbreviation resolution is a definitional step.
             let (e', pf) ← mkExprPf (← resolveTypeAbbrev e') pf
             stackContinuity stack e' pf
           else
             let (e', pf) ← mkExprPf e' pf
             stackContinuity stack e' pf

  | _ => throwEnvError "normConst: name expression expected but got {reprStr e}"

  where
    /-- Normalizing level in Expr.const due to normalization perform on sort (see normSort in Basic) -/
    @[always_inline, inline]
    normConstLevel (n : Name) (xs : List Level) : Expr :=
      Expr.const n (xs.map normLevel)

    @[always_inline, inline]
    normLevelStep (e' : Expr) : TranslateEnvT EqPf := do
      if !(← isTracking) then return .unknown
      clearSteps
      ruleStep e e' "normLevel"

    /-- Return evidence for rewriting `e` to `r` with an optional justification lemma `thm`. -/
    @[always_inline, inline]
    constStep (r : Expr) (label : String) (thm : Option Expr := none) : TranslateEnvT EqPf := do
      if !(← isTracking) then return .unknown
      clearSteps
      if let some p := thm then recordStep e r p
      ruleStep e r label

    /-- Same as `stackContinuity` but with evidence for rewriting `e` to `r`. -/
    @[always_inline, inline]
    constContinuity (r : Expr) (label : String) (thm : Option Expr := none)
      (skipCache := false) : TranslateEnvT OptimizeContinuity := do
      stackContinuity stack r (← constStep r label thm) skipCache

    /-- Apply the following normalization rules on opaque functions:
         - Nat.pred ==> λ n => n - 1
         - Nat.succ ==> λ n => 1 + n
         - Nat.le ==> ≤
         - Nat.ble ==> λ x y => Blaster.decide' (x ≤ y) (if isOptimizeRecCall)
         - Nat.beq ==> λ x y => x == y (if isOptimizeRecCall)
         - Int.negSucc ==> λ n => Int.neg (Int.ofNat (1 + n)) (if ¬ isInFunApp)
         - Int.le ==> ≤
         - ite ==> λ (α : Sort u) (p : Prop) [h : Decidable p] (t e : α) => Blaster.dite' α p (fun _ => t) (fun _ => e)
         - dite ==> λ (α : Sort u) (p : Prop) [h : Decidable p] (t : p → α) (e : ¬ p → α) => Blaster.dite' α p t e
         - Decidable.decide ==> λ (p : Prop) [h : Decidable p] => Blaster.decide' p
    -/
    @[always_inline, inline]
    isToNormOpaqueFun (n : Name) : TranslateEnvT (Option OptimizeContinuity) := do
     match n with
     | ``Nat.pred =>
           let body ← mkExpr $ mkApp2 (← mkNatSubOp) (mkBVar 0) (← mkNatLitExpr 1)
           let lam := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
           constContinuity (← mkExpr lam) "Nat.pred" (some (mkConst ``Blaster.Reconstruct.nat_pred_eq))

     | ``Nat.succ =>
           let body ← mkExpr $ mkApp2 (← mkNatAddOp) (← mkNatLitExpr 1) (mkBVar 0)
           let lam := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
           constContinuity (← mkExpr lam) "Nat.succ" (some (mkConst ``Blaster.Reconstruct.nat_succ_eq))

     | ``Nat.le => stackContinuity stack (← mkNatLeOp) (← defEqStep)

     | ``Nat.ble =>
           if (← isOptimizeRecCall) then
             let leExpr ← mkExpr $ mkApp2 (← mkNatLeOp) (mkBVar 1) (mkBVar 0)
             let body ← mkExpr $ mkApp (← mkBlasterDecideConst) leExpr
             let lam1 ← mkExpr $ mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
             let lam2 := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) lam1
             constContinuity (← mkExpr lam2) "Nat.ble" (some (mkConst ``Blaster.Reconstruct.nat_ble_eq))
           else stackContinuity stack (skipCache := true) e .defeq -- don't catch

     | ``Nat.beq =>
           if (← isOptimizeRecCall) then
             let body ← mkExpr $ mkApp2 (← mkNatBEqOp) (mkBVar 1) (mkBVar 0)
             let lam1 ← mkExpr $ mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
             let lam2 := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) lam1
             constContinuity (← mkExpr lam2) "Nat.beq" (some (mkConst ``Blaster.Reconstruct.nat_beq_eq))
           else stackContinuity stack (skipCache := true) e .defeq -- don't catch

     | ``Int.negSucc =>
             if !(← isInFunApp) then
               let addExpr ← mkExpr $ mkApp2 (← mkNatAddOp) (← mkNatLitExpr 1) (mkBVar 0)
               let intExpr ← mkExpr $ mkApp (← mkIntOfNat) addExpr
               let body ← mkExpr $ mkApp (← mkIntNegOp) intExpr
               let lam := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
               constContinuity (skipCache := true) (← mkExpr lam) "Int.negSucc"
                 (some (mkConst ``Blaster.Reconstruct.int_negSucc_eq)) -- don't catch
             else stackContinuity stack (skipCache := true) e .defeq -- don't catch

     | ``Int.le => stackContinuity stack (← mkIntLeOp) (← defEqStep)

     | ``ite =>
          let hName ← Term.mkFreshBinderName
          forallTelescope (← inferTypeEnv e) fun xs _ => do
            let thenExpr ← mkExpr $ mkLambda hName BinderInfo.default xs[1]! xs[3]!
            let notCond ← mkExpr $ mkApp (← mkPropNotOp) xs[1]!
            let elseExpr ← mkExpr $ mkLambda hName BinderInfo.default notCond xs[4]!
            let appExpr ← mkExpr $ mkApp4 (← mkBlasterDIteOp) xs[0]! xs[1]! thenExpr elseExpr
            let lam ← mkLambdaFVars xs appExpr
            constContinuity (← mkExpr lam) "ite" (some (mkConst ``Blaster.ite_to_dite'_equiv e.constLevels!))

     | ``dite =>
         forallTelescope (← inferTypeEnv e) fun xs _ => do
           let appExpr ← mkExpr $ mkApp4 (← mkBlasterDIteOp) xs[0]! xs[1]! xs[3]! xs[4]!
           let lam ← mkLambdaFVars xs appExpr
           constContinuity (← mkExpr lam) "dite" (some (mkConst ``Blaster.dite_equiv e.constLevels!))

     | ``Decidable.decide =>
          forallTelescope (← inferTypeEnv e) fun xs _ => do
            let appExpr ← mkExpr $ mkApp (← mkBlasterDecideConst) xs[0]!
            let lam ← mkLambdaFVars xs appExpr
            constContinuity (← mkExpr lam) "decide" (some (mkConst ``Blaster.decide'_equiv))

     | _ => return none

    @[always_inline, inline]
    isHOF (f : Name) (e : Expr) (pf : EqPf) : TranslateEnvT (Option OptimizeContinuity) := do
      if (← isInFunApp) then
        if (← hasImplicitArgs e) then return none
        if (← isNotFoldable e #[]) then return none
        if let some fbody ← getFunBody e then
          -- NOTE: unfolding a non-recursive definition is a definitional step.
          stackContinuity stack (skipCache := true) fbody pf -- don't catch
        else return none
      else
        if (← hasImplicitArgs e) then return none
        if (← isRecursiveFun f) then
          return (some $ Sum.inl $ .InitOpaqueRecExpr e #[] pf :: stack)
        if (← isNotFoldable e #[]) then return none
        -- non recursive function case
        if let some fbody ← getFunBody e then
          -- NOTE: unfolding a non-recursive definition is a definitional step.
          return (some $ Sum.inl $ (← pushTrans fbody pf stack))
        else return none

end Blaster.Optimize
