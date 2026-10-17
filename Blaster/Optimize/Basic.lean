import Lean
import Lean.Util.MonadCache
import Blaster.Command.Options
import Blaster.Logging
import Blaster.Optimize.Rewriting.FunPropagation
import Blaster.Optimize.Rewriting.OptimizeApp
import Blaster.Optimize.Rewriting.OptimizeConst
import Blaster.Optimize.Rewriting.OptimizeForAll

open Lean Elab Command Term Meta Blaster.Options Blaster.Reconstruct

namespace Blaster.Optimize


-- TODO: update formalization with inference rule style notation.
-- NOTE: Each rewrite performed by the optimizer is accompanied with evidence that the
-- rewritten expression is equal to the original one (see `Blaster.Reconstruct`).
partial def optimizeExprAux (stack : List OptimizeStack) : TranslateEnvT (Expr × EqPf) := do
  match stack with
  | .InitOptimizeExpr e :: xs =>
      match (← isInOptimizeEnvCache e xs) with
      | Sum.inl i_stack =>
          -- trace[Optimize.expr] "optimizing {← ppExpr e}"
          match e with
          | Expr.fvar _ =>
              match (← normFVar e i_stack) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.sort l =>
              -- sort is used for Type u, Prop, etc
              -- NOTE: universe levels are only normalized for the SMT translation, i.e., not when
              -- tracking proof terms (the normalization is not an equivalence preserving rewrite).
              let s := if (← isTracking) then e else Expr.sort (normLevel l)
              clearSteps
              let (s', pf) ← mkExprPf s (← ruleStep e s "normLevel")
              match (← stackContinuity i_stack s' pf) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.lit .. => -- number or string literal
              let (e', pf) ← mkExprPf e .defeq
              match (← stackContinuity i_stack e' pf) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.const .. =>
              match (← normConst e i_stack) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.forallE n t b bi =>
              optimizeExprAux (.InitOptimizeExpr t :: .ForallWaitForType n bi t b :: i_stack)

          | Expr.app .. =>
             let (f, ras) := getAppFnWithArgs e
             -- check if f is a lambda term
             if f.isLambda then
               -- perform beta reduction and apply optimization
               optimizeExprAux (.InitOptimizeExpr (betaLambda f ras) :: i_stack)
             else
               -- set inFunApp flag before optimizing `f`
               setInFunApp true
               let i_stack' := .AppWaitForConst ras :: i_stack
               optimizeExprAux (.InitOptimizeExpr f :: i_stack')

          | Expr.lam n t b bi => optimizeExprAux (optimizeLambda n t b bi i_stack)

          | Expr.letE n t v b _ =>
              -- NOTE: when tracking proof terms, let expressions are zeta-reduced with their original value,
              -- i.e., substituting the optimized value may yield ill-typed terms (e.g., `Decidable` instances
              -- of the original value).
              if (← isTracking) then optimizeExprAux (.InitOptimizeExpr (b.instantiate1 v) :: i_stack)
              else optimizeExprAux (inlineLet n t v b i_stack) -- inline let expression

          | Expr.mdata d me =>
              if (isTaggedRecursiveCall e) then
                setNormalizeFunCall false
                optimizeExprAux (.InitOptimizeExpr me :: .MDataRecCallWaitForExpr d :: i_stack)
              else optimizeExprAux (.InitOptimizeExpr me :: i_stack)

          | Expr.proj n idx s =>
              let i_stack' := .ProjWaitForExpr n idx :: i_stack
              optimizeExprAux (.InitOptimizeExpr s :: i_stack')

          | Expr.mvar .. => throwEnvError "optimizeExpr: unexpected meta variable {e}"
          | Expr.bvar .. => throwEnvError "optimizeExpr: unexpected bound variable {e}"

      | Sum.inr (Sum.inr e') => return e'
      | Sum.inr (Sum.inl stack') => optimizeExprAux stack'

  | s@(.InitOpaqueRecExpr ..) :: xs
  | s@(.RecFunDefStorage ..) :: xs =>
        match (← normOpaqueAndRecFun s xs) with
        | Sum.inr e => return e
        | Sum.inl stack' => optimizeExprAux stack'

  | .AppOptimizeImplicitArgs f args idx startIdx stopIdx pInfo pf :: xs =>
       if idx ≥ stopIdx then
         if isBlasterDiteConst f && args.size ≥ 2 then
           -- applying choice reduction to avoid optimizing unreachable arguments in Blaster.dite'
           let condOpt := .InitOptimizeExpr args[1]!
           optimizeExprAux (condOpt :: .DiteChoiceWaitForCond f args pInfo startIdx pf :: xs)
         else if let some mInfo ← isMatcher? f then
            -- try match reduction rule first to avoid unnecessary optimization on discriminators
            clearSteps
            if let some r ← matchReduction? f args mInfo then
              optimizeExprAux (← pushRuleStep f args r "matchReduction" pf xs)
            else
              -- applying choice reduction and match constant propagation to
              -- avoid optimizing unreachable rhs in match
              -- only optimizing match discriminators first
              optimizeExprAux (.MatchChoiceOptimizeDiscrs f args pInfo startIdx mInfo.getFirstDiscrPos mInfo pf :: xs)
         -- try to apply funPropagation to avoid optimizing ite/match multiple times
         else if let some r ← (do clearSteps; funPropagation? f args (reorderArgs := true)) then
           optimizeExprAux (← pushRuleStep f args r "funPropagation" pf xs)
         -- apply optimization on remaining explicit parameters before reduction
         else optimizeExprAux (.AppOptimizeExplicitArgs f args startIdx args.size pInfo none pf :: xs)

       else if idx < pInfo.paramsInfo.size -- handle case when HOF is the returned type
            then if !pInfo.paramsInfo[idx]!.isExplicit && !(← skipProofArg f pInfo idx)
                 then optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)
                 else optimizeExprAux (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo pf :: xs)
            else optimizeExprAux (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo pf :: xs)

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo pf :: xs =>
       if idx ≥ stopIdx then
         -- resolve pending congruence on dependent arguments (if any)
         let pf ← withLocalContext $ resolveDepArgs f args pf
         -- cast proof arguments whose type is no longer the expected one (only when tracking proofs)
         let args ← castProofArgs f args pInfo
         clearSteps
         -- normalizing ite/match function application
         if let some re ← normChoiceApplication? f args then
           -- trace[Optimize.normChoiceApp] "normalizing choice application {reprStr f} {reprStr args} => {reprStr re}"
           optimizeExprAux (← pushRuleStep f args re "normChoiceApplication" pf xs)
         -- apply match normalization rules
         else if let some argInfo := mInfo then
           match (← optimizeMatch f args argInfo xs pf) with
           | Sum.inr e' => return e'
           | Sum.inl stack' => optimizeExprAux stack'
         -- apply ite normalization rules only when fully applied
         else if isBlasterDiteConst f && args.size == 4 then
           match (← optimizeIfThenElse? f args xs pf) with
           | Sum.inr e' => return e'
           | Sum.inl stack' => optimizeExprAux stack'
         -- try to reduce app if all params are constructors
         else if let some re ← reduceApp? f args then
           -- trace[Optimize.reduceApp] "application reduction {reprStr f} {reprStr args} => {reprStr re}"
           optimizeExprAux (← pushRuleStep f args re "reduceApp" pf xs)
         -- unfold non-recursive and non-opaque functions
         -- NOTE: beta reduction performed by getUnfoldFunDef? when rf is a lambda term
         -- NOTE: we can only unfold once all parameters have been optimized.
         else if let some fdef ← getUnfoldFunDef? f args then
           -- trace[Optimize.unfoldDef] "unfolding function definition {reprStr f} {reprStr args} => {reprStr fdef}"
           -- NOTE: unfolding a non-recursive definition is a definitional step (delta + beta).
           optimizeExprAux (← pushTrans fdef (← pf.trans (← defEqStep)) xs)
         -- normalizing partially apply function after unfolding non-opaque functions
         else if let some pe ← normPartialFun? f args then
           -- trace[Optimize.normPartial] "normalizing partial function {reprStr f} {reprStr args} => {reprStr pe}"
           -- NOTE: eta expansion is a definitional step.
           optimizeExprAux (← pushTrans pe (← pf.trans (← defEqStep)) xs)
         -- applying optimization on opaque rec function and app and proceed with fun propagation rules
         else optimizeExprAux (.InitOpaqueRecExpr f args pf :: xs)
       else if idx < pInfo.paramsInfo.size
            then if pInfo.paramsInfo[idx]!.isExplicit
                 then optimizeExprAux (← optimizeExplicitArgs f args idx stopIdx pInfo mInfo pf stack xs)
                 else optimizeExprAux (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo pf :: xs)
            else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | .MatchChoiceOptimizeDiscrs f args pInfo startArgIdx idx mInfo pf :: xs =>
        if idx ≥ mInfo.getFirstAltPos then
          clearSteps
          if let some r ← matchReduction? f args mInfo then
            optimizeExprAux (← pushRuleStep f args r "matchReduction" pf xs)
          else
            -- apply optimization on remaining explicit parameters before reduction
            -- keep matchInfo to avoid unnecessary query and to avoid optimizing discriminators again
            optimizeExprAux (.AppOptimizeExplicitArgs f args startArgIdx args.size pInfo mInfo pf :: xs)
        else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | .MatchRhsLambdaNext next :: xs =>
      match next with
      | Expr.lam n t b bi =>
          optimizeExprAux (.InitOptimizeExpr t :: .MatchRhsLambdaWaitForType n bi b :: xs)
      | _ =>
         -- header on xs is expected to be .MatchRhsLambdaWaitForBody
         match (← stackContinuity xs next .unknown) with
         | Sum.inl stack' => optimizeExprAux stack'
         | _ => throwEnvError "optimizeExprAux: continuity expected for MatchRhsLambdaNext !!!"

  | _ => throwEnvError "optimizeExprAux: unexpected optimize stack continuity {reprStr stack} !!!"

  where

    /-- Return `true` when the argument at position `idx` is a proof that must not be optimized, i.e.,
        only when tracking proof terms. Rewriting inside proofs is useless (proof irrelevance) and may
        produce ill-typed proofs (e.g., when a proposition in an implicit argument is rewritten
        but not the instances depending on it).
    -/
    @[always_inline, inline]
    skipProofArg (f : Expr) (pInfo : FunEnvInfo) (idx : Nat) : TranslateEnvT Bool := do
      if h : idx < pInfo.paramsInfo.size then
        if pInfo.paramsInfo[idx].isProp then
          if !(← isTracking) then return false
          -- NOTE: match/casesOn arguments are handled by the match normalization rules
          if (← isMatcher? f).isSome then return false
          if let .const n _ := f then
            if isCasesOnRecursor (← getEnv) n || (← isMatchExpr f) then return false
          return true
      return false

    /-- When tracking proof terms, cast each proof argument of `f x₁ ... xₙ` whose type is not the expected
        one (i.e., because the data it refers to has been rewritten), using `Blaster.Reconstruct.castProof`.
        NOTE: By proof irrelevance, the evidence for the application is not affected.
    -/
    castProofArgs (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) : TranslateEnvT (Array Expr) := do
      if !(← isTracking) then return args
      let mut args := args
      for h : j in [:min args.size pInfo.paramsInfo.size] do
        if !pInfo.paramsInfo[j]!.isProp then continue
        -- NOTE: proof variables are left unchanged (e.g., pattern variables in match alternatives)
        if args[j]!.isFVar then continue
        let some (actual, expected) ← tryInLocalContext (do
            let .forallE _ d _ _ ← whnfD (← inferType (mkAppN f (args.extract 0 j))) | throwError "unexpected"
            return (← instantiateMVars (← inferType args[j]!), d))
          | continue
        if actual == expected then continue
        if (← sameDomain actual expected) then continue
        let some hEq ← withLocalContext (cachedEqProof actual expected) | continue
        args := args.set! j (mkApp4 (mkConst ``Blaster.Reconstruct.castProof) actual expected hEq args[j]!)
      return args

    /-- Given `pf : lhs = f x₁ ... xₙ` and `r` the result of applying a rewriting rule on
        `f x₁ ... xₙ`, push `r` on the stack to be optimized while keeping track of the evidence for `lhs = r`.
    -/
    @[always_inline, inline]
    pushRuleStep
      (f : Expr) (args : Array Expr) (r : Expr) (label : String)
      (pf : EqPf) (stack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := do
      if !(← isTracking) then return .InitOptimizeExpr r :: stack
      let step ← withLocalContext $ ruleStep (mkAppN f args) r label
      pushTrans r (← pf.trans step) stack

    /-- Given `e := Expr.fVar fv` perform the following:
         - When `some v := fv.getValue?`
             `return `Sum.inl (.InitOptimizeExpr v :: stack)`
         - Otherwise:
              `return `stackContinuity stack (← mkExpr e)`
    -/
    @[always_inline, inline]
    normFVar (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity :=
      withLocalContext $ do
        match ← e.fvarId!.getValue? with
        | none =>
            let (e', pf) ← mkExprPf e .defeq
            stackContinuity stack e' pf
        | some v =>
            return Sum.inl (.InitOptimizeExpr (← instantiateMVars v) :: stack)

    /-- Given a function `f := Expr const n l` perform the following:
         - When `n := mInfo ∈ isMatcherCache` (i.e., match info already optimized)
             - return `none`
         - When let some mInfo ← getMatcherRecInfo? n l (i.e., f's generic instance not optimized)
             - return `some $ Sum.inr (mInfo, matchFun)`
         - Otherwise `none`
    -/
    @[always_inline, inline]
    hasUnOptMatchInfo? (f : Expr) : TranslateEnvT (Option (MatcherRecInfo × Expr)) := do
      if (← isMatcher? f).isSome then return none -- already optimized
      else if let Expr.const n l := f then
        if let some mInfo ← getMatcherRecInfo? n l then
          let cInfo ← getConstEnvInfo n
          let matchFun ← instantiateValueLevelParams cInfo l
          return some (mInfo, matchFun)
        else return none
      else return none

    @[always_inline, inline]
    inlineLet (n : Name) (t : Expr) (v : Expr) (body : Expr) (stack : List OptimizeStack) : List OptimizeStack :=
      (.InitOptimizeExpr v :: .LetWaitForValue n t body :: stack)

    @[always_inline, inline]
    optimizeLambda
      (n : Name) (t : Expr) (b : Expr) (bi : BinderInfo)
      (xs : List OptimizeStack) (inDite := false) (declType : Option (Expr × Option Expr) := none) :
      List OptimizeStack :=
        .InitOptimizeExpr t :: .LambdaWaitForType n bi b inDite t declType :: xs

    /-- Optimize `Blaster.dite'` branch `e` with `branchType` the expected binder type,
        i.e., `c` (resp. `¬ c`) for the then (resp. else) branch, with `c` the optimized condition.
        NOTE: `branchType` is only considered when tracking proof terms (see `LambdaWaitForType`).
    -/
    @[always_inline, inline]
    optimizeDiteArg (e : Expr) (branchType : TranslateEnvT Expr) (isThen : Bool) (pf : EqPf)
      (stack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := do
      match e with
      | Expr.lam n t b bi =>
          if !(← isTracking) then return optimizeLambda n t b bi stack (inDite := true)
          let τ ← branchType
          return optimizeLambda n t b bi stack (inDite := true) (declType := some (τ, ← branchCast? isThen pf))
      | _ => return .InitOptimizeExpr e :: stack

    /-- Return a proof of `c' = c` (resp. `¬ c' = ¬ c`) for the then (resp. else) branch of a `dite'` whose
        condition `c` has been rewritten to `c'` (only when the evidence has no proof obligation).
    -/
    branchCast? (isThen : Bool) (pf : EqPf) : TranslateEnvT (Option Expr) := do
      let .depArgs _ pargs := pf | return none
      let some (_, _, .proof pc) := pargs.find? (·.1 == 1) | return none
      if containsHole pc then return none
      tryInLocalContext do
        let h ← mkEqSymm pc
        if isThen then return h else mkCongrArg (mkConst ``Not) h

    @[always_inline, inline]
    optimizeExplicitArgs
      (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat)
      (pInfo : FunEnvInfo) (mInfo : Option MatchInfo) (pf : EqPf) (stack : List OptimizeStack)
      (nxtStack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := withLocalContext $ do
      if ← skipProofArg f pInfo idx then
        return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo pf :: nxtStack)
      if isBlasterDiteConst f then
        if idx == 1 then
         -- skipping optimization for Blaster.dite' cond as already performed by choice reduction on dite
         return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo pf :: nxtStack)
        else if idx == 2 then optimizeDiteArg args[idx]! (pure args[1]!) true pf stack
        -- NOTE: the else branch binder type must be exactly `¬ c` when tracking proof terms, i.e., not
        -- rewritten with the global rewriting cache (see `mkExpr`).
        else if idx == 3 then
          let notCond := mkApp (← mkPropNotOp) args[1]!
          optimizeDiteArg args[idx]! (if (← isTracking) then pure notCond else mkExpr notCond) false pf stack
        else return (.InitOptimizeExpr args[idx]! :: stack)
      else if let some argInfo := mInfo then
         if idx >= argInfo.getFirstDiscrPos && idx < argInfo.getFirstAltPos then
           -- skipping optimization for discriminators as already performed by choice reduction on match
           return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo pf :: nxtStack)
         else if idx >= argInfo.getFirstAltPos && idx < argInfo.arity then
           optimizeMatchAlt f args argInfo idx args[idx]! stack
         else return (.InitOptimizeExpr args[idx]! :: stack)
      else return (.InitOptimizeExpr args[idx]! :: stack)


@[always_inline, inline]
def optimizeExpr (e : Expr) : TranslateEnvT Expr :=
  Prod.fst <$> optimizeExprAux [.InitOptimizeExpr e]

/-- Same as optimizeExpr but updates local context before optimizing expression -/
@[always_inline, inline]
def optimizeExpr' (e : Expr) : TranslateEnvT Expr := do
  -- set start local context
  updateLocalContext (← mkLocalContext)
  Prod.fst <$> optimizeExprAux [.InitOptimizeExpr e ]

/-- Populate the `recFunInstCache` with opaque recursive function definition.
    This function need to be call before performing optimization on a lean expression.
    NOTE: This function need to be updated each time we are opacifying a new recursive function.
-/
def cacheOpaqueRecFun : TranslateEnvT Unit := do
  callOptimize natAdd
  callOptimize natSub
  callOptimize natMul
  callOptimize natBle
  callOptimize natBeq
  callOptimize natPow
  callOptimize intPow

 where
   callOptimize (e : Expr) : TranslateEnvT Unit :=
     discard $ optimizeExprAux [.InitOpaqueRecExpr e #[] .unknown]

/-- Perform the following actions:
      - populate the recFunInstCache with default recursive function definitions.
      - optimize expression `e`
    Return the optimized expression `e'` together with the evidence that `e = e'`.
    NOTE: Proof terms are only tracked when proof reconstruction is activated
    (see option `reconstruct`). Otherwise, `EqPf.unknown` is returned.
-/
def Optimize.mainPf (e : Expr) (track : Option Bool := none) : TranslateEnvT (Expr × EqPf) := do
  -- set start local context
  updateLocalContext (← mkLocalContext)
  -- populate recFunInstCache with recursive function definition.
  setTracking false
  cacheOpaqueRecFun
  -- track proof terms only for the expression to be optimized
  setTracking (track.getD ((← get).optEnv.options.solverOptions.reconstruct > 0))
  let res ← optimizeExprAux [.InitOptimizeExpr e]
  setTracking false
  return res

/-- Same as `Optimize.mainPf` but only returns the optimized expression. -/
def Optimize.main (e : Expr) : TranslateEnvT Expr :=
  Prod.fst <$> Optimize.mainPf e


/-- Same as `command` but also returns the evidence that `e` is equal to the optimized expression
    (see option `reconstruct`).
-/
def commandPf (sOpts: BlasterOptions) (e : Expr) : MetaM ((Expr × EqPf) × TranslateEnv) := do
  -- keep the current name generator and restore it afterwards
  let ngen ← getNGen
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let res ← Optimize.mainPf e|>.run env
  -- restore name generator
  setNGen ngen
  return res

/-- Optimize an expression using the given solver options.
    ### Parameters
      - `sOpts`: The solver options to use for optimization.
      - `expr`: The expression to be optimized.
    ### Returns
      - A tuple containing the optimized expression and the optimization environment.
    NOTE: This function is to be used only by callOptimize in package Test.
-/
def command (sOpts: BlasterOptions) (e : Expr) : MetaM (Expr × TranslateEnv) := do
  let ((optExpr, _), env) ← commandPf sOpts e
  return (optExpr, env)


initialize
  registerTraceClass `Optimize.expr
  registerTraceClass `Optimize.funPropagation
  registerTraceClass `Optimize.normChoiceApp
  registerTraceClass `Optimize.normPartial
  registerTraceClass `Optimize.reduceApp
  registerTraceClass `Optimize.unfoldDef

end Blaster.Optimize
