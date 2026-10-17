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
partial def optimizeExprAux (stack : List OptimizeStack) : TranslateEnvT Expr := do
  match stack with
  | .InitOptimizeExpr e mvarDecls :: xs =>
      match (← isInOptimizeEnvCache e xs mvarDecls) with
      | Sum.inl i_stack =>
          -- trace[Optimize.expr] "optimizing {← ppExpr e}"
          match e with
          | Expr.fvar _ =>
              match (← normFVar e i_stack) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.mvar _ =>
              optimizeExprAux (.InitOptimizeExpr (← getMVarValue e) :: i_stack)

          | Expr.sort l =>
              -- sort is used for Type u, Prop, etc
              -- NOTE: universe levels are only normalized for the SMT translation, i.e., not when
              -- tracking proof terms (the normalization is not an equivalence preserving rewrite).
              let s' ← if (← isTracking) then pure e else mkExpr (Expr.sort (← normLevel l))
              match (← stackContinuity i_stack s' .defeq) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.lit .. => -- number or string literal
              match (← stackContinuity i_stack e .defeq) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.const .. =>
              match (← normConst e i_stack) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.forallE n t b bi =>
              match ← reuseContext? e 0 with
              | some reuse =>
                   let x := reuse.fvars[0]!
                   setAndCommitCtx reuse.scope
                   let body ← instantiateShared1 b x
                   -- NOTE: contexts are never reused when tracking proof terms (see `reuseContext?`)
                   optimizeExprAux (.InitOptimizeExpr body :: .ForallWaitForBody x t (some reuse.scope) true t .unknown body none :: i_stack)

              | none => optimizeExprAux (.InitOptimizeExpr t :: .ForallWaitForType n bi b t :: i_stack)

          | Expr.app f a =>
             let f ← if f.isMVar then getMVarValue f else pure f
             let (f, ras) := getAppFnWithArgs (mkApp f a)
             -- check if f is a lambda term
             if f.isLambda then
               -- perform beta reduction and apply optimization
               let betaRes ← betaLambdaEnv f ras
               optimizeExprAux (.InitOptimizeExpr betaRes.betaReduced betaRes.prevMVarIdDecls :: i_stack)
             else
               -- set inFunApp flag before optimizing `f`
               setInFunApp true
               let i_stack' := .AppWaitForConst ras :: i_stack
               optimizeExprAux (.InitOptimizeExpr f :: i_stack')

          | Expr.lam n t b bi =>
               if ← isPropEnv t then
                 -- skip proof term
                 match (← stackContinuity (.LambdaWaitForType n bi b t :: i_stack) t .defeq) with
                 | Sum.inl stack' => optimizeExprAux stack'
                 | _ => throwEnvError "optimizeExprAux: continuity expected for LambdaWaitForType !!!"
               else optimizeExprAux (.InitOptimizeExpr t :: .LambdaWaitForType n bi b t :: i_stack)

          | Expr.letE _n _t v b _ =>
              -- NOTE: when tracking proof terms, let expressions are zeta-reduced with their original value,
              -- i.e., substituting the optimized value may yield ill-typed terms (e.g., `Decidable` instances
              -- of the original value).
              if (← isTracking) then optimizeExprAux (.InitOptimizeExpr (← hashcons (b.instantiate1 v)) :: i_stack)
              else optimizeExprAux (inlineLet v b i_stack) -- inline let expression

          | Expr.mdata d me =>
              if (isTaggedRecursiveCall e) then
                setNormalizeFunCall false
                optimizeExprAux (.InitOptimizeExpr me :: .MDataRecCallWaitForExpr d :: i_stack)
              else optimizeExprAux (.InitOptimizeExpr me :: i_stack)

          | Expr.proj n idx s =>
              let i_stack' := .ProjWaitForExpr n idx :: i_stack
              optimizeExprAux (.InitOptimizeExpr s :: i_stack')

          | Expr.bvar .. => throwEnvError "optimizeExpr: unexpected bound variable {e}"

      | Sum.inr (Sum.inr e') => return e'
      | Sum.inr (Sum.inl stack') => optimizeExprAux stack'

  | .RecFunDefStorage uargs instApp subsInst params optDef startCtxId appExpr :: xs =>
        uncacheFunName instApp
        -- clean-up rewrite cache
        freeRewriteCacheRange startCtxId (← get).optEnv.options.nextCtxId
        -- trace[Optimize.recFun] "optimized rec body for {reprStr subsInst} got {reprStr optDef}"
        let fn' ← storeRecFunDef subsInst params optDef
        -- keep track of the established equivalence for proof reconstruction
        if (← isTracking) && !(exprEq fn' subsInst) && !fn'.hasFVar && !subsInst.hasFVar then
          modify fun env => { env with recon.recFunEquivs := env.recon.recFunEquivs.push (subsInst, fn') }
        -- trace[Optimize.recFun] "rec function instance {reprStr subsInst} is equivalent to {reprStr fn'}"
        match (← finalizeRecApp subsInst fn' uargs params xs (lhs? := some appExpr)) with
        | Sum.inr e => return e
        | Sum.inl stack' => optimizeExprAux stack'

  | .InitNonFunOptimizeArgs f args idx stopIdx pf :: xs =>
         -- try to apply funPropagation to avoid optimizing ite/match multiple times
         clearSteps
         if let some r ← funPropagation? f args (resolveArgs := true) (← isAppArg) then
           optimizeExprAux (← pushRuleFrame (← mkAppNExpr f args) r "funPropagation" pf xs)
         else
           let prevInCtor ← isCtorArg
           setIsCtorArg (← isCtorExpr f)
           optimizeExprAux (.NonFunOptimizeArgs f args idx stopIdx prevInCtor pf :: xs)

  | .NonFunOptimizeArgs f args idx stopIdx prevInCtor pf :: xs =>
        if idx ≥ stopIdx then
          -- restore previous isCtorArg flag
          setIsCtorArg prevInCtor
          match (← finalizeNonFunApp f args xs pf) with
          | Sum.inr e' => return e'
          | Sum.inl stack' => optimizeExprAux stack'
        -- NOTE: proof arguments are not optimized when tracking proof terms
        else if ← isTracking <&&> isProofArg f idx then
          optimizeExprAux (.NonFunOptimizeArgs f args (idx + 1) stopIdx prevInCtor pf :: xs)
        else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | .AppOptimizeImplicitArgs f args idx startIdx stopIdx pInfo prevInApp pf :: xs =>
       if idx ≥ stopIdx then
         -- normalizing ite/match function application first to
         -- avoid handling extra args in optimizeDITEChoice, matchReduction and funPropagation
         clearSteps
         if let some re ← normChoiceApplication? f args prevInApp then
           -- trace[Optimize.normChoiceApp] "normalizing choice application {reprStr f} {reprStr args} => {reprStr re}"
           optimizeExprAux (← pushRuleFrame (← mkAppNExpr f args) re "normChoiceApplication" pf xs)
         else if isBlasterDiteConst f && args.size ≥ 2 then
           -- applying choice reduction to avoid optimizing unreachable arguments in Blaster.dite'
           setIsAppArg true
           let condOpt := .InitOptimizeExpr args[1]!
           optimizeExprAux (condOpt :: .DiteChoiceWaitForCond f args pInfo prevInApp pf :: xs)
         else if let some mInfo ← isMatcher? f then
            -- try match reduction rule first to avoid unnecessary optimization on discriminators
            clearSteps
            if let some r ← matchReduction? f args mInfo (resolveArgs := true) prevInApp then
              optimizeExprAux (← pushRuleFrame (← mkAppNExpr f args) r "matchReduction" pf xs)
            else
              -- applying choice reduction and match constant propagation to
              -- avoid optimizing unreachable rhs in match
              -- only optimizing match return type and discriminators first
              setIsAppArg true
              optimizeExprAux (.MatchChoiceOptimizeDiscrs f args pInfo (mInfo.getFirstDiscrPos - 1) mInfo prevInApp pf :: xs)
         -- try to apply funPropagation to avoid optimizing ite/match multiple times
         else if let some r ← (do clearSteps; funPropagation? f args (reorderArgs := true) (resolveArgs := true) prevInApp) then
           optimizeExprAux (← pushRuleFrame (← mkAppNExpr f args) r "funPropagation" pf xs)
         -- apply optimization on remaining explicit parameters before reduction
         else optimizeExprAux (.AppOptimizeExplicitArgs f args startIdx args.size pInfo none prevInApp pf :: xs)

       else if idx < pInfo.paramsInfo.size -- handle case when HOF is the returned type
            then if !pInfo.paramsInfo[idx]!.isExplicit && !(← skipProofArg f pInfo idx)
                 then optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)
                 else optimizeExprAux (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo prevInApp pf :: xs)
            else optimizeExprAux (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo prevInApp pf :: xs)

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp pf :: xs =>
       if idx ≥ stopIdx then
         -- restore previous isAppArg flag
         setIsAppArg prevInApp
         -- resolve pending congruence on dependent arguments (if any)
         let pf ← withLocalContext $ resolveDepArgs f args pf
         -- cast proof arguments whose type is no longer the expected one (only when tracking proofs)
         let args ← castProofArgs f args pInfo
         -- apply match normalization rules
         if let some argInfo := mInfo then
           match (← optimizeMatch f args argInfo (← pushPf pf (← mkAppNExpr f args) xs)) with
           | Sum.inr e' => return e'
           | Sum.inl stack' => optimizeExprAux stack'
         -- apply ite normalization rules only when fully applied
         else if isBlasterDiteConst f && args.size == 4 then
           match (← optimizeIfThenElse? f args xs pf) with
           | Sum.inr e' => return e'
           | Sum.inl stack' => optimizeExprAux stack'
         -- unfold non-recursive and non-opaque functions
         -- NOTE: beta reduction performed by getUnfoldFunDef? when rf is a lambda term
         -- NOTE: we can only unfold once all parameters have been optimized.
         else if let some fdef ← getUnfoldFunDef? f args then
           -- trace[Optimize.unfoldDef] "unfolding function definition {reprStr f} {reprStr args} => {reprStr fdef}"
           -- NOTE: unfolding a non-recursive definition is a definitional step (delta + beta).
           optimizeExprAux (← pushTrans fdef.betaReduced pf xs fdef.prevMVarIdDecls)
         -- normalizing partially apply function after unfolding non-opaque functions
         else if let some pe ← normPartialFun? f args then
           -- trace[Optimize.normPartial] "normalizing partial function {reprStr f} {reprStr args} => {reprStr pe}"
           -- NOTE: eta expansion is a definitional step.
           optimizeExprAux (← pushTrans pe pf xs)
         -- applying optimization on opaque rec function and app and proceed with fun propagation rules
         else
           match (← optimizeApp f args (← pushPf pf (← mkAppNExpr f args) xs)) with
           | Sum.inr e' => return e'
           | Sum.inl stack' => optimizeExprAux stack'
       else if idx < pInfo.paramsInfo.size
            then if pInfo.paramsInfo[idx]!.isExplicit && !(← skipProofArg f pInfo idx)
                 then optimizeExprAux (← optimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp pf stack xs)
                 else optimizeExprAux (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo prevInApp pf :: xs)
            else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | .MatchChoiceOptimizeDiscrs f args pInfo idx mInfo prevInApp pf :: xs =>
        if idx ≥ mInfo.getFirstAltPos then
          -- restore prevous isAppArg flag
          setIsAppArg prevInApp
          clearSteps
          if let some r ← matchReduction? f args mInfo (matchToIte := true) prevInApp then
            optimizeExprAux (← pushRuleFrame (← mkAppNExpr f args) r "matchReduction" pf xs)
          else
            -- apply optimization on remaining explicit parameters before reduction
            -- keep matchInfo to avoid unnecessary query and to avoid optimizing discriminators again
            optimizeExprAux (.AppOptimizeExplicitArgs f args mInfo.getFirstAltPos args.size pInfo mInfo prevInApp pf :: xs)
        else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | .MatchRhsLambdaNext next :: xs =>
      match next with
      | Expr.lam n t b bi =>
          optimizeExprAux (.MatchLhsSkipForallType t :: .MatchRhsLambdaWaitForType n bi b :: xs)
      | _ =>
         -- header on xs is expected to be .MatchRhsLambdaWaitForBody
         match (← stackContinuity xs next) with
         | Sum.inl stack' => optimizeExprAux stack'
         | _ => throwEnvError "optimizeExprAux: continuity expected for MatchRhsLambdaNext !!!"

  | .MatchLhsSkipForallType e :: xs =>
      match e with
      | Expr.forallE n t b bi =>
          let stack' ←
            withLocalDecl' n bi t fun x => do
              pure $ .MatchLhsSkipForallType (← instantiateShared1 b x) :: .MatchLhsForallWaitForBody x :: xs
          optimizeExprAux stack'
      | _ => optimizeExprAux (.InitOptimizeExpr e :: xs) -- optimize lhs body

  | _ => throwEnvError "optimizeExprAux: unexpected optimize stack continuity {reprStr stack} !!!"

  where
    @[always_inline, inline]
    finalizeNonFunApp (f : Expr) (args : Array Expr) (stack : List OptimizeStack) (pf : EqPf) :
      TranslateEnvT OptimizeContinuity := do
      if ← isCtorExpr f
      then optimizeConstApp f args (← pushPf pf (← mkAppNExpr f args) stack)
      else stackContinuity stack (← mkAppNExpr f args) pf

    /-- Return `true` if the `idx`-th argument of `f` is a proof. -/
    @[always_inline, inline]
    isProofArg (f : Expr) (idx : Nat) : TranslateEnvT Bool := do
      try
        let pInfo ← getFunEnvInfo f
        if h : idx < pInfo.paramsInfo.size then return pInfo.paramsInfo[idx].isProp
        return false
      catch _ => return false

    /-- Return `true` only when tracking proof terms and the `idx`-th argument of `f` is a proof
        that is not handled by the match normalization rules.
    -/
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
        args := args.set! j (← hashcons (mkApp4 (mkConst ``Blaster.Reconstruct.castProof) actual expected hEq args[j]!))
      return args

    /-- Given `e := Expr.fVar fv` perform the following:
         - When `some v := fv.getValue?`
             - return `Sum.inl (.InitOptimizeExpr v :: stack)`
         - Otherwise:
             - return `stackContinuity stack (← mkExpr e)`
    -/
    @[always_inline, inline]
    normFVar (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
      match ← e.fvarId!.getEnvValue? with
      | none => stackContinuity stack e .defeq
      | some v => return Sum.inl (.InitOptimizeExpr (← hashcons v) :: stack)

    @[always_inline, inline]
    inlineLet (v : Expr) (body : Expr) (stack : List OptimizeStack) : List OptimizeStack :=
      (.InitOptimizeExpr v :: .LetWaitForValue body :: stack)

    /-- Return a proof of `c' = c` (resp. `¬ c' = ¬ c`) for the then (resp. else) branch of a `dite'` whose
        condition `c` has been rewritten to `c'`.
        NOTE: the evidence may contain proof obligations (e.g., a rewrite justified by a hypothesis),
        which are discharged with the other ones. Otherwise, the branch body would be ill-typed.
    -/
    branchCast? (isThen : Bool) (pf : EqPf) : TranslateEnvT (Option Expr) := do
      let .depArgs _ pargs := pf | return none
      let some (_, _, .proof pc) := pargs.find? (·.1 == 1) | return none
      tryInLocalContext do
        let h ← mkEqSymm pc
        if isThen then return h else mkCongrArg (mkConst ``Not) h

    /-- Optimize `Blaster.dite'` branch `e` w.r.t. the optimized condition `cond`.
        NOTE: When tracking proof terms, the branch binder type must respectively be `c` and `¬ c` for the
        then and else branch. When the condition has been rewritten, the body is instantiated with a cast
        from the new binder type to the original one (see `LambdaWaitForType`).
    -/
    @[always_inline, inline]
    optimizeDiteArg (e : Expr) (cond : Expr) (isThen : Bool) (pf : EqPf) (stack : List OptimizeStack) :
      TranslateEnvT (List OptimizeStack) := do
      match e with
      | Expr.lam n t b bi =>
           let mkCond (c : Expr) : TranslateEnvT Expr := do
             if isThen then return c
             else mkAppExpr (← mkPropNotOp) c
           match ← reuseContext? e 0 with
           | some reuse =>
               let x := reuse.fvars[0]!
               setAndCommitCtx reuse.scope
               let body ← instantiateShared1 b x
               return .InitOptimizeExpr body :: .LambdaWaitForBody x (some reuse.scope) true 0 .unknown body t false :: stack
           | none =>
               let t' ← mkCond cond
               -- cast from the new binder type `t'` to the original one `t` (when tracking proof terms)
               let castEq? ← do
                 if !(← isTracking) || exprEq t t' || !b.hasLooseBVars then pure none
                 -- NOTE: no cast needed when the binder types are definitionally equal
                 else if ← sameDomain t' t then pure none
                 else if let some h ← branchCast? isThen pf then pure (some h)
                 else boolNegCast? t' t
               withLocalDecl' n bi t' fun x => do
                 let body ← match castEq? with
                   | some h => pure (b.instantiate1 (mkApp4 (mkConst ``Blaster.Reconstruct.castProof) t' t h x))
                   | none => instantiateShared1 b x
                 let bodyOpt := .InitOptimizeExpr body
                 let mscope ← addHypotheses t' x
                 let pt := if exprEq t t' then EqPf.defeq else EqPf.unknown
                 return bodyOpt :: .LambdaWaitForBody x mscope true 0 pt body t castEq?.isSome :: stack
      | Expr.mvar _ => optimizeDiteArg (← getMVarValue e) cond isThen pf stack
      | _ => return .InitOptimizeExpr e :: stack

    @[always_inline, inline]
    optimizeExplicitArgs
     (f : Expr) (args : Array Expr) (idx : Nat) (_stopIdx : Nat)
     (_pInfo : FunEnvInfo) (mInfo : Option MatchInfo) (_prevInApp : Bool) (pf : EqPf)
     (stack : List OptimizeStack) (_nxtStack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := do
      let currArg := args[idx]!
      if isBlasterDiteConst f then
         -- NOTE: optimization on Blaster.dite' cond already performed at this stage
         -- and idx starts as from 2 (see continuation for DiteChoiceWaitForCond)
        if idx == 2 || idx == 3 then
          optimizeDiteArg currArg args[1]! (idx == 2) pf stack
        else return (.InitOptimizeExpr currArg :: stack)
      else if let some argInfo := mInfo then
         -- NOTE: optimization on discriminators already performed at this stage
         -- and idx starts as from getFirstDiscrPos (see continuation for MatchChoiceOptimizeDiscrs).
         if idx >= argInfo.getFirstAltPos && idx < argInfo.arity then
           optimizeMatchAlt args argInfo idx currArg stack
         else return (.InitOptimizeExpr currArg :: stack)
      else return (.InitOptimizeExpr currArg :: stack)

@[always_inline, inline]
def optimizeExpr (e : Expr) : TranslateEnvT Expr :=
  optimizeExprAux [.InitOptimizeExpr e]

/-- Populate the `recFunInstCache` with opaque recursive function definition.
    This function need to be call before performing optimization on a lean expression.
    NOTE: This function need to be updated each time we are opacifying a new recursive function.
-/
def cacheOpaqueRecFun : TranslateEnvT Unit := do
  let commonExpr := (← get).optEnv.memCache.commonExpr
  callOptimize commonExpr.natAdd
  callOptimize commonExpr.natSub
  callOptimize commonExpr.natMul
  callOptimize commonExpr.natBle
  callOptimize commonExpr.natBeq
  callOptimize commonExpr.natPow
  callOptimize commonExpr.intPow

 where
   callOptimize (e : Expr) (params := #[]) : TranslateEnvT Unit := do
     match ← normRecFun e params e [] with
     | Sum.inr _ => return ()
     | Sum.inl stack' => discard $ optimizeExprAux stack'


/-- Perform the following actions:
      - populate the recFunInstCache with default recursive function definitions.
      - optimize expression `e`
-/
def Optimize.mainAux (e : Expr) (applyHashCons := true) : TranslateEnvT Expr := do
  -- populate recFunInstCache with recursive function definition.
  cacheOpaqueRecFun
  -- hash cons expression before optimization
  if applyHashCons
  then optimizeExpr (← hashcons e)
  else optimizeExpr e

/-- Same as `Optimize.mainAux` but also sets the start local context and returns the evidence that
    `e` is equal to the optimized expression.
    NOTE: Proof terms are only tracked when `track` is set (by default, when proof reconstruction is activated,
    see option `reconstruct`). Otherwise, `EqPf.unknown` is returned.
-/
def Optimize.mainPf (e : Expr) (track : Option Bool := none) (applyHashCons := true) :
  TranslateEnvT (Expr × EqPf) := do
  -- set start local context
  updateLocalContext (← mkLocalContext)
  -- populate recFunInstCache with recursive function definition.
  setTracking false
  cacheOpaqueRecFun
  -- track proof terms only for the expression to be optimized
  let track := track.getD ((← get).optEnv.options.solverOptions.reconstruct > 0)
  setTracking track
  modify fun env => { env with recon.resultPf := .unknown }
  let e ← if applyHashCons then hashcons e else pure e
  let r ← optimizeExpr e
  let resPf := (← get).recon.resultPf
  let pf := if track then resPf else .unknown
  setTracking false
  return (r, pf)

/-- Same as mainAux but set localContext -/
def Optimize.main (e : Expr) (applyHashCons := true) : TranslateEnvT Expr := do
  -- set start local context
  updateLocalContext (← mkLocalContext)
  Optimize.mainAux e applyHashCons

/-- Same as `command` but also returns the evidence that `e` is equal to the optimized expression
    (see option `reconstruct`).
-/
def commandPf (sOpts: BlasterOptions) (e : Expr) : MetaM ((Expr × EqPf) × TranslateEnv) := do
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  Optimize.mainPf e |>.run env

/-- Optimize an expression using the given solver options.
    ### Parameters
      - `sOpts`: The solver options to use for optimization.
      - `expr`: The expression to be optimized.
    ### Returns
      - A tuple containing the optimized expression and the optimization environment.
    NOTE: This function is to be used only by callOptimize in package Test.
-/
def command (sOpts: BlasterOptions) (e : Expr) : MetaM (Expr × TranslateEnv) := do
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let res ← Optimize.main e|>.run env
  return res


initialize
  registerTraceClass `Optimize.expr
  registerTraceClass `Optimize.funPropagation
  registerTraceClass `Optimize.normChoiceApp
  registerTraceClass `Optimize.normPartial
  registerTraceClass `Optimize.reduceApp
  registerTraceClass `Optimize.unfoldDef

end Blaster.Optimize
