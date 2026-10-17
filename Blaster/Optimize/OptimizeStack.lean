import Lean
import Blaster.Optimize.Rewriting.OptimizeITE
import Blaster.Optimize.Rewriting.OptimizeProjection
import Blaster.Optimize.Telescope
import Blaster.Reconstruct.Proof

open Lean Meta Elab Blaster.Data.HashMap Blaster.Reconstruct

namespace Blaster.Optimize

abbrev HypsStackContext := Option CtxScope -- context scope to close on exit

instance : Repr (Option MVarIdDecls) where
  reprPrec _ _ := "<MVarIdDecls>"

/-- Continuation stack of the optimizer.
    NOTE: When tracking proof terms (see `Blaster.Reconstruct`), each frame waiting for the optimized
    form `v` of an expression `e` also receives evidence `pf : EqPf` that `e = v`. Frames that rewrite
    the expression being optimized keep track of the evidence accumulated so far in a `pf` field.
-/
inductive OptimizeStack where
 | InitOptimizeExpr (e : Expr) (mvarDecls : Option MVarIdDecls := none)
 | InitOptimizeReturn (e : Expr) (isGlobal : Bool) (mvarDecls : Option MVarIdDecls)
 | TransWith (pf : EqPf) (lhs : Expr) (forceHole : Bool)
 | RecFunDefWaitForStorage (args : Array Expr) (instApp : Expr)
                           (subsInts : Expr) (params : ImplicitParameters) (startCtxId : CtxId)
 | RecFunDefStorage (args : Array Expr) (instApp : Expr)
                    (subsInts : Expr) (params : ImplicitParameters) (optBody : Expr)
                    (startCtxId : CtxId)
 | ForallWaitForType (n : Name) (bi : BinderInfo) (body : Expr) (t : Expr)
 | ForallWaitForBody (x : Expr) (t : Expr) (hctx : HypsStackContext) (isProp : Bool)
                     (origT : Expr) (pt : EqPf) (origBody : Expr) (rawBody : Option Expr)
 | AppWaitForConst (args : Array Expr)
 | OptimizeMatchInfoWaitForInst (f : Expr) (args : Array Expr)
                                (startArgIdx : Nat) (pInfo : FunEnvInfo) (mInfo : MatcherRecInfo) (pf : EqPf)
 | AppOptimizeImplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (startArgIdx : Nat) (stopIdx : Nat)
                           (pInfo : FunEnvInfo) (prevInApp : Bool) (pf : EqPf)
 | AppOptimizeExplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (stopIdx : Nat) (pInfo : FunEnvInfo)
                           (mInfo : Option MatchInfo) (prevInApp : Bool) (pf : EqPf)
 | InitNonFunOptimizeArgs (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat) (pf : EqPf)
 | NonFunOptimizeArgs (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat) (prevInCtor : Bool) (pf : EqPf)
 | DiteChoiceWaitForCond (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (prevInApp : Bool) (pf : EqPf)
 | MatchChoiceOptimizeDiscrs (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo)
                             (idx : Nat) (mInfo : MatchInfo) (prevInApp : Bool) (pf : EqPf)
 | LambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr) (origT : Expr)
 | LambdaWaitForBody (x : Expr) (hctx : HypsStackContext) (inDite : Bool) (startCtxId : CtxId)
                     (pt : EqPf) (origBody : Expr) (origT : Expr) (casted : Bool)
 | MatchRhsLambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | MatchRhsLambdaNext (e : Expr)
 | MatchRhsLambdaWaitForBody (x : Expr)
 | MatchLhsSkipForallType (e : Expr)
 | MatchLhsForallWaitForBody (e : Expr)
 | MatchAltWaitForExpr (params : Array Expr) (hctx : HypsStackContext) (idx : USize) (matchInst : Expr)
 | LetWaitForValue (body : Expr)
 | MDataRecCallWaitForExpr (data : MData)
 | ProjWaitForExpr (n : Name) (idx : Nat)
 deriving Repr

abbrev OptimizeContinuity := Sum (List OptimizeStack) Expr

/-- Push `.InitOptimizeExpr e` on the stack such that the evidence `pf` obtained so far
    (i.e., `pf : lhs = e`) is composed with the evidence obtained when optimizing `e`.
-/
@[always_inline, inline]
def pushTrans (e : Expr) (pf : EqPf) (stack : List OptimizeStack) (mvarDecls : Option MVarIdDecls := none) :
  TranslateEnvT (List OptimizeStack) := do
  if !(← isTracking) then return .InitOptimizeExpr e mvarDecls :: stack
  return .InitOptimizeExpr e mvarDecls :: .TransWith pf e false :: stack

/-- When tracking proof terms, push `.TransWith pf lhs` on `stack` such that the evidence produced by a
    continuity (e.g., `optimizeApp`) for `lhs = e` is composed with `pf : e₀ = lhs`.
-/
@[always_inline, inline]
def pushPf (pf : EqPf) (lhs : Expr) (stack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := do
  if !(← isTracking) then return stack
  return .TransWith pf lhs false :: stack

/-- Same as `pushTrans` for a frame `s` produced by a rewriting rule applied on `lhs`, i.e., the rewrite step
    recorded by the rule (if any) is composed with `pf : e₀ = lhs` (see `ruleStep`).
    NOTE: Only frames of the form `.InitOptimizeExpr r` are justified, other frames yield proof obligations.
-/
@[always_inline, inline]
def pushRuleFrame (lhs : Expr) (s : OptimizeStack) (label : String) (pf : EqPf) (stack : List OptimizeStack) :
  TranslateEnvT (List OptimizeStack) := do
  if !(← isTracking) then return s :: stack
  match s with
  | .InitOptimizeExpr r mvarDecls =>
      let step ← ruleStep lhs r label
      pushTrans r (← pf.trans step) stack mvarDecls
  | .AppOptimizeImplicitArgs f args idx startArgIdx stopIdx pInfo prevInApp _ =>
      let step ← ruleStep lhs (← mkAppNExpr f args) label
      return .AppOptimizeImplicitArgs f args idx startArgIdx stopIdx pInfo prevInApp (← pf.trans step) :: stack
  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp _ =>
      let step ← ruleStep lhs (← mkAppNExpr f args) label
      return .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp (← pf.trans step) :: stack
  | _ => return s :: .TransWith pf lhs true :: stack

@[always_inline, inline]
def resetContext (h : HypsStackContext) : TranslateEnvT Unit := do
  match h with
  | some scope => endCtx scope
  | none => return ()


@[always_inline, inline]
def resetChoiceContext (h : HypsStackContext) (fvars : Array Expr) (lam : Expr) (idx : USize) : TranslateEnvT Unit := do
  match h with
  | some scope =>
       updateContextReuseCache lam idx ⟨scope, fvars⟩
       modifyOptEnv
         fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, ⟨s1, s2, s3, s4, _, s6, active, s7⟩, o12, o13, o14⟩ =>
             ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, ⟨s1, s2, s3, s4, scope.parent, s6, active.erase scope.current, s7⟩, o12, o13, o14⟩
  | none => return ()

def restoreMVarDecls (optDecls : Option MVarIdDecls) : TranslateEnvT Unit :=
  match optDecls with
  | none => pure ()
  | some mdecls =>
      let rec updateAssignments
        (idx : Nat) (stop : Nat) (mdecls : MVarIdDecls)
        (mAssignments : MVarAssignments) : MVarAssignments :=
        if idx ≥ stop then mAssignments
        else
          let d := mdecls[idx]!
          let mAssignments := mAssignments.insert d.mvar d.value
          updateAssignments (idx + 1) stop mdecls mAssignments
      modifyOptEnv
        fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, mAssignments⟩ =>
          let mAssignments := updateAssignments 0 mdecls.size mdecls mAssignments
          ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, mAssignments⟩

def isInEqualityMap (e : Expr) (isGlobal : Bool) : TranslateEnvT Expr := do
  if isGlobal then return e
  else
    match (← eqMapFind? e) with
    | none => return e
    | some b => return b

/-- Return a proof of `τ = origT` when `τ` and `origT` are Boolean negations of each other, i.e.,
    `(false = e) = ¬ (true = e)` or `(true = e) = ¬ (false = e)`. Otherwise `none`.
-/
def boolNegCast? (τ origT : Expr) : TranslateEnvT (Option Expr) := do
  let some arg := origT.not? | return none
  let some (_, l, e) := arg.eq? | return none
  let some (_, l', e') := τ.eq? | return none
  if !(exprEq e e') then return none
  let lemma? :=
    if l.isConstOf ``true && l'.isConstOf ``false then some ``Blaster.Reconstruct.not_true_eq_bool
    else if l.isConstOf ``false && l'.isConstOf ``true then some ``Blaster.Reconstruct.not_false_eq_bool
    else none
  let some lemma := lemma? | return none
  tryInLocalContext (mkEqSymm (mkApp (mkConst lemma) e))

/-- Return `true` if `t := (h : P) → β` with `P` a proposition. -/
def isFunOverProof (t : Expr) : TranslateEnvT Bool := do
  let .forallE _ d _ _ := t | return false
  let some r ← tryInLocalContext (isProp d) | return false
  return r

/-- Return the type with which a forall binder of type `t` (optimized to `t'` with evidence `pf`) must be
    declared, the evidence for the binder type and the (optional) cast `t' = t` for the body
    (see `ForallWaitForType`).
-/
def forallBinderType (t t' : Expr) (pf : EqPf) (body : Expr) : TranslateEnvT (Expr × EqPf × Option Expr) := do
  if !(← isTracking) || t == t' then return (t', pf, none)
  if !(← isPropEnv t) then
    -- keep the original type only for functions over proofs (i.e., with a proposition as domain),
    -- whose domain rewrite would otherwise make their applications ill-typed
    if !(← isFunOverProof t) then return (t', pf, none)
    if ← sameDomain t' t then return (t', pf, none)
    return (t, .defeq, none)
  if !body.hasLooseBVars then return (t', pf, none)
  let .proof p := pf | return (t', pf, none)
  if containsHole p then return (t', pf, none)
  let some h ← tryInLocalContext (mkEqSymm p) | return (t', pf, none)
  return (t', pf, some h)

def stackContinuity
  (stack : List OptimizeStack) (optExpr : Expr) (pf : EqPf := .unknown) (skipCache := false) :
  TranslateEnvT OptimizeContinuity := do
  match stack with
  | [] =>
      if ← isTracking then modify fun env => { env with recon.resultPf := pf }
      return Sum.inr optExpr

  | .InitOptimizeReturn e isGlobal mvarDecls :: xs =>
       let optExpr ← isInEqualityMap optExpr isGlobal
       let pf ← pf.close e optExpr
       if !skipCache then
         updateOptimizeEnvCache optExpr optExpr isGlobal
         if !e.hasMVar && !exprEq e optExpr then
           updateOptimizeEnvCache e optExpr isGlobal
           cacheProof e optExpr pf
       restoreMVarDecls mvarDecls
       match xs with
       | [] =>
           if ← isTracking then modify fun env => { env with recon.resultPf := pf }
           return Sum.inr optExpr
       | _ => stackContinuity xs optExpr pf

  | .TransWith p lhs forceHole :: xs =>
       -- optExpr corresponds to the optimized form of `lhs`, where `p : e₀ = lhs`.
       -- NOTE: a continuity providing no evidence for `lhs = optExpr` yields a proof obligation
       -- (or a definitional step when `optExpr` is `lhs`).
       let pf ← do
         if !(← isTracking) then pure EqPf.unknown
         else if forceHole || (match pf.simplify with | .unknown => true | _ => false) then
           if exprEq lhs optExpr || lhs == optExpr then pure EqPf.defeq
           else EqPf.close .unknown lhs optExpr (label := "continuity")
         else pure pf
       stackContinuity xs optExpr (← p.trans pf) skipCache

  | .RecFunDefWaitForStorage args instApp subsInst params startCtxId :: xs =>
       -- optExpr corresponds to optimized rec fun body
       -- continuity with normOpaqueAndRecFun
       -- NOTE: evidence for the optimized body is not needed to reconstruct the proof of the goal.
       return Sum.inl (.RecFunDefStorage args instApp subsInst params optExpr startCtxId :: xs)

  | .ForallWaitForType n bi body t :: xs =>
       -- optExpr corresponds to optimized forall binder type
       -- check forall reduction to avoid optimizing body
       let isProp ← isPropEnv (← mkForallExpr n bi optExpr body)
       if let some r ← forallReduction? optExpr body isProp then
         -- NOTE: the reduction is justified w.r.t. the forall with the optimized binder type
         let rpf ←
           if (← isTracking) && pf.isDefEq then do
             ruleStep (← mkForallExpr n bi optExpr body) r "forallReduction"
           else pure EqPf.unknown
         match r with
         | Expr.const ``True _ => stackContinuity xs r rpf
         | _ => return Sum.inl (← pushTrans r rpf xs)
       else
         -- continuity with optimizing forall body
         -- NOTE: When tracking proof terms, the following actions are performed to preserve type correctness:
         --  - binders that are not hypotheses (e.g., functions over proofs) keep their original type
         --    when the rewrite of their type is not definitional;
         --  - for hypotheses used in the body, the body is instantiated with a cast from the rewritten type
         --    to the original one (only when the evidence of the rewrite has no proof obligation).
         let (declT, pt, castEq?) ← forallBinderType t optExpr pf body
         withLocalDecl' n bi declT fun x => do
           let castEq? ← match castEq? with
             | some h => do if (← isPropEnv (← instantiateShared1 body x)) then pure (some h) else pure none
             | none => pure none
           let body' ← match castEq? with
             | some h => pure (body.instantiate1 (mkApp4 (mkConst ``Blaster.Reconstruct.castProof) declT t h x))
             | none => instantiateShared1 body x
           let mscope ← addHypotheses declT x (isPropBody := isProp)
           let rawBody := castEq?.map fun _ => body
           return Sum.inl ( .InitOptimizeExpr body' :: .ForallWaitForBody x declT mscope isProp t pt body' rawBody :: xs)

  | .ForallWaitForBody x t hctx isProp origT pt origBody rawBody :: xs =>
       -- optExpr corresponds to optimized forall body
       -- continuity with applying forall normalization rules.
       let (e, pf) ←
          if !(← isTracking) then
            pure (← optimizeForall x t optExpr hctx isProp, EqPf.unknown)
          else do
            let congrPf ← withLocalContext $ match rawBody with
              | some b0 => castForallCongr x origT t b0 optExpr pt pf
              | none => forallCongr x origT t origBody optExpr pt pf
            let lhs ← mkForallFVarExpr x optExpr
            clearSteps
            let e ← optimizeForall x t optExpr hctx isProp
            pure (e, ← congrPf.trans (← ruleStep lhs e "optimizeForall"))
       resetContext hctx
       if ← isRestart then
         resetRestart
         return Sum.inl (← pushTrans e pf xs)
       else -- continuity with optimizing next expression
         stackContinuity xs e pf

  | .AppWaitForConst args :: xs =>
       -- optExpr corresponds to optimized fun app
       -- reset inFunApp flag
       setInFunApp false
       let pf ← congrFunArgs pf args
       -- check if optExpr is a lambda
       if optExpr.isLambda then
         -- perform beta reduction and apply optimization
         let betaRes ← betaLambdaEnv optExpr (← resolveMVarsArgs #[] args)
         return Sum.inl (← pushTrans betaRes.betaReduced pf xs betaRes.prevMVarIdDecls)
       else
         let (rf, extraArgs) := getAppFnWithArgs optExpr
         let args ← resolveMVarsArgs extraArgs args
         let is_match ← isMatchExpr rf
         if (← isNotFun rf <&&> pure !is_match) then
            return Sum.inl (.InitNonFunOptimizeArgs rf args extraArgs.size args.size pf :: xs)
         else
           let pInfo ← getFunEnvInfo rf
           -- apply optimization on match generic instance (if necessary)
           match (← hasUnOptMatchInfo? rf) with
           | none =>
              -- continuity with optimization on implicit arguments
              let prevInApp ← isAppArg
              if !(isBlasterDiteConst rf) then setIsAppArg true
              return Sum.inl (.AppOptimizeImplicitArgs rf args extraArgs.size extraArgs.size args.size pInfo prevInApp pf :: xs)
           | some (mInfo, instApp) =>
              -- continuity with optimizing match generic instance
              -- NOTE: instApp is expected to be a lambda term
              -- NOTE: we here only want to optimize the lambda params type, which mainly
              -- correspond to the match lhs.
              match instApp with
              | Expr.lam n t b bi =>
                    let mWait := .OptimizeMatchInfoWaitForInst rf args extraArgs.size pInfo mInfo pf :: xs
                    -- NOTE: we only optimize the lhs forall body and not the types.
                    return Sum.inl (.MatchLhsSkipForallType t :: .MatchRhsLambdaWaitForType n bi b :: mWait)
              | _ => throwEnvError "stackContinuity: lambda expected for match instance but got {reprStr instApp}"


  | .OptimizeMatchInfoWaitForInst f args startArgIdx pInfo mInfo apf :: xs =>
       -- optExpr corresponds to optimized match generic instance
       -- update cache isMatcherCache
       if let Expr.const n _ := f then
         let argInfo := ({ name := n, nameExpr := f, instApp := optExpr, recInfo := mInfo } : MatchInfo)
         updateIsMatcherCache n argInfo
         -- apply optimization only on implicit parameters to remove mdata annotation
         -- we don't consider explicit parameters at this stage to avoid performing
         -- optimization on unreachable arguments
         let prevInApp ← isAppArg
         return Sum.inl (.AppOptimizeImplicitArgs f args startArgIdx startArgIdx args.size pInfo prevInApp apf :: xs)
       else throwEnvError "stackContinuity: name expression for match application but got {reprStr f} !!!"

  | .NonFunOptimizeArgs f args idx stopIdx prevInCtor apf :: xs =>
       -- optExpr corresponds to the optimized non-fun argument referenced by idx.
       -- continuity with optimizing the next implicit argument.
       -- Perform backward proof reconstruction in ctor/applied theorem (if necessary)
       -- NOTE: proof arguments are not rewritten when tracking proof terms (see `NonFunOptimizeArgs`)
       let optExpr ← if (← isTracking) then pure optExpr else normNonFunProof idx f args optExpr
       let args := args.set! idx optExpr
       let apf ← apf.trans (← congrArgAt f args idx pf)
       return Sum.inl (.NonFunOptimizeArgs f args (idx + 1) stopIdx prevInCtor apf :: xs)

  | .AppOptimizeImplicitArgs f args idx startArgIdx stopIdx pInfo prevInApp apf :: xs =>
       -- optExpr corresponds to the optimized implicit argument referenced by idx.
       -- continuity with optimizing the next implicit argument.
       let args := args.set! idx optExpr
       let apf ← apf.trans (← congrArgAt f args idx pf)
       return Sum.inl (.AppOptimizeImplicitArgs f args (idx + 1) startArgIdx stopIdx pInfo prevInApp apf :: xs)

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp apf :: xs =>
       -- optExpr corresponds to the optimized explicit argument referenced by idx.
       -- continuity with optimizing the next explicit argument.
       -- Perform backward proof reconstruction (if necessary)
       -- NOTE: proof arguments are not rewritten when tracking proof terms (see `optimizeExplicitArgs`)
       let optExpr ← if (← isTracking) then pure optExpr else normProof idx args optExpr pInfo
       let orig := args[idx]!
       let args := args.set! idx optExpr
       let apf ← addArgEvidence f args idx orig pf apf
       return Sum.inl (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo prevInApp apf :: xs)

  | .DiteChoiceWaitForCond f args pInfo prevInApp apf :: xs =>
       -- optExpr corresponds to the optimized Blaster.dite' conditional, i.e., referenced by index 1.
       -- When some r ← optimizeDiteChoice f (args.set! 1 optExpr)
       --  - continuity with optimizing `r`
       -- Otherwise
       --  - continuity with optimizing remaining explicit parameters before reduction
       -- set isAppArg to keep context for eventual constant match.
       setIsAppArg true
       let orig := args[1]!
       let args := args.set! 1 optExpr
       -- NOTE: when tracking proof terms, a dite' with a condition reduced to `True`/`False` is
       -- reduced with a proof of the original condition (instead of `True.intro`), such that the
       -- resulting expression is well-typed.
       if let some (r, rpf) ← constDiteChoice? f args orig pf apf then
         return Sum.inl (← pushTrans r rpf xs)
       let preApf := apf
       let apf ← addArgEvidence f args 1 orig pf apf
       clearSteps
       if let some r ← optimizeDITEChoice f args then
           -- swapping dependent branches requires casts to keep the result well-typed
           if let some (r', rpf) ← dependentSwap? f args orig pf preApf r then
             return Sum.inl (← pushTrans r' rpf xs)
           let step ← ruleStep (← mkAppNExpr f args) r "optimizeDITEChoice"
           return Sum.inl (← pushTrans r (← apf.trans step) xs)
       else
          return Sum.inl (.AppOptimizeExplicitArgs f args 2 args.size pInfo none prevInApp apf :: xs)

  | .MatchChoiceOptimizeDiscrs f args pInfo idx mInfo prevInApp apf :: xs =>
       -- optExpr corresponds to the optimized match discriminator referenced by idx.
       -- continuity with optimizing the next discriminator
       let args := args.set! idx optExpr
       let apf ← apf.trans (← congrArgAt f args idx pf)
       return Sum.inl (.MatchChoiceOptimizeDiscrs f args pInfo (idx + 1) mInfo prevInApp apf :: xs)

  | .LambdaWaitForType n bi body origT :: xs =>
       -- optExpr corresponds to optimized lambda type
       -- NOTE: when tracking proof terms, a lambda over a proposition whose body depends on the
       -- binder keeps its original binder type (the body may expect a proof of the original type).
       let keepOrig ←
         if body.hasLooseBVars && !(exprEq optExpr origT) && (← isTracking) then isPropEnv origT
         else pure false
       let declT := if keepOrig then origT else optExpr
       let pt := if keepOrig then EqPf.defeq else pf
       withLocalDecl' n bi declT fun x => do
         let body' ← instantiateShared1 body x
         let bodyOpt := .InitOptimizeExpr body'
         -- NOTE: keeping track of next ctxId to clean-up rewrite cache
         let nextCtxId := (← get).optEnv.options.nextCtxId
         return Sum.inl (bodyOpt :: .LambdaWaitForBody x none false nextCtxId pt body' origT false :: xs)

  | .LambdaWaitForBody x hctx inDite startCtxId pt origBody origT casted :: xs =>
       -- optExpr corresponds to optimized lambda body
       -- continuity with optimizing next expression
       let e ← mkLambdaFVarExpr x optExpr
       let pf ←
         if !(← isTracking) then pure EqPf.unknown
         else withLocalContext do
           if pt.isDefEq || (← sameDomain (← x.fvarId!.getType) origT) then funextCongr x origBody optExpr pf
           else lamBodyCongr x origBody optExpr pf (allowDep := casted)
       if inDite then
         if ← isCstIteMatch optExpr then updateCtorMatchPropCache e
         resetChoiceContext hctx #[x] e 0
         stackContinuity xs e pf
       else
         -- clean-up rewrite cache
         freeRewriteCacheRange startCtxId (← get).optEnv.options.nextCtxId
         stackContinuity xs e pf

  | .MatchRhsLambdaWaitForType n bi body :: xs =>
        -- optExpr corresponds to optimized lambda type
        -- continuity with optimizing body
        withLocalDecl' n bi optExpr fun x => do
          let bodyOpt := .MatchRhsLambdaNext (← instantiateShared1 body x)
          return Sum.inl (bodyOpt :: .MatchRhsLambdaWaitForBody x :: xs)

  | .MatchRhsLambdaWaitForBody x :: xs =>
        -- optExpr corresponds to optimized lambda body
        -- continuity with optimizing next expression
        -- NOTE: evidence for the generic match instance is not needed
        let e ← mkLambdaFVarExpr x optExpr
        stackContinuity xs e

  | .MatchAltWaitForExpr params hctx idx matchInst :: xs =>
       -- optExpr corresponds to the optimized match rhs
       -- continuity with optimizing next expression
       -- TODO: evidence for match alternatives optimized w.r.t. a match context
       let e ← mkLambdaFVarsExpr params optExpr
       if ← isCstIteMatch optExpr then updateCtorMatchPropCache e
       resetChoiceContext hctx params matchInst idx
       stackContinuity xs e

  | .MatchLhsForallWaitForBody x :: xs =>
       -- optExpr corresponds to the optimized lhs forall body
       -- continuity with optimizing next expression
       let e ← mkForallFVarExpr x optExpr
       stackContinuity xs e

  | .LetWaitForValue body :: xs =>
       -- optExpr corresponds to the optimized let value
       -- continuity with optimizing body
       -- NOTE: not used when tracking proof terms (see `optimizeExprAux`)
       return Sum.inl (.InitOptimizeExpr (← instantiateShared1 body optExpr) :: xs)

  | .MDataRecCallWaitForExpr d :: xs =>
       -- optExpr corresponds to the annotated rec call that is optimized when `normalizeFunCall` is set to false
       -- continuity with optimizing next expression
       setNormalizeFunCall true
       stackContinuity xs (← mkMDataExpr d optExpr) pf

  | .ProjWaitForExpr n idx :: xs =>
      -- optExpr corresponds to optimized projection structure
      let pf ← projCongr n idx optExpr pf
      clearSteps
      if let some re ← optimizeProjection? n idx optExpr then
         let step ← ruleStep (← mkProjExpr n idx optExpr) re "optimizeProjection"
         return Sum.inl (← pushTrans re (← pf.trans step) xs)
      else
        -- continuity with optimizing next expression
        stackContinuity xs (← mkProjExpr n idx optExpr) pf

  | _ => throwEnvError "stackContinuity: unexpected optimize stack continuity {reprStr stack} !!!"

  where
    /-- When tracking proof terms and `r` is the swapped form (see `isITESwap?`) of `dite' c₀ t e x₁ ... xₙ`
        with dependent branches, i.e., `dite' c e t` with `c₀` rewritten to `¬ c` (or `false = b` with
        `c := true = b`), return the well-typed swapped `dite'` (see `dite'_swap_dep`) and its evidence.
    -/
    dependentSwap? (f : Expr) (args : Array Expr) (orig : Expr) (pf : EqPf) (apf : EqPf) (r : Expr) :
      TranslateEnvT (Option (Expr × EqPf)) := do
      if !(← isTracking) || args.size < 4 then return none
      let t := args[2]!
      let e := args[3]!
      let (.lam _ _ tb _, .lam _ _ eb _) := (t, e) | return none
      if !tb.hasLooseBVars && !eb.hasLooseBVars then return none
      -- new condition `c` with `orig = ¬ c`
      let res ← tryInLocalContext do
        let pc₀ ← match pf with
          | .defeq => Meta.mkEqRefl orig
          | .proof p => if containsHole p then throwError "obligation" else pure p
          | _ => throwError "unknown"
        let (c, pc) ← match optExpr with
          | .app (.const ``Not _) c => pure (c, pc₀)
          | _ =>
            let some (_, .const ``false _, b) := optExpr.eq? | throwError "no swap"
            let c := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) (mkConst ``true) b
            pure (c, ← mkEqTrans pc₀ (← mkEqSymm (mkApp (mkConst ``Blaster.Reconstruct.not_true_eq_bool) b)))
        -- check that `r` is indeed the swapped form
        let extraArgs := args.extract 4 args.size
        let swapped := mkAppN f (#[args[0]!, c, e, t] ++ extraArgs)
        if !(r == swapped) then throwError "not a swap"
        let notC := mkApp (mkConst ``Not) c
        let thenB ← withLocalDeclD `h c fun h => do
          let h₀proof := Expr.lam `h₀ orig
            (mkApp (mkApp4 (mkConst ``Blaster.Reconstruct.castProof) orig notC pc (.bvar 0)) h) .default
          mkLambdaFVars #[h] (eb.instantiate1 h₀proof)
        let elseB ← withLocalDeclD `h notC fun h => do
          let cast := mkApp4 (mkConst ``Blaster.Reconstruct.castProof) notC orig (← mkEqSymm pc) h
          mkLambdaFVars #[h] (tb.instantiate1 cast)
        let r' := mkAppN f (#[args[0]!, c, thenB, elseB] ++ extraArgs)
        let lemma := mkAppN (mkConst ``Blaster.Reconstruct.dite'_swap_dep f.constLevels!)
                       #[args[0]!, orig, c, pc, t, e]
        let p ← extraArgs.foldlM (init := lemma) fun acc a => mkCongrFun acc a
        return (r', p)
      let some (r', p) := res | return none
      return some (← hashcons r', ← apf.trans (.proof p))

    /-- When tracking proof terms and the condition of `dite' c t e x₁ ... xₙ` has been rewritten to
        `True` (resp. `False`), return `t h x₁ ... xₙ` (resp. `e h x₁ ... xₙ`) with `h` a proof of `c`
        (resp. `¬ c`), together with the evidence of the rewrite.
    -/
    constDiteChoice? (f : Expr) (args : Array Expr) (orig : Expr) (pf : EqPf) (apf : EqPf) :
      TranslateEnvT (Option (Expr × EqPf)) := do
      if !(← isTracking) || args.size < 4 then return none
      let isTrue := optExpr.isConstOf ``True
      if !isTrue && !optExpr.isConstOf ``False then return none
      let some h ← withLocalContext (constCondProof orig pf isTrue) | return none
      let branch := if isTrue then args[2]! else args[3]!
      let extraArgs := args.extract 4 args.size
      let r := mkAppN (branch.beta #[h]) extraArgs
      let lemma := mkAppN (mkConst (if isTrue then ``Blaster.Reconstruct.dite'_pos else ``Blaster.Reconstruct.dite'_neg)
                    f.constLevels!) #[args[0]!, orig, args[2]!, args[3]!, h]
      let some p ← tryInLocalContext (extraArgs.foldlM (init := lemma) fun acc a => mkCongrFun acc a)
        | return none
      return some (← hashcons r, ← apf.trans (.proof p))

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
          let matchFun ← hashcons (← instantiateValueLevelParams cInfo l)
          return some (mInfo, matchFun)
        else return none
      else return none

    @[always_inline, inline]
    resolveMVarsArgs (extra_args : Array Expr) (args : Array Expr) : TranslateEnvT (Array Expr) := do
      let mAssignments := (← get).optEnv.mAssignments
      let rec visit (idx : Nat) (stop : Nat) (args : Array Expr) : Array Expr :=
         if idx ≥ stop then args
         else
           let e := args[idx]!
           match e with
           | Expr.mvar _ => visit (idx + 1) stop (args.set! idx (getEnvMVarValue' e mAssignments))
           | _ => visit (idx + 1) stop args
      let rec visit'
          (idx : Nat) (offset : Nat) (stop : Nat)
          (extra_args : Array Expr) (args : Array Expr) (pargs : Array Expr) : Array Expr :=
         if idx ≥ stop then pargs
         else
           let p := if idx < offset then extra_args[idx]! else args[idx - offset]!
           match p with
           | Expr.mvar _ => visit' (idx + 1) offset stop extra_args args (pargs.push (getEnvMVarValue' p mAssignments))
           | _ => visit' (idx + 1) offset stop extra_args args (pargs.push p)
      let extra_size := extra_args.size
      if mAssignments.size == 0 then
        -- no mvar assignments: resolution is the identity, only concatenation remains
        if extra_size == 0 then return args
        else return extra_args ++ args
      else if extra_size == 0 then
        return visit 0 args.size args
      else
        let stop := extra_size + args.size
        return visit' 0 extra_size stop extra_args args (Array.emptyWithCapacity stop)

    @[always_inline, inline]
    normProof (idx : Nat) (args : Array Expr) (optArg : Expr) (pInfo : FunEnvInfo) : TranslateEnvT Expr := do
     if idx ≥ pInfo.paramsInfo.size then return optArg
     else if pInfo.paramsInfo[idx]!.isProp then
       let argType ← inferArgTypeAt pInfo.type args idx
       match (← inHypMap argType) with
       | some p => return p
       | none =>
         if exprEq (← inferTypeEnv optArg) argType
         then return optArg
         else backwardProof argType
     else return optArg

    @[always_inline, inline]
    normNonFunProof (idx : Nat) (f : Expr) (args : Array Expr) (optArg : Expr) : TranslateEnvT Expr := do
      let pInfo ← getFunEnvInfo f
      normProof idx args optArg pInfo

/-- Given `pf : lhs = e`, perform the following:
     - When restart flag is set:
        - continue with optimizing `e` again
     - Otherwise:
        - continue with the stack continuity
-/
@[always_inline, inline]
def mkOptimizeContinuity (e : Expr) (stack : List OptimizeStack) (pf : EqPf := .unknown) : TranslateEnvT OptimizeContinuity := do
  if ← isRestart then
    resetRestart
    return Sum.inl (← pushTrans e pf stack)
  else stackContinuity stack e pf

/-- Apply simplification/normalization rules on Blaster.dite' expressions.
    Assume that f = Expr.const ``Blaster.dite'.
-/
@[always_inline, inline]
def optimizeIfThenElse? (f : Expr) (args : Array Expr) (stack : List OptimizeStack) (pf : EqPf := .unknown) :
  TranslateEnvT OptimizeContinuity := do
   clearSteps
   let e ← optimizeDITE f args
   let step ← if (← isTracking) then ruleStep (← mkAppNExpr f args) e "optimizeDITE" else pure .unknown
   mkOptimizeContinuity e stack (← pf.trans step)

@[always_inline, inline]
def isInOptimizeEnvCache (a : Expr) (stack : List OptimizeStack) (mvarDecls : Option MVarIdDecls) : TranslateEnvT (Sum (List OptimizeStack) OptimizeContinuity) := do
  let env ← get
  -- NOTE: An expression not containing any FVar/MVar may also be rewritten
  -- within a local context, see Issue348.lean
  let isGlobal := isGlobalContext env
  let useCache := !a.hasMVar
  if useCache then
    let cached := ← isInOptimizeCache? a isGlobal env
    if !exprEq cached instCacheMiss then Sum.inr <$> stackContinuity stack cached (← cachedProof a cached)
    else return Sum.inl (.InitOptimizeReturn a isGlobal mvarDecls :: stack)
  else return Sum.inl (.InitOptimizeReturn a isGlobal mvarDecls :: stack)

end Blaster.Optimize
