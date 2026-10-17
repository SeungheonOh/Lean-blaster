import Lean
import Blaster.Optimize.Rewriting.OptimizeITE
import Blaster.Optimize.Rewriting.OptimizeProjection
import Blaster.Optimize.Telescope
import Blaster.Reconstruct.Proof

open Lean Meta Blaster.Reconstruct

namespace Blaster.Optimize

structure HypsStackContext where
  newHCtx : UpdatedHypContext -- new hypothesis context
  oldHCtx : Option HypothesisContext -- old hypothesis context
  oldCache : Option RewriteCacheMap -- old local rewriting cache

structure MatchStackContext where
  oldMatchCtx : MatchContextMap -- old match context
  oldCache : RewriteCacheMap -- old local rewriting cache

structure LocalDeclStackContext where
  newCtx : LocalDeclContext -- new local decl context
  oldCtx : LocalDeclContext -- old local decl context

instance : Repr HypsStackContext where
  reprPrec _ _ := "<HypsStackContext>"

instance : Repr MatchStackContext where
  reprPrec _ _ := "<MatchStackContext>"

instance : Repr LocalDeclContext where
  reprPrec _ _ := "<LocalDeclContext>"

instance : Repr LocalContext where
  reprPrec _ _ := "<LocalContext>"

/-- Continuation stack of the optimizer.
    NOTE: Each frame waiting for the optimized form `v` of an expression `e` also receives
    evidence `pf : EqPf` that `e = v` (see `Blaster.Reconstruct`). Frames that rewrite the
    expression being optimized keep track of the evidence accumulated so far in a `pf` field.
-/
inductive OptimizeStack where
 | InitOptimizeExpr (e : Expr)
 | InitOptimizeReturn (e : Expr) (isGlobal : Bool)
 | TransWith (pf : EqPf)
 | InitOpaqueRecExpr (f : Expr) (args : Array Expr) (pf : EqPf)
 | RecFunDefWaitForStorage (args : Array Expr) (instApp : Expr)
                           (subsInts : Expr) (params : ImplicitParameters) (f : Expr) (pf : EqPf)
 | RecFunDefStorage (args : Array Expr) (instApp : Expr)
                    (subsInts : Expr) (params : ImplicitParameters) (optBody : Expr) (f : Expr) (pf : EqPf)
 | ForallWaitForType (n : Name) (bi : BinderInfo) (t : Expr) (body : Expr)
 | ForallWaitForBody (x : Expr) (t : Expr) (hctx : HypsStackContext) (lctx : LocalDeclContext)
                     (origT : Expr) (pt : EqPf) (origBody : Expr) (rawBody : Option Expr)
 | AppWaitForConst (args : Array Expr)
 | OptimizeMatchInfoWaitForInst (f : Expr) (args : Array Expr)
                                (startArgIdx : Nat) (pInfo : FunEnvInfo) (mInfo : MatcherRecInfo) (pf : EqPf)
 | AppOptimizeImplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (startArgIdx : Nat) (stopIdx : Nat) (pInfo : FunEnvInfo) (pf : EqPf)
 | AppOptimizeExplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (stopIdx : Nat) (pInfo : FunEnvInfo) (mInfo : Option MatchInfo) (pf : EqPf)
 | DiteChoiceWaitForCond (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (startArgIdx : Nat) (pf : EqPf)
 | MatchChoiceOptimizeDiscrs (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo)
                             (startArgIdx : Nat) (idx : Nat) (mInfo : MatchInfo) (pf : EqPf)
 | LambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr) (inDite : Bool)
                     (origT : Expr) (declType : Option (Expr × Option Expr))
 | LambdaWaitForBody (x : Expr) (lctx : LocalDeclContext) (hctx : Option HypsStackContext)
                     (pt : EqPf) (origBody : Expr) (origT : Expr) (casted : Bool)
 | MatchRhsLambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | MatchRhsLambdaNext (e : Expr)
 | MatchRhsLambdaWaitForBody (x : Expr) (lctx : LocalDeclContext)
 | MatchAltWaitForExpr (params : Array Expr) (lctx : LocalDeclContext) (mctx : MatchStackContext)
 | LetWaitForValue (n : Name) (t : Expr) (body : Expr)
 | MDataRecCallWaitForExpr (data : MData)
 | ProjWaitForExpr (n : Name) (idx : Nat)
 deriving Repr

abbrev OptimizeContinuity := Sum (List OptimizeStack) (Expr × EqPf)

/-- Push `.InitOptimizeExpr e` on the stack such that the evidence `pf` obtained so far
    (i.e., `pf : lhs = e`) is composed with the evidence obtained when optimizing `e`.
-/
@[always_inline, inline]
def pushTrans (e : Expr) (pf : EqPf) (stack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := do
  if pf.isDefEq || !(← isTracking) then return .InitOptimizeExpr e :: stack
  return .InitOptimizeExpr e :: .TransWith pf :: stack

@[always_inline, inline]
def mkHypStackContext (h : UpdatedHypContext) : TranslateEnvT HypsStackContext := do
  let ⟨_, ⟨_, localRewriteCache, _, _, _, _, _, _, hypothesisContext, _, _, _, _, _⟩, _⟩ ← get
  if h.1 then
    updateHypothesis h.2 Std.HashMap.emptyWithCapacity
    return {newHCtx := h, oldHCtx := some hypothesisContext, oldCache := some localRewriteCache}
  else return {newHCtx := h, oldHCtx := none, oldCache := none}

@[always_inline, inline]
def resetHypContext (h : HypsStackContext) : TranslateEnvT Unit := do
  match h.oldHCtx, h.oldCache with
  | some hyps, some cache => updateHypothesis hyps cache
  | none, none => pure ()
  | _, _ => throwEnvError "resetHypContext: invalid HypsStackContext !!!"

@[always_inline, inline]
def mkMatchStackContext (h : MatchContextMap) : TranslateEnvT MatchStackContext := do
  let ⟨_, ⟨_, localRewriteCache, _, _, _, _, _, _, _, matchInContext, _, _, _, _⟩, _⟩ ← get
  updateMatchContext h Std.HashMap.emptyWithCapacity
  return {oldMatchCtx := matchInContext, oldCache := localRewriteCache}

@[always_inline, inline]
def resetMatchContext (h : MatchStackContext) : TranslateEnvT Unit :=
  updateMatchContext h.oldMatchCtx h.oldCache

@[always_inline, inline]
def mkLocalDeclStackContext (newCtx : LocalDeclContext) : TranslateEnvT LocalDeclContext := do
  let oldCtx := (← get).optEnv.ctx
  updateLocalContext newCtx
  return oldCtx

@[always_inline, inline]
def resetLocalDeclContext (oldCtx : LocalDeclContext) : TranslateEnvT Unit :=
  updateLocalContext oldCtx

/-- Same as `mkExpr` but also returns the evidence for the possible rewrite performed
    via the global rewriting cache, i.e., given `pf : lhs = e`, return `(e', pf')` with `pf' : lhs = e'`.
-/
@[always_inline, inline]
def mkExprPf (e : Expr) (pf : EqPf) : TranslateEnvT (Expr × EqPf) := do
  let e' ← mkExpr e
  if exprEq e e' || !(← isTracking) then return (e', pf)
  return (e', ← pf.trans (← cachedProof e e'))

def stackContinuity
  (stack : List OptimizeStack) (optExpr : Expr) (pf : EqPf) (skipCache := false) : TranslateEnvT OptimizeContinuity := do
  match stack with
  | [] => return Sum.inr (optExpr, pf)

  | .InitOptimizeReturn e isGlobal :: xs =>
       let pf ← pf.close e optExpr
       if !skipCache then
         updateOptimizeEnvCache e optExpr isGlobal
         cacheProof e optExpr pf
       match xs with
       | [] => return Sum.inr (optExpr, pf)
       | _ => stackContinuity xs optExpr pf

  | .TransWith p :: xs =>
       -- optExpr corresponds to the optimized form of an expression `e` obtained after rewriting
       -- `lhs` to `e` with `p : lhs = e`.
       stackContinuity xs optExpr (← p.trans pf) skipCache

  | .RecFunDefWaitForStorage args instApp subsInst params f apf :: xs =>
       -- optExpr corresponds to optimized rec fun body
       -- continuity with normOpaqueAndRecFun
       -- NOTE: evidence for the optimized body is not needed to reconstruct the proof of the goal.
       return Sum.inl (.RecFunDefStorage args instApp subsInst params optExpr f apf :: xs)

  | .ForallWaitForType n bi t body :: xs =>
       -- optExpr corresponds to optimized forall binder type
       -- continuity with optimizing forall body
       -- NOTE: When tracking proof terms, the following actions are performed to preserve type correctness:
       --  - binders that are not hypotheses (e.g., functions over proofs) keep their original type
       --    when the rewrite of their type is not definitional;
       --  - for hypotheses used in the body, the body is instantiated with a cast from the rewritten type
       --    to the original one (only when the evidence of the rewrite has no proof obligation).
       withLocalContext $ do
         let (declT, pt, castEq?) ← forallBinderType t optExpr pf body
         withLocalDecl' n bi declT fun x => do
           -- NOTE: casts are only used for propositional bodies (see `castForallCongr`), e.g., not for
           -- the alternative types of a matcher.
           let castEq? ← match castEq? with
             | some h => do if (← isPropEnv (instantiate1' body x)) then pure (some h) else pure none
             | none => pure none
           let body' := match castEq? with
             | some h => body.instantiate1 (mkApp4 (mkConst ``Blaster.Reconstruct.castProof) declT t h x)
             | none => instantiate1' body x
           let isNotPropBody := !(← isPropEnv body')
           let hyps ← addHypotheses declT x isNotPropBody
           let hctx ← mkHypStackContext hyps
           let lctx ← mkLocalDeclStackContext (← mkLocalContext)
           let rawBody := castEq?.map fun _ => body
           return Sum.inl ( .InitOptimizeExpr body' :: .ForallWaitForBody x declT hctx lctx t pt body' rawBody :: xs)

  | .ForallWaitForBody x t hctx lctx origT pt origBody rawBody :: xs =>
       -- optExpr corresponds to optimized forall body
       -- continiuity with applying forall normalization rules
       resetHypContext hctx
       let (e, pf) ← withLocalContext $ do
          if !(← isTracking) then
            return (← optimizeForall x t hctx.newHCtx.2.1 optExpr, EqPf.unknown)
          let congrPf ← match rawBody with
            | some b0 => castForallCongr x origT t b0 optExpr pt pf
            | none => forallCongr x origT t origBody optExpr pt pf
          let lhs ← mkForallFVar x optExpr
          clearSteps
          let e ← optimizeForall x t hctx.newHCtx.2.1 optExpr
          return (e, ← congrPf.trans (← ruleStep lhs e "optimizeForall"))
       resetLocalDeclContext lctx
       if ← isRestart then
         resetRestart
         return Sum.inl (← pushTrans e pf xs)
       else -- continuity with optimizing next expression
         let (e, pf) ← mkExprPf e pf
         stackContinuity xs e pf

  | .AppWaitForConst args :: xs =>
       -- optExpr corresponds to optimized fun app
       -- reset inFunApp flag
       setInFunApp false
       let pf ← congrFunArgs pf args
       -- check if optExpr is a lambda
       if optExpr.isLambda then
         -- perform beta reduction and apply optimization
         return Sum.inl (← pushTrans (betaLambda optExpr args) pf xs)
       else
         let (rf, extraArgs) := getAppFnWithArgs optExpr
         let args := extraArgs ++ args
         let pInfo ← withLocalContext $ do getFunEnvInfo rf
         -- apply optimization on match generic instance (if necessary)
         match (← hasUnOptMatchInfo? rf) with
         | none =>
            -- continuity with optimization on implicit arguments
            return Sum.inl (.AppOptimizeImplicitArgs rf args extraArgs.size extraArgs.size args.size pInfo pf :: xs)
         | some (mInfo, instApp) =>
            -- continuity with optimizing match generic instance
            -- NOTE: instApp is expected to be a lambda term
            -- NOTE: we here only want to optimize the lambda params type, which mainly
            -- correspond to the match lhs.
            match instApp with
            | Expr.lam n t b bi =>
                let mWait := .OptimizeMatchInfoWaitForInst rf args extraArgs.size pInfo mInfo pf :: xs
                return Sum.inl (.InitOptimizeExpr t :: .MatchRhsLambdaWaitForType n bi b :: mWait)
            | _ => throwEnvError "stackContinuity: lambda expected for match instance but got {reprStr instApp}"


  | .OptimizeMatchInfoWaitForInst f args startArgIdx pInfo mInfo apf :: xs =>
       -- optExpr corresponds to optimized match generic instance
       -- update cache isMatcherCache
       if let Expr.const n _ := f then
         let argInfo := ({ name := n, nameExpr := f, instApp := optExpr, recInfo := mInfo } : MatchInfo)
         modify (fun env => { env with optEnv.memCache.isMatcherCache :=
                                       env.optEnv.memCache.isMatcherCache.insert n argInfo })
         -- apply optimization only on implicit parameters to remove mdata annotation
         -- we don't consider explicit parameters at this stage to avoid performing
         -- optimization on unreachable arguments
         return Sum.inl (.AppOptimizeImplicitArgs f args startArgIdx startArgIdx args.size pInfo apf :: xs)
       else throwEnvError "stackContinuity: name expression for match application but got {reprStr f} !!!"


  | .AppOptimizeImplicitArgs f args idx startArgIdx stopIdx pInfo apf :: xs =>
       -- optExpr corresponds to the optimized implicit argument referenced by idx.
       -- continuity with optimizing the next implicit argument.
       let args := args.set! idx optExpr
       let apf ← apf.trans (← congrArgAt f args idx pf)
       return Sum.inl (.AppOptimizeImplicitArgs f args (idx + 1) startArgIdx stopIdx pInfo apf :: xs)

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo apf :: xs =>
       -- optExpr corresponds to the optimized explicit argument referenced by idx.
       -- continuity with optimizing the next explicit argument.
       let orig := args[idx]!
       let args := args.set! idx optExpr
       let apf ← addArgEvidence f args idx orig pf apf
       return Sum.inl (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo apf :: xs)

  | .DiteChoiceWaitForCond f args pInfo startArgIdx apf :: xs =>
       -- optExpr corresponds to the optimized Blaster.dite' conditional, i.e., referenced by index 1.
       -- When some r ← optimizeDiteChoice f (args.set! 1 optExpr)
       --  - continuity with optimizing `r`
       -- Otherwise
       --  - continuity with optimizing remaining explicit parameters before reduction
       -- NOTE: keep matchInfo to avoid unnecessary query and to avoid optimizing discriminators again
       let orig := args[1]!
       let args := args.set! 1 optExpr
       -- NOTE: when tracking proof terms, a dite' with a condition reduced to `True`/`False` is
       -- reduced with a proof of the original condition (instead of `True.intro`), such that the
       -- resulting expression is well-typed.
       if let some (r, rpf) ← constDiteChoice? orig pf apf then
         return Sum.inl (← pushTrans r rpf xs)
       let preApf := apf
       let apf ← addArgEvidence f args 1 orig pf apf
       clearSteps
       if let some r ← optimizeDITEChoice f args then
           -- swapping dependent branches requires casts to keep the result well-typed
           if let some (r', rpf) ← dependentSwap? orig pf preApf r then
             return Sum.inl (← pushTrans r' rpf xs)
           let step ← ruleStep (mkAppN f args) r "optimizeDITEChoice"
           return Sum.inl (← pushTrans r (← apf.trans step) xs)
       else
          -- NOTE: keep matchInfo to avoid unnecessary query and to avoid optimizing discriminators again
          return Sum.inl (.AppOptimizeExplicitArgs f args startArgIdx args.size pInfo none apf :: xs)

  | .MatchChoiceOptimizeDiscrs f args pInfo startArgIdx idx mInfo apf :: xs =>
       -- optExpr corresponds to the optimized match discriminator referenced by idx.
       -- continuity with optimizing the next discriminator
       let args := args.set! idx optExpr
       let apf ← apf.trans (← congrArgAt f args idx pf)
       return Sum.inl (.MatchChoiceOptimizeDiscrs f args pInfo startArgIdx (idx + 1) mInfo apf :: xs)

  | .LambdaWaitForType n bi body inDite origT declInfo :: xs =>
       -- optExpr corresponds to optimized lambda type
       -- NOTE: When `declType` is provided (i.e., only when tracking proof terms), the lambda binder is
       -- declared with `declType` instead of `optExpr`. This is used to preserve type correctness of
       -- `Blaster.dite'` branches, whose binder types must respectively be `c` and `¬ c`, with `c` the
       -- optimized condition. The optimized type `optExpr` is still used as hypothesis.
       -- NOTE: When a cast `h : declType = origT` is provided, the body is instantiated with a proof of `origT`
       -- obtained from the binder, such that the body remains well-typed.
       withLocalContext $ do
         let declType := declInfo.map Prod.fst
         let castEq? := declInfo.bind Prod.snd
         withLocalDecl' n bi (declType.getD optExpr) fun x => do
           let (body', casted) := match declType, castEq? with
             | some τ, some h =>
                 if body.hasLooseBVars
                 then (body.instantiate1 (mkApp4 (mkConst ``Blaster.Reconstruct.castProof) τ origT h x), true)
                 else (body, false)
             | _, _ => (instantiate1' body x, false)
           let bodyOpt := .InitOptimizeExpr body'
           let lctx ← mkLocalDeclStackContext (← mkLocalContext)
           if inDite then
             let hyps ← addHypotheses optExpr x
             let hypsCtx ← mkHypStackContext hyps
             return Sum.inl (bodyOpt :: .LambdaWaitForBody x lctx (some hypsCtx) pf body' origT casted :: xs)
           else return Sum.inl (bodyOpt :: .LambdaWaitForBody x lctx none pf body' origT casted :: xs)

  | .LambdaWaitForBody x lctx hctx pt origBody origT casted :: xs =>
       -- optExpr corresponds to optimized lambda body
       -- continuity with optimizing next expression
       if let some h := hctx then resetHypContext h
       let (e, pf) ← withLocalContext $ do
          let pf ←
            if !(← isTracking) then pure .unknown
            else if pt.isDefEq || (← sameDomain (← x.fvarId!.getType) origT) then funextCongr x origBody optExpr pf
            else lamBodyCongr x origBody optExpr pf (allowDep := casted)
          mkExprPf (← mkLambdaFVar x optExpr) pf
       resetLocalDeclContext lctx
       stackContinuity xs e pf

  | .MatchRhsLambdaWaitForType n bi body :: xs =>
        -- optExpr corresponds to optimized lambda type
        -- continuity with optimizing body
        withLocalContext $ do
          withLocalDecl' n bi optExpr fun x => do
            let bodyOpt := .MatchRhsLambdaNext (instantiate1' body x)
            let lctx ← mkLocalDeclStackContext (← mkLocalContext)
            return Sum.inl (bodyOpt :: .MatchRhsLambdaWaitForBody x lctx :: xs)

  | .MatchRhsLambdaWaitForBody x lctx :: xs =>
        -- optExpr corresponds to optimized lambda body
        -- continuity with optimizing next expression
        -- NOTE: We can't catch optimize result here as match
        -- rhs has not been optimized yet.
        let e ← withLocalContext $ do mkLambdaFVar x optExpr
        resetLocalDeclContext lctx
        -- NOTE: evidence for the generic match instance is not needed
        stackContinuity xs e .unknown

  | .MatchAltWaitForExpr params lctx mctx :: xs =>
       -- optExpr corresponds to the optimized match rhs
       -- continuity with optimizing next expression
       -- TODO: proof reconstruction for match alternatives optimized w.r.t. a match context.
       let e ← withLocalContext $ do mkExpr (← mkLambdaFVars' params optExpr)
       resetMatchContext mctx
       resetLocalDeclContext lctx
       stackContinuity xs e .unknown

  | .LetWaitForValue n t body :: xs =>
       -- optExpr corresponds to the optimized let value
       -- continuity with optimizing body
       let pf ← letValueCongr n t body pf
       return Sum.inl (← pushTrans (body.instantiate1 optExpr) pf xs)

  | .MDataRecCallWaitForExpr d :: xs =>
       -- optExpr corresponds to the annotated rec call that is optimized when `normalizeFunCall` is set to false
       -- continuity with optimizing next expression
       setNormalizeFunCall true
       let (e, pf) ← mkExprPf (Expr.mdata d optExpr) pf
       stackContinuity xs e pf

  | .ProjWaitForExpr n idx :: xs =>
      -- optExpr corresponds to optimized projection structure
      let pf ← projCongr n idx optExpr pf
      clearSteps
      if let some re ← optimizeProjection? n idx optExpr then
         let step ← ruleStep (mkProj n idx optExpr) re "optimizeProjection"
         return Sum.inl (← pushTrans re (← pf.trans step) xs)
      else
        -- continuity with optimizing next expression
        let (e, pf) ← mkExprPf (mkProj n idx optExpr) pf
        stackContinuity xs e pf

  | _ => throwEnvError "stackContinuity: unexpected optimize stack continuity {reprStr stack} !!!"

  where
    /-- Return the type with which a forall binder of type `t` (optimized to `t'` with evidence `pf`) must be
        declared, the evidence for the binder type and the (optional) cast `t' = t` for the body
        (see `ForallWaitForType`).
    -/
    forallBinderType (t t' : Expr) (pf : EqPf) (body : Expr) : TranslateEnvT (Expr × EqPf × Option Expr) := do
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

    /-- When tracking proof terms and `r` is the swapped form (see `isITESwap?`) of `dite' c₀ t e x₁ ... xₙ`
        with dependent branches, i.e., `dite' c e t` with `c₀` rewritten to `¬ c` (or `false = b` with
        `c := true = b`), return the well-typed swapped `dite'` (see `dite'_swap_dep`) and its evidence.
    -/
    dependentSwap? (orig : Expr) (pf : EqPf) (apf : EqPf) (r : Expr) : TranslateEnvT (Option (Expr × EqPf)) := do
      let .DiteChoiceWaitForCond f args _ _ _ :: _ := stack | return none
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
      return some (r', ← apf.trans (.proof p))

    /-- Return `true` if `t := (h : P) → β` with `P` a proposition. -/
    isFunOverProof (t : Expr) : TranslateEnvT Bool := do
      let .forallE _ d _ _ := t | return false
      let some r ← tryInLocalContext (isProp d) | return false
      return r

    /-- When tracking proof terms and the condition of `dite' c t e x₁ ... xₙ` has been rewritten to
        `True` (resp. `False`), return `t h x₁ ... xₙ` (resp. `e h x₁ ... xₙ`) with `h` a proof of `c`
        (resp. `¬ c`), together with the evidence of the rewrite.
    -/
    constDiteChoice? (orig : Expr) (pf : EqPf) (apf : EqPf) : TranslateEnvT (Option (Expr × EqPf)) := do
      let .DiteChoiceWaitForCond f args _ _ _ :: _ := stack | return none
      if !(← isTracking) || args.size < 4 then return none
      let isTrue := optExpr.isConstOf ``True
      if !isTrue && !optExpr.isConstOf ``False then return none
      let some h ← withLocalContext (constCondProof orig pf isTrue) | return none
      let branch := if isTrue then args[2]! else args[3]!
      let extraArgs := args.extract 4 args.size
      let r := mkAppN (betaLambda branch #[h]) extraArgs
      let lemma := mkAppN (mkConst (if isTrue then ``Blaster.Reconstruct.dite'_pos else ``Blaster.Reconstruct.dite'_neg)
                    f.constLevels!) #[args[0]!, orig, args[2]!, args[3]!, h]
      let some p ← tryInLocalContext (extraArgs.foldlM (init := lemma) fun acc a => mkCongrFun acc a)
        | return none
      return some (r, ← apf.trans (.proof p))

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

/-- Given `pf : lhs = e`, perform the following:
     - When restart flag is set:
        - continue with optimizing `e` again
     - Otherwise:
        - continue with the stack continuity
-/
@[always_inline, inline]
def mkOptimizeContinuity (e : Expr) (stack : List OptimizeStack) (pf : EqPf) : TranslateEnvT OptimizeContinuity := do
  if ← isRestart then
    resetRestart
    return Sum.inl (← pushTrans e pf stack)
  else
    let (e, pf) ← mkExprPf e pf
    stackContinuity stack e pf

/-- Apply simplification/normalization rules on Blaster.dite' expressions.
    Assume that f = Expr.const ``Blaster.dite'.
-/
@[always_inline, inline]
def optimizeIfThenElse? (f : Expr) (args : Array Expr) (stack : List OptimizeStack) (pf : EqPf) :
  TranslateEnvT OptimizeContinuity := withLocalContext $ do
   clearSteps
   let e ← optimizeDITE f args
   let step ← ruleStep (mkAppN f args) e "optimizeDITE"
   mkOptimizeContinuity e stack (← pf.trans step)

@[always_inline, inline]
def isInOptimizeEnvCache (a : Expr) (stack : List OptimizeStack) : TranslateEnvT (Sum (List OptimizeStack) OptimizeContinuity) := do
  -- NOTE: Always consider global context when `a` does not contain any FVar.
  let isGlobal := !a.hasFVar || (← isGlobalContext)
  match (← isInOptimizeCache? a isGlobal) with
  | some b => Sum.inr <$> stackContinuity stack b (← cachedProof a b)
  | none => return Sum.inl (.InitOptimizeReturn a isGlobal :: stack)


end Blaster.Optimize
