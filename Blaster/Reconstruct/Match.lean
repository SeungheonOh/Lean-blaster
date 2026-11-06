import Lean

open Lean Meta

namespace Blaster.Reconstruct

/-! # Proofs over `match` alternatives

A rewrite of a `match` application `m := matcher ps motive d₁ ... dₙ alt₁ ... altₖ` into some `rhs` is
justified by a case split over the patterns of the matcher, i.e., via its *splitter*
(see `Lean.Meta.Match.getEquationsFor`). The splitter is applied to the motive
`fun x₁ ... xₙ => (dₙ = xₙ) → ... → (d₁ = x₁) → m[x₁ ... xₙ / d₁ ... dₙ] = rhs[x₁ ... xₙ]`,
such that the obligation for alternative `i` is
  `∀ (vars) (overlap hyps) (hⱼ : dⱼ = pᵢⱼ), altᵢ vars = rhs[pᵢ₁ ... pᵢₙ]`
after reducing `m[pᵢ₁ ... pᵢₙ]` with the `i`-th match equation. The equalities `hⱼ` connect
the discriminants with the patterns of the alternative, i.e., they correspond to the match context
under which the alternatives are optimized (see `Blaster.Optimize.optimizeMatchAlt`).
`casesOn` applications are handled in the same way, except that the alternatives are reduced by iota.
-/

/-- The congruences of `match` applications built by `mkMatchCongr`, by the application, the new alternatives and their
    evidence (structural equality). -/
abbrev MatchCongrs := Std.HashMap (Expr × Array Expr × Array (Option Expr)) Expr

/-- Matchers for which the generation of the match equations and splitter failed. -/
initialize matchEqnsFailures : IO.Ref NameSet ← IO.mkRef {}

/-- The match equations generated so far (see `getEquationsFor?`).
    NOTE: keyed by the name of the matcher, e.g., `_example.match_1` for the matchers of different `example`s, which is
    harmless: only the names of the equations and of the splitter are used, the same for all of them. -/
initialize matchEqnsCache : IO.Ref (Std.HashMap Name Match.MatchEqns) ← IO.mkRef {}

/-- Same as `Lean.Meta.Match.getEquationsFor` but return `none` when the match equations cannot be
    generated (e.g., heartbeats exhausted on matchers with many overlapping patterns).
    NOTE: The generation is performed via `realizeConst`, which reports failures as messages.
    Such messages are discarded, as they do not affect the validity of the reconstructed proof.
-/
def getEquationsFor? (n : Name) : MetaM (Option Match.MatchEqns) := do
  if (← matchEqnsFailures.get).contains n then return none
  -- NOTE: `Match.getEquationsFor` looks up the realized equations at each call (`realizeConst`), which is costly when
  -- called for each alternative of the many `match` applications of an optimization (e.g., a fifth of the proof run of
  -- a CEK evaluation); the equations are cached while their declarations are in the environment
  if let some eqns := (← matchEqnsCache.get)[n]? then
    -- NOTE: the splitter is realized (see `realizeConst`) on the current environment branch, or generated again: the
    -- realizations of the other branches are not looked up (e.g., the ones of the previous theorems, which would wait
    -- for their kernel checks)
    if (← getEnv).contains eqns.splitterName (skipRealize := true) then return some eqns
  let tasks := (← getThe Core.State).snapshotTasks
  let msgs := (← getThe Core.State).messages
  tryCatchRuntimeEx (do
      let eqns ← Match.getEquationsFor n
      matchEqnsCache.modify (·.insert n eqns)
      return some eqns) fun _ => do
    modifyThe Core.State fun s => { s with snapshotTasks := tasks, messages := msgs }
    matchEqnsFailures.modify (·.insert n)
    return none

/-- Return `true` if `e` is a `match` or `casesOn` application for which `mkMatchCasesProof` can
    be attempted.
-/
def isMatchCasesApp (e : Expr) : MetaM Bool := do
  let some app ← matchMatcherApp? e (alsoCasesOn := true) | return false
  return app.remaining.isEmpty && app.discrInfos.all (·.hName?.isNone)

/-- Return a proof of `False` obtained from an overlap hypothesis of the local context, i.e., a hypothesis
    `h : ∀ ys, d₁ = q₁ → ... → dₙ = qₙ → False` such that each equality `dⱼ = qⱼ` holds definitionally
    for some instantiation of `ys` (e.g., unreachable alternatives of a match over structures, due to
    structure eta).
-/
def absurdFromOverlap? : MetaM (Option Expr) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if !type.isForall then continue
    let s ← saveState
    let r ← observing? do
      let (mvars, _, concl) ← forallMetaTelescopeReducing type
      unless concl.isFalse do failure
      for mv in mvars do
        if (← mv.mvarId!.isAssigned) then continue
        let mvType ← instantiateMVars (← inferType mv)
        let some (_, a, b) := mvType.eq? | continue
        unless ← withTransparency .default (isDefEq a b) do failure
        mv.mvarId!.assign (← mkEqRefl a)
      let p ← instantiateMVars (mkAppN decl.toExpr mvars)
      if p.hasExprMVar then failure
      return p
    match r with
    | some p => return some p
    | none => s.restore
  return none

/-- `isDefEq l r` for applications of the same constant, unifying their arguments pairwise first.
    NOTE: `isDefEq` on the applications of a matcher first reduces them (`whnfCore`), e.g., the matcher instantiated
    at the patterns of an alternative (see `proveMatchAltEq`), while the unification of the arguments assigns the
    metavariables of the match equation directly.
-/
def unifyApps (l r : Expr) : MetaM Bool := do
  let (lf, rf) := (l.getAppFn, r.getAppFn)
  if lf.isConst && rf.isConst && lf.constName! == rf.constName! && l.getAppNumArgs == r.getAppNumArgs then
    let s ← saveState
    -- NOTE: the arguments that are unassigned metavariables of `l` (e.g., the parameters, motive and alternatives of a
    -- match equation) are assigned in order, i.e., without the unification of their types with the types of the large
    -- alternatives (`isDefEq` infers them), the types of the arguments being the instances of the binder types of the
    -- same constant; the other arguments (e.g., the patterns) are unified
    let ok ← isDefEq lf rf <&&> (l.getAppArgs.zip r.getAppArgs).allM fun (a, b) => do
      if let .mvar m := a then
        if !(← m.isAssigned) && !(← m.isDelayedAssigned) && !b.hasLooseBVars then
          m.assign b
          return true
      isDefEq a b
    if ok then return true
    s.restore
  isDefEq l r

/-- Given `m := matcher ps motive pats alts` (i.e., a matcher instantiated at the patterns of alternative
    `altIdx`), return a proof of `m = altᵢ args` with `args` the arguments of the alternative.
    The overlap hypotheses required by the match equation are looked up in the local context.
-/
def proveMatchAltEq (m : Expr) (alt : Expr) (altIdx : Nat) (isCasesOn : Bool) : MetaM Expr := do
  if !isCasesOn then
    let some app ← matchMatcherApp? m | throwError "proveMatchAltEq: matcher expected"
    let some eqns ← getEquationsFor? app.matcherName | throwError "proveMatchAltEq: no match equations"
    if h : altIdx < eqns.eqnNames.size then
      let c ← mkConstWithFreshMVarLevels eqns.eqnNames[altIdx]
      let (mvars, _, ty) ← forallMetaTelescopeReducing (← inferType c)
      if let some (_, lhs, rhs) := ty.eq? then
        if ← unifyApps lhs m <&&> isDefEq rhs alt then
          let lctx ← getLCtx
          let mut ok := true
          for mv in mvars do
            if (← mv.mvarId!.isAssigned) then continue
            let mvType ← instantiateMVars (← inferType mv)
            let some d ← lctx.findDeclRevM? (fun d => do
                if d.isImplementationDetail then return none
                if ← isDefEq d.type mvType then return some d else return none)
              | ok := false; break
            mv.mvarId!.assign d.toExpr
          if ok then
            let p ← instantiateMVars (mkAppN c mvars)
            if !p.hasExprMVar then return p
  -- reduction by iota (e.g., casesOn and non-overlapping patterns)
  if ← withTransparency .default <| isDefEq m alt then
    return ← mkExpectedTypeHint (← mkEqRefl m) (← mkEq m alt)
  -- unreachable alternative
  if let some h ← absurdFromOverlap? then
    return ← mkFalseElim (← mkEq m alt) h
  throwError "proveMatchAltEq: cannot reduce alternative {altIdx}"

/-- Return the free variables of the last `n` declarations of `lctx`, from the last one.
    NOTE: the local context is not traversed as a whole (unlike `LocalContext.getFVars`), as it may be
    large (e.g., the local context of the optimizer).
-/
def lastFVarsRev (lctx : LocalContext) (n : Nat) : Array Expr := Id.run do
  let mut r := #[]
  let mut i := lctx.decls.size
  while i > 0 && r.size < n do
    i := i - 1
    if let some d := lctx.decls.get! i then r := r.push d.toExpr
  return r

/-- `Match.forallAltVarsTelescope` lifted to a monad transformer (see `transformMatcherApp`). -/
def forallAltTelescopeAux
    {n} [Monad n] [MonadControlT MetaM n]
    {α} (origAltType : Expr) (numParams numDiscrEqs : Nat)
    (k : Array Expr → Array Expr → n α) : n α := do
  map2MetaM (fun k =>
    Match.forallAltVarsTelescope origAltType numParams numDiscrEqs
      fun ys args _mask _bodyType => k ys args
  ) k

/-- `Lean.Meta.MatcherApp.transform` (Lean 4 core, `Lean/Meta/Match/MatcherApp/Transform.lean`, Apache 2.0) without the
    type checking of the new motive applied to the discriminants (`isTypeCorrect`), whose type is only inferred (by
    `inferArgumentTypesN`), and with the match equations of `getEquationsFor?` (cached).
    NOTE: the check traverses the alternatives of the right-hand side of the motive of `mkMatchCasesProof`, i.e., the
    alternatives of the nested `match` applications again at each level (a third of the proof run of a CEK evaluation);
    `mkMatchCasesProof` checks that the sides of the equation of its motive have the same type, the alternatives being
    well typed (the kernel checks the resulting proof).
-/
def transformMatcherApp
    {n} [MonadLiftT MetaM n] [MonadControlT MetaM n] [Monad n] [MonadError n] [MonadEnv n] [MonadLog n]
    [AddMessageContext n] [MonadOptions n]
    (matcherApp : MatcherApp)
    (useSplitter := false)
    (addEqualities : Bool := false)
    (onParams : Expr → n Expr := pure)
    (onMotive : Array Expr → Expr → n Expr := fun _ e => pure e)
    (onAlt : Nat → Expr → Array Expr → Expr → n Expr := fun _ _ _ e => pure e)
    (onRemaining : Array Expr → n (Array Expr) := pure) :
    n MatcherApp := do

  -- We also handle CasesOn applications here, and need to treat them specially in a
  -- few places.
  -- TODO: Expand MatcherApp with the necessary fields to make this more uniform
  -- (in particular, include discrEq and whether there is a splitter)
  let isCasesOn := isCasesOnRecursor (← getEnv) matcherApp.matcherName

  let numDiscrEqs ←
    if isCasesOn then pure 0 else
    match ← getMatcherInfo? matcherApp.matcherName with
    | some info => pure info.getNumDiscrEqs
    | none      => throwError "matcher {matcherApp.matcherName} has no MatchInfo found"

  let params' ← matcherApp.params.mapM onParams
  let discrs' ← matcherApp.discrs.mapM onParams

  let (motive', uElim, addHEqualities) ← lambdaTelescope matcherApp.motive fun motiveArgs motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"
    let mut motiveBody' ← onMotive motiveArgs motiveBody

    -- Prepend `(x = e) →` or `(x ≍ e) → ` to the motive when an equality is requested
    -- and not already present, and remember whether we added an Eq or a HEq
    let mut addHEqualities : Array (Option Bool) := #[]
    for arg in motiveArgs, discr in discrs', di in matcherApp.discrInfos do
      if addEqualities && di.hName?.isNone then
        if ← isProof arg then
          addHEqualities := addHEqualities.push none
        else
          let heq ← mkEqHEq discr arg
          motiveBody' ← liftMetaM <| mkArrow heq motiveBody'
          addHEqualities := addHEqualities.push heq.isHEq
      else
        addHEqualities := addHEqualities.push none

    return (← mkLambdaFVars motiveArgs motiveBody', ← getLevel motiveBody', addHEqualities)

  let matcherLevels ← match matcherApp.uElimPos? with
    | none     => pure matcherApp.matcherLevels
    | some pos => pure <| matcherApp.matcherLevels.set! pos uElim

  -- We pass `Eq.refl`s for all the equations we added as extra arguments
  -- (and count them along the way)
  let mut remaining' := #[]
  let mut extraEqualities : Nat := 0
  for discr in discrs'.reverse, b in addHEqualities.reverse do
    match b with
    | none => pure ()
    | some is_heq =>
        remaining' := remaining'.push (← (if is_heq then mkHEqRefl else mkEqRefl) discr)
        extraEqualities := extraEqualities + 1

  if useSplitter && !isCasesOn then
    let aux1 := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) params'
    let aux1 := mkApp aux1 motive'
    let aux1 := mkAppN aux1 discrs'
    let origAltTypes ← inferArgumentTypesN matcherApp.alts.size aux1

    -- We replace the matcher with the splitter
    let some matchEqns ← liftMetaM (getEquationsFor? matcherApp.matcherName)
      | throwError "the splitter of {matcherApp.matcherName} cannot be generated"
    let splitter := matchEqns.splitterName

    let aux2 := mkAppN (mkConst splitter matcherLevels.toList) params'
    let aux2 := mkApp aux2 motive'
    let aux2 := mkAppN aux2 discrs'
    let altTypes ← inferArgumentTypesN matcherApp.alts.size aux2

    let mut alts' := #[]
    for altIdx in *...matcherApp.alts.size,
        alt in matcherApp.alts,
        numParams in matcherApp.altNumParams,
        splitterNumParams in matchEqns.splitterAltNumParams,
        origAltType in origAltTypes,
        altType in altTypes do
      let alt' ← forallAltTelescopeAux origAltType (numParams - numDiscrEqs) 0 fun ys args => do
        let altType ← instantiateForall altType ys
        -- The splitter inserts its extra parameters after the first ys.size parameters, before
        -- the parameters for the numDiscrEqs
        forallBoundedTelescope altType (splitterNumParams - ys.size) fun ys2 altType => do
          forallBoundedTelescope altType numDiscrEqs fun ys3 altType => do
            forallBoundedTelescope altType extraEqualities fun ys4 altType => do
              let altParams := args ++ ys3
              let alt ← try instantiateLambda alt altParams
                        catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
              let alt' ← onAlt altIdx altType altParams alt
              mkLambdaFVars (ys ++ ys2 ++ ys3 ++ ys4) alt'
      alts' := alts'.push alt'

    remaining' := remaining' ++ (← onRemaining matcherApp.remaining)

    return { matcherApp with
      matcherName   := splitter
      matcherLevels := matcherLevels
      params        := params'
      motive        := motive'
      discrs        := discrs'
      altNumParams  := matchEqns.splitterAltNumParams.map (· + extraEqualities)
      alts          := alts'
      remaining     := remaining'
    }
  else
    let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) params'
    let aux := mkApp aux motive'
    let aux := mkAppN aux discrs'
    let altTypes ← inferArgumentTypesN matcherApp.alts.size aux

    let mut alts' := #[]
    for altIdx in *...matcherApp.alts.size,
        alt in matcherApp.alts,
        numParams in matcherApp.altNumParams,
        altType in altTypes do
      let alt' ← forallBoundedTelescope altType numParams fun xs altType => do
        forallBoundedTelescope altType extraEqualities fun ys4 altType => do
          -- we should try to preserve the variable names in the alternative
          let names ← lambdaTelescope alt fun xs _ => xs.mapM (·.fvarId!.getUserName)
          MatcherApp.withUserNames xs names do
            let alt ← instantiateLambda alt xs
            let alt' ← onAlt altIdx altType xs alt
            mkLambdaFVars (xs ++ ys4) alt'
      alts' := alts'.push alt'

    remaining' := remaining' ++ (← onRemaining matcherApp.remaining)

    return { matcherApp with
      matcherLevels := matcherLevels
      params        := params'
      motive        := motive'
      discrs        := discrs'
      altNumParams  := matcherApp.altNumParams.map (· + extraEqualities)
      alts          := alts'
      remaining     := remaining'
    }

/-- Given a match application `m := matcher ps motive d₁ ... dₙ alt₁ ... altₖ` and `rhsFn` returning
    `rhs[x₁ ... xₙ]` for motive arguments `x₁ ... xₙ`, return a proof of `m = rhsFn #[d₁, ..., dₙ]`.
    The obligation for alternative `i` is provided by `altPf i args hs alt rhsᵢ` with:
      - `args`: the arguments of the alternative;
      - `hs`: the equalities `dⱼ = pᵢⱼ` (in discriminant order);
      - `alt`: the alternative instantiated with `args`;
      - `rhsᵢ`: `rhsFn #[pᵢ₁, ..., pᵢₙ]`;
    and must return a proof of `alt = rhsᵢ`.
    An exception is raised when the proof cannot be constructed.
-/
def mkMatchCasesProof {n} [MonadLiftT MetaM n] [MonadControlT MetaM n] [Monad n] [MonadError n]
  [MonadEnv n] [MonadLog n] [AddMessageContext n] [MonadOptions n]
  (m : Expr) (rhsFn : Array Expr → n Expr)
  (altPf : Nat → Array Expr → Array Expr → Expr → Expr → n Expr) : n Expr := do
  let some app ← matchMatcherApp? m (alsoCasesOn := true)
    | throwError "mkMatchCasesProof: match application expected"
  if !app.remaining.isEmpty then throwError "mkMatchCasesProof: over-applied match"
  if app.discrInfos.any (·.hName?.isSome) then throwError "mkMatchCasesProof: named discriminant"
  for d in app.discrs do
    if ← liftMetaM (isProof d) then throwError "mkMatchCasesProof: proof discriminant"
  let isCasesOn := isCasesOnRecursor (← getEnv) app.matcherName
  if !isCasesOn && (← liftMetaM (getEquationsFor? app.matcherName)).isNone then
    throwError "mkMatchCasesProof: no splitter for {app.matcherName}"
  let nDiscrs := app.discrs.size
  let mkM (discrs : Array Expr) : Expr :=
    mkAppN (mkConst app.matcherName app.matcherLevels.toList) (app.params ++ #[app.motive] ++ discrs ++ app.alts)
  let app' ← transformMatcherApp app (useSplitter := true) (addEqualities := true)
    (onMotive := fun xs _ => do
      let (lhs, rhs) := (mkM xs, ← rhsFn xs)
      liftMetaM do
        -- NOTE: the motive is not type checked as a whole (see `transformMatcherApp`)
        unless ← isDefEq (← inferType lhs) (← inferType rhs) do
          throwError "mkMatchCasesProof: the sides of the motive have different types"
        mkEq lhs rhs)
    (onAlt := fun altIdx altType args alt => do
      let some (_, lhs, rhs) := altType.eq? | throwError "mkMatchCasesProof: equality expected"
      -- the equalities added by `transform` are the last `nDiscrs` local declarations (in reverse order)
      let hs := lastFVarsRev (← liftMetaM getLCtx) nDiscrs
      if hs.size < nDiscrs then throwError "mkMatchCasesProof: missing equalities"
      for h in hs do
        if !(← liftMetaM (inferType h)).isEq then throwError "mkMatchCasesProof: heterogeneous equality"
      let pLhs ← liftMetaM (proveMatchAltEq lhs alt altIdx isCasesOn)
      let pAlt ← altPf altIdx args hs alt rhs
      liftMetaM (mkEqTrans pLhs pAlt))
  return app'.toExpr

/-- `p` without its `m` binders following its first `n` binders (i.e., `fun xs ys => b` as `fun xs => b`), when they
    don't occur in its body. -/
def dropUnusedBinders? (p : Expr) (n m : Nat) : Option Expr :=
  match n, p with
  | n + 1, .lam x d b bi => (dropUnusedBinders? b n m).map fun b' => .lam x d b' bi
  | 0, _ => strip p m
  | _, _ => none
where
  strip (e : Expr) : Nat → Option Expr
    | 0 => if (List.range m).any e.hasLooseBVar then none else some (e.lowerLooseBVars m m)
    | k + 1 => match e with
      | .lam _ _ b _ => strip b k
      | _ => none

/-- Proof of `f = g` from `pf := fun x₁ ... xₖ => b` with `b : f x₁ ... xₖ = g x₁ ... xₖ`, where `ty := ∀ x₁ ... xₖ, R`
    is the type of `f` and `g`: nested applications of `funext`, built under the binders of `pf` (no abstraction of its
    body). -/
partial def mkFunExtN (f g pf ty : Expr) (k : Nat) : MetaM Expr := do
  let lvls ← forallBoundedTelescope ty k fun xs r => do
    if xs.size != k then throwError "mkFunExtN: {k} binders expected"
    (Array.range k).mapM fun j => do
      return (← getLevel (← inferType xs[j]!), ← getLevel (← mkForallFVars (xs.extract (j + 1) k) r))
  let rec go (j : Nat) (pf ty : Expr) : MetaM Expr := do
    if j == k then return pf
    let .lam n d b bi := pf | throwError "mkFunExtN: lambda expected"
    let .forallE n' a b' bi' := ty | throwError "mkFunExtN: forall expected"
    let inner ← go (j + 1) b b'
    -- the binders of the enclosing applications of `funext`
    let vs := (Array.range j).reverse.map mkBVar
    let (u, v) := lvls[j]!
    return mkApp5 (mkConst ``funext [u, v]) a (.lam n' a b' bi') (mkAppN f vs) (mkAppN g vs) (.lam n d inner bi)
  go 0 pf ty

/-- `mkMatchCongr` by congruence on the alternatives (`congr`, `funext`), when the evidence of the alternatives doesn't
    use the equalities between the discriminants and the patterns, nor has proof obligations (`noHoles`, which may use
    them): no case split (i.e., no instance of the splitter and of the match equations of the alternatives). -/
def mkMatchCongrByAlts? (app : MatcherApp) (alts' : Array Expr) (altPfs : Array (Option Expr)) :
    MetaM (Option Expr) := do
  if app.alts.size != alts'.size || app.alts.size != altPfs.size || app.altNumParams.size != altPfs.size then
    return none
  let nDiscrs := app.discrs.size
  -- the evidence of the alternatives without the equalities
  let mut pfs := #[]
  for p? in altPfs, n in app.altNumParams do
    match p? with
    | none => pfs := pfs.push none
    | some p =>
        if p.hasMVar then return none
        let some p' := dropUnusedBinders? p n nDiscrs | return none
        pfs := pfs.push (some p')
  let f := mkAppN (mkConst app.matcherName app.matcherLevels.toList) (app.params ++ #[app.motive] ++ app.discrs)
  let mut ty ← inferType f
  let mut lhs := f
  let mut rhs := f
  -- `lhs = rhs` (`none`: the same alternatives so far)
  let mut cur : Option Expr := none
  for i in [:app.alts.size] do
    ty ← whnfD ty
    let .forallE _ a b _ := ty | return none
    if b.hasLooseBVars then return none
    let alt := app.alts[i]!
    let alt' := alts'[i]!
    let e? ← match pfs[i]! with
      | some p => pure (some (← mkFunExtN alt alt' p a app.altNumParams[i]!))
      | none => if alt == alt' then pure none else pure (some (← mkEqRefl alt))
    let u ← getLevel a
    let v ← getLevel b
    cur := match cur, e? with
      | none, none => none
      | none, some e => some (mkApp6 (mkConst ``congrArg [u, v]) a b alt alt' lhs e)
      | some c, none => some (mkApp6 (mkConst ``congrFun [u, v]) a (.lam `_ a b .default) lhs rhs c alt)
      | some c, some e => some (mkAppN (mkConst ``congr [u, v]) #[a, b, lhs, rhs, alt, alt', c, e])
    lhs := mkApp lhs alt
    rhs := mkApp rhs alt'
    ty := b
  match cur with
  | some p => return some p
  | none => return some (← mkEqRefl lhs)

/-- Given evidence for each alternative of a match application `m := matcher ps motive ds alts`,
    return a proof of `m = matcher ps motive ds alts'`. The evidence `altPfs[i]` for alternative `i` is:
      - `none` when `altᵢ` and `alt'ᵢ` are definitionally equal;
      - `some p` with `p : ∀ args (h₁ : d₁ = pᵢ₁) ... (hₙ : dₙ = pᵢₙ), altᵢ args = alt'ᵢ args`.
    When `noHoles` (the evidence has no proof obligation), the congruence is first built without case split (see
    `mkMatchCongrByAlts?`). The congruences of `cache` are reused when well-scoped; the result tells whether the
    congruence may be added to it (i.e., whether it is new and has no metavariable).
    NOTE: the congruence is not type checked here (the kernel checks the resulting proof).
-/
def mkMatchCongr (m : Expr) (alts' : Array Expr) (altPfs : Array (Option Expr)) (noHoles := false)
    (cache : MatchCongrs := {}) : MetaM (Expr × Bool) := do
  -- NOTE: the optimizer may justify the same rewrite of a `match` application several times (e.g., about a third of
  -- the congruences of a CEK evaluation)
  if let some p := cache[(m, alts', altPfs)]? then
    let lctx ← getLCtx
    if !p.hasAnyFVar (!lctx.contains ·) then return (p, false)
  let some app ← matchMatcherApp? m (alsoCasesOn := true)
    | throwError "mkMatchCongr: match application expected"
  -- extra arguments (i.e., match returning a function) are handled via `congrFun`
  if noHoles then
    if let some p ← tryCatchRuntimeEx (mkMatchCongrByAlts? app alts' altPfs) fun _ => pure none then
      let p ← instantiateMVars (← app.remaining.foldlM (init := p) fun acc a => mkCongrFun acc a)
      return (p, !p.hasMVar)
  let isCasesOn := isCasesOnRecursor (← getEnv) app.matcherName
  let mkM (discrs : Array Expr) (alts : Array Expr) : Expr :=
    mkAppN (mkConst app.matcherName app.matcherLevels.toList) (app.params ++ #[app.motive] ++ discrs ++ alts)
  let p ← mkMatchCasesProof (mkM app.discrs app.alts) (fun xs => pure (mkM xs alts'))
    (fun altIdx args hs _alt rhs => do
      -- `rhs := matcher ps motive pats alts'`
      let alt' := (alts'[altIdx]!).beta args
      let pRhs ← proveMatchAltEq rhs alt' altIdx isCasesOn
      let pRhs ← mkEqSymm pRhs
      match altPfs[altIdx]! with
      | none => return pRhs
      | some p => mkEqTrans (mkAppN p (args ++ hs)) pRhs)
  let p ← app.remaining.foldlM (init := p) fun acc a => mkCongrFun acc a
  let p ← instantiateMVars p
  return (p, !p.hasMVar)

/-- Given the applications `m := matcher ps motive ds alts` and `m' := matcher' ps' motive ds alts` of two matchers with
    the same patterns (e.g., the generated matchers of two functions matching on the same patterns, see
    `Blaster.Optimize.structEqMatch`), return a proof of `m = m'`: a case split over the alternatives of `m`, the `i`-th
    alternative of `m'` being reduced by the `i`-th match equation of `matcher'`. -/
def mkMatchEquivProof (m m' : Expr) : MetaM Expr := do
  let some app ← matchMatcherApp? m | throwError "mkMatchEquivProof: matcher application expected"
  let some app' ← matchMatcherApp? m' | throwError "mkMatchEquivProof: matcher application expected"
  if app.alts.size != app'.alts.size || app.discrs.size != app'.discrs.size || app.remaining != app'.remaining then
    throwError "mkMatchEquivProof: matchers with different alternatives"
  let mkM (discrs : Array Expr) : Expr :=
    mkAppN (mkConst app.matcherName app.matcherLevels.toList) (app.params ++ #[app.motive] ++ discrs ++ app.alts)
  let mkM' (discrs : Array Expr) : Expr :=
    mkAppN (mkConst app'.matcherName app'.matcherLevels.toList) (app'.params ++ #[app'.motive] ++ discrs ++ app'.alts)
  -- extra arguments (i.e., match returning a function) are handled via `congrFun`
  let p ← mkMatchCasesProof (mkM app.discrs) (fun xs => pure (mkM' xs))
    (fun altIdx _ _ alt rhs => do mkEqSymm (← proveMatchAltEq rhs alt altIdx false))
  app.remaining.foldlM (init := p) fun acc a => mkCongrFun acc a

/-- Given `inner := matcher ps motive d₁ ... dₙ alt₁ ... altₖ`, a context `F := fun z => F[z]` and
    `rhs := matcher ps' motive' d₁ ... dₙ alt'₁ ... alt'ₖ` such that each `alt'ᵢ` is definitionally equal to
    `fun args => F[altᵢ args]`, return a proof of `F[inner] = rhs`, i.e., the propagation of `F` over the
    alternatives of `inner` (e.g., `f (match d with alts) = match d with (f ∘ alts)`, case of case).
    Each alternative of `rhs` is justified by the corresponding match equation of `inner`
    (see `mkMatchCasesProof`).
-/
def mkMatchPushProof (F inner rhs : Expr) : MetaM Expr := do
  let some app ← matchMatcherApp? inner (alsoCasesOn := true)
    | throwError "mkMatchPushProof: match application expected"
  if !app.remaining.isEmpty then throwError "mkMatchPushProof: over-applied match"
  let isCasesOn := isCasesOnRecursor (← getEnv) app.matcherName
  let mkInner (discrs : Array Expr) : Expr :=
    mkAppN (mkConst app.matcherName app.matcherLevels.toList) (app.params ++ #[app.motive] ++ discrs ++ app.alts)
  let p ← mkMatchCasesProof rhs (fun xs => pure (F.beta #[mkInner xs]))
    (fun altIdx args hs alt rhsᵢ => do
      -- `rhsᵢ := F[inner[pats]]` with `pats` the patterns of the alternative (see the equalities `hs`)
      let pats ← hs.mapM fun h => do
        let some (_, _, p) := (← inferType h).eq? | throwError "mkMatchPushProof: equality expected"
        return p
      let pInner ← proveMatchAltEq (mkInner pats) (app.alts[altIdx]!.beta args) altIdx isCasesOn
      let p ← mkEqSymm (← mkCongrArg F pInner)
      mkExpectedTypeHint p (← mkEq alt rhsᵢ))
  mkEqSymm p

/-- User name of the equalities between the discriminants and the patterns declared in the local
    context when optimizing a match alternative (see `Blaster.Optimize.optimizeMatchAlt`).
-/
def matchHypName : Name := `h_match

/-- Return the equalities `dⱼ = pⱼ` between the discriminants and the patterns of alternative `altIdx` of the
    match application `f args` (with `numParams` parameters and `numDiscrs` discriminants), instantiated
    with the parameters `params` of the alternative.
    NOTE: The patterns are obtained from the matcher's type and not from the optimized generic instance
    (see `Blaster.Optimize.getMatchAlts`), as the latter may contain optimized patterns that are not
    definitionally equal to the patterns of the matcher (e.g., `Nat.add 1 n` instead of `n + 1`).
-/
def discrPatternEqs? (f : Expr) (args : Array Expr) (numParams numDiscrs altIdx : Nat) (params : Array Expr) :
    MetaM (Option (Array Expr)) := do
  let fType ← instantiateForall (← inferType f) (args.extract 0 numParams)
  Meta.forallTelescope fType fun fvars _ => do
    let some motive := fvars[0]? | return none
    let some altVar := fvars[1 + numDiscrs + altIdx]? | return none
    Meta.forallTelescope (← inferType altVar) fun xs b => do
      if !b.getAppFn.isFVarOf motive.fvarId! then return none
      let lhs := b.getAppArgs
      if xs.size != params.size || lhs.size != numDiscrs then return none
      let mut eqs := #[]
      for j in [0:numDiscrs] do
        let some d := args[numParams + 1 + j]? | return none
        let pattern := (lhs[j]!.replaceFVars xs params).replaceFVar motive args[numParams]!
        let eq ← mkEq d pattern
        Meta.check eq
        eqs := eqs.push eq
      return some eqs

/-- Return a proof of `a = b` given by an equality `h : a = p` (resp. `h : p = a`) between a discriminant and
    a pattern declared in the local context (see `matchHypName`) such that `p` and `b` are definitionally equal,
    i.e., the justification of a discriminant resolved with the equality map of the match context
    (see `Blaster.Optimize.reduceMatch?`).
-/
def matchHypEqProof? (a b : Expr) : MetaM (Option Expr) := do
  for decl in (← getLCtx).decls.toArray.reverse do
    let some decl := decl | continue
    if decl.userName != matchHypName then continue
    let some (_, l, r) := decl.type.eq? | continue
    let p? ←
      if l == a && (r == b || (← isDefEq r b)) then pure (some decl.toExpr)
      else if r == a && (l == b || (← isDefEq l b)) then some <$> mkEqSymm decl.toExpr
      else pure none
    if let some p := p? then
      return some (← mkExpectedTypeHint p (← mkEq a b))
  return none

/-- Given a match application `m := matcher ps motive d₁ ... dₙ alts` and `ds'` the discriminants such that
    each `d'ⱼ` is either `dⱼ` or its value in the match context (see `matchHypEqProof?`), return a proof of
    `m = r` with `r` the alternative to which `matcher ps motive d'₁ ... d'ₙ alts` reduces.
-/
def proveMatchReduction (m : Expr) (ds' : Array Expr) (r : Expr) : MetaM Expr := do
  let some app ← matchMatcherApp? m (alsoCasesOn := true)
    | throwError "proveMatchReduction: match application expected"
  let f := m.getAppFn
  let firstDiscr := app.params.size + 1
  let mut args := m.getAppArgs
  let mut pf? : Option Expr := none
  for h : j in [0:app.discrs.size] do
    let d := app.discrs[j]
    let some d' := ds'[j]? | throwError "proveMatchReduction: missing discriminant"
    if d == d' then continue
    let some h ← matchHypEqProof? d d' | throwError "proveMatchReduction: no equality for discriminant {j}"
    let motive := mkLambda `z .default (← inferType d) (mkAppN f (args.set! (firstDiscr + j) (.bvar 0)))
    let step ← mkCongrArg motive h
    pf? ← match pf? with
          | none => pure (some step)
          | some p => some <$> mkEqTrans p step
    args := args.set! (firstDiscr + j) d'
  let m' := mkAppN f args
  unless ← withTransparency .default (isDefEq m' r) do throwError "proveMatchReduction: not reducible"
  let refl ← mkExpectedTypeHint (← mkEqRefl m') (← mkEq m' r)
  match pf? with
  | none => return refl
  | some p => mkEqTrans p refl

/-- Given a match application `m := matcher ps motive d₁ ... dₙ alts`, replace each discriminant `dⱼ`
    for which an equality `h : dⱼ = pⱼ` is declared in the local context (see `matchHypName`) with `pⱼ`.
    Return the resulting match application `m'` together with a proof of `m = m'` (if `m` is rewritten).
-/
def rewriteDiscrsWithHyps (m : Expr) : MetaM (Expr × Option Expr) := do
  let some app ← matchMatcherApp? m (alsoCasesOn := true) | throwError "rewriteDiscrsWithHyps: match expected"
  let lctx ← getLCtx
  let firstDiscr := app.params.size + 1
  let f := m.getAppFn
  let mut args := m.getAppArgs
  let mut pf := none
  for j in [0:app.discrs.size] do
    let d := app.discrs[j]!
    let some decl := lctx.findDeclRev? (fun decl =>
        if decl.userName == matchHypName && (decl.type.eq?.map (·.2.1 == d)).getD false
        then some decl else none)
      | continue
    let some (_, _, q) := decl.type.eq? | continue
    let motive := mkLambda `z .default (← inferType d) (mkAppN f (args.set! (firstDiscr + j) (.bvar 0)))
    let step ← mkCongrArg motive decl.toExpr
    pf ← match pf with
         | none => pure (some step)
         | some p => some <$> mkEqTrans p step
    args := args.set! (firstDiscr + j) q
  return (mkAppN f args, pf)

/-- Return a proof of `m = rhs` with `m` a match application that reduces to `rhs` (i.e., alternative `altIdx`)
    once its discriminants are replaced with the patterns given by the equalities of the local context.
-/
def proveMatchInContext (m rhs : Expr) (altIdx : Nat) : MetaM Expr := do
  let isCasesOn := isCasesOnRecursor (← getEnv) m.getAppFn.constName!
  let (m', pf) ← rewriteDiscrsWithHyps m
  let p ← proveMatchAltEq m' rhs altIdx isCasesOn
  match pf with
  | none => return p
  | some q => mkEqTrans q p

end Blaster.Reconstruct
