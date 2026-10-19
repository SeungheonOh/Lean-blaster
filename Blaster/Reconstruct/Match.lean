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

/-- Matchers for which the generation of the match equations and splitter failed. -/
initialize matchEqnsFailures : IO.Ref NameSet ← IO.mkRef {}

/-- Same as `Lean.Meta.Match.getEquationsFor` but return `none` when the match equations cannot be
    generated (e.g., heartbeats exhausted on matchers with many overlapping patterns).
    NOTE: The generation is performed via `realizeConst`, which reports failures as messages.
    Such messages are discarded, as they do not affect the validity of the reconstructed proof.
-/
def getEquationsFor? (n : Name) : MetaM (Option Match.MatchEqns) := do
  if (← matchEqnsFailures.get).contains n then return none
  let tasks := (← getThe Core.State).snapshotTasks
  let msgs := (← getThe Core.State).messages
  tryCatchRuntimeEx (some <$> Match.getEquationsFor n) fun _ => do
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
        if ← isDefEq lhs m <&&> isDefEq rhs alt then
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
  let app' ← app.transform (useSplitter := true) (addEqualities := true)
    (onMotive := fun xs _ => do liftMetaM (mkEq (mkM xs) (← rhsFn xs)))
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

/-- Given evidence for each alternative of a match application `m := matcher ps motive ds alts`,
    return a proof of `m = matcher ps motive ds alts'`. The evidence `altPfs[i]` for alternative `i` is:
      - `none` when `altᵢ` and `alt'ᵢ` are definitionally equal;
      - `some p` with `p : ∀ args (h₁ : d₁ = pᵢ₁) ... (hₙ : dₙ = pᵢₙ), altᵢ args = alt'ᵢ args`.
-/
def mkMatchCongr (m : Expr) (alts' : Array Expr) (altPfs : Array (Option Expr)) : MetaM Expr := do
  let some app ← matchMatcherApp? m (alsoCasesOn := true)
    | throwError "mkMatchCongr: match application expected"
  let isCasesOn := isCasesOnRecursor (← getEnv) app.matcherName
  let mkM (discrs : Array Expr) (alts : Array Expr) : Expr :=
    mkAppN (mkConst app.matcherName app.matcherLevels.toList) (app.params ++ #[app.motive] ++ discrs ++ alts)
  -- extra arguments (i.e., match returning a function) are handled via `congrFun`
  let p ← mkMatchCasesProof (mkM app.discrs app.alts) (fun xs => pure (mkM xs alts'))
    (fun altIdx args hs _alt rhs => do
      -- `rhs := matcher ps motive pats alts'`
      let alt' := (alts'[altIdx]!).beta args
      let pRhs ← proveMatchAltEq rhs alt' altIdx isCasesOn
      let pRhs ← mkEqSymm pRhs
      match altPfs[altIdx]! with
      | none => return pRhs
      | some p => mkEqTrans (mkAppN p (args ++ hs)) pRhs)
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
