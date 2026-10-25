import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Rewriting.OptimizeNat
import Blaster.Optimize.Rewriting.OptimizeInt


open Lean Meta Elab Blaster.Reconstruct
namespace Blaster.Optimize


@[always_inline, inline]
def getMatchAlts (args : Array Expr) (mInfo : MatchInfo) : TranslateEnvT (Array Expr) := do
 let genApp ← mkAppRangeExpr mInfo.instApp 0 mInfo.getFirstDiscrPos args
 match (← get).optEnv.memCache.matchAltsCache.get? genApp with
 | some alts => return alts
 | none =>
    let auxApp ← betaLambdaSharedRange mInfo.instApp mInfo.getFirstAltPos args
    let alts ← getLambdaBoundedBinderTypes auxApp mInfo.numAlts
    -- update cache
    updateMatchAltsCache genApp alts
    return alts

/-- Return `true` is p is a nat, integer or string literal expression. -/
def isCstLiteral (p : Expr) : Bool :=
  (isNatValue? p).isSome || (isIntValue? p).isSome || (isStrValue? p).isSome


/-- Only apply NatAdd and IntNeg optimization on match pattern --/
@[always_inline, inline]
def optimizePattern (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  match f with
  | Expr.const ``Nat.add _ => optimizeNatAdd f args
  | Expr.const ``Int.neg _ => optimizeIntNeg f args
  | _ => mkAppNExpr f args

/-- Remove all namedPattern expression in `p` and apply optimizePattern whenever necessary.
    TODO: change function to pure tail rec call using stack-based approach
-/
partial def removeNamedPatternExpr (p : Expr) : TranslateEnvT Expr := do
 match p with
 | Expr.const .. | Expr.lit .. | Expr.fvar .. => return p
 | Expr.app .. =>
      let (f, args) := getAppFnWithArgs p
      match f with
      | Expr.const n _ =>
         if n == ``namedPattern then
           removeNamedPatternExpr args[2]!
         else
           let mut args := args
           let pInfo ← getFunEnvInfo f
           for i in [:args.size] do
             if i < pInfo.paramsInfo.size then
              if pInfo.paramsInfo[i]!.isExplicit then
                args ← args.modifyM i removeNamedPatternExpr
             else
                args ← args.modifyM i removeNamedPatternExpr
           optimizePattern f args
      | _ => throwEnvError "removeNamedPatternExpr: const expression expected but got {reprStr f}"
 | _ => throwEnvError "removeNamedPatternExpr: unexpected pattern expression: {reprStr p}"

/-- Assign `fv` to `v` in the local context s.t.,
     - When fv has a lambda free variable declaration (i.e., LocalDecl.cdecl)
         - replace it with a let free variable declaration (i.e., LocalDecl.ldecl with value set to `v`)
     - When fv is a let free variable declaration only replace the let bind value with `v`
-/
def modifyFVarValue (fv : FVarId) (v : Expr) : TranslateEnvT Unit :=
  modifyOptEnv fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ⟨ctx, localInsts⟩, o14⟩ =>
               ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ⟨ctx.modifyLocalDecl fv declModifier, localInsts⟩, o14⟩

 where
   declModifier (d : LocalDecl) : LocalDecl :=
     match d with
     | LocalDecl.cdecl idx fvarId userName type _ kind =>
        LocalDecl.ldecl idx fvarId userName type v false kind
     | LocalDecl.ldecl idx fvarId userName type _v nonDep kind =>
        LocalDecl.ldecl idx fvarId userName type v nonDep kind

/-- Return `some (C, #[xₖ, ..., xₙ])` when p := `C x₁ ... xₙ` such that:
     - C is a ctor name.
     - x₁ ... xₖ₋₁ correspond to the polymorphic parameters of the corresponding inductive datatype.
-/
def isCtorPattern (p : Expr) : TranslateEnvT (Option (Name × Array Expr)) := do
 match p.getAppFn' with
 | Expr.const n _ =>
     match (← getConstEnvInfo n) with
     | ConstantInfo.ctorInfo info =>
         let args := p.getAppArgs
         return (n, args[info.numParams:args.size].toArray)
     | _ => return none
 | _ => return none

mutual
/-- Special let expression case for parameterized constructors when normalizing a `match` to ite, s.t.,
     Given p = C x₁ ... xₙ and `t`  the match right-hand side expression,
       return `(mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t))))`
     where,
      mkCstLet e t :
       := t             if e = C
       := t             if isIntNatStrCst(e)
       := let n := removeNamedPatternExpr pe in (mkCstLet pe t) if e = namedPattern t n pe h
       := let n := removeNamedPatternExpr pe in (mkCstLet pe t) if e = N + (namedPattern t n pe h) ∧ Type(N) = Nat
       := (mkCstLet pe t)  if e = Int.ofNat pe
       := (mkCstLet pe t)  if e = Int.neg pe
       := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t)))) if e = C x₁ ... xₖ
       := ⊥  otherwise
-/
private partial def mkLetCtors
  (c : Name) (idx : Nat) (args : Array Expr) (t : Expr)
  (k : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  if idx == 0 then
    mkCstLet args[idx]! t k
  else
    mkCstLet args[idx]! t
      fun t' => mkLetCtors c (idx - 1) args t' k

private partial def mkCstLet
   (e : Expr) (t : Expr) (k : Expr → TranslateEnvT Expr) := do
   if isCstLiteral e then return (← k t) -- case: isIntNatStrCst(e)
   match e with
   | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h
   | Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal _)))
      (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h) =>
      -- case: e = namedPattern t n pe h
      -- case: e = N + (namedPattern t n pe h) ∧ Type(N) = Nat
      mkCstLet pe t
        fun t' => do
          modifyFVarValue fv (← removeNamedPatternExpr pe)
          k (← mkLetFVarsExpr #[np] t')

   | Expr.app (Expr.const ``Int.ofNat _) pe
   | Expr.app (Expr.const ``Int.neg _) pe =>
        -- case: e = Int.ofNat pe
        -- case: e = Int.neg pe
        mkCstLet pe t k
   | _ =>
     let some (n, args) ← isCtorPattern e
       | throwEnvError "mkCstLet: unexpected pattern expression: {reprStr e}"
     if args.size == 0 then
       -- case: e = C (i.e., nullary constructor)
       k t
     else mkLetCtors n (args.size - 1) args t k -- case: e = C x₁ ... xₖ

end

/-- Generate the necessary let expressions when normalizing a `match` to ite, s.t.,
    given `e` a match discriminator, `p` its corresponding match expression and
    `t` the match right-hand side expression, `mkLet e p t` is defined as follows:
       := let v := e in t  if p = v
       := t                if p = C (i.e., nullary constructor)
       := t                if isIntNatStrCst(p)
       := let n := e in (mkLet n pe t)  if p = namedPattern s n pe h
       := let n := e - N in t  if p = N + n ∧ Type(N) = Nat
       := let n := e - N in (mkLet n pe t)  if p = N + (namedPattern s n pe h) ∧ Type(N) = Nat
       := let n := Int.toNat e in t         if p = Int.ofNat n
       := let n := Int.toNat e in (mkLet n pe t)  if p = Int.ofNat (namedPattern s n pe t)
       := let n := Int.toNat e - N in t  if p = Int.ofNat (N + n)
       := let n := Int.toNat e - N in (mkLet n pe t)  if p = Int.ofNat (N + namedPattern s n pe h)
       := let n := (Int.toNat (Int.neg e)) - N in t   if p = Int.neg (Int.ofNat (N + n))
       := let n := (Int.toNat (Int.neg e)) - N in (mkLet n pe t)  if p = Int.neg (Int.ofNat (N + namedPattern s n pe h))
       := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t)))) if p = C x₁ ... xₖ
       := ⊥  otherwise
-/
private partial def mkLet
  (e : Expr) (p : Expr) (t : Expr)
  (k : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  if isCstLiteral p then return (← k t) -- case: isIntNatStrCst(p)
  match p with
  | Expr.fvar fv =>
      -- case: p = v
      modifyFVarValue fv e
      k (← mkLetFVarsExpr #[p] t)

  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _s) np@(Expr.fvar fv)) pe) _h =>
      -- case: p := namedPattern s n pe h
      mkLet np pe t
       fun t' => do
         modifyFVarValue fv e
         k (← mkLetFVarsExpr #[np] t')

  | Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) a =>
      let v ← mkApp2Expr (← mkNatSubOp) e n
      match a with
      | Expr.fvar fv =>
          -- case: p = N + n ∧ Type(N) = Nat
          modifyFVarValue fv v
          k (← mkLetFVarsExpr #[a] t)

      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _s) np@(Expr.fvar fv)) pe) _h =>
          mkLet np pe t
            fun t' => do
              modifyFVarValue fv v
              k (← mkLetFVarsExpr #[np] t')

      | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.ofNat _) a =>
       let v ← mkAppExpr (← mkIntToNatOp) e
       match a with
       | Expr.fvar fv =>
            -- case: p = Int.ofNat n
            modifyFVarValue fv v
            k (← mkLetFVarsExpr #[a] t)

       | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h =>
            -- case: p = Int.ofNat (namedPattern s n pe t)
            mkLet np pe t
              fun t' => do
                modifyFVarValue fv v
                k (← mkLetFVarsExpr #[np] t')

       | Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) b =>
           let bv ← mkApp2Expr (← mkNatSubOp) (← mkAppExpr (← mkIntToNatOp) e) n
           match b with
           | Expr.fvar fv =>
               -- case: p = Int.ofNat (N + n)
               modifyFVarValue fv bv
               k (← mkLetFVarsExpr #[b] t)

           | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _s) np@(Expr.fvar fv)) pe) _h =>
               -- case: p = Int.ofNat (N + namedPattern s n pe h)
                mkLet np pe t
                  fun t' => do
                    modifyFVarValue fv bv
                    k (← mkLetFVarsExpr #[np] t')

           | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

       | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.neg _)
      (Expr.app (Expr.const ``Int.ofNat _)
        (Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) a)) =>
      let v ← mkApp2Expr (← mkNatSubOp) (← mkAppExpr (← mkIntToNatOp) (← mkAppExpr (← mkIntNegOp) e)) n
      match a with
      | Expr.fvar fv =>
           -- case: p = Int.neg (Int.ofNat (N + n))
           modifyFVarValue fv v
           k (← mkLetFVarsExpr #[a] t)

      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _s) np@(Expr.fvar fv)) pe) _h =>
           -- case: p = Int.neg (Int.ofNat (N + namedPattern s n pe h))
           mkLet np pe t
             fun t' => do
               modifyFVarValue fv v
               k (← mkLetFVarsExpr #[np] t')

      | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

  | _ =>
     let some (n, args) ← isCtorPattern p
       | throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"
     if args.size == 0 then
       -- case: p = C (i.e., nullary constructor)
       k t
     else
       -- case: p' = C x₁ ... xₖ
       mkLetCtors n (args.size - 1) args t k

/-- Generate the necessary ite condition expressions when normalizing a `match` to ite, such that:
    given `e` a match discriminator and `pp` its corresponding match expression
    for which `p ← removeNamedPatternExpr pp`,
    `mkCond e p` is defined as follows:
       := e = p            if (p ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatStrCst(p)
       := N ≤ e            if p = N + n ∧ Type(N) = Nat
       := Int.ofNat 0 ≤ e  if p = Int.ofNat n
       := Int.ofNat N ≤ e  if p = Int.ofNat (N + n)
       := e ≤ -N           if p = Int.neg (Int.ofNat (N + n))
       := True             if p = v
       := ⊥                otherwise
-/
private def mkCond (e : Expr) (p : Expr) (eType : Expr) (andTerms : Array Expr) : TranslateEnvT (Array Expr) := do
  if !(p.isFVar || (isNatType eType) || (isIntType eType)) || (isCstLiteral p) then
    -- case: (p ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatStrCst(p)
    return andTerms.push (← mkApp3Expr (← mkEqOp) eType p e)
  match p with
  | Expr.fvar _ => return andTerms -- case: p = v

  | Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) (Expr.fvar _fv) =>
     -- case: p = N + n ∧ Type(N) = Nat
     return andTerms.push (← mkAppExpr (← mkPropNotOp) (← mkApp2Expr (← mkNatLtOp) e n))

  | Expr.app (Expr.const ``Int.ofNat _) (Expr.fvar _fv) =>
      -- case: p = Int.ofNat n
      return andTerms.push (← mkAppExpr (← mkPropNotOp) (← mkApp2Expr (← mkIntLtOp) e (← mkIntLitExpr (Int.ofNat 0))))

  | Expr.app (Expr.const ``Int.ofNat _)
     (Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) (Expr.fvar _fv)) =>
      -- case: p = Int.ofNat (N + n)
      return andTerms.push (← mkAppExpr (← mkPropNotOp) (← mkApp2Expr (← mkIntLtOp) e (← mkAppExpr (← mkIntOfNat) n)))

  | Expr.app (Expr.const ``Int.neg _)
    (Expr.app (Expr.const ``Int.ofNat _)
    (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) (Expr.fvar _fv))) =>
      -- case: p = Int.neg (Int.ofNat (N + n))
      return andTerms.push (← mkAppExpr (← mkPropNotOp) (← mkApp2Expr (← mkIntLtOp) (← mkNatNegExpr n) e))

  | _ => throwEnvError "mkCond: unexpected pattern: {reprStr p}"

/- Return `true` only when `e` corresponds to an optimized Int/Nat const literal.
   Assumes that `e` corresponds to a pattern match.
-/
def isIntNatPatternExpr (e : Expr) : TranslateEnvT Bool := do
 match e.getAppFn' with
 | Expr.const ``Int.ofNat _
 | Expr.const ``Int.neg _
 | Expr.lit (Literal.natVal _)
 | Expr.const ``Nat.add _ => return true
 | fv@(Expr.fvar _) => do
       let t ← inferTypeEnv fv
       return (isNatType t || isIntType t)
 | _ => return false

partial def patternHasFVar (p : Expr) : TranslateEnvT Bool := do
 let rec visit (e : Expr) : TranslateEnvT Bool := do
   match e with
   | Expr.fvar .. => return true
   | Expr.app .. =>
      let (f, args) := getAppFnWithArgs e
      match e.getAppFn with
      | Expr.const n _ =>
         -- constructor application
         match (← getConstEnvInfo n) with
         | ConstantInfo.ctorInfo info =>
             -- constructor application
             let args := e.getAppArgs
             let ctorArgs := args[info.numParams:args.size]
             for h : i in [:ctorArgs.size] do
               if ← visit ctorArgs[i] then return true
             return false
         | _ =>
             for h : i in [:args.size] do
               if ← visit args[i] then return true
             return false
      | _ => throwEnvError "retrieveAltsArgs: const expression expected but got {reprStr f}"
   | _ => return false
 visit p

/-- Is the accumulator `rewriter` function to be used with `matchExprRewriter` when attempting
    to normalize a `match` expression to `if-then-else` (see `normMatchExpr?`).
    Asssumes that matchType := λ β₁ => ... => βₘ
-/
def normMatchExprAux?
  (lastPattern : Bool) (mInfo : MatchInfo) (margs : Array Expr)
  (lhs : Array Expr) (rhs : Expr) (params : Array Expr)
  (acc : Option Expr) : TranslateEnvT (Option Expr) := do
  let plhs ← removeNamedPatterns lhs
  if !(← isItePattern plhs) then return none
  -- NOTE: when tracking proof terms, the equations of the discriminants (i.e., `h : d = p` for `match h : d with`)
  -- are still free variables of `params` (see `matchExprRewriter`)
  let heqs ← heqParams
  if lastPattern then
    let rhs ← betaLambdaShared rhs (← reflHeqs params heqs)
    return some (← mkRhs lhs rhs (lastPattern := true)) -- last pattern
  let some elseExpr := acc | return acc
  let rhs ← betaLambdaShared rhs params
  mkIte lhs plhs rhs elseExpr heqs

 where

   /-- The positions in `params` of the equations of the discriminants, together with the discriminants and their
       types (see `assignEqRefl`).
       NOTE: the parameters of the alternatives and the discriminants are free variables of the optimizer's local
       context (see `withLocalContext`).
   -/
   heqParams : TranslateEnvT (Array (Nat × Expr × Expr)) := do
     if !(← isTracking) then return #[]
     let discrsType ← getLambdaBinderTypes margs[mInfo.getFirstDiscrPos - 1]!
     let mut heqs := #[]
     let mut nbHeq := 0
     for i in [:mInfo.discrInfos.size] do
       let idxDiscr := mInfo.discrInfos.size - i - 1
       if (mInfo.discrInfos[idxDiscr]!).hName?.isSome then
         nbHeq := nbHeq + 1
         if nbHeq ≤ params.size && params[params.size - nbHeq]!.isFVar then
           heqs := heqs.push (params.size - nbHeq, margs[mInfo.getFirstDiscrPos + idxDiscr]!, discrsType[idxDiscr]!)
     return heqs

   /-- `Eq.refl d` for each equation `h : d = p` of the discriminants (see `assignEqRefl`). -/
   reflHeqs (params : Array Expr) (heqs : Array (Nat × Expr × Expr)) : TranslateEnvT (Array Expr) := do
     let mut params := params
     for (j, d, dType) in heqs do
       params := params.set! j (← mkApp2Expr (← mkEqRefl [← getLevelEnv dType]) dType d)
     return params

   /-- Replace each equation `h : d = p` of the discriminants occurring in `e` with its proof from the conjuncts
       `cs` (proof and type) of the condition of the branch (e.g., `h.1 : x = 2` for `h : x = 2 ∧ y = 1`), or with
       `Eq.refl d` when no conjunct proves it (e.g., a pattern with variables). Unlike `Eq.refl d`, which only has
       the expected type `d = p` once `d` is rewritten to `p`, the proofs keep the branch well-typed.
   -/
   proveHeqs (e : Expr) (heqs : Array (Nat × Expr × Expr)) (cs : Array (Expr × Expr)) : TranslateEnvT Expr := do
     let mut fvars := #[]
     let mut proofs := #[]
     for (j, d, dType) in heqs do
       let hq := params[j]!
       let lvl ← getLevelEnv dType
       let refl ← mkApp2Expr (← mkEqRefl [lvl]) dType d
       let ty ← inferTypeEnv hq
       -- NOTE: the pattern variables are bound in the branch (see `mkRhs`)
       let hasPatternVar := (ty.find? fun s => s.isFVar && params.contains s).isSome
       let mut pf? := none
       if !hasPatternVar then
         for (c, ct) in cs do
           let some (α, a, b) := ct.eq? | continue
           let same (t : Expr) : TranslateEnvT Bool := do
             try withLocalContext (withNewMCtxDepth (isDefEq t ty)) catch _ => pure false
           if ← same ct then pf? := some c; break
           if ← same (mkApp3 (mkConst ``Eq [lvl]) α b a) then
             pf? := some (mkApp4 (mkConst ``Eq.symm [lvl]) α a b c); break
       fvars := fvars.push hq
       proofs := proofs.push (pf?.getD refl)
     hashcons (e.replaceFVars fvars proofs)

   removeNamedPatterns (lhs : Array Expr) : TranslateEnvT (Array Expr) := do
     let mut plhs := Array.emptyWithCapacity lhs.size
     for h : i in [:lhs.size] do
       plhs := plhs.push (← removeNamedPatternExpr lhs[i])
     return plhs

   /-- Return `true` only when the "match" normalization condition is satisfied, i.e,:
        - ∀ i ∈ [1..m], ∀ j ∈ [1..n], ( NoFreeVar(p₍ᵢ₎₍ⱼ₎) ∨ p₍ᵢ₎₍ⱼ₎ = v ∨ isIntNatStrCst(p₍ᵢ₎₍ⱼ₎) ∨ Type(eⱼ) ∈ {Nat, Int} )
   -/
   isItePattern (plhs : Array Expr) : TranslateEnvT Bool := do
     for h : i in [:plhs.size] do
       let p := plhs[i]
       if (← patternHasFVar p) && !p.isFVar && !(isCstLiteral p) && !(← isIntNatPatternExpr p)
       then return false
     return true

   replaceDiscrInLastRhs (lastPattern : Bool) (discr : Expr) (pattern : Expr) (rhs : Expr) : TranslateEnvT Expr := do
     if lastPattern then
       let pattern' ← removeNamedPatternExpr pattern
       if (← isCtorExpr discr.getAppFn') || pattern'.isFVar
       then return rhs
       else replaceShared rhs (λ a => do if exprEq a discr then return pattern' else return none) (resolveMVars := true)
     else return rhs

   mkRhs (lhs : Array Expr) (rhs : Expr) (lastPattern := false) : TranslateEnvT Expr := do
    let mut mrhs := rhs
    let nbPatterns := lhs.size
    for i in [:nbPatterns] do
      let idx := nbPatterns - i - 1
      let pattern := lhs[idx]!
      let discr := margs[mInfo.getFirstDiscrPos + idx]!
      mrhs ← replaceDiscrInLastRhs lastPattern discr pattern mrhs
      mrhs ← mkLet discr lhs[idx]! mrhs (λ x => return x)
    return mrhs

   mkIte (lhs : Array Expr) (plhs: Array Expr) (rhs : Expr) (elseExpr : Expr) (heqs : Array (Nat × Expr × Expr)) :
     TranslateEnvT (Option Expr) := do
     let matchType := margs[mInfo.getFirstDiscrPos - 1]!
     let discrsType ← getLambdaBinderTypes matchType
     let thenExpr ← mkRhs lhs rhs
     let mut andTerms := (#[] : Array Expr)
     for h : i in [:plhs.size] do
       andTerms ← mkCond margs[mInfo.getFirstDiscrPos + i]! plhs[i] discrsType[i]! andTerms
     let nbCond := andTerms.size
     if nbCond == 0 then -- case when else unreachable (i.e., renaming pattern redundant)
       return ← if heqs.isEmpty then pure thenExpr else proveHeqs thenExpr heqs #[]
     let mut condTerm := andTerms[nbCond-1]!
     let andOp ← mkPropAndOp
     for i in [1:nbCond] do
       let idx := nbCond - i - 1
       condTerm ← mkApp2Expr andOp andTerms[idx]! condTerm
     let hName ← Term.mkFreshBinderName
     let lam1 ←
       if heqs.isEmpty then mkLambdaExpr hName BinderInfo.default condTerm thenExpr
       else withLocalDecl' hName BinderInfo.default condTerm fun h => do
         -- the proofs of the conjuncts of the condition (i.e., `andTerms[0] ∧ (andTerms[1] ∧ ...)`)
         let mut cs := #[]
         let mut cur := h
         let mut curType := condTerm
         for i in [:nbCond] do
           if i + 1 == nbCond then cs := cs.push (cur, andTerms[i]!)
           else
             let rest := curType.appArg!
             cs := cs.push (mkApp3 (mkConst ``And.left) andTerms[i]! rest cur, andTerms[i]!)
             cur := mkApp3 (mkConst ``And.right) andTerms[i]! rest cur
             curType := rest
         let thenExpr ← proveHeqs thenExpr heqs cs
         mkLambdaExpr hName BinderInfo.default condTerm (thenExpr.abstract #[h])
     let notCond ← mkAppExpr (← mkPropNotOp) condTerm
     let lam2 ← mkLambdaExpr hName BinderInfo.default notCond elseExpr
     mkBlasterDIteApp (getLambdaBody matchType) condTerm lam1 lam2

/-- Instantiating Heq match equation in provided rhs parameters  -/
partial def assignEqRefl (mInfo : MatchInfo) (rhs_params : Array Expr) (margs : Array Expr) : TranslateEnvT (Array Expr) := do
  let discrsType ← getLambdaBinderTypes margs[mInfo.getFirstDiscrPos - 1]!
  let rec visit (idx : Nat) (stop : Nat) (nbHeq : Nat) (xs : Array Expr) : TranslateEnvT (Array Expr) := do
    if idx < stop then return xs
    else
      let idxDiscr := idx - mInfo.getFirstDiscrPos
      if (mInfo.discrInfos[idxDiscr]!).hName?.isSome then
        -- assign mvars to mkEqRefl
        let dType := discrsType[idxDiscr]!
        let lvl ← getLevelEnv dType
        let nbHeq := nbHeq + 1
        let idxMVar := xs.size - nbHeq
        visit (idx - 1) stop nbHeq (xs.set! idxMVar (← mkApp2Expr (← mkEqRefl [lvl]) dType margs[idx]!))
      else
        visit (idx - 1) stop nbHeq xs
   -- traverse discrs in reverse order to properly set heq
   visit (mInfo.getFirstAltPos - 1) mInfo.getFirstDiscrPos 0 rhs_params

/-- A generic match expression rewriter that given a `MatchInfo` instance representing a match application,
    apply the `rewriter` function on each match pattern. The `rewriter` function
    is applied from the last match pattern to the first one.
    Concretely, given a match expression of the form:
      match e₁, ..., eₙ with
      | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
      ...
      | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

   `matchExprRewriter` return the following evaluation:
     rewriter m-1 [e₁, ..., eₙ] [p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎] t₁ matchType
       ...
       (rewriter 1 [e₁, ..., eₙ] [p₍ₘ₋₁₎₍₁₎, ..., p₍ₘ₋₁₎₍ₙ₎] tₘ₋₁ matchType
         (rewriter 0 [e₁, ..., eₙ] [p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎] tₘ matchType none))
   where,
     - matchType := args[mInfo.getFirstDiscrPos - 1]!
     - the first application is passed the `none` accumulator
     - the `Nat` argument corresponding to the traversed index, starting with 0.
   NOTE: The evaluation stops when at least one of the `rewriter` invocation return `none`.
   NOTE: The equations of the discriminants (i.e., `h : d = p` for `match h : d with`) are passed to `rewriter` as
   `Eq.refl d`, unless `keepHeq` is set, in which case they are left as free variables, to be eliminated by `rewriter`.
-/
@[specialize]
def matchExprRewriter
    (mInfo : MatchInfo) (args : Array Expr)
    (rewriter : Bool → MatchInfo → Array Expr → Array Expr → Expr → Array Expr → Option α → TranslateEnvT (Option α))
    (keepHeq := false) :
    TranslateEnvT (Option α) := do
    commonMatchRewriter args (← getMatchAlts args mInfo)

  where
    commonMatchRewriter (margs : Array Expr) (alts : Array Expr) : TranslateEnvT (Option α) := do
      let mut accExpr := (none : Option α)
      -- traverse in reverse order to handle last pattern first
      let nbAlts := alts.size
      for i in [:nbAlts] do
        let idx := nbAlts - i - 1
        accExpr ←
          forallTelescope alts[idx]! fun xs b => do
            let mut lhs := b.getAppArgs
            -- trace[Optimize.normMatch.pattern] "match patterns to optimize {reprStr lhs}"
            -- NOTE: lhs is now implicitly normalized when computing MatchInfo
            let xs ← if keepHeq then pure xs else assignEqRefl mInfo xs margs
            rewriter (i == 0) mInfo margs lhs args[mInfo.getFirstAltPos + idx]! xs accExpr
        unless (accExpr.isSome) do return accExpr -- break if accExpr is still none
      return accExpr


/-- Normalize a `match` expression to `if-then-else` only when each match pattern is either
      - an constructor application that does not contain any free variables (e.g., `Nat.zero`, `some Nat.zero`, `List.const 0 (List.nil)`); or
      - a `Nat`, `Int` or `String` literal; or
      - a `Nat` or `Int` expression; or
      - a free variable `v`

    Concretely:
      match e₁, ..., eₙ with
      | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
      ...
      | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
     ===>
       sif h1 : (mkCond e₁ p₍₁₎₍₁₎) ∧ ... ∧ (mkCond eₙ p₍₁₎₍ₙ₎) then (mkRhs [e₁ ... eₙ] [p₍₁₎₍₁₎ ... p₍₁₎₍ₙ₎] t₁)
       else sif h2 : (mkCond e₁ p₍₂₎₍₁₎) ∧ ... ∧ (mkCond eₙ p₍₂₎₍ₙ₎) then (mkRhs [e₁ ... eₙ] [p₍₂₎₍₁₎ ... p₍₂₎₍ₙ₎] t₂)
       ...
       else (mkRhs [e₁ ... eₙ] [p₍ₘ₎₍₁₎ ... p₍ₘ₎₍ₙ₎] tₘ)
     when:
       - ∀ i ∈ [1..m], ∀ j ∈ [1..n],
           ( NoFreeVar(p₍ᵢ₎₍ⱼ₎) ∨ p₍ᵢ₎₍ⱼ₎ = v ∨ isIntNatStrCst(p₍ᵢ₎₍ⱼ₎) ∨ Type(eⱼ) ∈ {Nat, Int} )
     with:
       - mkCond e p :
          let p' ← removeNamedPatternExpr p;
           := e = p'           if (p ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatStrCst(p)
           := N ≤ e            if p' = N + n ∧ Type(N) = Nat
           := Int.ofNat 0 ≤ e  if p' = Int.ofNat n
           := (Int.ofNat N ≤ e if p' = Int.ofNat (N + n)
           := e ≤ -N           if p' = Int.neg (Int.ofNat (N + n))
           := True             if p' = v
           := ⊥                otherwise

       - mkRhs [e₁ ... eₙ] [p₁ ... pₙ] t :
           := (mkLet e₁ p₁ ( ... (mkLet eₙ₋₁ ₙ₋₁ (mkLet eₙ pₙ t))))

       - mkLet e p t :
          let t' := t[e/p']   if (isIntNatStrCst(p') ∨ isCtorPattern p') with p' ← (removeNamedPatternExpr p)
                 := t         otherwise
           := let v := e in t'  if p = v
           := t'                if p = C (i.e., nullary constructor)
           := t'                if isIntNatStrCst(p)
           := let n := e in (mkLet n pe t')  if p = namedPattern t n pe h ∧ ¬ isIntNatStrCst(pe') ∧
                                               ( Type(eⱼ) ∈ {Nat, Int} ∨ ¬ isCtorPattern pe' )
                                             with pe' ← (removeNamedPatternExpr pe)
           := let n := pe' in (mkCstLet pe t')  if p = namedPattern t n pe h ∧
                                                   (isIntNatStrCst(pe') ∨ (Type(eⱼ) ∉ {Nat, Int} ∧ isCtorPattern pe'))
                                                with pe' ← (removeNamedPatternExpr pe)
           := let n := e - N in t'  if p = N + n ∧ Type(N) = Nat
           := let n := e - N in (mkLet n pe t')  if p = N + (namedPattern t n pe h) ∧ Type(N) = Nat ∧ ¬ isIntNatStrCst(pe')
                                                 with pe' ← (removeNamedPatternExpr pe)
           := let n := pe' in (mkCstLet pe t')  if p = N + (namedPattern t n pe h) ∧ Type(N) = Nat ∧ isIntNatStrCst(pe')
                                                with pe' ← (removeNamedPatternExpr pe)
           := let n := Int.toNat e in t'        if p = Int.ofNat n
           := let n := Int.toNat e in (mkLet n pe t')  if p = Int.ofNat (namedPattern t n pe t) ∧ ¬ isIntNatStrCst(pe')
                                                       with pe' ← (removeNamedPatternExpr pe)
           := let n := pe' in (mkCstLet pe t')  if p = Int.ofNat (namedPattern t n pe t) ∧ isIntNatStrCst(pe')
                                                with pe' ← (removeNamedPatternExpr pe)
           := let n := Int.toNat e - N in t'  if p = Int.ofNat (N + n)
           := let n := Int.toNat e - N in (mkLet n pe t')  if p = Int.ofNat (N + namedPattern t n pe h) ∧ ¬ isIntNatStrCst(pe')
                                                           with pe' ← (removeNamedPatternExpr pe)
           := let n := pe' in (mkCstLet pe t')  if p = Int.ofNat (N + namedPattern t n pe h) ∧ isIntNatStrCst(pe')
                                                with pe' ← (removeNamedPatternExpr pe)
           := let n := (Int.toNat (Int.neg e)) - N in t'   if p = Int.neg (Int.ofNat (N + n))
           := let n := (Int.toNat (Int.neg e)) - N in (mkLet n pe t')  if p = Int.neg (Int.ofNat (N + namedPattern t n pe h)) ∧
                                                                          ¬ isIntNatStrCst(pe')
                                                                       with pe' ← (removeNamedPatternExpr pe)
           := let n := pe' in (mkCstLet n pe t')  if p = Int.neg (Int.ofNat (N + namedPattern t n pe h)) ∧ isIntNatStrCst(pe')
                                                  with pe' ← (removeNamedPatternExpr pe)
           := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t')))) if p = C x₁ ... xₖ
           := ⊥  otherwise

       - mkCstLet e t :
           := t             if e = C
           := t             if isIntNatStrCst(e)
           := let n := removeNamedPatternExpr pe in (mkCstLet pe t) if e = namedPattern t n pe h
           := let n := removeNamedPatternExpr pe in (mkCstLet pe t) if e = N + (namedPattern t n pe h) ∧ Type(N) = Nat
           := (mkCstLet pe t)  if e = Int.ofNat pe
           := (mkCstLet pe t)  if e = Int.neg pe
           := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t)))) if e = C x₁ ... xₖ
           := ⊥  otherwise
-/
def normMatchExpr? (args : Array Expr) (mInfo : MatchInfo) : TranslateEnvT (Option Expr) := do
  match (← get).optEnv.memCache.isMatchToIte.get? mInfo.name with
  | some b => if b then matchExprRewriter mInfo args normMatchExprAux? (keepHeq := ← isTracking)
                   else return none
  | none =>
      let r ← matchExprRewriter mInfo args normMatchExprAux? (keepHeq := ← isTracking)
      updateMatchToIteCache mInfo.name r.isSome
      return r

initialize
  registerTraceClass `Optimize.normMatch.pattern

end Blaster.Optimize
