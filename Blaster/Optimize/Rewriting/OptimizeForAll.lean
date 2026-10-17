import Lean
import Blaster.Optimize.Hypotheses

open Lean Meta Elab Blaster.Reconstruct
namespace Blaster.Optimize

/-- `mkImpliesExpr a b` return expression `a → b` without applying any normalization. -/
def mkImpliesExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  return mkForall (← Term.mkFreshBinderName) BinderInfo.default a b

/-- Given `h : a → b`, apply the simplification rules:
      - When `a := True ∧ Type(b) = Prop`:
         - When ¬ fVarInExpr h.fvarId! b:
            - return `some b`
         - When fVarInExpr h.fvarId! b:
            - return `some b[h/True.intro]`
      - When `a := False ∧ Type(b) = Prop`:
          - return `some True`
      - Otherwise
          - return `none`

    TODO: We need to find a way to replace h in body with the proper h in hypothesis.
-/
def isCstImplies? (h : Expr) (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
 if !(← isPropEnv b) then return none
 match a with
 | Expr.const ``True _ =>
     if fVarInExpr h.fvarId! b
     then return (← mkExpr $ Expr.replaceFVar b h (← mkTrueIntro))
     else return b
 | Expr.const ``False _ => return (← mkPropTrue)
 | _ => return none

 /-- Given `a → b`, apply the following normalization rule:
      - When `b := False ∧ Type(a) = Prop`
         - return `some ¬ a`
      - Otherwise
         - return `none`
 -/
 def isNotDef? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  if !(← isPropEnv a) then return none
  match b with
  | Expr.const ``False _ =>
      setRestart
      return mkApp (← mkPropNotOp) a
  | _ => return none

 /-- Given `a → b`, apply the simplification rules:
     - When ∃ e := _ ∈ h, e = ¬ b
        - return `some ¬ a`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ b
        - return `some ¬ a`
     - Otherwise:
        - return `none`
 -/
 def impliesToNeg? (a : Expr) (b : Expr) (h : HypothesisMap) : TranslateEnvT (Option Expr) := do
  let notOp ← mkPropNotOp
  if (← notInHypMap b h).isSome then
    setRestart
    return mkApp notOp a
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  if (← notInHypMap b hyps).isSome then
    setRestart
    return mkApp notOp a
  return none

 /-- Given `a → b`, apply the simplification rules:
     - When ∃ e := _ ∈ h, e = b
        - return `some True`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = b
        - return `some True`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ a
        - return `some True`
     - Otherwise:
        - return `none`
 -/
 def impliesToTrue? (a : Expr) (b : Expr) (h : HypothesisMap) : TranslateEnvT (Option Expr) := do
  if (← inHypMap b h).isSome then return ← mkPropTrue
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  if (← inHypMap b hyps).isSome then return ← mkPropTrue
  if !(← isPropEnv b) then return none
  if (← notInHypMap a hyps).isSome then return ← mkPropTrue
  return none


/-- Given `h : a → b` returns `true` only when the following condition is satisfied:
     - ∃ h : a → b := _ ∈ hypothesisContext.hypothesisMap,
-/
def impliesInHyp (h : Expr) (b : Expr) : TranslateEnvT Bool := do
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  return hyps.contains (← mkForallFVar h b)

/-- Given `h : a → b`, apply the simplification rules:
    - When a := p ∈ hypothesisContext.hypothesisMap ∧ Type(b) = Prop
       - When ¬ fVarInExpr h.fvarId! b
          - return `some b`
       - When fVarInExpr h.fvarId! b
          - return `some b[h/p]
    - Otherwise:
       - return `none`
-/
def hypReduction? (h : Expr) (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
 if !(← isPropEnv b) then return none
 let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
 match (← inHypMap a hyps) with
 | none => return none
 | some p =>
    if !fVarInExpr h.fvarId! b
    then return b
    else return (← mkExpr $ Expr.replaceFVar b h p)

/-- Apply the following simplification/normalized rules on `forallE`.
    Note that implication `a → b` is internally represented as `forallE _ a b bi`.
    The simplification/normalization rules applied are:
      - ∀ (n : t), True | e → True ==> True
      - False → e ==> True (if Type(e) = Prop)
      - h : True → e ==> e (if Type(e) = Prop ∧ ¬ fVarInExpr h.fvarId! e)
      - h : True → e ==> e[h/True.intro] (if Type(e) = Prop ∧ fVarInExpr h.fvarId! e)
            TODO: replace True.intro with proper proof
      - e → False ==> ¬ e
      - e1 → e2 ==> True (if e1 =ₚₜᵣ e2 ∧ Type(e1) = Prop)
      - e1 → e2 ==> True (if ∃ e1 → e2 := _ ∈ hypothesisContext.hypothesisMap)
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ h, e = ¬ e2)
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e2)
      - e1 → e2 ==> True (if e2 := _ ∈ h)
      - e1 → e2 ==> True (if e2 := _ ∈ hypothesisContext.hypothesisMap)
      - e1 → e2 ==> True (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e1 ∧ Type(e2) = Prop)
      - h : e1 → e2 ==> e2 (if e1 := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop)
      - h : e1 → e2 ==> e2[h/h'] (if e1 := h' ∈ hypothesisContext.hypothesisMap ∧ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop )
      - ∀ (n : t), e ===> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ fVarInExpr n.fvarId! e)
  Assume that `n` is a free variable expression. An error is triggered if this is not the case.
  Assume that `h` corresponds to the hypothesis map updated with hypotheses in `t`.
-/
def optimizeForallCore (n : Expr) (t : Expr) (h : HypothesisMap) (b : Expr) : TranslateEnvT Expr := do
  if let Expr.const ``True _ := b then return b
  if let some r ← isCstImplies? n t b then return r
  if let some r ← isNotDef? t b then return r
  if exprEq t b then if ← isPropEnv t then return (← mkPropTrue)
  if (← impliesInHyp n b) then return (← mkPropTrue)
  if let some r ← impliesToNeg? t b h then return r
  if let some r ← impliesToTrue? t b h then return r
  if let some r ← hypReduction? n t b then return r
  if (← (isSortOrInhabited t) <&&> (isPropEnv b) <&&> (pure !fVarInExpr n.fvarId! b)) then return b
  mkForallFVar n b

/-- Same as `optimizeForallCore` but also records the justification of the applied rule
    when tracking proof terms (see `Blaster.Reconstruct`).
-/
def optimizeForall (n : Expr) (t : Expr) (h : HypothesisMap) (b : Expr) : TranslateEnvT Expr := do
  if !(← isTracking) then return ← optimizeForallCore n t h b
  -- record the justification for the applied simplification rule (see `Blaster.Reconstruct`)
  let lhs ← mkForallFVar n b
  let r ← optimizeForallCore n t h b
  if lhs == r then return r
  let isArrow := !fVarInExpr n.fvarId! b
  let isPropBody ← isPropEnv b
  if let Expr.const ``True _ := b then
    return ← withProofM lhs r (return mkApp (mkConst ``forall_true' [← getLevel t]) t)
  if isPropBody then
    match t with
    | Expr.const ``True _ =>
        if isArrow then return ← withThm lhs r ``true_imp_eq #[b]
        return ← withProofM lhs r (return mkApp (mkConst ``forall_true_dep) (← mkLambdaFVars #[n] b))
    | Expr.const ``False _ =>
        return ← withProofM lhs r (return mkApp (mkConst ``false_imp_eq) (← mkLambdaFVars #[n] b))
    | _ => pure ()
  if let Expr.const ``False _ := b then
    if (← isPropEnv t) then return ← withDefEq lhs r -- `a → False` is `¬ a` by definition
  if !isArrow || !isPropBody || !(← isPropEnv t) then
    -- `∀ (n : t), e ===> e` (when t is inhabited)
    if isArrow && isPropBody && exprEq r b then
      return ← withProofM lhs r (mkAppOptM ``forall_const' #[t, none, b])
    return r
  -- non-dependent implication `t → b` between propositions
  if exprEq t b then return ← withThm lhs r ``imp_self_eq #[t]
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  if r.isConstOf ``True then
    if let some p ← inHypMap lhs hyps then return ← withHypThm lhs r lhs p ``eq_true #[lhs]
    if let some p ← inHypMap b h then
      -- hypothesis obtained from `t`
      return ← withProofM lhs r (do
        let p ← mkLambdaFVars #[n] p
        return mkApp2 (mkConst ``eq_true) lhs p)
    if let some p ← inHypMap b hyps then return ← withHypThm lhs r b p ``imp_eq_true_of_right #[t, b]
    if let some p ← notInHypMap t hyps then
      return ← withHypThm lhs r (mkApp (← mkPropNotOp) t) p ``imp_eq_true_of_not_left #[t, b]
    return r
  if let some ne := propNot? r then
    if exprEq ne t then
      if let some p ← notInHypMap b h then
        return ← withProofM lhs r (do
          let p ← mkLambdaFVars #[n] p
          if (← inferType p) != (← mkForallFVar n (mkApp (← mkPropNotOp) b)) then throwError "unexpected hypothesis"
          return mkApp3 (mkConst ``imp_eq_not_of_imp) t b p)
      if let some p ← notInHypMap b hyps then
        return ← withHypThm lhs r (mkApp (← mkPropNotOp) b) p ``imp_eq_not_of #[t, b]
      return r
  if exprEq r b then
    if let some p ← inHypMap t hyps then return ← withHypThm lhs r t p ``imp_eq_of_left #[t, b]
  return r

end Blaster.Optimize
