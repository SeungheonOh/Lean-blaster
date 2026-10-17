import Lean
import Blaster.Optimize.Rewriting.OptimizeForAll

open Lean Meta Blaster.Reconstruct
namespace Blaster.Optimize

 /-- Given `a` and `b` the operands for `And`, apply the simplification rules:
     - When a := _ ∈ hypothesisContext.hypothesisMap,
        - return `some b`
     - When b := _ ∈ hypothesisContext.hypothesisMap,
        - return `some a`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ a
        - return `some False`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ b
        - return `some False`
     - Otherwise:
        - return `none`
 -/
 def andPropReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  let lhs := mkApp2 (← mkPropAndOp) a b
  if let some h ← inHypMap a hyps then
    if let some h ← hypProof? a h then return ← withThm lhs b ``and_eq_right_of #[a, b, h]
    return b
  if let some h ← inHypMap b hyps then
    if let some h ← hypProof? b h then return ← withThm lhs a ``and_eq_left_of #[a, b, h]
    return a
  if (← notInHypMap a hyps).isSome then return (← mkPropFalse)
  if (← notInHypMap b hyps).isSome then return (← mkPropFalse)
  return none


/-- Apply the following simplification/normalization rules on `And` :
     - False ∧ e ==> False
     - True ∧ e ==> e
     - e1 ∧ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∧ ¬ e ==> False
     - true = e ∧ false = e ==> False
     - e1 ∧ (e1 → e2) ==> e1 ∧ e2 (if ¬ e2.hasLooseBVars)
     - e1 ∧ (e2 → e1) ==> e1
     - (e1 → e2) ∧ (¬ e1 → e2) ==> e2
     - e1 ∧ e2 ==> e2 (if e1 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 ∧ e2 ==> e1 (if e2 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 ∧ e2 ==> False (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e1)
     - e1 ∧ e2 ==> False (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e2)
     - e1 ∧ e2 ==> e2 ∧ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``And.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `And` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeAnd: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 let lhs := mkApp2 f op1 op2
 if let Expr.const ``False _  := op1 then return ← withThm lhs op1 ``false_and' #[op2]
 if let Expr.const ``True _ := op1 then return ← withThm lhs op2 ``true_and' #[op2]
 if exprEq op1 op2 then return ← withThm lhs op1 ``and_self' #[op1]
 if isNotExprOf op2 op1 then return ← withThm lhs (← mkPropFalse) ``and_not_self' #[op1]
 if isNegBoolEqOf op2 op1 then
   let some (_, _, c) := eq? op1 | return ← mkPropFalse
   return ← withThm lhs (← mkPropFalse) ``and_bool_neg #[c]
 if let some r ← andImpliesReduce? op1 op2 then return r
 if let some r ← andPropReduction? op1 op2 then return r
 -- no caching at this level as optimizeAnd is called by optimizeBoolPropAnd
 return mkApp2 f op1 op2

 where
   /-- Given `a` and `b` the operands for `And`, apply the simplification rules:
       - When `b := a → c ∧ ¬ c.hasLooseBVars`
          - return `some a ∧ c`
       - When `b := c → a`
          - return `some a`
       - When `a := c → d ∧ b := ¬ c → d`
          - return `some d`
       - Otherwise:
         - return `none`
   -/
   andImpliesReduce? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
     let lhs := mkApp2 f a b
     match b with
     | Expr.forallE _ t1 c1 _ =>
         if exprEq t1 a && !(c1.hasLooseBVars) then
           setRestart
           return ← withThm lhs (mkApp2 f a c1) ``and_imp_self #[a, c1]
         if exprEq c1 a then
           -- no need to restart here
           if !b.isArrow then return a
           return ← withThm lhs a ``and_imp_left #[a, t1]
         match a with
         | Expr.forallE _ t2 c2 _ =>
            if !(exprEq c1 c2) then return none
            let not_t2 ← optimizeNot (← mkPropNotOp) (cacheResult := false) #[t2]
            if t1 == not_t2 then
              -- no need to restart here
              if a.isArrow && b.isArrow && t1 == mkApp (← mkPropNotOp) t2 then
                return ← withThm lhs c1 ``imp_and_not_imp #[t2, c1]
              return c1
            else return none
         | _ => return none
     | _ => return none

 /-- Given `a` and `b` the operands for `Or`, apply the simplification rules:
     - When a := _ ∈ hypothesisContext.hypothesisMap,
        - return `some True`
     - When b := _ ∈ hypothesisContext.hypothesisMap,
        - return `some True`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ a
        - return `some b`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ b
        - return `some a`
     - Otherwise:
        - return `none`
 -/
 def orPropReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  let lhs := mkApp2 (← mkPropOrOp) a b
  if let some h ← inHypMap a hyps then
    if let some h ← hypProof? a h then return ← withThm lhs (← mkPropTrue) ``or_eq_true_of_left #[a, b, h]
    return (← mkPropTrue)
  if let some h ← inHypMap b hyps then
    if let some h ← hypProof? b h then return ← withThm lhs (← mkPropTrue) ``or_eq_true_of_right #[a, b, h]
    return (← mkPropTrue)
  if (← notInHypMap a hyps).isSome then return b
  if (← notInHypMap b hyps).isSome then return a
  return none


/-- Given `a` and `b` the operands for `Or`, apply the simplification rules:
    - When `b := a → c`
       - return `some True`
    - When `b := c → a`
       - return `some b`
    - Otherwise:
      - return `none`
-/
def orImpliesReduce? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let lhs := mkApp2 (← mkPropOrOp) a b
  match b with
  | Expr.forallE _ t c _ =>
      if !b.isArrow then
        if exprEq t a then return (← mkPropTrue)
        if exprEq c a then return b
        return none
      if exprEq t a then return ← withThm lhs (← mkPropTrue) ``or_imp_self #[a, c]
      if exprEq c a then return ← withThm lhs b ``or_imp_left #[a, t]
      return none
  | _ => return none

/-- Apply the following simplification/normalization rules on `Or` :
     - False ∨ e ==> e
     - True ∨ e ==> True
     - e1 ∨ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∨ ¬ e ==> True (classical)
     - true = e ∨ false = e ==> True
     - e1 ∨ (e1 → e2) ==> True
     - e1 ∨ (e2 → e1) ==> (e2 → e1)
     - e1 ∨ e2 ==> True (if e1 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 ∨ e2 ==> True (if e2 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 ∨ e2 ==> e2 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e1)
     - e1 ∨ e2 ==> e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e2)
     - e1 ∨ e2 ==> e2 ∨ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``Or.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Or` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeOr: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 let lhs := mkApp2 f op1 op2
 if let Expr.const ``False _ := op1 then return ← withThm lhs op2 ``false_or' #[op2]
 if let Expr.const ``True _ := op1 then return ← withThm lhs op1 ``true_or' #[op2]
 if exprEq op1 op2 then return ← withThm lhs op1 ``or_self' #[op1]
 if isNotExprOf op2 op1 then return ← withThm lhs (← mkPropTrue) ``or_not_self' #[op1]
 if isNegBoolEqOf op2 op1 then
   let some (_, _, c) := eq? op1 | return (← mkPropTrue)
   return ← withThm lhs (← mkPropTrue) ``or_bool_neg #[c]
 if let some r ← orImpliesReduce? op1 op2 then return r
 if let some r ← orPropReduction? op1 op2 then return r
 -- no caching at this level as optimizeOr is called by optimizeBoolPropOr
 return mkApp2 f op1 op2


/-- Normalize `p ↔ p` to `p → q ∧ p → q`
    An error is triggered when args.size ≠ 2 (i.e., only fully applied `↔` expected at this stage)
-/
def optimizeIff (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIff: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 setRestart
 let r := mkApp2 (← mkPropAndOp) (← mkImpliesExpr op1 op2) (← mkImpliesExpr op2 op1)
 withThm (mkApp2 (mkConst ``Iff) op1 op2) r ``iff_eq_and_imp #[op1, op2]

end Blaster.Optimize
