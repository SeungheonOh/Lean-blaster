import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Env


open Lean Meta Blaster.Reconstruct
namespace Blaster.Optimize

 /-- Given `a` and `b` the operands for `and`, apply the simplification rules:
     - When true = a := _ ∈ hypothesisContext.hypothesisMap,
        - return `some b`
     - When true = b := _ ∈ hypothesisContext.hypothesisMap,
        - return `some a`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = a
        - return `some false`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = b
        - return `some false`
     - Otherwise:
        - return `none`
 -/
 def andBoolReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let lhs ← mkApp2Expr (← mkBoolAndOp) a b
  if let some h ← hypMapFind? (← mkEqBool a true) then
    return ← withHypThm lhs b (← mkEqBool a true) h ``bool_and_eq_right_of #[a, b]
  if let some h ← hypMapFind? (← mkEqBool b true) then
    return ← withHypThm lhs a (← mkEqBool b true) h ``bool_and_eq_left_of #[a, b]
  if let some h ← hypMapFind? (← mkEqBool a false) then
    return ← withHypThm lhs (← mkBoolFalse) (← mkEqBool a false) h ``bool_and_eq_false_of_left #[a, b]
  -- NOTE: `false` (and not `False`) is expected as result of `&&`.
  if let some h ← hypMapFind? (← mkEqBool b false) then
    return ← withHypThm lhs (← mkBoolFalse) (← mkEqBool b false) h ``bool_and_eq_false_of_right #[a, b]
  return none

/-- Apply the following simplification/normalization rules on `and` :
     - false && e ==> false
     - true && e ==> e
     - e && not e ==> false
     - e1 && e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 && e2 ===> e2 (if true = e1 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 && e2 ===> e1 (if true = e2 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 && e2 ===> false (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e1)
     - e1 && e2 ===> false (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e2)
     - e1 && e2 ==> e2 && e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``and.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `and` expected at this stage)

   TODO: reordering on list of `&&` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
   TODO: consider additional simplification rules
-/
def optimizeBoolAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeBoolAnd: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 let lhs ← mkApp2Expr f op1 op2
 if let Expr.const ``false _ := op1 then return ← withThm lhs op1 ``bool_false_and #[op2]
 if let Expr.const ``true _ := op1 then return ← withThm lhs op2 ``bool_true_and #[op2]
 if exprEq op1 op2 then return ← withThm lhs op1 ``bool_and_self #[op1]
 if isBoolNotExprOf op2 op1 then return ← withThm lhs (← mkBoolFalse) ``bool_and_not_self #[op1]
 if let some r ← andBoolReduction? op1 op2 then return r
 -- no caching at this level as optimizeBoolAnd is called by optimizeDecideBoolAnd
 mkApp2Expr f op1 op2

 /-- Given `a` and `b` the operands for `or`, apply the simplification rules:
     - When true = a := _ ∈ hypothesisContext.hypothesisMap,
        - return `some true`
     - When true = b := _ ∈ hypothesisContext.hypothesisMap,
        - return `some true`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = a
        - return `some b`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = b
        - return `some a`
     - Otherwise:
        - return `none`
 -/
 def orBoolReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let lhs ← mkApp2Expr (← mkBoolOrOp) a b
  if let some h ← hypMapFind? (← mkEqBool a true) then
    return ← withHypThm lhs (← mkBoolTrue) (← mkEqBool a true) h ``bool_or_eq_true_of_left #[a, b]
  if let some h ← hypMapFind? (← mkEqBool b true) then
    return ← withHypThm lhs (← mkBoolTrue) (← mkEqBool b true) h ``bool_or_eq_true_of_right #[a, b]
  if let some h ← hypMapFind? (← mkEqBool a false) then
    return ← withHypThm lhs b (← mkEqBool a false) h ``bool_or_eq_right_of #[a, b]
  if let some h ← hypMapFind? (← mkEqBool b false) then
    return ← withHypThm lhs a (← mkEqBool b false) h ``bool_or_eq_left_of #[a, b]
  return none

/-- Apply the following simplification/normalization rules on `or` :
     - false || e ==> e
     - true || e ==> true
     - e || not e ==> true
     - e1 || e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 || e2 ===> true (if true = e1 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 || e2 ===> true (if true = e2 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 || e2 ===> e2 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e1)
     - e1 || e2 ===> e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e2)
     - e1 || e2 ==> e2 || e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``or.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `or` expected at this stage)

   TODO: reordering on list of `||` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
   TODO: consider additional simplification rules
-/
def optimizeBoolOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeBoolOr: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 let lhs ← mkApp2Expr f op1 op2
 if let Expr.const ``false _ := op1 then return ← withThm lhs op2 ``bool_false_or #[op2]
 if let Expr.const ``true _ := op1 then return ← withThm lhs op1 ``bool_true_or #[op2]
 if exprEq op1 op2 then return ← withThm lhs op1 ``bool_or_self #[op1]
 if isBoolNotExprOf op2 op1 then return ← withThm lhs (← mkBoolTrue) ``bool_or_not_self #[op1]
 if let some r ← orBoolReduction? op1 op2 then return r
 -- no caching at this level as optimizeBoolAnd is called by optimizeDecideBoolOr
 mkApp2Expr f op1 op2

end Blaster.Optimize
