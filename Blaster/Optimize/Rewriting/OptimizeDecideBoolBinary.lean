import Lean
import Blaster.Optimize.Rewriting.OptimizeBoolBinary


open Lean Meta
namespace Blaster.Optimize


/-- Given `op1` and `op2` corresponding to the operands for a Boolean binary operator:
    - return `some (decide' (mkOpExpr #[e1, e2]))` when `op1 := decide' e1 ∧ op2 := decide' e2`
    - return `some (decide' (mkOpExpr #[e1, true = e2]))` when `op1 := decide' e1 ∧ op2 := e2`
    - return `some (decide' (mkOpExpr #[e1, true = e2]))` when `op1 := e2 ∧ op2 := decide' e1`
    Otherwise `none`.
-/
def decideOpDecide?
  (op1 : Expr) (op2 : Expr)
  (mkOpExpr : Expr → Expr → TranslateEnvT Expr) : TranslateEnvT (Option Expr) := do
  match decide'? op1, decide'? op2 with
  | some e1, some e2 =>
      setRestart
      mkAppExpr (← mkBlasterDecideConst) (← mkOpExpr e1 e2)
  | some e1, _ =>
      setRestart
      mkAppExpr (← mkBlasterDecideConst) (← mkOpExpr e1 (← mkApp3Expr (← mkEqOp) (← mkBoolType) (← mkBoolTrue) op2))
  | _, some e1 =>
      setRestart
      mkAppExpr (← mkBlasterDecideConst) (← mkOpExpr e1 (← mkApp3Expr (← mkEqOp) (← mkBoolType) (← mkBoolTrue) op1))
  | _, _ => return none


/-- When tracking proof terms, record the justification of the rewrite of `e := op1 ⊕ op2` into `r` by
    `decideOpDecide?`, with `both`, `left` and `right` the lemmas for `decide' e1 ⊕ decide' e2`, `decide' e1 ⊕ b`
    and `b ⊕ decide' e1` (e.g., `Blaster.Reconstruct.decide'_and_decide'`), and return `r`.
-/
def recordDecideOp (e r op1 op2 : Expr) (both left right : Name) : TranslateEnvT Expr := do
  match decide'? op1, decide'? op2 with
  | some e1, some e2 => Blaster.Reconstruct.withThm e r both #[e1, e2]
  | some e1, _ => Blaster.Reconstruct.withThm e r left #[e1, op2]
  | _, some e1 => Blaster.Reconstruct.withThm e r right #[op1, e1]
  | _, _ => return r

/-- Call `optimizeBoolAnd f args` and apply the following `decide` simplification/normalization
    rules on the resulting `and` expression (if any):
     - decide' e1 && decide' e2 ==> decide' (e1 ∧ e2)
     - decide' e1 && e2 | e2 && decide' e1 ==> decide' (e1 ∧ true = e2)

   Assume that f = Expr.const ``and.

   TODO: reordering on list of `&&` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
-/
def optimizeDecideBoolAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeBoolAnd f args
 let some (op1, op2) := boolAnd? e | return e
 if let some r ← decideOpDecide? op1 op2 (mkApp2Expr (← mkPropAndOp)) then
   return ← recordDecideOp e r op1 op2
     ``Blaster.Reconstruct.decide'_and_decide' ``Blaster.Reconstruct.decide'_and_bool
     ``Blaster.Reconstruct.bool_and_decide'
 return e

/-- Call `optimizeBoolOr f args` and apply the following `decide` simplification/normalization
    rules on the resulting `or` expression (if any):
     - decide' e1 || decide' e2 ==> decide' (e1 ∨ e2)
     - decide' e1 || e2 | e2 || decide' e1 ==> decide' (e1 ∨ true = e2)

   Assume that f = Expr.const ``or.

   Do nothing if operator is partially applied (i.e., args.size < 2)
   TODO: reordering on list of `||` must be performed to regroup all `decide' e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
   TODO: consider additional simplification rules
-/
def optimizeDecideBoolOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeBoolOr f args
 let some (op1, op2) := boolOr? e | return e
 if let some r ← decideOpDecide? op1 op2 (mkApp2Expr (← mkPropOrOp)) then
   return ← recordDecideOp e r op1 op2
     ``Blaster.Reconstruct.decide'_or_decide' ``Blaster.Reconstruct.decide'_or_bool
     ``Blaster.Reconstruct.bool_or_decide'
 return e


/-- Apply simplification/normalization rules on Boolean binary operators.
-/
def optimizeBoolBinary? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 let Expr.const n _ := f | return none
 match n with
 | ``and => optimizeDecideBoolAnd f args
 | ``or => optimizeDecideBoolOr f args
 | _=> return none

end Blaster.Optimize
