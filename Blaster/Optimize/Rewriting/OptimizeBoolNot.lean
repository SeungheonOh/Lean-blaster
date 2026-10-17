import Lean
import Blaster.Optimize.Rewriting.Utils

open Lean Meta Blaster.Reconstruct
namespace Blaster.Optimize

/-- Given op the operand for `not`,
     - When op := decide' e
        - return `some decide' (¬ e)`
    - Otherwise:
        - return `none`
-/
@[always_inline, inline]
def notDecideProp? (op : Expr) : TranslateEnvT (Option Expr) := do
 let some e := decide'? op | return none
 setRestart
 return mkApp op.getAppFn (mkApp (← mkPropNotOp) e)

/-- Apply the following simplification/normalization rules on `not` :
     - ! true ==> false
     - ! false ==> true
     - ! (! e) ==> e
     - !(decide' e) ==> decide' (¬ e)
   Assume that f = Expr.const ``not.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `not` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeBoolNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeBoolNot: exactly one argument expected"
 let op := args[0]!
 let lhs := mkApp f op
 match op with
 | Expr.const ``true _ => withThm lhs (← mkBoolFalse) ``bool_not_true #[]
 | Expr.const ``false _ => withThm lhs (← mkBoolTrue) ``bool_not_false #[]
 | _ =>
    if let some e := boolNot? op then return ← withThm lhs e ``bool_not_not #[e]
    if let some r ← notDecideProp? op then
      let some e := decide'? op | return r
      return ← withThm lhs r ``bool_not_decide' #[e]
    return lhs

/-- Apply simplification/normalization rules on Boolean `not` operator.
-/
def optimizeBoolNot? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const ``not _ => optimizeBoolNot f args
 | _ => pure none

end Blaster.Optimize
