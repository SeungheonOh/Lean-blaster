import Lean
import Blaster.Optimize.Rewriting.Utils

open Lean Meta Elab Blaster.Reconstruct
namespace Blaster.Optimize

/-- Apply the following simplification/normalization rules on `Blaster.decide'`:
      - decide' False ==> false
      - decide' True ==> true
      - decide' (true = p) ==> p
      - decide' (false = p) ==> ! p
    An error is trigerred if args.size ≠ 2.
-/
def optimizeDecideCore (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 1 then throwEnvError "optimizeDecideCore: one argument expected but got {reprStr args}"
  -- args[0] proposition
  let p := args[0]!
  let lhs := mkApp f p
  if let Expr.const ``False _ := p then return ← withThm lhs (← mkBoolFalse) ``decide'_False #[]
  if let Expr.const ``True _ := p then return ← withThm lhs (← mkBoolTrue) ``decide'_True #[]
  if let some r ← decideBoolEq? p then
    match eq? p with
    | some (_, Expr.const ``true _, b) => return ← withThm lhs r ``decide'_true_eq #[b]
    | some (_, Expr.const ``false _, b) => return ← withThm lhs r ``decide'_false_eq #[b]
    | _ => return r
  return lhs

where
  /-- Return `some p` if `e := true = p`
      Return `some (! p)` if `e := false = p`
      Otherwise `none`.
  -/
  decideBoolEq? (e : Expr) : TranslateEnvT (Option Expr) := do
   match eq? e with
   | some (_, Expr.const ``true _, p) => return (some p)
   | some (_, Expr.const ``false _, p) => return (mkApp (← mkBoolNotOp) p)
   | _ => return none

/-- Apply simplification/normalization rules on `Blaster.decide'`. -/
def optimizeDecide? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  match f with
  | Expr.const ``Blaster.decide' _ => optimizeDecideCore f args
  | _ => pure none

end Blaster.Optimize
