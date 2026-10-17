import Lean
import Blaster.Optimize.Rewriting.Utils

open Lean Meta Blaster.Reconstruct
namespace Blaster.Optimize

/-- Return `true` when `e` corresponds to the zero nat literal. -/
@[always_inline, inline]
def isZeroNat (e : Expr) : Bool :=
  match isNatValue? e with
  | some 0 => true
  | _ => false

/-- Given `ne` the operand for `Not` apply the following normalization rules:
     - When `ne := false = e`
        - return `some (true = e)`
     - When `ne := true = e`
        - return `some (false = e)`
     - Otherwise:
        - return `none`.
-/
def notEqSimp? (ne : Expr) : TranslateEnvT (Option Expr) := do
  match eq? ne with
  | some (eq_sort, op1, op2) =>
     match op1 with
     | Expr.const ``false _ =>
         return (mkApp3 ne.getAppFn eq_sort (← mkBoolTrue) op2)
     | Expr.const ``true _ =>
         return (mkApp3 ne.getAppFn eq_sort (← mkBoolFalse) op2)
     | _ => return none
  | none => return none

/-- Given `ne` the operand for `Not`, apply the following normalization rule:
    - When `ne := 0 < e` ∧ Type(a) = Nat:
       - return `some (0 = e)`
    - Otherwise:
       - return `none`
-/
def notLTNumNorm? (ne : Expr) (restart := true) : TranslateEnvT (Option Expr) := do
  let some (_t, _i, e1, e2) := lt? ne | return none
  if isZeroNat e1 then
    if restart then setRestart
    mkNatEqExpr e1 e2
  else return none


/-- Apply the following simplification/normalization rules on `Not` :
     - ¬ False ==> True
     - ¬ True ==> False
     - ¬ (¬ e) ==> e (classical)
     - ¬ (false = e) ==> true = e
     - ¬ (true = e) ==> false = e
     - ¬ (0 < e) ==> (0 = e) (if Type(e) = Nat)
   Assume that f = Expr.const ``Not.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `Not` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeNot (f : Expr) (args : Array Expr) (cacheResult := true) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeNot: exactly one argument expected"
 let e := args[0]!
 let lhs := mkApp f e
 if let Expr.const ``False _ := e then return ← withThm lhs (← mkPropTrue) ``not_false_eq' #[]
 if let Expr.const ``True _ := e then return ← withThm lhs (← mkPropFalse) ``not_true_eq' #[]
 if let some op := propNot? e then return ← withThm lhs op ``not_not_eq' #[op]
 if let some r ← notEqSimp? e then
   let some (_, op1, op2) := eq? e | return r
   return ← withThm lhs r (if op1.isConstOf ``false then ``not_false_eq_bool else ``not_true_eq_bool) #[op2]
 if let some r ← notLTNumNorm? e cacheResult then
   let some (_, _, _, op2) := lt? e | return r
   return ← withThm lhs r ``nat_not_zero_lt #[op2]
 return lhs


/-- Given `ne` the operand for `Not` apply the following normalization rules:
     - When `ne := ¬ e1 ∧ ¬ e2`
        - return `e1 ∨ e2`
     - When `ne := ¬ e1 ∨ ¬ e2`
        - return `e1 ∧ e2`
     - Otherwise:
        - return `none`.
-/
def notLogicalSimp? (ne : Expr) : TranslateEnvT (Option Expr) := do
  match propAnd? ne with
  | some (ne1, ne2) => notPropagation? ne1 ne2 (← mkPropOrOp)
  | _ =>
    match propOr? ne with
    | some (ne1, ne2) => notPropagation? ne1 ne2 (← mkPropAndOp)
    | _ => return none

 where
   notPropagation? (ne1 : Expr) (ne2 : Expr) (op : Expr) : TranslateEnvT (Option Expr) := do
     match propNot? ne1, propNot? ne2 with
     | some e1, some e2 =>
           setRestart
           return mkApp2 op e1 e2
     | _, _ => return none

/-- Call `optimizeNot f args` and apply the following simplification/normalization rules on `Not` :
     - ¬ (¬ e1 ∧ ¬ e2) ==> (e1 ∨ e2)
     - ¬ (¬ e1 ∨ ¬ e2) ==> (e1 ∧ e2)
   Assume that f = Expr.const ``Not.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `Not` expected at this stage)
-/
def optimizeAdvancedNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  let e ← optimizeNot f args
  let some ne := propNot? e | return e
  if let some r ← notLogicalSimp? ne then
    if let some (ne1, ne2) := propAnd? ne then
      if let (some e1, some e2) := (propNot? ne1, propNot? ne2) then
        return ← withThm e r ``not_and_not_eq #[e1, e2]
    if let some (ne1, ne2) := propOr? ne then
      if let (some e1, some e2) := (propNot? ne1, propNot? ne2) then
        return ← withThm e r ``not_or_not_eq #[e1, e2]
    return r
  return e


/-- Apply simplification and normalization rules on proposition `Not` formulae. -/
def optimizePropNot? (f: Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  match f with
  | Expr.const ``Not _ => optimizeAdvancedNot f args
  | _ => return none

end Blaster.Optimize
