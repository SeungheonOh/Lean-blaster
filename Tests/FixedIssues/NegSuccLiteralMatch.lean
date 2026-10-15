import Lean
import Blaster
import Tests.Utils

namespace Tests.NegSuccLiteralMatch

-- Issue: matching a negative `Int` literal against an `Int.negSucc m` pattern binds `m` one too
--        low, e.g., `Int.natAbs (-7)` reduces to `6`: `blaster` falsifies `Int.natAbs (-7) = 7`
--        and proves `Int.natAbs (-7) = 6`.

def negOf (i : Int) : Nat := match i with | .ofNat m => m | .negSucc m => m

#testOptimize ["NatAbsNegLit"] Int.natAbs (-7) = 7 ===> True
#testOptimize ["NatAbsNegOne"] Int.natAbs (-1) = 1 ===> True
#testOptimize ["NegSuccArgLit"] negOf (-7) = 6 ===> True
#testOptimize ["NegSuccArgOne"] negOf (-1) = 0 ===> True
#testOptimize ["NatAbsNegLitOffByOne"] Int.natAbs (-7) = 6 ===> False
#testOptimize ["NegSuccArgLitOffByOne"] negOf (-7) = 5 ===> False

-- the literal reaches the match through a hypothesis
theorem natAbs_of_eq_neg_lit : ∀ (x : Int), x = -7 → x.natAbs = 7 := by blaster

theorem negOf_neg_lit : ∀ (x : Int), x = -1234 → negOf x = 1233 := by blaster

-- symbolic `Int.negSucc` already worked; it must keep working
theorem natAbs_negSucc : ∀ (m : Nat), Int.natAbs (Int.negSucc m) = m + 1 := by blaster

theorem negOf_negSucc : ∀ (m : Nat), negOf (Int.negSucc m) = m := by blaster

-- must be falsified, not merely undetermined
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x = -7 → x.natAbs = 6]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x = -1234 → negOf x = 1232]

end Tests.NegSuccLiteralMatch
