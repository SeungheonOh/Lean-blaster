import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.UnifyPattern

/-! ## Test objectives to validate pattern/discriminator unification on match alternatives
     (i.e., `unifyAndUpdateEqMap`): when a match expression is neither reduced nor normalized
     to `ite`, each discriminator is unified with the pattern of the alternative being optimized
     and the resulting equalities are propagated in the rhs of the alternative through the
     equality map.

     NOTE: In every test case below, the first alternative cannot be decided (its pattern contains
     a literal/constructor compared with a free variable) so that choice reduction does not apply,
     and at least one pattern is a constructor application with free variables of a user-defined
     inductive type so that the match is not normalized to `ite`.

     NOTE: The named pattern hypothesis section covers the hypothesis of a named pattern (`p@hp:pat`),
     which is instantiated with `Eq.refl` both when the match is reduced and when it is not.
     The last section (`UnifyPattern_63` and `UnifyPattern_64`) documents a known issue with the
     hypothesis of a named pattern containing a nested named pattern: these test cases encode the
     expected result and currently FAIL.

-/

inductive Value where
  | nat : Nat → Value
  | int : Int → Value
  | str : String → Value
  | pair : Nat → Nat → Value
  | wrap : Value → Nat → Value
  | unit : Value
  | none : Value
  deriving Inhabited

opaque v0 : Value

variable (m n : Nat) (w : Int) (s : String) (c1 c2 : Char) (cs : List Char) (ms : List Nat) (v u : Value)
variable (h : Nat → Nat) (hi : Int → Int) (f : Nat → Value) (g : Value → Nat) (gi : Int → Nat)

/-! ### Variable patterns and Nat literal patterns -/

def natArg (x : Value) (z : Nat) : Nat :=
  match x with
  | .nat 5 => z + 100
  | .nat k => k + z
  | _ => 0

-- natArg (.nat m) m ===>
--   match Value.nat m with
--   | .nat 5 => 105
--   | .nat k => Nat.add m m
--   | _ => 0
-- NOTE: literal pattern vs free variable discriminator binds `m := 5`,
--       variable pattern vs free variable discriminator binds `k := m`
#testOptimize [ "UnifyPattern_1" ] (norm-result: 1)
  natArg (.nat m) m ===>
    match Value.nat m with
    | .nat 5 => 105
    | .nat _k => Nat.add m m
    | _ => 0

-- natArg (.nat (m + 2)) m ===>
--   match Value.nat (Nat.add 2 m) with
--   | .nat 5 => 103
--   | .nat k => Nat.add m (Nat.add 2 m)
--   | _ => 0
-- NOTE: literal pattern vs offset discriminator `2 + m` binds `m := 3` (5 ≥ 2),
--       variable pattern vs expression discriminator binds `k := 2 + m`
#testOptimize [ "UnifyPattern_2" ] (norm-result: 1)
  natArg (.nat (m + 2)) m ===>
    match Value.nat (Nat.add 2 m) with
    | .nat 5 => 103
    | .nat _k => Nat.add m (Nat.add 2 m)
    | _ => 0

def pairArg (x : Value) (z : Nat) : Nat :=
  match x with
  | .pair _ 3 => z + 100
  | .pair 5 k => k + z
  | .pair 7 k => k * z
  | .pair j k => j + k + z
  | _ => 0

-- pairArg (.pair 5 m) m ===>
--   match Value.pair 5 m with
--   | .pair _ 3 => 103
--   | .pair 5 k => Nat.add m m
--   | .pair 7 k => Nat.mul m k
--   | .pair j k => Nat.add m (Nat.add 5 m)
--   | _ => 0
-- NOTE: equal literals (`5` vs `5`) continue the unification with the pending arguments (`k := m`),
--       distinct literals (`7` vs `5`) stop the unification (`k` is left unbound)
#testOptimize [ "UnifyPattern_3" ] (norm-result: 1)
  pairArg (.pair 5 m) m ===>
    match Value.pair 5 m with
    | .pair _ 3 => 103
    | .pair 5 _k => Nat.add m m
    | .pair 7 k => Nat.mul m k
    | .pair _j _k => Nat.add m (Nat.add 5 m)
    | _ => 0

-- pairArg (.pair (h m + 2) m) (h m) ===>
--   match Value.pair (Nat.add 2 (h m)) m with
--   | .pair _ 3 => Nat.add 100 (h 3)
--   | .pair 5 k => Nat.add 3 m
--   | .pair 7 k => Nat.mul 5 m
--   | .pair j k => Nat.add (h m) (Nat.add m (Nat.add 2 (h m)))
--   | _ => 0
-- NOTE: literal pattern vs offset discriminator `2 + h m` binds the expression `h m := 3` and `h m := 5`
#testOptimize [ "UnifyPattern_4" ] (norm-result: 1)
  pairArg (.pair (h m + 2) m) (h m) ===>
    match Value.pair (Nat.add 2 (h m)) m with
    | .pair _ 3 => Nat.add 100 (h 3)
    | .pair 5 _k => Nat.add 3 m
    | .pair 7 _k => Nat.mul 5 m
    | .pair _j _k => Nat.add (h m) (Nat.add m (Nat.add 2 (h m)))
    | _ => 0

-- pairArg (.pair (h m + 7) m) (h m) ===>
--   match Value.pair (Nat.add 7 (h m)) m with
--   | .pair _ 3 => Nat.add 100 (h 3)
--   | .pair 5 k => Nat.add k (h m)
--   | .pair 7 k => 0
--   | .pair j k => Nat.add (h m) (Nat.add m (Nat.add 7 (h m)))
--   | _ => 0
-- NOTE: literal `5` smaller than offset `7` stops the unification (`k` is left unbound),
--       literal `7` vs offset `7 + h m` binds `h m := 0`
#testOptimize [ "UnifyPattern_5" ] (norm-result: 1)
  pairArg (.pair (h m + 7) m) (h m) ===>
    match Value.pair (Nat.add 7 (h m)) m with
    | .pair _ 3 => Nat.add 100 (h 3)
    | .pair 5 k => Nat.add k (h m)
    | .pair 7 _k => 0
    | .pair _j _k => Nat.add (h m) (Nat.add m (Nat.add 7 (h m)))
    | _ => 0

-- pairArg (.pair (h m) m) (h m) ===>
--   match Value.pair (h m) m with
--   | .pair _ 3 => Nat.add 100 (h 3)
--   | .pair 5 k => Nat.add 5 m
--   | .pair 7 k => Nat.mul 7 m
--   | .pair j k => Nat.add (h m) (Nat.add m (h m))
--   | _ => 0
-- NOTE: literal pattern vs non constructor application discriminator binds `h m := 5` and `h m := 7`
#testOptimize [ "UnifyPattern_6" ] (norm-result: 1)
  pairArg (.pair (h m) m) (h m) ===>
    match Value.pair (h m) m with
    | .pair _ 3 => Nat.add 100 (h 3)
    | .pair 5 _k => Nat.add 5 m
    | .pair 7 _k => Nat.mul 7 m
    | .pair _j _k => Nat.add (h m) (Nat.add m (h m))
    | _ => 0

/-! ### Nat offset patterns (`k + c`) -/

def natOffset (x : Value) (z : Nat) : Nat :=
  match x with
  | .nat 5 => z + 100
  | .nat (k + 2) => k + z
  | .nat k => k * z
  | _ => 0

-- natOffset (.nat (m + 5)) m ===>
--   match Value.nat (Nat.add 5 m) with
--   | .nat 5 => 100
--   | .nat (k + 2) => Nat.add m (Nat.add 3 m)
--   | .nat k => Nat.mul m (Nat.add 5 m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs offset discriminator `5 + m` binds `k := 3 + m` (2 < 5)
#testOptimize [ "UnifyPattern_7" ] (norm-result: 1)
  natOffset (.nat (m + 5)) m ===>
    match Value.nat (Nat.add 5 m) with
    | .nat 5 => 100
    | .nat (_k + 2) => Nat.add m (Nat.add 3 m)
    | .nat _k => Nat.mul m (Nat.add 5 m)
    | _ => 0

-- natOffset (.nat (m + 2)) m ===>
--   match Value.nat (Nat.add 2 m) with
--   | .nat 5 => 103
--   | .nat (k + 2) => Nat.add m m
--   | .nat k => Nat.mul m (Nat.add 2 m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs offset discriminator `2 + m` binds `k := m` (2 = 2)
#testOptimize [ "UnifyPattern_8" ] (norm-result: 1)
  natOffset (.nat (m + 2)) m ===>
    match Value.nat (Nat.add 2 m) with
    | .nat 5 => 103
    | .nat (_k + 2) => Nat.add m m
    | .nat _k => Nat.mul m (Nat.add 2 m)
    | _ => 0

-- natOffset (.nat (m + 1)) m ===>
--   match Value.nat (Nat.add 1 m) with
--   | .nat 5 => 104
--   | .nat (k + 2) => Nat.add k (Nat.add 1 k)
--   | .nat k => Nat.mul m (Nat.add 1 m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs offset discriminator `1 + m` binds `m := 1 + k` (2 > 1)
#testOptimize [ "UnifyPattern_9" ] (norm-result: 1)
  natOffset (.nat (m + 1)) m ===>
    match Value.nat (Nat.add 1 m) with
    | .nat 5 => 104
    | .nat (k + 2) => Nat.add k (Nat.add 1 k)
    | .nat _k => Nat.mul m (Nat.add 1 m)
    | _ => 0

-- natOffset (.nat m) m ===>
--   match Value.nat m with
--   | .nat 5 => 105
--   | .nat (k + 2) => Nat.add k (Nat.add 2 k)
--   | .nat k => Nat.mul m m
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs free variable discriminator binds `m := 2 + k`
#testOptimize [ "UnifyPattern_10" ] (norm-result: 1)
  natOffset (.nat m) m ===>
    match Value.nat m with
    | .nat 5 => 105
    | .nat (k + 2) => Nat.add k (Nat.add 2 k)
    | .nat _k => Nat.mul m m
    | _ => 0

-- natOffset (.nat (h m)) (h m) ===>
--   match Value.nat (h m) with
--   | .nat 5 => 105
--   | .nat (k + 2) => Nat.add k (Nat.add 2 k)
--   | .nat k => Nat.mul (h m) (h m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs non constructor application discriminator binds `h m := 2 + k`
#testOptimize [ "UnifyPattern_11" ] (norm-result: 1)
  natOffset (.nat (h m)) (h m) ===>
    match Value.nat (h m) with
    | .nat 5 => 105
    | .nat (k + 2) => Nat.add k (Nat.add 2 k)
    | .nat _k => Nat.mul (h m) (h m)
    | _ => 0

def wrapNat (x : Value) (z : Nat) : Nat :=
  match x with
  | .wrap _ 5 => z + 100
  | .wrap (.nat 5) j => z + j
  | .wrap (.nat (k + 2)) j => k + j + z
  | .wrap (.nat k) j => k * j * z
  | _ => 0

-- wrapNat (.wrap (.nat 7) m) m ===>
--   match Value.wrap (Value.nat 7) m with
--   | .wrap _ 5 => 105
--   | .wrap (.nat 5) j => Nat.add m j
--   | .wrap (.nat (k + 2)) j => Nat.add m (Nat.add 5 m)
--   | .wrap (.nat k) j => Nat.mul m (Nat.mul 7 m)
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs literal discriminator `7` binds `k := 5` (7 ≥ 2),
--       distinct literals (`5` vs `7`) stop the unification (`j` is left unbound)
#testOptimize [ "UnifyPattern_12" ] (norm-result: 1)
  wrapNat (.wrap (.nat 7) m) m ===>
    match Value.wrap (Value.nat 7) m with
    | .wrap _ 5 => 105
    | .wrap (.nat 5) j => Nat.add m j
    | .wrap (.nat (_k + 2)) _j => Nat.add m (Nat.add 5 m)
    | .wrap (.nat _k) _j => Nat.mul m (Nat.mul 7 m)
    | _ => 0

-- wrapNat (.wrap (.nat 1) m) m ===>
--   match Value.wrap (Value.nat 1) m with
--   | .wrap _ 5 => 105
--   | .wrap (.nat 5) j => Nat.add m j
--   | .wrap (.nat (k + 2)) j => Nat.add m (Nat.add k j)
--   | .wrap (.nat k) j => Nat.mul m m
--   | _ => 0
-- NOTE: offset pattern `2 + k` vs literal discriminator `1` stops the unification (1 < 2)
#testOptimize [ "UnifyPattern_13" ] (norm-result: 1)
  wrapNat (.wrap (.nat 1) m) m ===>
    match Value.wrap (Value.nat 1) m with
    | .wrap _ 5 => 105
    | .wrap (.nat 5) j => Nat.add m j
    | .wrap (.nat (k + 2)) j => Nat.add m (Nat.add k j)
    | .wrap (.nat _k) _j => Nat.mul m m
    | _ => 0

-- wrapNat (.wrap (.nat 5) m) m ===>
--   match Value.wrap (Value.nat 5) m with
--   | .wrap _ 5 => 105
--   | .wrap (.nat 5) j => Nat.add m m
--   | .wrap (.nat (k + 2)) j => Nat.add m (Nat.add 3 m)
--   | .wrap (.nat k) j => Nat.mul m (Nat.mul 5 m)
--   | _ => 0
-- NOTE: equal literals (`5` vs `5`) continue the unification with the pending arguments (`j := m`)
#testOptimize [ "UnifyPattern_14" ] (norm-result: 1)
  wrapNat (.wrap (.nat 5) m) m ===>
    match Value.wrap (Value.nat 5) m with
    | .wrap _ 5 => 105
    | .wrap (.nat 5) _j => Nat.add m m
    | .wrap (.nat (_k + 2)) _j => Nat.add m (Nat.add 3 m)
    | .wrap (.nat _k) _j => Nat.mul m (Nat.mul 5 m)
    | _ => 0

/-! ### Int patterns (`Int.ofNat`, `Int.negSucc`, literals and offsets) -/

def intArg (gi : Int → Nat) (x : Value) (z : Int) : Nat :=
  match x with
  | .int 3 => gi z + 100
  | .int (.ofNat 7) => gi z + 107
  | .int (.negSucc 2) => gi z + 300
  | .int (.ofNat (k + 1)) => gi z + k
  | .int (.negSucc (k + 1)) => gi z + 2 * k
  | .int (.ofNat k) => gi z + 3 * k
  | .int (.negSucc k) => gi z + 4 * k
  | _ => 0

-- intArg gi (.int (Int.ofNat m)) (Int.ofNat m) ===>
--   match Value.int (Int.ofNat m) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat m))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat m)) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 m)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.ofNat` patterns unify with the `Int.ofNat m` discriminator (`m := 3`, `m := 7`, `m := 1 + k`, `k := m`),
--       `Int.negSucc` patterns (normalized to `Int.neg (Int.ofNat _)` or kept as literals) do not unify
#testOptimize [ "UnifyPattern_15" ] (norm-result: 1)
  intArg gi (.int (Int.ofNat m)) (Int.ofNat m) ===>
    match Value.int (Int.ofNat m) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat m))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat m)) (Nat.mul 2 k)
    | .int (.ofNat _k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 m)
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (Int.ofNat (m + 2))) (Int.ofNat (m + 2)) ===>
--   match Value.int (Int.ofNat (Nat.add 2 m)) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat (Nat.add 2 m)))
--   | .int (.ofNat (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.add 1 m)
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 3 (Nat.add 2 m))
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.ofNat` literal patterns vs offset discriminator `2 + m` bind `m := 1` and `m := 5`,
--       offset pattern `1 + k` vs offset discriminator `2 + m` binds `k := 1 + m`
#testOptimize [ "UnifyPattern_16" ] (norm-result: 1)
  intArg gi (.int (Int.ofNat (m + 2))) (Int.ofNat (m + 2)) ===>
    match Value.int (Int.ofNat (Nat.add 2 m)) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat (Nat.add 2 m)))
    | .int (.ofNat (_k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.add 1 m)
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 2 k)
    | .int (.ofNat _k) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 3 (Nat.add 2 m))
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 2 m))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int w) w ===>
--   match Value.int w with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: every Int pattern binds the free variable discriminator `w` to its (normalized) pattern
#testOptimize [ "UnifyPattern_17" ] (norm-result: 1)
  intArg gi (.int w) w ===>
    match Value.int w with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (-w)) (-w) ===>
--   match Value.int (Int.neg w) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.ofNat _` and `Int.negSucc _` patterns vs `Int.neg w` discriminator (`w` not an `Int.ofNat`
--       expression) bind the expression `Int.neg w` to the pattern
#testOptimize [ "UnifyPattern_18" ] (norm-result: 1)
  intArg gi (.int (-w)) (-w) ===>
    match Value.int (Int.neg w) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (hi w)) (hi w) ===>
--   match Value.int (hi w) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: every Int pattern binds the non constructor application discriminator `hi w` to its pattern
#testOptimize [ "UnifyPattern_19" ] (norm-result: 1)
  intArg gi (.int (hi w)) (hi w) ===>
    match Value.int (hi w) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat 3))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat 7))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (Nat.add 1 k)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 2 k)))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat k)) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 k)))) (Nat.mul 4 k)
    | _ => 0

def intNegDiscr (gi : Int → Nat) (x : Value) (z : Int) : Nat :=
  match x with
  | .int (.ofNat 7) => gi z + 107
  | .int (.negSucc 2) => gi z + 300
  | .int (.ofNat (k + 1)) => gi z + k
  | .int (.ofNat k) => gi z + 3 * k
  | _ => 0

-- intNegDiscr gi (.int (Int.negSucc m)) (Int.negSucc m) ===>
--   match Value.int (Int.neg (Int.ofNat (Nat.add 1 m))) with
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.neg (Int.ofNat (Nat.add 1 m))))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.neg (Int.ofNat (Nat.add 1 m))))
--   | .int (.ofNat k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 m)))) (Nat.mul 3 k)
--   | _ => 0
-- NOTE: `Int.negSucc m` discriminator is normalized to `Int.neg (Int.ofNat (1 + m))`:
--       `Int.ofNat` patterns do not unify, the `Int.negSucc 2` literal pattern binds `m := 2`
--       (`3` vs `1 + m`), and `Int.neg (Int.ofNat 3)` is folded back to `Int.negSucc 2`
#testOptimize [ "UnifyPattern_20" ] (norm-result: 1)
  intNegDiscr gi (.int (Int.negSucc m)) (Int.negSucc m) ===>
    match Value.int (Int.neg (Int.ofNat (Nat.add 1 m))) with
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.neg (Int.ofNat (Nat.add 1 m))))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.negSucc 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.neg (Int.ofNat (Nat.add 1 m))))
    | .int (.ofNat k) => Nat.add (gi (Int.neg (Int.ofNat (Nat.add 1 m)))) (Nat.mul 3 k)
    | _ => 0

def intLit (gi : Int → Nat) (x : Value) (z : Int) : Nat :=
  match x with
  | .wrap _ 5 => 100
  | .wrap (.int 3) j => gi z + j + 100
  | .wrap (.int (.negSucc 2)) j => gi z + j + 300
  | .wrap (.int (.ofNat (k + 1))) j => gi z + k + j
  | .wrap (.int (.negSucc (k + 1))) j => gi z + 2 * k + j
  | .wrap (.int (.ofNat k)) j => gi z + 3 * k + j
  | .wrap (.int (.negSucc k)) j => gi z + 4 * k + j
  | _ => 0

-- intLit gi (.wrap (.int 3) m) 3 ===>
--   match Value.wrap (Value.int (Int.ofNat 3)) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 3) j => Nat.add 100 (Nat.add m (gi (Int.ofNat 3)))
--   | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.ofNat 3)))
--   | .wrap (.int (.ofNat (k + 1))) j => Nat.add m (Nat.add 2 (gi (Int.ofNat 3)))
--   | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.ofNat 3)) (Nat.mul 2 k))
--   | .wrap (.int (.ofNat k)) j => Nat.add m (Nat.add 9 (gi (Int.ofNat 3)))
--   | .wrap (.int (.negSucc k)) j => Nat.add j (Nat.add (gi (Int.ofNat 3)) (Nat.mul 4 k))
--   | _ => 0
-- NOTE: positive literal discriminator: `Int.ofNat` patterns unify (`j := m`, `k := 2`, `k := 3`),
--       `Int.negSucc` patterns stop the unification (`j` is left unbound)
#testOptimize [ "UnifyPattern_21" ] (norm-result: 1)
  intLit gi (.wrap (.int 3) m) 3 ===>
    match Value.wrap (Value.int (Int.ofNat 3)) m with
    | .wrap _ 5 => 100
    | .wrap (.int 3) _j => Nat.add 100 (Nat.add m (gi (Int.ofNat 3)))
    | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.ofNat 3)))
    | .wrap (.int (.ofNat (_k + 1))) _j => Nat.add m (Nat.add 2 (gi (Int.ofNat 3)))
    | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.ofNat 3)) (Nat.mul 2 k))
    | .wrap (.int (.ofNat _k)) _j => Nat.add m (Nat.add 9 (gi (Int.ofNat 3)))
    | .wrap (.int (.negSucc k)) j => Nat.add j (Nat.add (gi (Int.ofNat 3)) (Nat.mul 4 k))
    | _ => 0

-- intLit gi (.wrap (.int (-3)) m) (-3) ===>
--   match Value.wrap (Value.int (Int.negSucc 2)) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.negSucc 2)))
--   | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add m (gi (Int.negSucc 2)))
--   | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.negSucc 2)))
--   | .wrap (.int (.negSucc (k + 1))) j => Nat.add m (Nat.add 2 (gi (Int.negSucc 2)))
--   | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.negSucc 2)) (Nat.mul 3 k))
--   | .wrap (.int (.negSucc k)) j => Nat.add m (Nat.add 8 (gi (Int.negSucc 2)))
--   | _ => 0
-- NOTE: negative literal discriminator `Int.negSucc 2`: the `Int.negSucc 2` literal pattern continues
--       the unification (`j := m`), `Int.negSucc (k + 1)` (normalized to `Int.neg (Int.ofNat (2 + k))`)
--       binds `k := 1` (`2 + k` vs `3`), `Int.negSucc k` binds `k := 2`, `Int.ofNat` patterns stop the unification
#testOptimize [ "UnifyPattern_22" ] (norm-result: 1)
  intLit gi (.wrap (.int (-3)) m) (-3) ===>
    match Value.wrap (Value.int (Int.negSucc 2)) m with
    | .wrap _ 5 => 100
    | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.negSucc 2)))
    | .wrap (.int (.negSucc 2)) _j => Nat.add 300 (Nat.add m (gi (Int.negSucc 2)))
    | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.negSucc 2)))
    | .wrap (.int (.negSucc (_k + 1))) _j => Nat.add m (Nat.add 2 (gi (Int.negSucc 2)))
    | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.negSucc 2)) (Nat.mul 3 k))
    | .wrap (.int (.negSucc _k)) _j => Nat.add m (Nat.add 8 (gi (Int.negSucc 2)))
    | _ => 0

-- intLit gi (.wrap (.int 0) m) 0 ===>
--   match Value.wrap (Value.int (Int.ofNat 0)) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.ofNat 0)))
--   | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.ofNat 0)))
--   | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.ofNat 0)))
--   | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.ofNat 0)) (Nat.mul 2 k))
--   | .wrap (.int (.ofNat k)) j => Nat.add m (gi (Int.ofNat 0))
--   | .wrap (.int (.negSucc k)) j => Nat.add j (Nat.add (gi (Int.ofNat 0)) (Nat.mul 4 k))
--   | _ => 0
-- NOTE: offset pattern `Int.ofNat (1 + k)` vs literal `Int.ofNat 0` stops the unification (0 < 1),
--       `Int.ofNat k` binds `k := 0` and `j := m`
#testOptimize [ "UnifyPattern_23" ] (norm-result: 1)
  intLit gi (.wrap (.int 0) m) 0 ===>
    match Value.wrap (Value.int (Int.ofNat 0)) m with
    | .wrap _ 5 => 100
    | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.ofNat 0)))
    | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.ofNat 0)))
    | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.ofNat 0)))
    | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.ofNat 0)) (Nat.mul 2 k))
    | .wrap (.int (.ofNat _k)) _j => Nat.add m (gi (Int.ofNat 0))
    | .wrap (.int (.negSucc k)) j => Nat.add j (Nat.add (gi (Int.ofNat 0)) (Nat.mul 4 k))
    | _ => 0

-- intLit gi (.wrap (.int (-1)) m) (-1) ===>
--   match Value.wrap (Value.int (Int.negSucc 0)) m with
--   | .wrap _ 5 => 100
--   | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.negSucc 0)))
--   | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.negSucc 0)))
--   | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.negSucc 0)))
--   | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.negSucc 0)) (Nat.mul 2 k))
--   | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.negSucc 0)) (Nat.mul 3 k))
--   | .wrap (.int (.negSucc k)) j => Nat.add m (gi (Int.negSucc 0))
--   | _ => 0
-- NOTE: `Int.negSucc (k + 1)` (normalized to `Int.neg (Int.ofNat (2 + k))`) vs literal `Int.negSucc 0`
--       stops the unification (1 < 2), `Int.negSucc 2` vs `Int.negSucc 0` stops the unification,
--       `Int.negSucc k` binds `k := 0` and `j := m`
#testOptimize [ "UnifyPattern_24" ] (norm-result: 1)
  intLit gi (.wrap (.int (-1)) m) (-1) ===>
    match Value.wrap (Value.int (Int.negSucc 0)) m with
    | .wrap _ 5 => 100
    | .wrap (.int 3) j => Nat.add 100 (Nat.add j (gi (Int.negSucc 0)))
    | .wrap (.int (.negSucc 2)) j => Nat.add 300 (Nat.add j (gi (Int.negSucc 0)))
    | .wrap (.int (.ofNat (k + 1))) j => Nat.add j (Nat.add k (gi (Int.negSucc 0)))
    | .wrap (.int (.negSucc (k + 1))) j => Nat.add j (Nat.add (gi (Int.negSucc 0)) (Nat.mul 2 k))
    | .wrap (.int (.ofNat k)) j => Nat.add j (Nat.add (gi (Int.negSucc 0)) (Nat.mul 3 k))
    | .wrap (.int (.negSucc _k)) _j => Nat.add m (gi (Int.negSucc 0))
    | _ => 0

/-! ### String patterns (literals and `String.mk`) -/

def strLit (x : Value) (z : String) : Nat :=
  match x with
  | .str "ab" => z.length + 100
  | .str _ => z.length
  | _ => 0

-- strLit (.str s) s ===>
--   match Value.str s with
--   | .str "ab" => 102
--   | .str _ => String.length s
--   | _ => 0
-- NOTE: string literal pattern vs free variable discriminator binds `s := "ab"`
#testOptimize [ "UnifyPattern_25" ] (norm-result: 1)
  strLit (.str s) s ===>
    match Value.str s with
    | .str "ab" => 102
    | .str _ => String.length s
    | _ => 0

-- strLit (.str (String.mk [c1, c2])) (String.mk [c1, c2]) ===>
--   match Value.str (String.mk [c1, c2]) with
--   | .str "ab" => Nat.add 100 (String.length (String.mk ['a', 'b']))
--   | .str _ => String.length (String.mk [c1, c2])
--   | _ => 0
-- NOTE: string literal pattern vs `String.mk` discriminator is unified as a list of characters
--       (`c1 := 'a'`, `c2 := 'b'`)
#testOptimize [ "UnifyPattern_26" ] (norm-result: 1)
  strLit (.str (String.mk [c1, c2])) (String.mk [c1, c2]) ===>
    match Value.str (String.mk [c1, c2]) with
    | .str "ab" => Nat.add 100 (String.length (String.mk ['a', 'b']))
    | .str _ => String.length (String.mk [c1, c2])
    | _ => 0

-- strLit (.str (String.mk cs)) (String.mk cs) ===>
--   match Value.str (String.mk cs) with
--   | .str "ab" => Nat.add 100 (String.length (String.mk ['a', 'b']))
--   | .str _ => String.length (String.mk cs)
--   | _ => 0
-- NOTE: string literal pattern vs `String.mk cs` discriminator binds `cs := ['a', 'b']`
#testOptimize [ "UnifyPattern_27" ] (norm-result: 1)
  strLit (.str (String.mk cs)) (String.mk cs) ===>
    match Value.str (String.mk cs) with
    | .str "ab" => Nat.add 100 (String.length (String.mk ['a', 'b']))
    | .str _ => String.length (String.mk cs)
    | _ => 0

def strCtor (x : Value) (z : String) : Nat :=
  match x with
  | .wrap _ 5 => z.length + 100
  | .wrap (.str ⟨cs⟩) j => cs.length + z.length + j
  | _ => 0

-- strCtor (.wrap (.str s) m) s ===>
--   match Value.wrap (Value.str s) m with
--   | .wrap _ 5 => Nat.add 100 (String.length s)
--   | .wrap (.str ⟨cs⟩) j => Nat.add m (Nat.add (String.length (String.mk cs)) (List.length cs))
--   | _ => 0
-- NOTE: `String.mk cs` pattern vs free variable discriminator binds `s := String.mk cs`
#testOptimize [ "UnifyPattern_28" ] (norm-result: 1)
  strCtor (.wrap (.str s) m) s ===>
    match Value.wrap (Value.str s) m with
    | .wrap _ 5 => Nat.add 100 (String.length s)
    | .wrap (.str ⟨cs⟩) _j => Nat.add m (Nat.add (String.length (String.mk cs)) (List.length cs))
    | _ => 0

-- strCtor (.wrap (.str (String.mk [c1, c2])) m) (String.mk [c1, c2]) ===>
--   match Value.wrap (Value.str (String.mk [c1, c2])) m with
--   | .wrap _ 5 => Nat.add 100 (String.length (String.mk [c1, c2]))
--   | .wrap (.str ⟨cs⟩) j => Nat.add m (Nat.add 2 (String.length (String.mk [c1, c2])))
--   | _ => 0
-- NOTE: `String.mk cs` pattern vs `String.mk [c1, c2]` discriminator binds `cs := [c1, c2]`
#testOptimize [ "UnifyPattern_29" ] (norm-result: 1)
  strCtor (.wrap (.str (String.mk [c1, c2])) m) (String.mk [c1, c2]) ===>
    match Value.wrap (Value.str (String.mk [c1, c2])) m with
    | .wrap _ 5 => Nat.add 100 (String.length (String.mk [c1, c2]))
    | .wrap (.str ⟨_cs⟩) _j => Nat.add m (Nat.add 2 (String.length (String.mk [c1, c2])))
    | _ => 0

-- strCtor (.wrap (.str "ab") m) "ab" ===>
--   match Value.wrap (Value.str "ab") m with
--   | .wrap _ 5 => 102
--   | .wrap (.str ⟨cs⟩) j => Nat.add 4 m
--   | _ => 0
-- NOTE: `String.mk cs` pattern vs string literal discriminator binds `cs := ['a', 'b']`
#testOptimize [ "UnifyPattern_30" ] (norm-result: 1)
  strCtor (.wrap (.str "ab") m) "ab" ===>
    match Value.wrap (Value.str "ab") m with
    | .wrap _ 5 => 102
    | .wrap (.str ⟨_cs⟩) _j => Nat.add 4 m
    | _ => 0

/-! ### Constructor constants, opaque constants and function applications as discriminators -/

def wrapCtor (g : Value → Nat) (x : Value) : Nat :=
  match x with
  | .wrap .unit 5 => 100
  | .wrap .unit k => g x + k
  | .wrap (.nat 5) k => g x + k
  | .wrap (.nat n) k => g x + n + k
  | .wrap .none k => g x + k
  | .wrap w k => g w + k
  | _ => 0

-- wrapCtor g (.wrap .unit m) ===>
--   match Value.wrap Value.unit m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add m (g (Value.wrap Value.unit m))
--   | .wrap (.nat 5) k => Nat.add k (g (Value.wrap Value.unit m))
--   | .wrap (.nat n) k => Nat.add k (Nat.add n (g (Value.wrap Value.unit m)))
--   | .wrap .none k => Nat.add k (g (Value.wrap Value.unit m))
--   | .wrap w k => Nat.add m (g Value.unit)
--   | _ => 0
-- NOTE: equal constructor constants (`.unit` vs `.unit`) continue the unification (`k := m`), a constructor
--       application or a distinct constructor constant vs `.unit` stops the unification (`k` is left unbound),
--       variable pattern `w` binds `w := .unit`
#testOptimize [ "UnifyPattern_31" ] (norm-result: 1)
  wrapCtor g (.wrap .unit m) ===>
    match Value.wrap Value.unit m with
    | .wrap .unit 5 => 100
    | .wrap .unit _k => Nat.add m (g (Value.wrap Value.unit m))
    | .wrap (.nat 5) k => Nat.add k (g (Value.wrap Value.unit m))
    | .wrap (.nat n) k => Nat.add k (Nat.add n (g (Value.wrap Value.unit m)))
    | .wrap .none k => Nat.add k (g (Value.wrap Value.unit m))
    | .wrap _w _k => Nat.add m (g Value.unit)
    | _ => 0

-- wrapCtor g (.wrap (.nat n) m) ===>
--   match Value.wrap (Value.nat n) m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add k (g (Value.wrap (Value.nat n) m))
--   | .wrap (.nat 5) k => Nat.add m (g (Value.wrap (Value.nat 5) m))
--   | .wrap (.nat n_1) k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
--   | .wrap .none k => Nat.add k (g (Value.wrap (Value.nat n) m))
--   | .wrap w k => Nat.add m (g (Value.nat n))
--   | _ => 0
-- NOTE: constructor constant vs constructor application discriminator stops the unification,
--       `.nat 5` binds `n := 5` which is also propagated in the discriminator occurrence `g x`
#testOptimize [ "UnifyPattern_32" ] (norm-result: 1)
  wrapCtor g (.wrap (.nat n) m) ===>
    match Value.wrap (Value.nat n) m with
    | .wrap .unit 5 => 100
    | .wrap .unit k => Nat.add k (g (Value.wrap (Value.nat n) m))
    | .wrap (.nat 5) _k => Nat.add m (g (Value.wrap (Value.nat 5) m))
    | .wrap (.nat _n) _k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
    | .wrap .none k => Nat.add k (g (Value.wrap (Value.nat n) m))
    | .wrap _w _k => Nat.add m (g (Value.nat n))
    | _ => 0

-- wrapCtor g (.wrap (f n) m) ===>
--   match Value.wrap (f n) m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add m (g (Value.wrap Value.unit m))
--   | .wrap (.nat 5) k => Nat.add m (g (Value.wrap (Value.nat 5) m))
--   | .wrap (.nat n) k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
--   | .wrap .none k => Nat.add m (g (Value.wrap Value.none m))
--   | .wrap w k => Nat.add m (g (f n))
--   | _ => 0
-- NOTE: constructor constant and constructor application patterns vs non constructor application
--       discriminator bind `f n` to the pattern
#testOptimize [ "UnifyPattern_33" ] (norm-result: 1)
  wrapCtor g (.wrap (f n) m) ===>
    match Value.wrap (f n) m with
    | .wrap .unit 5 => 100
    | .wrap .unit _k => Nat.add m (g (Value.wrap Value.unit m))
    | .wrap (.nat 5) _k => Nat.add m (g (Value.wrap (Value.nat 5) m))
    | .wrap (.nat n) _k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
    | .wrap .none _k => Nat.add m (g (Value.wrap Value.none m))
    | .wrap _w _k => Nat.add m (g (f n))
    | _ => 0

-- wrapCtor g (.wrap v0 m) ===>
--   match Value.wrap v0 m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add m (g (Value.wrap Value.unit m))
--   | .wrap (.nat 5) k => Nat.add m (g (Value.wrap (Value.nat 5) m))
--   | .wrap (.nat n) k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
--   | .wrap .none k => Nat.add m (g (Value.wrap Value.none m))
--   | .wrap w k => Nat.add m (g v0)
--   | _ => 0
-- NOTE: constructor constant and constructor application patterns vs opaque constant
--       discriminator bind `v0` to the pattern
#testOptimize [ "UnifyPattern_34" ] (norm-result: 1)
  wrapCtor g (.wrap v0 m) ===>
    match Value.wrap v0 m with
    | .wrap .unit 5 => 100
    | .wrap .unit _k => Nat.add m (g (Value.wrap Value.unit m))
    | .wrap (.nat 5) _k => Nat.add m (g (Value.wrap (Value.nat 5) m))
    | .wrap (.nat n) _k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
    | .wrap .none _k => Nat.add m (g (Value.wrap Value.none m))
    | .wrap _w _k => Nat.add m (g v0)
    | _ => 0

-- wrapCtor g (.wrap v m) ===>
--   match Value.wrap v m with
--   | .wrap .unit 5 => 100
--   | .wrap .unit k => Nat.add m (g (Value.wrap Value.unit m))
--   | .wrap (.nat 5) k => Nat.add m (g (Value.wrap (Value.nat 5) m))
--   | .wrap (.nat n) k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
--   | .wrap .none k => Nat.add m (g (Value.wrap Value.none m))
--   | .wrap w k => Nat.add m (g v)
--   | _ => 0
-- NOTE: constructor constant and constructor application patterns vs free variable
--       discriminator bind `v` to the pattern
#testOptimize [ "UnifyPattern_35" ] (norm-result: 1)
  wrapCtor g (.wrap v m) ===>
    match Value.wrap v m with
    | .wrap .unit 5 => 100
    | .wrap .unit _k => Nat.add m (g (Value.wrap Value.unit m))
    | .wrap (.nat 5) _k => Nat.add m (g (Value.wrap (Value.nat 5) m))
    | .wrap (.nat n) _k => Nat.add m (Nat.add n (g (Value.wrap (Value.nat n) m)))
    | .wrap .none _k => Nat.add m (g (Value.wrap Value.none m))
    | .wrap _w _k => Nat.add m (g v)
    | _ => 0

/-! ### Named patterns -/

def namedArg (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x, y with
  | _, p@(.nat 5) => g p + 100
  | p@(.nat k), _ => g p + k
  | p@(.pair a b), _ => g p + a + b
  | p@.unit, _ => g p
  | p@(.wrap q@(.nat k) j), _ => g p + g q + k + j
  | _, _ => 0

-- namedArg g v u ===>
--   match v, u with
--   | _, p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat k), _ => Nat.add k (g (Value.nat k))
--   | p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
--   | p@.unit, _ => g Value.unit
--   | p@(.wrap q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
--   | _, _ => 0
-- NOTE: each named pattern alias (incl. nested ones) is bound to its pattern (without named patterns)
#testOptimize [ "UnifyPattern_36" ] (norm-result: 1)
  namedArg g v u ===>
    match v, u with
    | _, _p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat k), _ => Nat.add k (g (Value.nat k))
    | _p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
    | _p@.unit, _ => g Value.unit
    | _p@(.wrap _q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
    | _, _ => 0

-- namedArg g (.nat (m + 2)) u ===>
--   match Value.nat (Nat.add 2 m), u with
--   | _, p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat k), _ => Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)
--   | p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
--   | p@.unit, _ => g Value.unit
--   | p@(.wrap q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
--   | _, _ => 0
#testOptimize [ "UnifyPattern_37" ] (norm-result: 1)
  namedArg g (.nat (m + 2)) u ===>
    match Value.nat (Nat.add 2 m), u with
    | _, _p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat _k), _ => Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)
    | _p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
    | _p@.unit, _ => g Value.unit
    | _p@(.wrap _q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
    | _, _ => 0

-- namedArg g (.pair m (m + 1)) u ===>
--   match Value.pair m (Nat.add 1 m), u with
--   | _, p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat k), _ => Nat.add k (g (Value.nat k))
--   | p@(.pair a b), _ => Nat.add (Nat.add m (g (Value.pair m (Nat.add 1 m)))) (Nat.add 1 m)
--   | p@.unit, _ => g Value.unit
--   | p@(.wrap q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
--   | _, _ => 0
#testOptimize [ "UnifyPattern_38" ] (norm-result: 1)
  namedArg g (.pair m (m + 1)) u ===>
    match Value.pair m (Nat.add 1 m), u with
    | _, _p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat k), _ => Nat.add k (g (Value.nat k))
    | _p@(.pair _a _b), _ => Nat.add (Nat.add m (g (Value.pair m (Nat.add 1 m)))) (Nat.add 1 m)
    | _p@.unit, _ => g Value.unit
    | _p@(.wrap _q@(.nat k) j), _ => Nat.add j (Nat.add k (Nat.add (g (Value.nat k)) (g (Value.wrap (Value.nat k) j))))
    | _, _ => 0

-- namedArg g (.wrap (.nat (m + 2)) m) u ===>
--   match Value.wrap (Value.nat (Nat.add 2 m)) m, u with
--   | _, p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat k), _ => Nat.add k (g (Value.nat k))
--   | p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
--   | p@.unit, _ => g Value.unit
--   | p@(.wrap q@(.nat k) j), _ =>
--       Nat.add m (Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (g (Value.wrap (Value.nat (Nat.add 2 m)) m))) (Nat.add 2 m))
--   | _, _ => 0
#testOptimize [ "UnifyPattern_39" ] (norm-result: 1)
  namedArg g (.wrap (.nat (m + 2)) m) u ===>
    match Value.wrap (Value.nat (Nat.add 2 m)) m, u with
    | _, _p@(.nat 5) => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat k), _ => Nat.add k (g (Value.nat k))
    | _p@(.pair a b), _ => Nat.add b (Nat.add a (g (Value.pair a b)))
    | _p@.unit, _ => g Value.unit
    | _p@(.wrap _q@(.nat _k) _j), _ =>
        Nat.add m (Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (g (Value.wrap (Value.nat (Nat.add 2 m)) m))) (Nat.add 2 m))
    | _, _ => 0

/-! ### Polymorphic constructors (type arguments) -/

def optPoly {α : Type} (g : Option α → Nat) (x : Option α) (y : Value) : Nat :=
  match x, y with
  | some v, .nat 5 => g (some v)
  | some _, .nat k => g x + k
  | _, _ => 0

-- ∀ (α : Type) (a : α) (g : Option α → Nat), optPoly g (some a) (.nat m) = n ===>
-- ∀ (α : Type) (a : α) (g : Option α → Nat),
--   n = match some a, Value.nat m with
--       | some v, .nat 5 => g (some a)
--       | some _, .nat k => Nat.add m (g (some a))
--       | _, _ => 0
-- NOTE: the type argument `α` of `some` is the same free variable in the pattern and in the discriminator
--       (no binding), the value argument binds `v := a`
#testOptimize [ "UnifyPattern_40" ] (norm-result: 1)
  ∀ (α : Type) (a : α) (g : Option α → Nat), optPoly g (some a) (.nat m) = n ===>
  ∀ (α : Type) (a : α) (g : Option α → Nat),
    n = match some a, Value.nat m with
        | some _v, .nat 5 => g (some a)
        | some _, .nat _k => Nat.add m (g (some a))
        | _, _ => 0

def optList (x : Option (List Nat)) (z : List Nat) : Nat :=
  match x with
  | some [5] => 100
  | some (k :: ks) => k + ks.length + z.length
  | _ => 0

-- optList (some (m :: ms)) (m :: ms) ===>
--   match some (m :: ms) with
--   | some [5] => 100
--   | some (k :: ks) => Nat.add (Nat.add m (List.length ms)) (Nat.add 1 (List.length ms))
--   | _ => 0
-- NOTE: the type argument `List Nat` of `some` (an inductive type application) is skipped,
--       the nested constructor `List.cons` binds `k := m` and `ks := ms`
#testOptimize [ "UnifyPattern_41" ] (norm-result: 1)
  optList (some (m :: ms)) (m :: ms) ===>
    match some (m :: ms) with
    | some [5] => 100
    | some (_k :: _ks) => Nat.add (Nat.add m (List.length ms)) (Nat.add 1 (List.length ms))
    | _ => 0

/-! ### Opaque constant discriminator -/

def opaqueDiscr (g : Value → Nat) (x : Value) : Nat :=
  match x with
  | .nat k => g x + k
  | y => g x + g y

-- opaqueDiscr g v0 ===>
--   match v0 with
--   | .nat k => Nat.add k (g (Value.nat k))
--   | y => Nat.add (g v0) (g v0)
-- NOTE: constructor application pattern vs opaque constant discriminator binds `v0 := Value.nat k`
--       and the match alternative is optimized in a new context (the binding must not leak into
--       the following alternatives: `g v0` is left unchanged in the variable pattern alternative)
#testOptimize [ "UnifyPattern_42" ] (norm-result: 1)
  opaqueDiscr g v0 ===>
    match v0 with
    | .nat k => Nat.add k (g (Value.nat k))
    | _y => Nat.add (g v0) (g v0)

-- intArg gi (.int (Int.negSucc m)) (Int.ofNat m) ===>
--   match Value.int (Int.neg (Int.ofNat (Nat.add 1 m))) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat m))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat m))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 2))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat m))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 m)
--   | _ => 0
-- NOTE: `Int.negSucc m` discriminator is normalized to `Int.neg (Int.ofNat (1 + m))`: the `Int.negSucc`
--       variable patterns (normalized to `Int.neg (Int.ofNat _)`) unify through `Int.neg` and `Int.ofNat`
--       (`m := 1 + k` and `k := m`), the `Int.negSucc 2` literal pattern binds `m := 2`
#testOptimize [ "UnifyPattern_43" ] (norm-result: 1)
  intArg gi (.int (Int.negSucc m)) (Int.ofNat m) ===>
    match Value.int (Int.neg (Int.ofNat (Nat.add 1 m))) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat m))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat m))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 2))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat m))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 k)
    | .int (.negSucc _k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 m)
    | _ => 0

-- intArg gi (.int (-w)) w ===>
--   match Value.int (Int.neg w) with
--   | .int 3 => Nat.add 100 (gi w)
--   | .int (.ofNat 7) => Nat.add 107 (gi w)
--   | .int (.negSucc 2) => Nat.add 300 (gi w)
--   | .int (.ofNat (k + 1)) => Nat.add k (gi w)
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi w) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.neg w` discriminator (`w` free variable): the `Int.negSucc` variable patterns unify through
--       `Int.neg` and bind `w := Int.ofNat (2 + k)` and `w := Int.ofNat (1 + k)`, the other patterns
--       bind the expression `Int.neg w` to the pattern (not visible in the rhs)
#testOptimize [ "UnifyPattern_44" ] (norm-result: 1)
  intArg gi (.int (-w)) w ===>
    match Value.int (Int.neg w) with
    | .int 3 => Nat.add 100 (gi w)
    | .int (.ofNat 7) => Nat.add 107 (gi w)
    | .int (.negSucc 2) => Nat.add 300 (gi w)
    | .int (.ofNat (k + 1)) => Nat.add k (gi w)
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi w) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (-(hi w))) (hi w) ===>
--   match Value.int (Int.neg (hi w)) with
--   | .int 3 => Nat.add 100 (gi (hi w))
--   | .int (.ofNat 7) => Nat.add 107 (gi (hi w))
--   | .int (.negSucc 2) => Nat.add 300 (gi (hi w))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (hi w))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (hi w)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.neg (hi w)` discriminator (non constructor application under `Int.neg`): the `Int.negSucc`
--       variable patterns unify through `Int.neg` and bind `hi w := Int.ofNat (2 + k)` and `hi w := Int.ofNat (1 + k)`
#testOptimize [ "UnifyPattern_45" ] (norm-result: 1)
  intArg gi (.int (-(hi w))) (hi w) ===>
    match Value.int (Int.neg (hi w)) with
    | .int 3 => Nat.add 100 (gi (hi w))
    | .int (.ofNat 7) => Nat.add 107 (gi (hi w))
    | .int (.negSucc 2) => Nat.add 300 (gi (hi w))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (hi w))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (hi w)) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (-(Int.ofNat (h n)))) (Int.ofNat (h n)) ===>
--   match Value.int (Int.neg (Int.ofNat (h n))) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat (h n)))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat (h n)))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 3))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (h n)))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat (h n))) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
--   | _ => 0
-- NOTE: `Int.neg (Int.ofNat (h n))` discriminator: the `Int.negSucc` patterns unify through `Int.neg` and
--       `Int.ofNat` down to the Nat argument and bind `h n := 3`, `h n := 2 + k` and `h n := 1 + k`
#testOptimize [ "UnifyPattern_46" ] (norm-result: 1)
  intArg gi (.int (-(Int.ofNat (h n)))) (Int.ofNat (h n)) ===>
    match Value.int (Int.neg (Int.ofNat (h n))) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat (h n)))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat (h n)))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 3))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat (h n)))
    | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat (Nat.add 2 k))) (Nat.mul 2 k)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat (h n))) (Nat.mul 3 k)
    | .int (.negSucc k) => Nat.add (gi (Int.ofNat (Nat.add 1 k))) (Nat.mul 4 k)
    | _ => 0

-- intArg gi (.int (-(Int.ofNat (m + 2)))) (Int.ofNat m) ===>
--   match Value.int (Int.neg (Int.ofNat (Nat.add 2 m))) with
--   | .int 3 => Nat.add 100 (gi (Int.ofNat m))
--   | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat m))
--   | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 1))
--   | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat m))
--   | .int (.negSucc (k + 1)) => Nat.add (gi (Int.ofNat m)) (Nat.mul 2 m)
--   | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 k)
--   | .int (.negSucc k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 (Nat.add 1 m))
--   | _ => 0
-- NOTE: `Int.neg (Int.ofNat (2 + m))` discriminator: the `Int.negSucc` patterns unify through `Int.neg` and
--       `Int.ofNat` down to the Nat offsets and bind `m := 1` (3 ≥ 2), `k := m` (2 = 2) and `k := 1 + m` (1 < 2)
#testOptimize [ "UnifyPattern_47" ] (norm-result: 1)
  intArg gi (.int (-(Int.ofNat (m + 2)))) (Int.ofNat m) ===>
    match Value.int (Int.neg (Int.ofNat (Nat.add 2 m))) with
    | .int 3 => Nat.add 100 (gi (Int.ofNat m))
    | .int (.ofNat 7) => Nat.add 107 (gi (Int.ofNat m))
    | .int (.negSucc 2) => Nat.add 300 (gi (Int.ofNat 1))
    | .int (.ofNat (k + 1)) => Nat.add k (gi (Int.ofNat m))
    | .int (.negSucc (_k + 1)) => Nat.add (gi (Int.ofNat m)) (Nat.mul 2 m)
    | .int (.ofNat k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 3 k)
    | .int (.negSucc _k) => Nat.add (gi (Int.ofNat m)) (Nat.mul 4 (Nat.add 1 m))
    | _ => 0

/-! ### Named patterns: alias re-optimized w.r.t. the unification of its pattern -/

def namedOffset (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => g y + 100
  | p@(.nat (k + 2)), _ => g p + k
  | p@(.nat k), _ => g p + k
  | _, _ => 0

-- namedOffset g (.nat (m + 5)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 5 m), Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat (k + 2)), _ => Nat.add (g (Value.nat (Nat.add 5 m))) (Nat.add 3 m)
--   | p@(.nat k), _ => Nat.add (g (Value.nat (Nat.add 5 m))) (Nat.add 5 m)
--   | _, _ => 0
-- NOTE: the alias `p` is bound to its pattern `Value.nat (2 + k)` and re-optimized once replaced:
--       with `k := 3 + m`, `g p` becomes `g (Value.nat (5 + m))` (offsets are folded)
#testOptimize [ "UnifyPattern_48" ] (norm-result: 1)
  namedOffset g (.nat (m + 5)) (.nat (h n)) ===>
    match Value.nat (Nat.add 5 m), Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat (_k + 2)), _ => Nat.add (g (Value.nat (Nat.add 5 m))) (Nat.add 3 m)
    | _p@(.nat _k), _ => Nat.add (g (Value.nat (Nat.add 5 m))) (Nat.add 5 m)
    | _, _ => 0

-- namedOffset g (.nat 7) (.nat (h n)) ===>
--   match Value.nat 7, Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat (k + 2)), _ => Nat.add 5 (g (Value.nat 7))
--   | p@(.nat k), _ => Nat.add 7 (g (Value.nat 7))
--   | _, _ => 0
-- NOTE: with `k := 5`, the alias `p` (bound to `Value.nat (2 + k)`) is re-optimized to `Value.nat 7`
#testOptimize [ "UnifyPattern_49" ] (norm-result: 1)
  namedOffset g (.nat 7) (.nat (h n)) ===>
    match Value.nat 7, Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat (_k + 2)), _ => Nat.add 5 (g (Value.nat 7))
    | _p@(.nat _k), _ => Nat.add 7 (g (Value.nat 7))
    | _, _ => 0

-- namedOffset g (.nat (h m)) (.nat (h n)) ===>
--   match Value.nat (h m), Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@(.nat (k + 2)), _ => Nat.add k (g (Value.nat (Nat.add 2 k)))
--   | p@(.nat k), _ => Nat.add (h m) (g (Value.nat (h m)))
--   | _, _ => 0
-- NOTE: offset pattern vs non constructor application discriminator binds `h m := 2 + k`, the alias `p`
--       is left bound to its pattern `Value.nat (2 + k)`; variable pattern binds `k := h m` and the alias
--       `p` is re-optimized to `Value.nat (h m)`
#testOptimize [ "UnifyPattern_50" ] (norm-result: 1)
  namedOffset g (.nat (h m)) (.nat (h n)) ===>
    match Value.nat (h m), Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@(.nat (k + 2)), _ => Nat.add k (g (Value.nat (Nat.add 2 k)))
    | _p@(.nat _k), _ => Nat.add (h m) (g (Value.nat (h m)))
    | _, _ => 0

def varAlias (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => g y + 100
  | p@k, .wrap q _ => g p + g k + g q
  | _, _ => 0

-- varAlias g (.nat (m + 2)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 2 m), Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@k, .wrap q _ => Nat.add (g q) (Nat.add (g (Value.nat (Nat.add 2 m))) (g (Value.nat (Nat.add 2 m))))
--   | _, _ => 0
-- NOTE: named variable pattern `p@k`: `k` is bound to the discriminator and the alias `p` (bound to `k`)
--       is re-optimized to the discriminator as well
#testOptimize [ "UnifyPattern_51" ] (norm-result: 1)
  varAlias g (.nat (m + 2)) (.nat (h n)) ===>
    match Value.nat (Nat.add 2 m), Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@_k, .wrap q _ => Nat.add (g q) (Nat.add (g (Value.nat (Nat.add 2 m))) (g (Value.nat (Nat.add 2 m))))
    | _, _ => 0

-- varAlias g v (.nat (h n)) ===>
--   match v, Value.nat (h n) with
--   | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
--   | p@k, .wrap q _ => Nat.add (g q) (Nat.add (g v) (g v))
--   | _, _ => 0
-- NOTE: named variable pattern `p@k` vs free variable discriminator: `k := v` and the alias `p` is
--       re-optimized to `v`
#testOptimize [ "UnifyPattern_52" ] (norm-result: 1)
  varAlias g v (.nat (h n)) ===>
    match v, Value.nat (h n) with
    | _, .nat 5 => Nat.add 100 (g (Value.nat 5))
    | _p@_k, .wrap q _ => Nat.add (g q) (Nat.add (g v) (g v))
    | _, _ => 0

-- NOTE: `generalizing := false` so that the named pattern hypothesis `h : p = Value.nat k` is not added
--       as an extra discriminator of the inner match
def nestedAlias (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x with
  | .nat 5 => 100
  | p@(.nat k) =>
      match (generalizing := false) y, p with
      | .nat 5, _ => 50
      | _, .nat j => g p + j + k
      | _, _ => 0
  | _ => 0

-- nestedAlias g v (.nat (h n)) ===>
--   match v with
--   | .nat 5 => 100
--   | p@(.nat k) =>
--     match Value.nat (h n), Value.nat k with
--     | .nat 5, _ => 50
--     | _, .nat j => Nat.add k (Nat.add k (g (Value.nat k)))
--     | _, _ => 0
--   | _ => 0
-- NOTE: alias `p` used as discriminator of a nested match: `p` is replaced by its pattern `Value.nat k`
--       and the nested variable pattern then binds `j := k`
#testOptimize [ "UnifyPattern_53" ] (norm-result: 1)
  nestedAlias g v (.nat (h n)) ===>
    match v with
    | .nat 5 => 100
    | _p@(.nat k) =>
      match Value.nat (h n), Value.nat k with
      | .nat 5, _ => 50
      | _, .nat _j => Nat.add k (Nat.add k (g (Value.nat k)))
      | _, _ => 0
    | _ => 0

-- nestedAlias g (.nat (m + 2)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 2 m) with
--   | .nat 5 => 100
--   | p@(.nat k) =>
--     match Value.nat (h n), Value.nat (Nat.add 2 m) with
--     | .nat 5, _ => 50
--     | _, .nat j => Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)) (Nat.add 2 m)
--     | _, _ => 0
--   | _ => 0
-- NOTE: alias `p` used as discriminator of a nested match: with `k := 2 + m`, `p` is re-optimized to
--       `Value.nat (2 + m)` (also as discriminator) and the nested variable pattern binds `j := 2 + m`
#testOptimize [ "UnifyPattern_54" ] (norm-result: 1)
  nestedAlias g (.nat (m + 2)) (.nat (h n)) ===>
    match Value.nat (Nat.add 2 m) with
    | .nat 5 => 100
    | _p@(.nat _k) =>
      match Value.nat (h n), Value.nat (Nat.add 2 m) with
      | .nat 5, _ => 50
      | _, .nat _j => Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)) (Nat.add 2 m)
      | _, _ => 0
    | _ => 0

-- nestedAlias g (.nat (h m)) (.nat (h n)) ===>
--   match Value.nat (h m) with
--   | .nat 5 => 100
--   | p@(.nat k) =>
--     match Value.nat (h n), Value.nat (h m) with
--     | .nat 5, _ => 50
--     | _, .nat j => Nat.add (h m) (Nat.add (h m) (g (Value.nat (h m))))
--     | _, _ => 0
--   | _ => 0
-- NOTE: alias `p` used as discriminator of a nested match: with `k := h m`, `p` is re-optimized to
--       `Value.nat (h m)` (also as discriminator) and the nested variable pattern binds `j := h m`
#testOptimize [ "UnifyPattern_55" ] (norm-result: 1)
  nestedAlias g (.nat (h m)) (.nat (h n)) ===>
    match Value.nat (h m) with
    | .nat 5 => 100
    | _p@(.nat _k) =>
      match Value.nat (h n), Value.nat (h m) with
      | .nat 5, _ => 50
      | _, .nat _j => Nat.add (h m) (Nat.add (h m) (g (Value.nat (h m))))
      | _, _ => 0
    | _ => 0

/-! ### Named pattern hypothesis -/

variable (q : ∀ {a b : Value}, a = b → Nat)

def hypUse (q : ∀ {a b : Value}, a = b → Nat) (x : Value) : Nat :=
  match x with
  | .pair _ 3 => 100
  | _p@hp:(.nat k) => q hp + k
  | _ => 0

-- hypUse q v ===>
--   match v with
--   | .pair _ 3 => 100
--   | p@hp:(.nat k) => Nat.add k (q (Eq.refl (Value.nat k)))
--   | _ => 0
-- NOTE: match not reduced (free variable discriminator): the named pattern hypothesis `hp : p = Value.nat k`
--       is replaced by `Eq.refl (Value.nat k)` since the alias `p` is bound to its pattern
#testOptimize [ "UnifyPattern_56" ] (norm-result: 1)
  hypUse q v ===>
    match v with
    | .pair _ 3 => 100
    | _p@_hp:(.nat k) => Nat.add k (q (Eq.refl (Value.nat k)))
    | _ => 0

-- hypUse q (.nat (m + 2)) ===> Nat.add (Nat.add 2 m) (q (Eq.refl (Value.nat (Nat.add 2 m))))
-- NOTE: the match is reduced to the named pattern alternative (`k := 2 + m`) and, as in the definition
--       of the matcher `hypUse.match_1`, the hypothesis `hp` is instantiated with `Eq.refl`.
#testOptimize [ "UnifyPattern_57" ] (norm-result: 1)
  hypUse q (.nat (m + 2)) ===> Nat.add (Nat.add 2 m) (q (Eq.refl (Value.nat (Nat.add 2 m))))

-- NOTE: the nested match on the alias `p` implicitly uses the named pattern hypothesis
--       (added as an extra discriminator by Lean, see `nestedAlias` above)
def nestedAliasHyp (g : Value → Nat) (x : Value) : Nat :=
  match x with
  | .pair _ 3 => 100
  | p@(.nat k) =>
      match p with
      | .nat j => g p + j + k
      | _ => 0
  | _ => 0

-- nestedAliasHyp g (.nat (m + 2)) ===>
--   Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)) (Nat.add 2 m)
-- NOTE: the outer match is reduced to the named pattern alternative (`k := 2 + m`, `p := Value.nat (2 + m)`)
--       and the nested match is then reduced as well (`j := 2 + m`).
#testOptimize [ "UnifyPattern_58" ] (norm-result: 1)
  nestedAliasHyp g (.nat (m + 2)) ===>
    Nat.add (Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add 2 m)) (Nat.add 2 m)

def hypTwo (q : ∀ {a b : Value}, a = b → Nat) (x y : Value) : Nat :=
  match x, y with
  | .pair _ 3, _ => 100
  | _p@hp:(.nat k), _r@hr:(.nat j) => q hp + q hr + k + j
  | _, _ => 0

-- hypTwo q (.nat (m + 2)) v ===>
--   match Value.nat (Nat.add 2 m), v with
--   | .pair _ 3, _ => 100
--   | p@hp:(.nat k), r@hr:(.nat j) =>
--       Nat.add j (Nat.add (Nat.add (q (Eq.refl (Value.nat j))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m))
--   | _, _ => 0
-- NOTE: match not reduced (second discriminator is a free variable): both named pattern hypotheses are
--       replaced by `Eq.refl` of their (unified) pattern, `k := 2 + m` and `v := Value.nat j`
#testOptimize [ "UnifyPattern_59" ] (norm-result: 1)
  hypTwo q (.nat (m + 2)) v ===>
    match Value.nat (Nat.add 2 m), v with
    | .pair _ 3, _ => 100
    | _p@_hp:(.nat _k), _r@_hr:(.nat j) =>
        Nat.add j (Nat.add (Nat.add (q (Eq.refl (Value.nat j))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m))
    | _, _ => 0

-- hypTwo q (.nat (m + 2)) (.nat (h m)) ===>
--   Nat.add (h m) (Nat.add (Nat.add (q (Eq.refl (Value.nat (h m)))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m))
-- NOTE: match reduced on two discriminators with named patterns: both hypotheses are instantiated with `Eq.refl`
#testOptimize [ "UnifyPattern_60" ] (norm-result: 1)
  hypTwo q (.nat (m + 2)) (.nat (h m)) ===>
    Nat.add (h m) (Nat.add (Nat.add (q (Eq.refl (Value.nat (h m)))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m))

def hypMatchH (q : ∀ {a b : Value}, a = b → Nat) (x : Value) : Nat :=
  match hx : x with
  | .pair _ 3 => 100
  | _p@hp:(.nat k) => q hp + q hx + k
  | _ => 0

-- hypMatchH q v ===>
--   match hx : v with
--   | .pair _ 3 => 100
--   | p@hp:(.nat k) => Nat.add k (Nat.add (q (Eq.refl (Value.nat k))) (q (Eq.refl (Value.nat k))))
--   | _ => 0
-- NOTE: `match hx : x with` hypothesis and named pattern hypothesis are both replaced by `Eq.refl` of the pattern.
--       The expected term is written as an explicit matcher application: the binder type of `hx` in the
--       named pattern alternative is `v = namedPattern p (Value.nat k) hp` (as elaborated by Lean in the
--       definition), which cannot be obtained with the `match` syntax.
#testOptimize [ "UnifyPattern_61" ] (norm-result: 1)
  hypMatchH q v ===>
    hypMatchH.match_1 (fun _ => Nat) v
      (fun (a : Nat) (_hx : v = Value.pair a 3) => 100)
      (fun (_p : Value) (k : Nat) (hp : _p = Value.nat k) (_hx : v = namedPattern _p (Value.nat k) hp) =>
         Nat.add k (Nat.add (q (Eq.refl (Value.nat k))) (q (Eq.refl (Value.nat k)))))
      (fun (x : Value) (_hx : v = x) => 0)

-- hypMatchH q (.nat (m + 2)) ===>
--   Nat.add (Nat.add (q (Eq.refl (Value.nat (Nat.add 2 m)))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m)
-- NOTE: match reduced: `match hx : x with` hypothesis and named pattern hypothesis are both instantiated with `Eq.refl`
#testOptimize [ "UnifyPattern_62" ] (norm-result: 1)
  hypMatchH q (.nat (m + 2)) ===>
    Nat.add (Nat.add (q (Eq.refl (Value.nat (Nat.add 2 m)))) (q (Eq.refl (Value.nat (Nat.add 2 m))))) (Nat.add 2 m)


def hypNested (q : ∀ {a b : Value}, a = b → Nat) (x : Value) : Nat :=
  match x with
  | .pair _ 3 => 100
  | _p@hp:(.wrap _r@hr:(.nat k) j) => q hp + q hr + k + j
  | _ => 0

-- hypNested q v ===>
--   match v with
--   | .pair _ 3 => 100
--   | p@hp:(.wrap r@hr:(.nat k) j) =>
--       Nat.add j (Nat.add k (Nat.add (q (Eq.refl (Value.nat k))) (q (Eq.refl (Value.wrap (Value.nat k) j)))))
--   | _ => 0
-- NOTE: the hypothesis `hp : p = Value.wrap (namedPattern r (Value.nat k) hr) j` of the outer named pattern
--       must be replaced by `Eq.refl` of its pattern without named patterns.
#testOptimize [ "UnifyPattern_63" ] (norm-result: 1)
  hypNested q v ===>
    match v with
    | .pair _ 3 => 100
    | _p@_hp:(.wrap _r@_hr:(.nat k) j) =>
        Nat.add j (Nat.add k (Nat.add (q (Eq.refl (Value.nat k))) (q (Eq.refl (Value.wrap (Value.nat k) j)))))
    | _ => 0

-- hypNested q (.wrap (.nat (m + 2)) m) ===>
--   Nat.add m (Nat.add (Nat.add (q (Eq.refl (Value.nat (Nat.add 2 m)))) (q (Eq.refl (Value.wrap (Value.nat (Nat.add 2 m)) m)))) (Nat.add 2 m))
-- NOTE: match reduced: the hypothesis `hp` of the outer named pattern must be instantiated with `Eq.refl`
--       of the discriminator.
#testOptimize [ "UnifyPattern_64" ] (norm-result: 1)
  hypNested q (.wrap (.nat (m + 2)) m) ===>
    Nat.add m (Nat.add (Nat.add (q (Eq.refl (Value.nat (Nat.add 2 m)))) (q (Eq.refl (Value.wrap (Value.nat (Nat.add 2 m)) m)))) (Nat.add 2 m))

/-! ### Named pattern hypothesis: alias re-optimized w.r.t. the unification of its pattern -/

def hypVar (q : ∀ {a b : Value}, a = b → Nat) (g : Value → Nat) (x y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => 100
  | p@hp:k, .wrap _ _ => q hp + g p + g k
  | _, _ => 0

-- hypVar q g (.nat (m + 2)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 2 m), Value.nat (h n) with
--   | _, .nat 5 => 100
--   | p@hp:k, .wrap _ _ =>
--       Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add (g (Value.nat (Nat.add 2 m))) (q (Eq.refl (Value.nat (Nat.add 2 m)))))
--   | _, _ => 0
-- NOTE: named variable pattern `p@hp:k`: `k` is bound to the discriminator, the alias `p` and the hypothesis
--       `hp` (bound to `k` and `Eq.refl k`) are re-optimized to the discriminator
#testOptimize [ "UnifyPattern_65" ] (norm-result: 1)
  hypVar q g (.nat (m + 2)) (.nat (h n)) ===>
    match Value.nat (Nat.add 2 m), Value.nat (h n) with
    | _, .nat 5 => 100
    | _p@_hp:_k, .wrap _ _ =>
        Nat.add (g (Value.nat (Nat.add 2 m))) (Nat.add (g (Value.nat (Nat.add 2 m))) (q (Eq.refl (Value.nat (Nat.add 2 m)))))
    | _, _ => 0

def hypOffset (q : ∀ {a b : Value}, a = b → Nat) (g : Value → Nat) (x y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => 100
  | p@hp:(.nat (k + 2)), _ => q hp + g p + k
  | _p@hp:(.nat k), _ => q hp + k
  | _, _ => 0

-- hypOffset q g (.nat (m + 5)) (.nat (h n)) ===>
--   match Value.nat (Nat.add 5 m), Value.nat (h n) with
--   | _, .nat 5 => 100
--   | p@hp:(.nat (k + 2)), _ =>
--       Nat.add (Nat.add (g (Value.nat (Nat.add 5 m))) (q (Eq.refl (Value.nat (Nat.add 5 m))))) (Nat.add 3 m)
--   | p@hp:(.nat k), _ => Nat.add (Nat.add 5 m) (q (Eq.refl (Value.nat (Nat.add 5 m))))
--   | _, _ => 0
-- NOTE: with `k := 3 + m`, the alias `p` and the hypothesis `hp` (bound to `Value.nat (2 + k)` and
--       `Eq.refl (Value.nat (2 + k))`) are re-optimized with the offsets folded
#testOptimize [ "UnifyPattern_66" ] (norm-result: 1)
  hypOffset q g (.nat (m + 5)) (.nat (h n)) ===>
    match Value.nat (Nat.add 5 m), Value.nat (h n) with
    | _, .nat 5 => 100
    | _p@_hp:(.nat (_k + 2)), _ =>
        Nat.add (Nat.add (g (Value.nat (Nat.add 5 m))) (q (Eq.refl (Value.nat (Nat.add 5 m))))) (Nat.add 3 m)
    | _p@_hp:(.nat _k), _ => Nat.add (Nat.add 5 m) (q (Eq.refl (Value.nat (Nat.add 5 m))))
    | _, _ => 0

-- hypOffset q g (.nat (h m)) (.nat (h n)) ===>
--   match Value.nat (h m), Value.nat (h n) with
--   | _, .nat 5 => 100
--   | p@hp:(.nat (k + 2)), _ => Nat.add k (Nat.add (g (Value.nat (Nat.add 2 k))) (q (Eq.refl (Value.nat (Nat.add 2 k)))))
--   | p@hp:(.nat k), _ => Nat.add (h m) (q (Eq.refl (Value.nat (h m))))
--   | _, _ => 0
-- NOTE: offset pattern vs non constructor application discriminator binds `h m := 2 + k`, the hypothesis `hp`
--       is `Eq.refl` of the pattern; variable pattern binds `k := h m` and `hp` is re-optimized to
--       `Eq.refl (Value.nat (h m))`
#testOptimize [ "UnifyPattern_67" ] (norm-result: 1)
  hypOffset q g (.nat (h m)) (.nat (h n)) ===>
    match Value.nat (h m), Value.nat (h n) with
    | _, .nat 5 => 100
    | _p@_hp:(.nat (k + 2)), _ => Nat.add k (Nat.add (g (Value.nat (Nat.add 2 k))) (q (Eq.refl (Value.nat (Nat.add 2 k)))))
    | _p@_hp:(.nat _k), _ => Nat.add (h m) (q (Eq.refl (Value.nat (h m))))
    | _, _ => 0

def hypInt (q : ∀ {a b : Value}, a = b → Nat) (g : Value → Nat) (x y : Value) : Nat :=
  match x, y with
  | _, .nat 5 => 100
  | p@hp:(.int (.negSucc (k + 1))), _ => q hp + g p + k
  | _, _ => 0

-- hypInt q g (.int (-w)) (.nat (h n)) ===>
--   match Value.int (Int.neg w), Value.nat (h n) with
--   | _, .nat 5 => 100
--   | p@hp:(.int (.negSucc (k + 1))), _ =>
--       Nat.add k (Nat.add (g (Value.int (Int.neg (Int.ofNat (Nat.add 2 k))))) (q (Eq.refl (Value.int (Int.neg (Int.ofNat (Nat.add 2 k)))))))
--   | _, _ => 0
-- NOTE: the alias `p` and the hypothesis `hp` are bound to the normalized pattern
--       `Value.int (Int.neg (Int.ofNat (2 + k)))` (`w := Int.ofNat (2 + k)` is not visible in the rhs)
#testOptimize [ "UnifyPattern_68" ] (norm-result: 1)
  hypInt q g (.int (-w)) (.nat (h n)) ===>
    match Value.int (Int.neg w), Value.nat (h n) with
    | _, .nat 5 => 100
    | _p@_hp:(.int (.negSucc (k + 1))), _ =>
        Nat.add k (Nat.add (g (Value.int (Int.neg (Int.ofNat (Nat.add 2 k))))) (q (Eq.refl (Value.int (Int.neg (Int.ofNat (Nat.add 2 k)))))))
    | _, _ => 0

/-! ### Named pattern hypothesis: generalized by a nested match on the alias -/

-- NOTE: the nested match generalizes the hypothesis `h : p = Value.nat k` of the named pattern
--       (added as an extra discriminator by Lean, cf. `nestedAlias` with `generalizing := false`)
def nestedAliasGen (g : Value → Nat) (x : Value) (y : Value) : Nat :=
  match x with
  | .nat 5 => 100
  | p@(.nat k) =>
      match y, p with
      | .nat 5, _ => 50
      | _, .nat j => g p + j + k
      | _, _ => 0
  | _ => 0

-- nestedAliasGen g v (.nat (h n)) ===>
--   match v with
--   | .nat 5 => 100
--   | p@h_1:(.nat k) =>
--     nestedAliasGen.match_1 k (fun (y p : Value) (h : p = Value.nat k) => Nat) (Value.nat (h n)) (Value.nat k)
--       (Eq.refl (Value.nat k))
--       (fun (x : Value) (h : x = Value.nat k) => 50)
--       (fun (x : Value) (j : Nat) (h : Value.nat j = Value.nat k) => Nat.add k (Nat.add k (g (Value.nat k))))
--       (fun (x p : Value) (h : p = Value.nat k) => 0)
--   | _ => 0
-- NOTE: the alias `p` and the hypothesis `h_1` are replaced by `Value.nat k` and `Eq.refl (Value.nat k)` as
--       discriminators of the nested match (which is not reduced), the nested variable pattern binds `j := k`.
--       The nested match is written as an explicit matcher application because of its dependent motive.
#testOptimize [ "UnifyPattern_69" ] (norm-result: 1)
  nestedAliasGen g v (.nat (h n)) ===>
    match v with
    | .nat 5 => 100
    | _p@(.nat k) =>
      nestedAliasGen.match_1 k (fun (_y _p : Value) (_h : _p = Value.nat k) => Nat) (Value.nat (h n)) (Value.nat k)
        (Eq.refl (Value.nat k))
        (fun (_x : Value) (_h : _x = Value.nat k) => 50)
        (fun (_x : Value) (_j : Nat) (_h : Value.nat _j = Value.nat k) => Nat.add k (Nat.add k (g (Value.nat k))))
        (fun (_x _p : Value) (_h : _p = Value.nat k) => 0)
    | _ => 0

end Tests.UnifyPattern
