import Blaster
import Tests.FixedIssues.NatLog2

namespace Tests.CharBitVec

-- Issue: Inductive datatype with instance parameters not supported: `BitVec
-- Diagnosis: `Char` is a structure over `UInt32`, which wraps `BitVec 32`, itself a structure over
--            `Fin (2 ^ 32)`. Both `BitVec w` and `Fin n` are parameterized by a value (i.e., not a sort),
--            which could not be represented in the Smt datatype declaration.
--            Moreover, `String.mk` applied to a non-literal `List Char` was translated to an
--            undeclared Smt function.
-- Fix: - Value parameters are erased from the Smt datatype declaration (e.g., `(declare-datatype @Fin ...)`),
--        i.e., all instances share the same Smt sort, while the constraints imposed by the value
--        parameters are captured by each instance's predicate qualifier (e.g., `@isFin_xxx` for `Fin 5`).
--      - Value parameters are normalized (e.g., `(instOfNatNat 8).1` in `UInt8.toBitVec : BitVec 8`).
--      - `String.mk` is translated to a recursive Smt function concatenating the characters of the list
--        (see `translateStringMk`).

-- Reproducer
def k (b : Bool) (r : List Char) : String := if b then ⟨r⟩ else ⟨r.reverse⟩
#blaster [∀ (b : Bool) (r : List Char), r = [] → (k b r).length = 0]

-- Fin
#blaster [∀ (x : Fin 5), x.val < 5]
#blaster [∀ (x : Fin (2 ^ 3)), x.val < 8]
#blaster [∀ (x y : Fin 2), x ≠ y → x.val + y.val = 1]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Fin 5), x.val < 4]

-- BitVec
#blaster [∀ (x : BitVec 3), x.toNat < 8]
#blaster [∀ (x : BitVec 32), x.toNat < 4294967296]
#blaster [∀ (w : Nat) (x : BitVec w), x.toNat < 2 ^ w]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 3), x.toNat < 7]

-- UIntN
#blaster [∀ (x : UInt8), x.toNat < 256]
#blaster [∀ (x : UInt16), x.toNat < 65536]
#blaster [∀ (x : UInt32), x.toNat < 4294967296]
#blaster [∀ (x : UInt64), x.toNat < 18446744073709551616]
#blaster [∀ (x y : UInt8), x = y → y = x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x.toNat < 255]

-- Char
#blaster [∀ (c : Char), c.toNat < 1114112]
#blaster [∀ (c : Char), c.toNat < 55296 ∨ 57343 < c.toNat]
#blaster [∀ (cs : List Char), cs.length ≤ cs.length + 1]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (c : Char), c.toNat < 55296]

-- String.mk on non-literal list of chars
#blaster [∀ (c : Char), (String.mk [c]).length = 1]
#blaster [∀ (c d : Char), (String.mk [c, d]).length = 2]
#blaster [∀ (c : Char), c = 'a' → String.mk [c] = "a"]
#blaster [∀ (c : Char) (s : String), s = String.mk [c] → s.length = 1]
#blaster [∀ (r : List Char), r = ['a', 'b'] → String.mk r = "ab"]
#blaster [∀ (r : List Char), r = ['a', 'b'] → String.mk r.reverse = "ba"]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (c : Char), String.mk [c] = "a"]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (r : List Char), (String.mk r).length > 0]

-- Characters beyond the Smt string alphabet (i.e., > 0x2FFFF) are mapped to unspecified singleton strings.
#blaster [∀ (c : Char), c.toNat = 0x10FFFF → (String.mk [c]).length = 1]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (c : Char), c.toNat = 0x10FFFF → String.mk [c] = "a"]

-- Real-world example (PlutusCore integerToByteString builtin, see `NatLog2.lean`)
open Tests.NatLog2

def Except.isError (e : Except ε α) : Bool := not (Except.isOk e)

#blaster [∀ (e : Bool) (w n : Integer), w < 0 ∨ w > 8192 → (integerToByteString e w n |> Except.isError)]

-- Requires reasoning on `itobs_be_loop` over up to 8192 iterations: must not error.
#blaster (timeout: 5) (solve-result: 2)
  [∀ (e : Bool) (w n : Integer), n < 0 ∨ n ≥ 2 ^ 65536 → (integerToByteString e w n |> Except.isError)]

end Tests.CharBitVec
