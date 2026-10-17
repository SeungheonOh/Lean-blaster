import Blaster

namespace Tests.NatLog2

-- Issue: translateApp: unexpected application ... Nat.rec ... Bool.rec
-- Diagnosis: `Nat.log2` is defined in core directly via `Nat.rec` / `Bool.rec`
--            (i.e., not via the equation compiler). Blaster therefore considered it as a
--            non-recursive function and unfolded it to raw recursor applications that
--            cannot be translated to SMT-Lib.
-- Fix: `Nat.log2` is now an opaque function, translated to the following Smt function:
--        (define-fun-rec @Nat.log2 ((@x Nat)) Nat
--          (ite (<= 2 @x) (+ (@Nat.log2 (div @x 2)) 1) 0))

-- Requires induction: not provable by the backend solver, but must not error.
#blaster (timeout: 2) (solve-result: 2) [∀ (n : Nat), Nat.log2 n ≤ n]

-- constant folding
#blaster [Nat.log2 0 = 0]
#blaster [Nat.log2 1 = 0]
#blaster [Nat.log2 1024 = 10]
#blaster [Nat.log2 (2 ^ 65536) = 65536]

#blaster [∀ (n : Nat), n < 4 → Nat.log2 n ≤ 1]
#blaster [∀ (n : Nat), n ≥ 2 → Nat.log2 n = Nat.log2 (n / 2) + 1]
#blaster [∀ (n : Nat), n = 8 → Nat.log2 n = 3]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (n : Nat), n = 8 → Nat.log2 n = 4]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (n : Nat), Nat.log2 n = 0]

-- Nat.log2 passed as argument.
-- NOTE: The parameter of `Nat.log2` is annotated with `@&`, which was kept when eta-expanding
-- `Nat.log2`, producing a distinct Smt arrow type instance (i.e., with a distinct @apply function)
-- and leading to an unexpected `Falsified` result.
#blaster [∀ (xs : List Nat), xs = [1, 2, 8] → xs.map Nat.log2 = [0, 1, 3]]
#blaster [∀ (xs : List String), xs = ["a", "bc"] → xs.map String.length = [1, 2]]

-- Real-world example (PlutusCore integerToByteString builtin)
abbrev Integer := Int

def maxOutputLength     : Nat := 8192
def maxOutputBitsLength : Nat := 8 * maxOutputLength

def integerLog2 : Integer → Nat
  | .negSucc _ => 0
  | .ofNat   n => Nat.log2 n

def integerWidth : Nat → Nat
  | 0 => 0
  | n => Nat.log2 n / 8 + 1

def itobs_be_loop : Nat → List Char → Nat → Except String (List Char)
  | .succ p, a, n => itobs_be_loop p (Char.ofNat (n % 256) :: a) (n / 256)
  | .zero  , a, 0 => pure a
  | .zero  , _, _ => throw "integerToByteString: cannot represent Integer in given number of bytes"

def integerToByteString (e : Bool) (w n : Integer) : Except String String :=
       if w < 0                                       then throw "integerToByteString: negative length argument"
  else if w > maxOutputLength                         then throw s!"integerToByteString: requested length is too long (maximum is {maxOutputLength} bytes)"
  else if w = 0 ∧ integerLog2 n ≥ maxOutputBitsLength then throw s!"integerToByteString: input too long (maximum is 2^{maxOutputBitsLength}-1)"
  else if n < 0                                       then throw "integerToByteString: cannot convert negative Integer"
  else do
    let r ← match w, n with
             | 0        , 0         => pure []
             | 0        , .ofNat n' => itobs_be_loop (integerWidth n') [] n'
             | .ofNat w', .ofNat n' => itobs_be_loop w'                [] n'
             | _        , _         => unreachable!
    if e then pure ⟨r⟩
         else pure ⟨r.reverse⟩

#blaster [∀ (e : Bool) (w n : Integer), 0 ≤ w → w ≤ 8192 → n < 0 →
           integerToByteString e w n = .error "integerToByteString: cannot convert negative Integer"]

end Tests.NatLog2
