import Lean

/-!
# S-expressions

A small S-expression reader for the output of SMT solvers (proofs and SMT-LIB commands).
It is used by the proof replay (see `Blaster.Reconstruct.SmtProof`) and is independent from
the SMT backend producing the text.
-/

namespace Blaster.Reconstruct.SmtProof

/-- S-expression as produced by SMT solvers. -/
inductive SExpr where
  /-- symbol, keyword (starting with `:`) or numeral/decimal/bit-vector literal -/
  | atom (s : String)
  /-- string literal (without quotes, with `""` unescaped) -/
  | str (s : String)
  | list (xs : Array SExpr)
  deriving Inhabited, BEq, Repr

namespace SExpr

partial def toString : SExpr → String
  | .atom s => s
  | .str s => "\"" ++ s.replace "\"" "\"\"" ++ "\""
  | .list xs => "(" ++ " ".intercalate (xs.toList.map toString) ++ ")"

instance : ToString SExpr := ⟨SExpr.toString⟩

def isAtom (e : SExpr) (s : String) : Bool :=
  match e with
  | .atom a => a == s
  | _ => false

def atom? : SExpr → Option String
  | .atom a => some a
  | _ => none

def list? : SExpr → Option (Array SExpr)
  | .list xs => some xs
  | _ => none

/-- Return the head symbol of a list `(f ...)`. -/
def head? : SExpr → Option String
  | .list xs => if h : 0 < xs.size then xs[0].atom? else none
  | _ => none

end SExpr

/-- Parser state: the input as a byte array and the current position. -/
structure ParserState where
  input : ByteArray
  pos : Nat := 0

abbrev ParserM := StateT ParserState (Except String)

namespace Parser

@[inline] def peek? : ParserM (Option UInt8) := do
  let s ← get
  if h : s.pos < s.input.size then return some s.input[s.pos] else return none

@[inline] def advance : ParserM Unit := modify fun s => { s with pos := s.pos + 1 }

def isWhitespace (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13

/-- Skip whitespace and `;` comments. -/
partial def skipWs : ParserM Unit := do
  match ← peek? with
  | some c =>
      if isWhitespace c then advance; skipWs
      else if c == 59 then -- ';'
        let rec skipLine : ParserM Unit := do
          match ← peek? with
          | some 10 => pure ()
          | some _ => advance; skipLine
          | none => pure ()
        skipLine; skipWs
      else pure ()
  | none => pure ()

def isAtomChar (c : UInt8) : Bool :=
  !(isWhitespace c) && c != 40 && c != 41 && c != 34 && c != 59 && c != 124

/-- Extract the substring `[start, stop)` of the input. -/
def slice (start stop : Nat) : ParserM String := do
  let s ← get
  match String.fromUTF8? (s.input.extract start stop) with
  | some str => return str
  | none => throw s!"invalid UTF-8 at position {start}"

partial def parseAtom : ParserM String := do
  let start := (← get).pos
  let rec loop : ParserM Unit := do
    match ← peek? with
    | some c => if isAtomChar c then advance; loop else pure ()
    | none => pure ()
  loop
  slice start (← get).pos

/-- Parse a `|quoted symbol|`, returning the symbol with its bars (as printed by the solvers). -/
partial def parseQuoted : ParserM String := do
  let start := (← get).pos
  advance
  let rec loop : ParserM Unit := do
    match ← peek? with
    | some 124 => advance
    | some _ => advance; loop
    | none => throw "unterminated quoted symbol"
  loop
  -- NOTE: a quoted symbol may be directly followed by other symbol characters (not in SMT-LIB)
  slice start (← get).pos

/-- Parse a string literal (SMT-LIB 2.6: `""` denotes a double quote). -/
partial def parseString : ParserM String := do
  advance
  let rec loop (acc : ByteArray) : ParserM ByteArray := do
    match ← peek? with
    | some 34 =>
        advance
        match ← peek? with
        | some 34 => advance; loop (acc.push 34)
        | _ => return acc
    | some c => advance; loop (acc.push c)
    | none => throw "unterminated string literal"
  let bytes ← loop ByteArray.empty
  match String.fromUTF8? bytes with
  | some s => return s
  | none => throw "invalid UTF-8 in string literal"

partial def parseSExpr : ParserM SExpr := do
  skipWs
  match ← peek? with
  | none => throw "unexpected end of input"
  | some 40 => -- '('
      advance
      let rec items (acc : Array SExpr) : ParserM (Array SExpr) := do
        skipWs
        match ← peek? with
        | some 41 => advance; return acc
        | none => throw "unexpected end of input (missing ')')"
        | _ => items (acc.push (← parseSExpr))
      return .list (← items #[])
  | some 41 => throw s!"unexpected ')' at position {(← get).pos}"
  | some 34 => return .str (← parseString)
  | some 124 => return .atom (← parseQuoted)
  | some _ => return .atom (← parseAtom)

partial def parseAll : ParserM (Array SExpr) := do
  let rec loop (acc : Array SExpr) : ParserM (Array SExpr) := do
    skipWs
    match ← peek? with
    | none => return acc
    | _ => loop (acc.push (← parseSExpr))
  loop #[]

end Parser

/-- Parse all the S-expressions of `s`. -/
def parseSExprs (s : String) : Except String (Array SExpr) :=
  (Parser.parseAll.run' { input := s.toUTF8 })

/-- Parse a single S-expression. -/
def parseSExpr (s : String) : Except String SExpr := do
  let es ← parseSExprs s
  if h : es.size = 1 then return es[0] else throw s!"expected one S-expression, got {es.size}"

end Blaster.Reconstruct.SmtProof
