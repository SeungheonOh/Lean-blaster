import Blaster.Reconstruct.SmtProof.SExpr

/-!
# SMT terms

SMT-LIB terms as they occur in the proofs produced by SMT solvers. `let` bindings are expanded
when converting from S-expressions, preserving sharing (i.e., a let-bound term is represented by a
single object referenced several times), such that terms can be traversed with a cache on
object addresses (see `TermCache`).
-/

namespace Blaster.Reconstruct.SmtProof

inductive QuantKind where
  | forall | exists | lambda
  deriving Inhabited, BEq, Repr

/-- SMT-LIB term. Sorts are kept as S-expressions. -/
inductive STerm where
  /-- symbol (constant, variable or nullary function) -/
  | sym (s : String)
  | num (n : Nat)
  /-- decimal, hexadecimal or binary literal, kept as printed -/
  | lit (s : String)
  | str (s : String)
  /-- application of a symbol -/
  | app (f : String) (args : Array STerm)
  /-- application of an indexed symbol `((_ f i₁ ... iₙ) args)`, e.g., `quant-inst` or `th-lemma` -/
  | iapp (f : String) (idx : Array STerm) (args : Array STerm)
  /-- `(as f sort)` applied to `args` (no argument for a qualified constant) -/
  | qual (f : String) (sort : SExpr) (args : Array STerm)
  | quant (k : QuantKind) (vars : Array (String × SExpr)) (body : STerm)
  /-- annotated term `(! t attrs)` -/
  | annot (t : STerm) (attrs : Array SExpr)
  deriving Inhabited, Repr

namespace STerm

def isApp (t : STerm) (f : String) : Bool :=
  match t with
  | .app g _ => f == g
  | _ => false

def args : STerm → Array STerm
  | .app _ as | .iapp _ _ as | .qual _ _ as => as
  | _ => #[]

/-- Remove annotations. -/
partial def stripAnnot : STerm → STerm
  | .annot t _ => stripAnnot t
  | t => t

def isTrue (t : STerm) : Bool := match t.stripAnnot with | .sym "true" => true | _ => false
def isFalse (t : STerm) : Bool := match t.stripAnnot with | .sym "false" => true | _ => false

/-- Return `some a` when `t := (not a)`. -/
def not? (t : STerm) : Option STerm :=
  match t.stripAnnot with
  | .app "not" #[a] => some a
  | _ => none

partial def toSExpr : STerm → SExpr
  | .sym s => .atom s
  | .num n => .atom (toString n)
  | .lit s => .atom s
  | .str s => .str s
  | .app f args => if args.isEmpty then .atom f else .list (#[.atom f] ++ args.map toSExpr)
  | .iapp f idx args =>
      let h := SExpr.list (#[.atom "_", .atom f] ++ idx.map toSExpr)
      if args.isEmpty then h else .list (#[h] ++ args.map toSExpr)
  | .qual f s args =>
      let h := SExpr.list #[.atom "as", .atom f, s]
      if args.isEmpty then h else .list (#[h] ++ args.map toSExpr)
  | .quant k vars body =>
      let kw := match k with | .forall => "forall" | .exists => "exists" | .lambda => "lambda"
      .list #[.atom kw, .list (vars.map fun (x, s) => .list #[.atom x, s]), toSExpr body]
  | .annot t attrs => .list (#[.atom "!", toSExpr t] ++ attrs)

instance : ToString STerm := ⟨fun t => toString t.toSExpr⟩

end STerm

/-- Conversion from S-expressions, expanding `let` bindings (with sharing). -/
partial def STerm.ofSExpr (env : Std.HashMap String STerm := {}) (e : SExpr) : Except String STerm := do
  match e with
  | .str s => return .str s
  | .atom a =>
      if let some t := env.get? a then return t
      if let some n := a.toNat? then return .num n
      if a.startsWith "#" || (a.any (· == '.') && (a.get 0).isDigit) then return .lit a
      return .sym a
  | .list xs =>
      if xs.isEmpty then throw "empty application"
      match xs[0]! with
      | .atom "let" =>
          let some binds := xs[1]? >>= SExpr.list? | throw s!"ill-formed let: {e}"
          let mut env' := env
          -- NOTE: SMT-LIB `let` is parallel, i.e., bound terms are evaluated in the outer environment
          for b in binds do
            let some #[.atom x, v] := b.list? | throw s!"ill-formed let binding: {b}"
            env' := env'.insert x (← ofSExpr env v)
          ofSExpr env' xs[2]!
      | .atom "forall" | .atom "exists" | .atom "lambda" =>
          let k := match xs[0]! with
            | .atom "forall" => QuantKind.forall
            | .atom "exists" => .exists
            | _ => .lambda
          let some vs := xs[1]? >>= SExpr.list? | throw s!"ill-formed binder: {e}"
          let mut vars := #[]
          let mut env' := env
          for v in vs do
            let some #[.atom x, s] := v.list? | throw s!"ill-formed sorted variable: {v}"
            vars := vars.push (x, s)
            env' := env'.erase x
          return .quant k vars (← ofSExpr env' xs[2]!)
      | .atom "!" =>
          return .annot (← ofSExpr env xs[1]!) (xs.extract 2 xs.size)
      | .atom "as" =>
          let some f := xs[1]? >>= SExpr.atom? | throw s!"ill-formed qualified identifier: {e}"
          return .qual f xs[2]! #[]
      | .atom f =>
          let args ← (xs.extract 1 xs.size).mapM (ofSExpr env)
          -- a let-bound symbol can't be applied
          return .app f args
      | .list hd =>
          let args ← (xs.extract 1 xs.size).mapM (ofSExpr env)
          match hd.toList with
          | .atom "_" :: .atom f :: idx => return .iapp f (← idx.toArray.mapM (ofSExpr env)) args
          -- β-redex (e.g., after the expansion of named lambdas)
          | [.atom "lambda", .list vs, body] =>
              if vs.size != args.size then throw s!"ill-formed β-redex: {e}"
              let mut env' := env
              for (v, a) in vs.zip args do
                let some (x : String) := v.list? >>= (·[0]?) >>= SExpr.atom? | throw s!"ill-formed binder: {v}"
                env' := env'.insert x a
              ofSExpr env' body
          | [.atom "as", .atom f, s] => return .qual f s args
          | _ => throw s!"unsupported application head: {SExpr.list hd}"
      | h => throw s!"unsupported application head: {h}"

/-- Cache on term object addresses, for traversals of terms with sharing. -/
abbrev TermCache (α : Type) := Std.HashMap USize α

@[inline] unsafe def termAddrImpl (t : STerm) : USize := ptrAddrUnsafe t
@[implemented_by termAddrImpl] opaque termAddr (t : STerm) : USize

end Blaster.Reconstruct.SmtProof
