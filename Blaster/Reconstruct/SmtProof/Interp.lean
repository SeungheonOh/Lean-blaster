import Lean
import Blaster.Reconstruct.SmtProof.Term

/-!
# Interpretation of SMT terms in Lean

SMT terms occurring in a proof are interpreted as Lean terms:
 - `Int`-sorted terms are interpreted as Lean `Int` terms. Lean terms of type `Nat` occurring in
   `Int` positions are cast (`(↑n : Int)`), and `Int` terms occurring in Lean positions of type `Nat`
   (e.g., arguments of Lean functions, constructor fields) are converted with `Int.toNat`;
 - `Bool`-sorted terms are interpreted as propositions, and converted with `decide` (resp. `= true`)
   when a Lean `Bool` is expected (resp. given);
 - other sorts (e.g., datatypes, `String`, uninterpreted sorts) are interpreted as the corresponding
   Lean types.

The interpretation of the symbols of the query is given by a `SymTable`. Each step of an SMT proof is
then replayed as a Lean proof of the interpretation of its conclusion. Since the Lean proof is checked by
the kernel, an inadequate interpretation (e.g., a step that is not valid for the chosen interpretation)
only results in a failed replay.
-/

open Lean Meta

namespace Blaster.Reconstruct.SmtProof

/-- Interpretation of an SMT function symbol. -/
inductive SymInterp where
  /-- a Lean term (constant, free variable, function): applications are built with casts on arguments -/
  | expr (e : Expr)
  /-- an SMT macro (`define-fun`), expanded during interpretation -/
  | macro (params : Array (String × SExpr)) (body : STerm)
  /-- a type predicate of Blaster's encoding, interpreted as `fun _ => True` -/
  | trueFun
  /-- a datatype constructor -/
  | ctor (n : Name)
  /-- a datatype selector: constructor, index of the field -/
  | selector (ctor : Name) (idx : Nat)
  /-- a datatype tester -/
  | tester (ctor : Name)
  deriving Inhabited

/-- Interpretation of the symbols and sorts of an SMT query. -/
structure SymTable where
  syms : Std.HashMap String SymInterp := {}
  /-- sort symbols (after alias expansion) to Lean type constructors -/
  sorts : Std.HashMap String Expr := {}
  /-- sort aliases (`define-sort` without parameters) -/
  aliases : Std.HashMap String SExpr := {}
  /-- Lean types of the datatype sorts as they occur in proofs (aliases expanded), e.g., `(@List Int) ↦ List Nat`
      when the query only uses `(@List Nat)`. -/
  expandedSorts : Std.HashMap String Expr := {}
  deriving Inhabited

structure InterpCtx where
  table : SymTable
  /-- bound variables (quantifiers, `proof-bind`, fresh definitions) -/
  locals : Std.HashMap String Expr := {}

abbrev InterpM := ReaderT InterpCtx MetaM

/-! ## Casts -/

def intType : Expr := mkConst ``Int
def natType : Expr := mkConst ``Nat

def isNatType (t : Expr) : Bool := t.isConstOf ``Nat
def isIntType (t : Expr) : Bool := t.isConstOf ``Int
def isBoolType (t : Expr) : Bool := t.isConstOf ``Bool

/-- `(↑e : Int)`, in the canonical form expected by tactics (`Nat.cast`). Nat literals are converted
    to `Int` literals. -/
def mkIntOfNat (e : Expr) : Expr :=
  match e.rawNatLit?, e.nat? with
  | some n, _ | _, some n => mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Int) (mkRawNatLit n)
                                (mkApp (mkConst ``instOfNat) (mkRawNatLit n))
  | _, _ => mkApp3 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt) e

def mkIntToNat (e : Expr) : Expr :=
  -- `Int.toNat (↑n) = n`
  match e.getAppFnArgs with
  | (``Nat.cast, #[_, _, n]) => n
  | (``Int.ofNat, #[n]) => n
  | (``OfNat.ofNat, #[_, n, _]) => mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Nat) n (mkApp (mkConst ``instOfNatNat) n)
  | _ => mkApp (mkConst ``Int.toNat) e

/-- `decide p` with the classical instance. -/
def mkClassicalDecide (p : Expr) : Expr :=
  mkApp2 (mkConst ``Decidable.decide) p (mkApp (mkConst ``Classical.propDecidable) p)

def mkBoolTrue (b : Expr) : Expr :=
  -- `decide p = true` is `p`
  match b.getAppFnArgs with
  | (``Decidable.decide, #[p, _]) => p
  | _ => mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- Coerce `e : actual` to `expected` (Nat ↔ Int, Bool ↔ Prop). -/
def coerce (e actual expected : Expr) : MetaM Expr := do
  if ← isDefEq actual expected then return e
  let actual ← whnfR actual
  let expected' ← whnfR expected
  if isNatType actual && isIntType expected' then return mkIntOfNat e
  if isIntType actual && isNatType expected' then return mkIntToNat e
  if actual.isProp && isBoolType expected' then return mkClassicalDecide e
  if isBoolType actual && expected'.isProp then return mkBoolTrue e
  throwError "smt proof: can't coerce {e} : {actual} to {expected}"

/-- Normalize the type of an interpreted term for the SMT world: `Nat` terms are cast to `Int`,
    `Bool` terms are converted to propositions. -/
def toSmtWorld (e : Expr) : MetaM Expr := do
  let t ← whnfR (← inferType e)
  if isNatType t then return mkIntOfNat e
  if isBoolType t then return mkBoolTrue e
  return e

/-- Apply `f` to `args`, instantiating implicit arguments by unification and coercing explicit
    arguments when necessary. Arguments whose type is `Int` or `Prop` (i.e., flexible w.r.t. coercions)
    are unified last. -/
def mkAppCoerce (f : Expr) (args : Array Expr) : MetaM Expr := do
  let fty ← inferType f
  let (mvars, bis, _) ← forallMetaTelescopeReducing fty
  let explicit := (List.range mvars.size).toArray.filter fun i => bis[i]!.isExplicit
  if explicit.size < args.size then throwError "smt proof: too many arguments for {f}"
  let types ← args.mapM inferType
  -- first pass: rigid arguments
  let mut done := Array.replicate args.size false
  for h : j in [:args.size] do
    let t ← whnfR types[j]!
    if isIntType t || t.isProp then continue
    let m := mvars[explicit[j]!]!
    if ← isDefEq (← inferType m) types[j]! then
      m.mvarId!.assign args[j]!
      done := done.set! j true
  -- second pass: flexible arguments, with coercions
  for h : j in [:args.size] do
    if done[j]! then continue
    let m := mvars[explicit[j]!]!
    let expected ← instantiateMVars (← inferType m)
    if expected.isMVar then
      -- no constraint on the type: keep the SMT type
      m.mvarId!.assign args[j]!
      discard <| isDefEq expected types[j]!
    else
      m.mvarId!.assign (← coerce args[j]! types[j]! expected)
  -- remaining implicit arguments: instances
  for h : i in [:mvars.size] do
    let m := mvars[i]
    if (← instantiateMVars m).isMVar then
      if bis[i]!.isInstImplicit then
        let inst ← synthInstance (← instantiateMVars (← inferType m))
        m.mvarId!.assign inst
  let r ← instantiateMVars (mkAppN f (mvars.extract 0 (if args.size = explicit.size then mvars.size else explicit[args.size]!)))
  if r.hasExprMVar then throwError "smt proof: can't infer implicit arguments of {f}"
  return r

/-! ## Sorts -/

partial def expandSort (tbl : SymTable) (s : SExpr) : SExpr :=
  match s with
  | .atom a => match tbl.aliases.get? a with
    | some s' => expandSort tbl s'
    | none => s
  | .list xs => .list (xs.map (expandSort tbl))
  | s => s

/-- Lean type of an SMT sort. -/
partial def sortToType (s : SExpr) : InterpM Expr := do
  let tbl := (← read).table
  match s with
  | .atom "Int" => return intType
  | .atom "Bool" => return mkSort levelZero
  | .atom "String" => return mkConst ``String
  | .atom "Real" => throwError "smt proof: Real sort not supported"
  | _ =>
    if let some t := tbl.expandedSorts.get? (toString (expandSort tbl s)) then return t
    match s with
    | .atom a =>
        if let some s' := tbl.aliases.get? a then return ← sortToType s'
        match tbl.sorts.get? a with
        | some t => return t
        | none => throwError "smt proof: unknown sort {a}"
    | .list xs =>
        let some (SExpr.atom a) := xs[0]? | throwError "smt proof: unsupported sort {s}"
        let some t := tbl.sorts.get? a | throwError "smt proof: unknown sort {a}"
        let args ← (xs.extract 1 xs.size).mapM sortToType
        -- NOTE: `Int` arguments may stand for `Nat` (aliases are expanded in proofs)
        return mkAppN t args
    | _ => throwError "smt proof: unsupported sort {s}"

/-! ## Terms -/

def mkIntLit (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Int) (mkRawNatLit n) (mkApp (mkConst ``instOfNat) (mkRawNatLit n))

def binIntOp (n : Name) (inst : Name) : Expr :=
  mkApp4 (mkConst n [levelZero, levelZero, levelZero]) intType intType intType (mkConst inst)

def mkIntAdd (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HAdd.hAdd [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHAdd [0]) intType (mkConst ``Int.instAdd))) a b
def mkIntSub (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HSub.hSub [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHSub [0]) intType (mkConst ``Int.instSub))) a b
def mkIntMul (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HMul.hMul [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHMul [0]) intType (mkConst ``Int.instMul))) a b
def mkIntDiv (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HDiv.hDiv [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHDiv [0]) intType (mkConst ``Int.instDiv))) a b
def mkIntMod (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HMod.hMod [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHMod [0]) intType (mkConst ``Int.instMod))) a b
def mkIntNeg (a : Expr) : Expr := mkApp (mkApp2 (mkConst ``Neg.neg [0]) intType (mkConst ``Int.instNegInt)) a
def mkIntLe (a b : Expr) : Expr := mkApp4 (mkConst ``LE.le [0]) intType (mkConst ``Int.instLEInt) a b
def mkIntLt (a b : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) intType (mkConst ``Int.instLTInt) a b

/-- `if c then a else b` with the classical instance. -/
def mkClassicalIte (c a b : Expr) : MetaM Expr := do
  let t ← inferType a
  let u ← getLevel t
  return mkApp5 (mkConst ``ite [u]) t c (mkApp (mkConst ``Classical.propDecidable) c) a b

/-- Left-associated application of a binary operation. -/
def foldBin (op : Expr → Expr → Expr) (args : Array Expr) : MetaM Expr := do
  let some a := args[0]? | throwError "smt proof: operation without arguments"
  return (args.extract 1 args.size).foldl op a

def foldBinRight (op : Expr → Expr → Expr) (args : Array Expr) : MetaM Expr := do
  let some a := args.back? | throwError "smt proof: operation without arguments"
  return args.pop.foldr op a

/-- Chain of relations `r a₀ a₁ ∧ r a₁ a₂ ∧ ...`. -/
def chain (r : Expr → Expr → MetaM Expr) (args : Array Expr) : MetaM Expr := do
  if args.size < 2 then throwError "smt proof: relation with less than two arguments"
  let mut cs := #[]
  for i in [:args.size - 1] do cs := cs.push (← r args[i]! args[i+1]!)
  foldBinRight mkAnd cs

/-- Equality of interpreted terms (with coercions to a common type). -/
def mkEqSmt (a b : Expr) : MetaM Expr := do
  let ta ← inferType a
  let tb ← inferType b
  if ← isDefEq ta tb then return ← mkEq a b
  let a ← toSmtWorld a
  let b ← toSmtWorld b
  mkEq a b

/-- Selector of field `idx` of constructor `ctor` applied to `x`, defined by case analysis (with
    `default` for the other constructors). -/
def mkSelector (ctor : Name) (idx : Nat) (x : Expr) : MetaM Expr := do
  let some (.ctorInfo cinfo) := (← getEnv).find? ctor | throwError "smt proof: unknown constructor {ctor}"
  let xt ← whnfR (← inferType x)
  let some (.inductInfo iinfo) := (← getEnv).find? cinfo.induct | throwError "smt proof: unknown inductive {cinfo.induct}"
  let params := xt.getAppArgs.extract 0 iinfo.numParams
  -- structure: projection
  if iinfo.ctors.length == 1 && iinfo.numIndices == 0 && !iinfo.isRec then
    return mkProj cinfo.induct idx x
  let fieldTy ← forallTelescopeReducing (← instantiateForall cinfo.type params) fun fs _ => do
    let t ← inferType fs[idx]!
    if t.hasAnyFVar (fs.contains <| .fvar ·) then throwError "smt proof: dependent field selector not supported"
    return t
  let dflt ← mkDefault fieldTy
  let motive := mkLambda `x .default xt fieldTy
  let mut minors := #[]
  for c in iinfo.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? c | unreachable!
    let minor ← forallTelescopeReducing (← instantiateForall ci.type params) fun fs _ => do
      if c == ctor then mkLambdaFVars fs fs[idx]! else mkLambdaFVars fs dflt
    minors := minors.push minor
  let u ← getLevel fieldTy
  -- NOTE: universe levels of the inductive are taken from the type of `x`
  let lvls := xt.getAppFn.constLevels!
  return mkAppN (mkConst (cinfo.induct ++ `casesOn) (u :: lvls)) (params ++ #[motive, x] ++ minors)
where
  mkDefault (t : Expr) : MetaM Expr := do
    let u ← getLevel t
    try
      let inst ← synthInstance (mkApp (mkConst ``Inhabited [u]) t)
      return mkApp2 (mkConst ``Inhabited.default [u]) t inst
    catch _ =>
      let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) t)
      return mkApp2 (mkConst ``Classical.ofNonempty [u]) t inst

/-- Tester for constructor `ctor` applied to `x`: a proposition defined by case analysis. -/
def mkTester (ctor : Name) (x : Expr) : MetaM Expr := do
  let some (.ctorInfo cinfo) := (← getEnv).find? ctor | throwError "smt proof: unknown constructor {ctor}"
  let xt ← whnfR (← inferType x)
  let some (.inductInfo iinfo) := (← getEnv).find? cinfo.induct | throwError "smt proof: unknown inductive {cinfo.induct}"
  let params := xt.getAppArgs.extract 0 iinfo.numParams
  let motive := mkLambda `x .default xt (mkSort levelZero)
  let mut minors := #[]
  for c in iinfo.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? c | unreachable!
    let minor ← forallTelescopeReducing (← instantiateForall ci.type params) fun fs _ =>
      mkLambdaFVars fs (if c == ctor then mkConst ``True else mkConst ``False)
    minors := minors.push minor
  let lvls := xt.getAppFn.constLevels!
  return mkAppN (mkConst (cinfo.induct ++ `casesOn) (levelOne :: lvls)) (params ++ #[motive, x] ++ minors)

mutual
/-- Interpret the SMT term `t` as a Lean term. -/
partial def interp (t : STerm) : InterpM Expr := do
  match t with
  | .num n => return mkIntLit n
  | .lit s => throwError "smt proof: unsupported literal {s}"
  | .str s => return mkStrLit s
  | .annot t _ => interp t
  | .sym s => interpApp s #[]
  | .app f args => interpApp f args
  | .qual f sort args =>
      let ty ← sortToType sort
      let e ← interpApp f args
      let ety ← inferType e
      if ← isDefEq ety ty then return e
      coerce e ety ty
  | .iapp f _ _ => throwError "smt proof: unsupported indexed symbol {f}"
  | .quant k vars body => interpQuant k vars body

partial def interpQuant (k : QuantKind) (vars : Array (String × SExpr)) (body : STerm) : InterpM Expr := do
  let types ← vars.mapM fun (_, s) => sortToType s
  let rec go (i : Nat) (fvars : Array Expr) : InterpM Expr := do
    if h : i < vars.size then
      withLocalDeclD (Name.mkSimple vars[i].1) types[i]! fun x =>
        withReader (fun ctx => { ctx with locals := ctx.locals.insert vars[i].1 x }) (go (i + 1) (fvars.push x))
    else
      let b ← interp body
      match k with
      | .forall => mkForallFVars fvars b
      | .lambda => mkLambdaFVars fvars b
      | .exists =>
          let mut r := b
          for x in fvars.reverse do
            r ← mkAppM ``Exists #[← mkLambdaFVars #[x] r]
          return r
  go 0 #[]

partial def interpApp (f : String) (args : Array STerm) : InterpM Expr := do
  let ctx ← read
  if let some x := ctx.locals.get? f then
    if args.isEmpty then return x
    return ← mkAppCoerce x (← args.mapM interp)
  match f, args.size with
  | "true", 0 => return mkConst ``True
  | "false", 0 => return mkConst ``False
  | "not", 1 => return mkNot (← interp args[0]!)
  | "and", _ => if args.isEmpty then return mkConst ``True else foldBinRight mkAnd (← args.mapM interp)
  | "or", _ => if args.isEmpty then return mkConst ``False else foldBinRight mkOr (← args.mapM interp)
  | "=>", _ => foldBinRight (fun a b => mkForall `h .default a b) (← args.mapM interp)
  | "xor", 2 => return mkNot (← mkEq (← interp args[0]!) (← interp args[1]!))
  | "=", _ => chain mkEqSmt (← args.mapM interp)
  -- equisatisfiability (Z3): interpreted as an implication
  | "~", 2 => return mkForall `h .default (← interp args[0]!) (← interp args[1]!)
  | "distinct", _ =>
      let es ← args.mapM interp
      let mut cs := #[]
      for i in [:es.size] do
        for j in [i+1:es.size] do cs := cs.push (mkNot (← mkEqSmt es[i]! es[j]!))
      if cs.isEmpty then return mkConst ``True else foldBinRight mkAnd cs
  | "ite", 3 => mkClassicalIte (← interp args[0]!) (← interpInt? args[1]!) (← interpInt? args[2]!)
  | "+", _ => foldBin mkIntAdd (← args.mapM interpInt)
  | "-", 1 => return mkIntNeg (← interpInt args[0]!)
  | "-", _ => foldBin mkIntSub (← args.mapM interpInt)
  | "*", _ => foldBin mkIntMul (← args.mapM interpInt)
  | "div", _ => foldBin mkIntDiv (← args.mapM interpInt)
  | "mod", 2 => return mkIntMod (← interpInt args[0]!) (← interpInt args[1]!)
  | "abs", 1 => return mkApp (mkConst ``Int.natAbs) (← interpInt args[0]!) |> mkIntOfNat
  | "<=", _ => chain (fun a b => pure (mkIntLe a b)) (← args.mapM interpInt)
  | "<", _ => chain (fun a b => pure (mkIntLt a b)) (← args.mapM interpInt)
  | ">=", _ => chain (fun a b => pure (mkIntLe b a)) (← args.mapM interpInt)
  | ">", _ => chain (fun a b => pure (mkIntLt b a)) (← args.mapM interpInt)
  | "str.++", _ => foldBin (fun a b => mkApp2 (mkConst ``String.append) a b) (← args.mapM interp)
  | "str.len", 1 => return mkIntOfNat (mkApp (mkConst ``String.length) (← interp args[0]!))
  | _, _ =>
    match ctx.table.syms.get? f with
    | some (.expr e) =>
        if args.isEmpty then return e
        mkAppCoerce e (← args.mapM interp)
    | some (.macro params body) =>
        if params.size != args.size then throwError "smt proof: wrong number of arguments for {f}"
        let vals ← args.mapM interp
        let locals := (params.zip vals).foldl (fun m ((x, _), v) => m.insert x v) ctx.locals
        withReader (fun c => { c with locals }) (interp body)
    | some .trueFun => return mkConst ``True
    | some (.ctor n) =>
        mkAppCoerce (← mkConstWithFreshMVarLevels n) (← args.mapM interp)
    | some (.selector c i) =>
        let some a := args[0]? | throwError "smt proof: selector without argument"
        let e ← mkSelector c i (← interp a)
        toSmtWorld e
    | some (.tester c) =>
        let some a := args[0]? | throwError "smt proof: tester without argument"
        mkTester c (← interp a)
    | none => throwError "smt proof: unknown symbol {f}"

/-- Interpret `t` as an `Int` term (casting `Nat` terms). -/
partial def interpInt (t : STerm) : InterpM Expr := do
  let e ← interp t
  let ty ← whnfR (← inferType e)
  if isNatType ty then return mkIntOfNat e
  return e

/-- Interpret `t`, casting `Nat`/`Bool` terms to the SMT world. -/
partial def interpInt? (t : STerm) : InterpM Expr := do
  toSmtWorld (← interp t)
end

end Blaster.Reconstruct.SmtProof
