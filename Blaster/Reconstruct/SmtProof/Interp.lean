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
   Lean types; the sorts `@Instance` and `@Type` of Blaster's polymorphic encoding are interpreted as a
   sort variable and `Unit`, or as the universe `Poly.Univ.{u}` of the values of `Sort u` and `Sort u`
   (see `Poly.lean`).

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
  /-- a Lean function given as a lambda (e.g., the membership predicates of the polymorphic encoding, see
      `Poly.lean`): applications are β-reduced -/
  | lam (e : Expr)
  /-- a datatype constructor -/
  | ctor (n : Name)
  /-- a datatype selector: constructor, index of the field -/
  | selector (ctor : Name) (idx : Nat)
  /-- a datatype tester -/
  | tester (ctor : Name)
  /-- application of a function value (Blaster's `@apply` functions for higher-order arguments) -/
  | apply
  /-- skolem function of Z3's `sk` steps: for `¬ ∀ x, φ(ys, x)` (resp. `∃ x, φ(ys, x)`) where `ys` are the
      variables of the context, `fun ys => ε x, ¬ φ(ys, x)` (resp. `ε x, φ(ys, x)`) -/
  | skolem (params : Array String) (x : String) (sort : SExpr) (body : STerm) (neg : Bool)
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
  /-- interpretation of the (closed) terms already interpreted, on term object addresses: terms are
      shared DAGs (e.g., after the expansion of `let`), which must not be traversed as trees -/
  cache : Option (IO.Ref (TermCache Expr)) := none

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
partial def coerce (e actual expected : Expr) : MetaM Expr := do
  if ← isDefEq actual expected then return e
  let actual ← whnfR actual
  let expected' ← whnfR expected
  if isNatType actual && isIntType expected' then return mkIntOfNat e
  if isIntType actual && isNatType expected' then return mkIntToNat e
  if actual.isProp && isBoolType expected' then return mkClassicalDecide e
  if isBoolType actual && expected'.isProp then return mkBoolTrue e
  -- proof arguments (e.g., proof fields of constructors, encoded as `true` by Blaster): a proof by decision
  -- of the expected proposition
  if (actual.isProp || isBoolType actual) && (← isProp expected) then
    try
      let d ← mkDecide expected
      if (← withAtLeastTransparency .default (whnf d)).isConstOf ``Bool.true then
        return ← mkDecideProof expected
    catch _ => pure ()
  -- constructor applications of another instance of the datatype (e.g., `some (x + y) : Option Int` where
  -- `Option Nat` is expected): the arguments are coerced
  if let .const c _ := e.getAppFn then
    if let some (.ctorInfo info) := (← getEnv).find? c then
      if actual.getAppFn.isConstOf info.induct && expected'.getAppFn.isConstOf info.induct then
        let args := e.getAppArgs
        if args.size == info.numParams + info.numFields then
          let k ← mkConstWithFreshMVarLevels c
          let (ms, _, rt) ← forallMetaTelescopeReducing (← inferType k)
          if ms.size == args.size && (← isDefEq rt expected) then
            for i in [info.numParams:args.size] do
              let fty ← instantiateMVars (← inferType ms[i]!)
              ms[i]!.mvarId!.assign (← coerce args[i]! (← inferType args[i]!) fty)
            let r ← instantiateMVars (mkAppN k ms)
            if !r.hasExprMVar then return r
  -- functions (e.g., lambda terms with `Nat` parameters and an `Int` body where `Nat → Nat` is expected): the
  -- arguments are coerced back and the results coerced, pointwise
  if let (.forallE _ a b _, .forallE n a' b' bi) := (actual, expected') then
    if !b.hasLooseBVars && !b'.hasLooseBVars then
      return ← withLocalDecl n bi a' fun y => do
        let x ← coerce y a' a
        mkLambdaFVars #[y] (← coerce (mkApp e x).headBeta b b')
  throwError "smt proof: can't coerce {e} : {actual} to {expected}"

/-- Normalize the type of an interpreted term for the SMT world: `Nat` terms are cast to `Int`,
    `Bool` terms are converted to propositions. -/
def toSmtWorld (e : Expr) : MetaM Expr := do
  let t ← whnfR (← inferType e)
  if isNatType t then return mkIntOfNat e
  if isBoolType t then return mkBoolTrue e
  return e

/-- User name of the metavariables standing for the default values of selectors (see `mkSelector`). -/
def defaultMVarName : Name := `_blaster_selector_default

/-- Apply `f` to `args`, instantiating implicit arguments by unification and coercing explicit
    arguments when necessary. Arguments whose type is `Int` or `Prop` (i.e., flexible w.r.t. coercions)
    are unified last. -/
def mkAppCoerce (f : Expr) (args : Array Expr) (allowMVars := false) : MetaM Expr := do
  let fty ← inferType f
  let (mvars, bis, _) ← forallMetaTelescopeReducing fty
  let explicit := (List.range mvars.size).toArray.filter fun i => bis[i]!.isExplicit
  if explicit.size < args.size then throwError "smt proof: too many arguments for {f}"
  let types ← args.mapM inferType
  -- first pass: rigid arguments
  let mut done := Array.replicate args.size false
  for j in [:args.size] do
    let t ← whnfR types[j]!
    if isIntType t || t.isProp then continue
    let m := mvars[explicit[j]!]!
    if ← isDefEq (← inferType m) types[j]! then
      m.mvarId!.assign args[j]!
      done := done.set! j true
  -- second pass: flexible arguments, with coercions
  for j in [:args.size] do
    if done[j]! then continue
    let m := mvars[explicit[j]!]!
    let expected ← instantiateMVars (← inferType m)
    if expected.isMVar then
      -- no constraint on the type: keep the SMT type, except for formulas (e.g., `(Option.some true)`),
      -- interpreted as Lean `Bool` terms
      if types[j]!.isProp then
        if ← isDefEq expected (mkConst ``Bool) then
          m.mvarId!.assign (mkClassicalDecide args[j]!)
          continue
      if !(← isDefEq expected types[j]!) then throwError "smt proof: ill-typed argument for {f}"
      m.mvarId!.assign args[j]!
    else
      m.mvarId!.assign (← coerce args[j]! types[j]! expected)
  -- remaining implicit arguments: instances (of the used prefix)
  let used := if args.size = explicit.size then mvars.size else explicit[args.size]!
  for i in [:used] do
    let m := mvars[i]!
    if (← instantiateMVars m).isMVar then
      if bis[i]!.isInstImplicit then
        let inst ← synthInstance (← instantiateMVars (← inferType m))
        m.mvarId!.assign inst
  let r ← instantiateMVars (mkAppN f (mvars.extract 0 used))
  -- NOTE: the remaining implicit arguments (e.g., the type parameter `α` of `Sum.inr (b : β) : α ⊕ β`) may be
  -- assigned by unification with the context
  if r.hasMVar && !allowMVars then
    -- NOTE: the default values of selectors may be chosen later (see `mkSelector`)
    if r.hasLevelMVar || (← (← getMVars r).anyM fun m => return (← m.getDecl).userName != defaultMVarName) then
      throwError "smt proof: can't infer implicit arguments of {f}"
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
        | some (.const n []) =>
            let info ← getConstInfo n
            return mkConst n (info.levelParams.map fun _ => levelZero)
        | some t => return t
        | none => throwError "smt proof: unknown sort {a}"
    | .list xs =>
        let some (SExpr.atom a) := xs[0]? | throwError "smt proof: unsupported sort {s}"
        -- NOTE: in the sort arguments of the query, `Nat` stands for Lean `Nat` (e.g., `List Nat`) and
        -- `Bool` for Lean `Bool` (e.g., `List Bool`)
        let args ← (xs.extract 1 xs.size).mapM fun s =>
          if s == .atom "Nat" then pure natType
          else if s == .atom "Bool" then pure (mkConst ``Bool)
          else sortToType s
        -- arrow sorts of Blaster's encoding of function values
        if a.startsWith "@@ArrowT" then
          let some r := args.back? | throwError "smt proof: ill-formed arrow sort {s}"
          return args.pop.foldr (fun d acc => mkForall `x .default d acc) r
        let some t := tbl.sorts.get? a | throwError "smt proof: unknown sort {a}"
        -- NOTE: universe levels are inferred from the arguments
        if let .const n _ := t then return ← mkAppM n args
        return mkAppN t args
    | _ => throwError "smt proof: unsupported sort {s}"

/-! ## Terms -/

/-- Decode the escape sequences `\u{h...}` and `\uhhhh` of SMT-LIB string literals. -/
partial def decodeSmtString (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '\\' && i + 1 < cs.size && cs[i+1]! == 'u' then
      let hexVal (ds : List Char) : Option Nat :=
        if ds.isEmpty then none else ds.foldlM (fun acc d =>
          if d.isDigit then some (16 * acc + (d.toNat - '0'.toNat))
          else if 'a' ≤ d && d ≤ 'f' then some (16 * acc + (d.toNat - 'a'.toNat + 10))
          else if 'A' ≤ d && d ≤ 'F' then some (16 * acc + (d.toNat - 'A'.toNat + 10))
          else none) 0
      if i + 2 < cs.size && cs[i+2]! == '{' then
        let mut j := i + 3
        while j < cs.size && cs[j]! != '}' do j := j + 1
        if let some v := hexVal (cs.extract (i+3) j).toList then
          out := out.push (Char.ofNat v); i := j + 1; continue
      else if i + 5 < cs.size then
        if let some v := hexVal (cs.extract (i+2) (i+6)).toList then
          out := out.push (Char.ofNat v); i := i + 6; continue
    out := out.push cs[i]!
    i := i + 1
  return out

def mkIntLit (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Int) (mkRawNatLit n) (mkApp (mkConst ``instOfNat) (mkRawNatLit n))

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
  let ta ← inferType a
  let tb ← inferType b
  if ← isDefEq ta tb then return ← mkEq a b
  -- e.g., constructor applications of different instances of a datatype
  try return ← mkEq (← coerce a ta tb) b
  catch _ => mkEq a (← coerce b tb ta)

/-- Selector of field `idx` of constructor `ctor` applied to `x`, defined by case analysis (with
    `default` for the other constructors). -/
partial def mkSelector (ctor : Name) (idx : Nat) (x : Expr) (deferDefault := false) : MetaM Expr := do
  let some (.ctorInfo cinfo) := (← getEnv).find? ctor | throwError "smt proof: unknown constructor {ctor}"
  let xt ← whnfD (← inferType x)
  if !xt.getAppFn.isConstOf cinfo.induct then throwError "smt proof: selector {ctor} applied to {xt}"
  let lvls := xt.getAppFn.constLevels!
  let some (.inductInfo iinfo) := (← getEnv).find? cinfo.induct | throwError "smt proof: unknown inductive {cinfo.induct}"
  let params := xt.getAppArgs.extract 0 iinfo.numParams
  -- structure: projection (a proof field is interpreted as its proposition)
  if iinfo.ctors.length == 1 && iinfo.numIndices == 0 && !iinfo.isRec then
    let p := mkProj cinfo.induct idx x
    if ← isProof p then return ← inferType p
    return p
  let ctorType (c : ConstantInfo) := c.instantiateTypeLevelParams lvls
  let fieldTy ← forallTelescopeReducing (← instantiateForall (ctorType (.ctorInfo cinfo)) params) fun fs _ => do
    let t ← inferType fs[idx]!
    if t.hasAnyFVar (fs.contains <| .fvar ·) then throwError "smt proof: dependent field selector not supported"
    return t
  -- default value for the other constructors: `x` itself when the field has the type of `x` (e.g., the
  -- argument of a recursive constructor), an inhabitant of the field type otherwise
  -- NOTE: when the field type is not known yet (e.g., `List.nil` of an unknown instance), the inhabitant can be
  -- chosen after the interpretation of the whole term (`deferDefault`, see `fillDefaults`)
  let dflt ← if ← isDefEq fieldTy xt then pure x
    else if deferDefault && (← instantiateMVars fieldTy).hasExprMVar then mkFreshExprMVar fieldTy (userName := defaultMVarName)
    else mkDefault fieldTy
  let motive := mkLambda `x .default xt fieldTy
  let mut minors := #[]
  for c in iinfo.ctors do
    let some ci := (← getEnv).find? c | unreachable!
    let minor ← forallTelescopeReducing (← instantiateForall (ctorType ci) params) fun fs _ => do
      if c == ctor then mkLambdaFVars fs fs[idx]! else mkLambdaFVars fs dflt
    minors := minors.push minor
  let u ← getLevel fieldTy
  let casesOn ← getConstInfo (cinfo.induct ++ `casesOn)
  if casesOn.levelParams.length != lvls.length + 1 then throwError "smt proof: no large elimination for {cinfo.induct}"
  return mkAppN (mkConst (cinfo.induct ++ `casesOn) (u :: lvls)) (params ++ #[motive, x] ++ minors)
where
  mkDefault (t : Expr) : MetaM Expr := do
    if let some v ← inhabitant? t 8 then return v
    throwError "smt proof: no inhabitant found for {t}"
  /-- An inhabitant of `t`: from an instance, or a constructor application with inhabited fields. -/
  inhabitant? (t : Expr) (depth : Nat) : MetaM (Option Expr) := do
    let u ← getLevel t
    try
      let inst ← synthInstance (mkApp (mkConst ``Inhabited [u]) t)
      return some (mkApp2 (mkConst ``Inhabited.default [u]) t inst)
    catch _ => pure ()
    try
      let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) t)
      return some (mkApp2 (mkConst ``Classical.ofNonempty [u]) t inst)
    catch _ => pure ()
    if depth == 0 then return none
    let t ← whnfD t
    let .const n lvls := t.getAppFn | return none
    let some (.inductInfo info) := (← getEnv).find? n | return none
    let params := t.getAppArgs.extract 0 info.numParams
    for c in info.ctors do
      let ci ← getConstInfo c
      let r ← forallTelescopeReducing (← instantiateForall (ci.instantiateTypeLevelParams lvls) params) fun fs _ => do
        let mut vals := #[]
        for f in fs do
          let ft ← inferType f
          -- non-dependent fields only
          if ft.hasAnyFVar (fs.contains <| .fvar ·) then return none
          match ← inhabitant? ft (depth - 1) with
          | some v => vals := vals.push v
          | none => return none
        return some (mkAppN (mkAppN (mkConst c lvls) params) vals)
      if r.isSome then return r
    return none

/-- Assign the metavariables of `e` standing for default values of selectors (see `mkSelector`) whose type is
    known, with inhabitants of their types. -/
def fillDefaults (e : Expr) : MetaM Expr := do
  if !e.hasExprMVar then return e
  for m in (← getMVars e) do
    if (← m.isAssigned) || (← m.getDecl).userName != defaultMVarName then continue
    let t ← instantiateMVars (← m.getType)
    if t.hasExprMVar || (← isProp t) then continue
    if let some v ← mkSelector.inhabitant? t 8 then m.assign v
  instantiateMVars e

/-- Tester for constructor `ctor` applied to `x`: a proposition defined by case analysis. -/
def mkTester (ctor : Name) (x : Expr) : MetaM Expr := do
  let some (.ctorInfo cinfo) := (← getEnv).find? ctor | throwError "smt proof: unknown constructor {ctor}"
  let xt ← whnfD (← inferType x)
  if !xt.getAppFn.isConstOf cinfo.induct then throwError "smt proof: tester {ctor} applied to {xt}"
  let lvls := xt.getAppFn.constLevels!
  let some (.inductInfo iinfo) := (← getEnv).find? cinfo.induct | throwError "smt proof: unknown inductive {cinfo.induct}"
  let params := xt.getAppArgs.extract 0 iinfo.numParams
  let motive := mkLambda `x .default xt (mkSort levelZero)
  let mut minors := #[]
  for c in iinfo.ctors do
    let some ci := (← getEnv).find? c | unreachable!
    let minor ← forallTelescopeReducing (← instantiateForall (ci.instantiateTypeLevelParams lvls) params) fun fs _ =>
      mkLambdaFVars fs (if c == ctor then mkConst ``True else mkConst ``False)
    minors := minors.push minor
  let casesOn ← getConstInfo (cinfo.induct ++ `casesOn)
  if casesOn.levelParams.length != lvls.length + 1 then throwError "smt proof: no large elimination for {cinfo.induct}"
  return mkAppN (mkConst (cinfo.induct ++ `casesOn) (levelOne :: lvls)) (params ++ #[motive, x] ++ minors)

/-- Interpret `e` as a proposition (a Lean `Bool` term `b` is interpreted as `b = true`). -/
def asProp (e : Expr) : MetaM Expr := do
  let t ← whnfR (← inferType e)
  if isBoolType t then return mkBoolTrue e
  return e

mutual
/-- Interpret the SMT term `t` as a Lean term. -/
partial def interp (t : STerm) : InterpM Expr := do
  let ctx ← read
  -- NOTE: terms are memoized when no local variable is in scope (closed terms)
  if let some ref := ctx.cache then
    if ctx.locals.isEmpty then
      let addr := termAddr t
      if let some e := (← ref.get).get? addr then return e
      let e ← interpCore t
      if !e.hasMVar then ref.modify (·.insert addr e)
      return e
  interpCore t

/-- Interpret the SMT formula `t` as a proposition. -/
partial def interpProp (t : STerm) : InterpM Expr := do
  asProp (← interp t)

partial def interpCore (t : STerm) : InterpM Expr := do
  match t with
  | .num n => return mkIntLit n
  | .lit s => throwError "smt proof: unsupported literal {s}"
  | .str s => return mkStrLit (decodeSmtString s)
  | .annot t _ => interp t
  | .sym s => interpApp s #[]
  | .app f args => interpApp f args
  | .qual f sort args =>
      let ty ← sortToType sort
      -- constructors: the parameters of the datatype are given by the sort (e.g., `(as Option.some (Option Nat))`
      -- applied to an `Int` term)
      if let some (.ctor n) := (← read).table.syms.get? f then
        if !args.isEmpty then
          let c ← mkConstWithFreshMVarLevels n
          let (ms, bis, rt) ← forallMetaTelescopeReducing (← inferType c)
          let explicit := (List.range ms.size).toArray.filter fun i => bis[i]!.isExplicit
          if explicit.size == args.size && (← isDefEq rt ty) then
            for (i, a) in explicit.zip args do
              let v ← interp a
              let expected ← instantiateMVars (← inferType ms[i]!)
              ms[i]!.mvarId!.assign (← coerce v (← inferType v) expected)
            let r ← instantiateMVars (mkAppN c ms)
            if !r.hasExprMVar then return r
      let e ← interpApp f args
      let ety ← inferType e
      if ← isDefEq ety ty then return e
      coerce e ety ty
  | .iapp f idx args =>
      -- testers: `((_ is C) x)` and `((_ is-C C is-C) x)` (Z3)
      -- character literals `(_ Char n)`
      if f == "Char" && args.isEmpty then
        let some (STerm.num n) := idx[0]? | throwError "smt proof: ill-formed character {t}"
        return mkApp (mkConst ``Char.ofNat) (mkRawNatLit n)
      if f == "is" || f.startsWith "is-" then
        let ctorSym := if f == "is" then (match idx[0]? with | some (STerm.sym c) => c | _ => "") else f.drop 3
        let some x := args[0]? | throwError "smt proof: tester without argument"
        match (← read).table.syms.get? ctorSym with
        | some (.ctor c) => mkTester c (← interp x)
        | _ => throwError "smt proof: unknown constructor {ctorSym}"
      else
        -- indexed applications of recursive functions (e.g., `((_ @Nat.pow 0) x y)` in Z3 proofs)
        interpApp f args
  | .quant k vars body => interpQuant k vars body

partial def interpQuant (k : QuantKind) (vars : Array (String × SExpr)) (body : STerm) : InterpM Expr := do
  -- NOTE: the parameters of sort `Nat` of lambda terms (e.g., Blaster's translation of Lean lambdas) are
  -- interpreted as Lean `Nat` variables, i.e., as `↑x` in the body
  let natParam (s : SExpr) : Bool := k == .lambda && s == .atom "Nat"
  let types ← vars.mapM fun (_, s) => if natParam s then pure natType else sortToType s
  let rec go (i : Nat) (fvars : Array Expr) : InterpM Expr := do
    if h : i < vars.size then
      withLocalDeclD (Name.mkSimple vars[i].1) types[i]! fun x =>
        let v := if natParam vars[i].2 then mkIntOfNat x else x
        withReader (fun ctx => { ctx with locals := ctx.locals.insert vars[i].1 v }) (go (i + 1) (fvars.push x))
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
  | "not", 1 => return mkNot (← interpProp args[0]!)
  | "and", _ => if args.isEmpty then return mkConst ``True else foldBinRight mkAnd (← args.mapM interpProp)
  | "or", _ => if args.isEmpty then return mkConst ``False else foldBinRight mkOr (← args.mapM interpProp)
  | "=>", _ => foldBinRight (fun a b => mkForall `h .default a b) (← args.mapM interpProp)
  | "xor", 2 => return mkNot (← mkEq (← interpProp args[0]!) (← interpProp args[1]!))
  | "=", _ => chain mkEqSmt (← args.mapM interp)
  -- equisatisfiability (Z3): interpreted as an implication
  | "~", 2 => return mkForall `h .default (← interpProp args[0]!) (← interpProp args[1]!)
  | "distinct", _ =>
      let es ← args.mapM interp
      let mut cs := #[]
      for i in [:es.size] do
        for j in [i+1:es.size] do cs := cs.push (mkNot (← mkEqSmt es[i]! es[j]!))
      if cs.isEmpty then return mkConst ``True else foldBinRight mkAnd cs
  | "ite", 3 => mkClassicalIte (← interpProp args[0]!) (← interpInt? args[1]!) (← interpInt? args[2]!)
  | "+", _ => foldBin mkIntAdd (← args.mapM interpInt)
  | "-", 1 => return mkIntNeg (← interpInt args[0]!)
  | "-", _ => foldBin mkIntSub (← args.mapM interpInt)
  | "*", _ => foldBin mkIntMul (← args.mapM interpInt)
  | "div", _ => foldBin mkIntDiv (← args.mapM interpInt)
  | "mod", 2 => return mkIntMod (← interpInt args[0]!) (← interpInt args[1]!)
  -- Z3's (unspecified) division and modulo by zero (e.g., `(= (div x y) (div0 x y))` in the lemmas on `y = 0`),
  -- interpreted as the division and modulo
  | "div0", 2 => return mkIntDiv (← interpInt args[0]!) (← interpInt args[1]!)
  | "mod0", 2 => return mkIntMod (← interpInt args[0]!) (← interpInt args[1]!)
  | "abs", 1 => return mkApp (mkConst ``Int.natAbs) (← interpInt args[0]!) |> mkIntOfNat
  | "<=", _ => chain (fun a b => pure (mkIntLe a b)) (← args.mapM interpInt)
  | "<", _ => chain (fun a b => pure (mkIntLt a b)) (← args.mapM interpInt)
  | ">=", _ => chain (fun a b => pure (mkIntLe b a)) (← args.mapM interpInt)
  | ">", _ => chain (fun a b => pure (mkIntLt b a)) (← args.mapM interpInt)
  | "str.++", _ | "seq.++", _ => foldBin (fun a b => mkApp2 (mkConst ``String.append) a b) (← args.mapM interp)
  | "str.len", 1 | "seq.len", 1 => return mkIntOfNat (mkApp (mkConst ``String.length) (← interp args[0]!))
  -- strings as sequences of characters (Z3 proofs): `(seq.unit (_ Char n))`
  | "seq.unit", 1 => return mkApp (mkConst ``String.singleton) (← interp args[0]!)
  | "seq.empty", 0 => return mkStrLit ""
  | _, _ =>
    match ctx.table.syms.get? f with
    | some (.expr e) =>
        if args.isEmpty then return e
        mkAppCoerce e (← args.mapM interp)
    | some (.macro params body) =>
        if args.isEmpty && !params.isEmpty then
          -- the function itself (e.g., `(= @isNat (lambda ((x Int)) (<= 0 x)))` in cvc5 proofs)
          return ← interpQuant .lambda params body
        if params.size != args.size then throwError "smt proof: wrong number of arguments for {f}"
        let vals ← args.mapM interp
        -- NOTE: macro bodies only refer to their parameters
        let locals := (params.zip vals).foldl (fun m ((x, _), v) => m.insert x v) {}
        withReader (fun c => { c with locals }) (interp body)
    | some .trueFun => return mkConst ``True
    | some (.lam e) =>
        if args.isEmpty then return e
        return (← mkAppCoerce e (← args.mapM interp)).headBeta
    | some (.ctor n) =>
        let c ← mkConstWithFreshMVarLevels n
        if args.isEmpty then
          -- nullary constructor (e.g., `List.nil`): parameters are left as metavariables, to be
          -- assigned by unification with the context (e.g., the other side of an equality)
          let (ms, _, _) ← forallMetaTelescopeReducing (← inferType c)
          return mkAppN c ms
        mkAppCoerce c (← args.mapM interp) (allowMVars := true)
    | some (.selector c i) =>
        let some a := args[0]? | throwError "smt proof: selector without argument"
        let e ← mkSelector c i (← interp a) (deferDefault := true)
        toSmtWorld e
    | some (.tester c) =>
        let some a := args[0]? | throwError "smt proof: tester without argument"
        mkTester c (← interp a)
    | some (.skolem params x sort body neg) =>
        if params.size != args.size then throwError "smt proof: wrong number of arguments for {f}"
        let vals ← args.mapM interp
        let ty ← sortToType sort
        let u ← getLevel ty
        let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) ty)
        withLocalDeclD (Name.mkSimple x) ty fun fx => do
          let locals := (params.zip vals).foldl (fun m (y, v) => m.insert y v) ctx.locals |>.insert x fx
          let φ ← withReader (fun c => { c with locals }) (interpProp body)
          let p ← mkLambdaFVars #[fx] (if neg then mkNot φ else φ)
          return mkApp3 (mkConst ``Classical.epsilon [u]) ty inst p
    | some .apply =>
        let some fn := args[0]? | throwError "smt proof: apply without argument"
        let r ← mkAppCoerce (← interp fn) (← (args.extract 1 args.size).mapM interp)
        toSmtWorld r
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
