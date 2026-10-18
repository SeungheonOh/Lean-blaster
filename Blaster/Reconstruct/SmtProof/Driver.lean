import Lean
import Blaster.Smt.Translate
import Blaster.Reconstruct.Discharge
import Blaster.Reconstruct.SmtProof.Z3
import Blaster.Reconstruct.SmtProof.Alethe
import Blaster.Reconstruct.SmtProof.Replay
import Blaster.Reconstruct.SmtProof.Bridge
import Blaster.Reconstruct.SmtProof.NlArith

/-!
# Proof reconstruction from SMT proofs

Given a residual goal proved valid by the SMT solver, this module:
 1. translates the goal to SMT-LIB with Blaster's translation (top-level variables are introduced
    as Lean free variables such that the SMT constants can be mapped back to them);
 2. runs a proof producing backend (see `Backend`) on the query and parses its proof
    into the backend independent representation (`Proof`);
 3. builds the interpretation of the SMT symbols in Lean (`SymTable`) from the query and from
    Blaster's translation caches;
 4. replays the proof (see `Replay.lean`) to obtain a proof of `False` from the negation of the goal.
-/

open Lean Meta Elab Term Tactic Blaster.Smt Blaster.Optimize Blaster.Options

namespace Blaster.Reconstruct.SmtProof

/-! ## Backends -/

def isZ3SpecificCommand (c : SExpr) : Bool :=
  match c with
  | .list xs =>
      match xs[0]?, xs[1]? with
      | some (SExpr.atom "set-simplifier"), _ => true
      | some (SExpr.atom "set-option"), some (SExpr.atom o) =>
          -- options set by the backend preamble, and options incompatible with proofs
          o == ":print-success" || o == ":produce-models" || o == ":produce-proofs" ||
          o == ":smt.macro_finder" || o == ":timeout" ||
          -- version specific options
          o.startsWith ":smt.arith.nl"
      | _, _ => false
  | _ => false

/-- Commands of Blaster's query that are set by the backend preamble or version specific (the simplifiers
    of the query, e.g., `recfun-finder`, are kept). -/
def isZ3PreambleCommand (c : SExpr) : Bool :=
  match c with
  | .list xs =>
      match xs[0]?, xs[1]? with
      | some (SExpr.atom "set-option"), some (SExpr.atom o) =>
          o == ":print-success" || o == ":produce-models" || o == ":produce-proofs" || o == ":timeout" ||
          o.startsWith ":smt.arith.nl"
      | _, _ => false
  | _ => false

/-- Z3 with legacy proof objects. With `simplifiers`, the simplifiers of Blaster's query (e.g., `recfun-finder`,
    `macro_finder`) are kept, which may be needed to find a proof, but produce coarser proofs. -/
def z3Backend (cmd : String) (timeoutSec : Nat) (simplifiers := false) : Backend where
  name := if simplifiers then "z3+" else "z3"
  cmd := cmd
  args := #["-smt2", s!"-T:{timeoutSec}"]
  -- NOTE: `pp.simplify_implies` prints `(=> a (=> b c))` as `(=> (and a b) c)` by default
  preamble := #["(set-option :produce-proofs true)", "(set-option :pp.simplify_implies false)"]
  dropCommand := if simplifiers then isZ3PreambleCommand else isZ3SpecificCommand
  parseProof := Z3.parseProof

/-- Guard the top-level universally quantified assertions over `Nat` (e.g., the definitions of recursive
    functions `∀ x, f x = f_LRec x`) with `0 ≤ x`, such that they hold for the interpretation of `Nat`
    functions in Lean (see `Interp.lean`). This only weakens the query. -/
def guardNatQuantifiers (c : SExpr) : SExpr :=
  match c with
  | .list #[.atom "assert", .list #[.atom "forall", .list vars, body]] =>
      let natVars := vars.filterMap fun v => match v with
        | .list #[.atom x, .atom "Nat"] => some x
        | _ => none
      if natVars.isEmpty then c else
      let guard (b : SExpr) : SExpr :=
        natVars.foldr (fun x acc => .list #[.atom "=>", .list #[.atom "<=", .atom "0", .atom x], acc]) b
      let body' := match body with
        | .list xs => if xs[0]? == some (.atom "!") then .list (xs.set! 1 (guard xs[1]!)) else guard body
        | _ => guard body
      .list #[.atom "assert", .list #[.atom "forall", .list vars, body']]
  | c => c

/-- Commands of Blaster's query that are specific to Z3 (all options are set by the backend preamble). -/
def isZ3OnlyCommand (c : SExpr) : Bool :=
  match c.head? with
  | some "set-simplifier" | some "set-option" | some "set-logic" => true
  | _ => false

/-- cvc5 with Alethe proofs. -/
def cvc5Backend (cmd : String) (timeoutSec : Nat) : Backend where
  name := "cvc5"
  cmd := cmd
  args := #["--lang=smt2", "--parsing-mode=lenient", s!"--tlimit={timeoutSec * 1000}", "--proof-format-mode=alethe",
            "--proof-granularity=dsl-rewrite"]
  preamble := #["(set-option :produce-proofs true)", "(set-logic ALL)"]
  dropCommand := isZ3OnlyCommand
  parseProof := Alethe.parseProof

/-- Run `backend` on the query `cmds`, returning the raw proof output. The query is written to a
    temporary file (no interaction with the solver's pipes during the run). -/
def runBackend (backend : Backend) (cmds : Array SExpr) : IO (Except String String) := do
  let query := String.intercalate "\n" (backend.preamble.toList ++
    (cmds.filter (!backend.dropCommand ·)).toList.map toString ++ ["(check-sat)", "(get-proof)", "(exit)"])
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_DUMP" then IO.FS.writeFile f query
  let (h, path) ← IO.FS.createTempFile
  try
    h.putStr query
    h.flush
    let out ← IO.Process.output { cmd := backend.cmd, args := backend.args.push path.toString }
    -- the first line among `sat`, `unsat` and `unknown` (e.g., after warnings on unsupported options)
    let lines := out.stdout.splitOn "\n"
    -- errors on the query (e.g., unsupported declarations): its verdict and proof are not used
    let errors := lines.filter (·.trimLeft.startsWith "(error")
    if !errors.isEmpty then
      return .error s!"{backend.name}: {String.intercalate " " (errors.take 3) |>.take 600}"
    match lines.findIdx? (fun l => ["sat", "unsat", "unknown"].contains l.trim) with
    | some i =>
        if lines[i]!.trim == "unsat" then
          return .ok (String.intercalate "\n" (lines.drop (i + 1)))
        return .error s!"{backend.name}: {lines[i]!.trim}"
    | none => return .error s!"{backend.name}: {out.stdout.take 300} {out.stderr.take 300}"
  finally
    IO.FS.removeFile path

/-- Results of the backends on the last query, reused by the replays of a goal with the different interpretations
    of the polymorphic encoding (see `proveBySmtProof`). -/
initialize backendRuns : IO.Ref (String × Std.HashMap String (Except String String)) ← IO.mkRef ("", {})

/-- `runBackend`, reusing the result of a previous run of `backend` on the same query. -/
def runBackendCached (backend : Backend) (cmds : Array SExpr) : IO (Except String String) := do
  let query := String.intercalate "\n" (cmds.toList.map toString)
  let (q, runs) ← backendRuns.get
  let runs := if q == query then runs else {}
  if let some r := runs.get? backend.name then return r
  let r ← runBackend backend cmds
  backendRuns.set (query, runs.insert backend.name r)
  return r

/-! ## Interpretation of the query symbols -/

/-- Lean name of an SMT symbol produced by `nameToSmtSymbol` (possibly quoted). -/
def symbolToName (s : String) : Name :=
  let s := if s.startsWith "|" && s.endsWith "|" then (s.drop 1 |>.dropRight 1) else s
  s.toName

/-- Interpretation of Blaster's auxiliary recursive functions (as Lean functions on `Int`). -/
def auxiliaryInterp (s : String) : MetaM (Option Expr) := do
  let int := Lean.mkConst ``Int
  let toNat (x : Expr) := mkApp (Lean.mkConst ``Int.toNat) x
  let ofNat (n : Expr) := mkApp3 (Lean.mkConst ``Nat.cast [levelZero]) int (Lean.mkConst ``instNatCastInt) n
  match s with
  | "@Nat.pow" =>
      withLocalDeclD `x int fun x => withLocalDeclD `y int fun y => do
        mkLambdaFVars #[x, y] (ofNat (← mkAppM ``HPow.hPow #[toNat x, toNat y]))
  | "@Int.pow" =>
      withLocalDeclD `x int fun x => withLocalDeclD `y int fun y => do
        mkLambdaFVars #[x, y] (← mkAppM ``HPow.hPow #[x, toNat y])
  | "@Nat.log2" =>
      withLocalDeclD `x int fun x => do
        mkLambdaFVars #[x] (ofNat (mkApp (Lean.mkConst ``Nat.log2) (toNat x)))
  -- the string of a list of characters
  | "@String.mk" => return some (Lean.mkConst ``String.mk)
  | _ => return none

/-- Remove the bars of a quoted symbol. -/
def unquote (s : String) : String :=
  if s.startsWith "|" && s.endsWith "|" && s.length ≥ 2 then (s.drop 1).dropRight 1 else s

/-- Interpretation of Blaster's polymorphic encoding (see `Poly`), given the sort variables of the goal with their
    SMT symbols: the membership predicates of the types with sort variables are the images of their worlds (e.g.,
    `@isFun α β f` is `Img (liftFun (inj α) (inj β) _) f`), and the constants of the goal the images of their values
    (e.g., `x : α` is `inj α x`). The sorts `@Type` and `@Instance` and the predicates `@isInstance` are interpreted by
    `buildSymTable`. -/
def polySymTable (tbl : SymTable) (cmds : Array SExpr) (env : TranslateEnv) (consts : Std.HashMap String Expr)
    (sortVars : Array (String × Expr)) : MetaM SymTable := do
  let mut tbl := tbl
  for (s, α) in sortVars do tbl := { tbl with syms := tbl.syms.insert s (.expr α) }
  -- membership predicates of the types with sort variables (cached as `fun αs => T`): `fun αs v => Img w v`
  for (k, decl) in env.smtEnv.indTypeInstCache.toList do
    let .lam .. := k.expr | continue
    try
      let sort ← ofExcept (parseSExpr (toString decl.instSort))
      let d ← (sortToType sort).run { table := tbl }
      let pred ← lambdaTelescope k.expr fun αs t => do
        if ← αs.anyM fun α => do return !isTypeUniverse (← inferType α) then throwError "not a sort variable"
        let some (w, _) ← Poly.mkWorld t d | throwError "no world for {t}"
        withLocalDeclD `v d fun v => do mkLambdaFVars (αs.push v) (← mkAppM ``Poly.Img #[w, v])
      let n := toString decl.instName
      -- NOTE: the recursive definitions of the predicates of datatypes (`_LRec`) have the same interpretation
      let rec_ := if n.startsWith "|" then s!"|{unquote n}_LRec|" else s!"{n}_LRec"
      tbl := { tbl with syms := tbl.syms.insert n (.lam pred) |>.insert rec_ (.lam pred) }
    catch _ => pure ()
  -- constants of the goal
  for c in cmds do
    let some #[SExpr.atom "declare-const", SExpr.atom n, s] := c.list? | continue
    let some x := consts.get? n | continue
    try
      let d ← (sortToType s).run { table := tbl }
      if let some (w, _) ← Poly.mkWorld (← inferType x) d then
        tbl := { tbl with syms := tbl.syms.insert n (.expr (Poly.applyWorld w x)) }
    catch _ => pure ()
  return tbl

/-- Build the interpretation of the symbols of the query `cmds`, given the translation environment
    and the map from SMT constants (`$k`) to Lean free variables. Blaster's polymorphic encoding is interpreted
    with `@Instance` as `instanceType?` (a single sort variable), or as `Poly.Univ` given the sort variables
    `polySortVars?` (see `polySymTable`). -/
def buildSymTable (cmds : Array SExpr) (env : TranslateEnv) (consts : Std.HashMap String Expr)
    (instanceType? : Option Expr := none) (polySortVars? : Option (Array (String × Expr)) := none) :
    MetaM SymTable := do
  let mut tbl : SymTable := {}
  -- polymorphic encoding: the sorts `@Type` and `@Instance` of the sort variables of `Sort u` (cached on `Sort u`),
  -- and their membership predicates `@isInstance v α`
  let mut polySorts : Std.HashMap String Expr := {}
  if polySortVars?.isSome then
    for (k, decl) in env.smtEnv.indTypeInstCache.toList do
      let .sort u := k.expr | continue
      let (.SymbolSort ty, some (.SymbolSort inst)) := (decl.instSort, decl.instInstanceSort) | continue
      let univ := Lean.mkConst ``Poly.Univ [u]
      let mem ← withLocalDeclD `v univ fun v => withLocalDeclD `α (mkSort u) fun α => do
        mkLambdaFVars #[v, α] (← mkAppM ``Poly.Img #[mkApp (Lean.mkConst ``Poly.inj [u]) α, v])
      polySorts := polySorts.insert (toString ty) (mkSort u) |>.insert (toString inst) univ
      tbl := { tbl with syms := tbl.syms.insert (toString decl.instName) (.lam mem) }
  -- Lean functions of the translation
  let mut funs : Std.HashMap String Expr := {}
  for (k, v) in env.smtEnv.funInstCache.toList do
    let nm := match v with
      | .SimpleIdent s => toString s
      | .QualifiedIdent s _ => toString s
    funs := funs.insert nm (← instantiateSortParams instanceType? k.expr)
  let mut datatypeSorts : Array SExpr := #[]
  for c in cmds do
    let some xs := c.list? | continue
    match xs[0]?.bind SExpr.atom?, xs[1]?.bind SExpr.atom? with
    | some "declare-sort", some n =>
        -- polymorphic encoding (see `proveBySmtProof`)
        if let some t := polySorts.get? n then
          tbl := { tbl with sorts := tbl.sorts.insert n t }
        else if n.startsWith "@Type" then
          tbl := { tbl with sorts := tbl.sorts.insert n (mkConst ``Unit) }
        else if n.startsWith "@Instance" then
          if let some t := instanceType? then tbl := { tbl with sorts := tbl.sorts.insert n t }
    | some "define-sort", some n =>
        if let some (SExpr.list #[]) := xs[2]? then
          tbl := { tbl with aliases := tbl.aliases.insert n xs[3]! }
    | some "declare-const", some n =>
        if let some e := consts.get? n then
          tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
        else if let some (SExpr.atom s) := xs[2]? then
          -- sort variables (polymorphic encoding)
          if s.startsWith "@Type" then tbl := { tbl with syms := tbl.syms.insert n (.expr (mkConst ``Unit.unit)) }
        if let some s := xs[2]? then datatypeSorts := datatypeSorts.push s
    | some "declare-fun", some n =>
        if let some e := funs.get? n then
          tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
        else if n.startsWith "@apply" then
          tbl := { tbl with syms := tbl.syms.insert n .apply }
        else if n.startsWith "@is" && !tbl.syms.contains n then
          tbl := { tbl with syms := tbl.syms.insert n .trueFun }
    | some "define-fun", some n =>
        let some (SExpr.list ps) := xs[2]? | continue
        let params := ps.filterMap fun p => match p with
          | .list #[.atom x, s] => some (x, s)
          | _ => none
        match STerm.ofSExpr {} xs[4]! with
        | .ok body => tbl := { tbl with syms := tbl.syms.insert n (.macro params body) }
        | .error _ => pure ()
    | some "define-fun-rec", some n =>
        if n.startsWith "@is" then
          tbl := { tbl with syms := tbl.syms.insert n .trueFun }
        else if let some e ← auxiliaryInterp n then
          tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
        else if (unquote n).endsWith "_LRec" then
          -- the definition of a recursive function: same interpretation as the function
          let base := (unquote n).dropRight 5
          if let some e := funs.get? base <|> funs.get? s!"|{base}|" then
            tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
    | some "assert", _ =>
        -- definitions of lambda terms (see `Blaster.Smt.translateLambda`):
        -- `(forall (xs) (! (= (@apply @lambda_n xs) b) :qid @lambda_n_def_cstr))`, and
        -- `(forall (ys xs) (! (= (@apply (@apply @global_lambda_n ys) xs) b) :qid @global_lambda_n_def_cstr))`
        if let some (n, t) := lambdaDef? xs[1]! then
          if !tbl.syms.contains n then tbl := { tbl with syms := tbl.syms.insert n (.macro #[] t) }
    | some "declare-datatype", some n =>
        tbl ← addDatatype tbl n xs[2]!
    | some "declare-datatypes", _ =>
        let some (SExpr.list sorts) := xs[1]? | continue
        let some (SExpr.list decls) := xs[2]? | continue
        for (s, d) in sorts.zip decls do
          let some (SExpr.atom n) := s.list? >>= (·[0]?) | continue
          tbl ← addDatatype tbl n d
    | _, _ => pure ()
  if let some sortVars := polySortVars? then tbl ← polySymTable tbl cmds env consts sortVars
  -- datatype sorts of the query as they occur in proofs (with expanded aliases)
  let ctx : InterpCtx := { table := tbl }
  let mut expanded : Std.HashMap String (Option Expr) := {}
  for s in datatypeSorts do
    let some _ := s.list? | continue
    try
      let t ← (sortToType s).run ctx
      let key := toString (expandSort tbl s)
      match expanded.get? key with
      | some (some t') => if !(← isDefEq t t') then expanded := expanded.insert key none
      | some none => pure ()
      | none => expanded := expanded.insert key (some t)
    catch _ => pure ()
  for (k, v) in expanded.toList do
    if let some t := v then tbl := { tbl with expandedSorts := tbl.expandedSorts.insert k t }
  return tbl
where
  /-- Lean functions of the translation abstracted over their generic parameters (instances of
      `Blaster.Optimize.getInstApp`, e.g., `fun α [BEq α] a b => a == b`), which are erased in their SMT
      signatures: with a single sort variable `α` interpreting `@Instance`, the explicit sort parameters are
      instantiated with `α` (the instances are synthesized when the function is applied, and the implicit
      parameters inferred from the arguments, see `mkAppCoerce`). -/
  instantiateSortParams (instanceType? : Option Expr) (e : Expr) : MetaM Expr := do
    let some α := instanceType? | return e
    let ty ← inferType α
    let mut e := e.headBeta
    for _ in [:16] do
      let .lam _ t b bi := e | break
      if !bi.isExplicit || !(← isDefEq t ty) then break
      e := (b.instantiate1 α).headBeta
    return e
  lambdaDef? (e : SExpr) : Option (String × STerm) := Id.run do
    let some #[SExpr.atom "forall", SExpr.list vs, SExpr.list ann] := e.list? | return none
    if ann[0]? != some (SExpr.atom "!") then return none
    -- NOTE: the guards of the definition are removed: `0 ≤ x` for the variables of sort `Nat` (see
    -- `guardNatQuantifiers`), and the membership predicates of the parameters (see `Blaster.Smt.translateLambda`)
    let rec unguard (e : SExpr) (fuel : Nat) : SExpr :=
      match fuel, e with
      | fuel + 1, .list #[.atom "=>", .list #[.atom "<=", .atom "0", .atom _], b] => unguard b fuel
      | fuel + 1, .list #[.atom "=>", g, b] =>
          if (g.head?.map unquote).any (·.startsWith "@is") then unguard b fuel else e
      | _, e => e
    let some #[SExpr.atom "=", SExpr.list lhs, body] := (ann[1]?.map (unguard · (3 * vs.size))) >>= SExpr.list? | return none
    let vars := vs.filterMap fun v => match v with
      | .list #[.atom x, s] => some (x, s)
      | _ => none
    let some (SExpr.atom apply) := lhs[0]? | return none
    if !apply.startsWith "@apply" then return none
    let .ok b := STerm.ofSExpr {} body | return none
    match lhs[1]? with
    | some (SExpr.atom l) =>
        if !l.startsWith "@lambda" then return none
        return some (l, .quant .lambda vars b)
    | some (SExpr.list inner) =>
        let some (SExpr.atom g) := inner[1]? | return none
        if !g.startsWith "@global_lambda" then return none
        let k := inner.size - 2
        if k > vars.size then return none
        let ys := vars.extract 0 k
        let xs := vars.extract k vars.size
        return some (g, .quant .lambda ys (if xs.isEmpty then b else .quant .lambda xs b))
    | _ => return none
  addDatatype (tbl : SymTable) (n : String) (decl : SExpr) : MetaM SymTable := do
    -- `(par (params) (ctors))` or `(ctors)`
    let ctors := match decl with
      | .list #[.atom "par", _, .list cs] => cs
      | .list cs => cs
      | _ => #[]
    let mut tbl := tbl
    for c in ctors do
      let (cname, fields) := match c with
        | .atom a => (a, #[])
        | .list xs => (xs[0]!.atom?.getD "", xs.extract 1 xs.size)
        | _ => ("", #[])
      let leanCtor := symbolToName cname
      let some (.ctorInfo info) := (← getEnv).find? leanCtor | continue
      tbl := { tbl with
        syms := tbl.syms.insert cname (.ctor leanCtor) |>.insert s!"is-{cname}" (.tester leanCtor),
        sorts := tbl.sorts.insert n (mkConst info.induct) }
      for h : i in [:fields.size] do
        if let some (SExpr.atom sel) := fields[i].list? >>= (·[0]?) then
          tbl := { tbl with syms := tbl.syms.insert sel (.selector leanCtor i) }
    return tbl

/-- `buildSymTable` with the polymorphic encoding interpreted by `Poly`, for the sort variables `sortVars` (declared
    by the translation `env`). -/
def polyBuildSymTable (cmds : Array SExpr) (env : TranslateEnv) (consts : Std.HashMap String Expr)
    (sortVars : Array Expr) : TermElabM SymTable := do
  let (syms, _) ← (sortVars.mapM fun α => do
      return (toString (← typeParamNameToSmtSymbol α.fvarId!), α) : TranslateEnvT (Array (String × Expr))).run env
  buildSymTable cmds env consts (polySortVars? := some syms)

/-- Interpretation of the skolem constants introduced by `sk` steps (Z3): for
    `(~ (not (forall ((x S)) φ)) (not φ[x := c]))` (resp. `(~ (exists ((x S)) φ) φ[x := c])`),
    the constant `c` (named `x!n`) is interpreted as `Classical.epsilon (fun x => ¬ φ)`
    (resp. `Classical.epsilon (fun x => φ)`). Only steps with a single bound variable are handled. -/
partial def addSkolems (proof : Proof) (tbl : SymTable) : MetaM SymTable := do
  let mut tbl := tbl
  -- names introduced by `intro-def` (Z3's Tseitin names): `(= t k)` defines `k` as `t`
  for step in proof.steps do
    if step.rule != "intro-def" then continue
    match step.concl.stripAnnot with
    | .app "=" #[t, .sym k] | .app "=" #[.sym k, t] =>
        if !tbl.syms.contains k then tbl := { tbl with syms := tbl.syms.insert k (.macro #[] t) }
    | _ => pure ()
  for step in proof.steps do
    if step.rule != "sk" then continue
    let .app _ #[a, b] := step.concl.stripAnnot | continue
    let (vars, body, neg) := match a.stripAnnot with
      | .app "not" #[.quant .forall vs φ] => (vs, φ, true)
      | .quant .exists vs φ => (vs, φ, false)
      | _ => (#[], .sym "true", false)
    let #[(x, sort)] := vars | continue
    -- skolem function applied to the variables of the context: `(x!n y₁ ... yₖ)`
    if let some (c, ys) := findSkolemApp (x ++ "!") b (fun c => !tbl.syms.contains c) then
      tbl := { tbl with syms := tbl.syms.insert c (.skolem ys x sort body neg) }
      continue
    -- the skolem constant: a symbol of `b` named `x!n`, not occurring in `a` and not yet interpreted
    let some c := findSkolem (x ++ "!") b fun c => !tbl.syms.contains c && (findSkolem c a fun _ => true).isNone
      | continue
    try
      let e ← (do
        let ty ← sortToType sort
        let u ← getLevel ty
        let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) ty)
        withLocalDeclD (Name.mkSimple x) ty fun fx => do
          let φ ← withReader (fun c => { c with locals := c.locals.insert x fx }) (interp body)
          let p ← mkLambdaFVars #[fx] (if neg then mkNot φ else φ)
          return mkApp3 (mkConst ``Classical.epsilon [u]) ty inst p : InterpM Expr).run { table := tbl }
      tbl := { tbl with syms := tbl.syms.insert c (.expr e) }
    catch _ => pure ()
  return tbl
where
  findSkolemApp (pre : String) (t : STerm) (ok : String → Bool) : Option (String × Array String) :=
    match t with
    | .app f args =>
        let syms := args.filterMap fun a => match a with | .sym s => some s | _ => none
        if f.startsWith pre && !args.isEmpty && syms.size == args.size && ok f then some (f, syms)
        else args.findSome? (findSkolemApp pre · ok)
    | .iapp _ _ args | .qual _ _ args => args.findSome? (findSkolemApp pre · ok)
    | .quant _ _ b => findSkolemApp pre b ok
    | .annot t _ => findSkolemApp pre t ok
    | _ => none
  findSkolem (pre : String) (t : STerm) (ok : String → Bool) : Option String :=
    match t with
    | .sym s => if s.startsWith pre && ok s then some s else none
    | .app f args =>
        if f.startsWith pre && args.isEmpty && ok f then some f else args.findSome? (findSkolem pre · ok)
    | .iapp _ _ args | .qual _ _ args => args.findSome? (findSkolem pre · ok)
    | .quant _ _ b => findSkolem pre b ok
    | .annot t _ => findSkolem pre t ok
    | _ => none

/-! ## Bridge tactics -/

/-- Introduce the universally quantified variables of the goal, substituting `x := ↑n` for the
    `Int` variables guarded by `0 ≤ x`. -/
macro "blaster_nat_intros" : tactic =>
  `(tactic| repeat (first | (intro x hx; obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hx; subst hn) | intro _))

syntax (name := blasterDivMod) "blaster_divmod" : tactic

/-- Facts on the `Int` divisions and modulos by non-literal divisors of the goal (for `omega`, which treats
    them as atoms): `y * (x / y) + x % y = x`, `y ≠ 0 → 0 ≤ x % y`, `0 < y → x % y < y`, `y < 0 → x % y < -y`. -/
@[tactic blasterDivMod] def evalBlasterDivMod : Tactic := fun _ => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let mut pairs : Array (Expr × Expr) := #[]
  let mut todo := #[tgt]
  for d in ← getLCtx do
    if !d.isImplementationDetail then todo := todo.push (← instantiateMVars d.type)
  let found := todo.foldl (fun acc e => acc ++ (collect e)) #[]
  for s in found do
    let p := (s.getArg! 4, s.getArg! 5)
    if !(pairs.any fun q => q.1 == p.1 && q.2 == p.2) then pairs := pairs.push p
  if pairs.isEmpty then throwError "blaster_divmod: no division"
  for (x, y) in pairs do
    let xs ← Term.exprToSyntax x
    let ys ← Term.exprToSyntax y
    evalTactic (← `(tactic| have := Int.mul_ediv_add_emod $xs $ys))
    evalTactic (← `(tactic| have : $ys ≠ 0 → 0 ≤ $xs % $ys := fun h => Int.emod_nonneg $xs h))
    evalTactic (← `(tactic| have : 0 < $ys → $xs % $ys < $ys := fun h => Int.emod_lt_of_pos $xs h))
    evalTactic (← `(tactic| have : $ys < 0 → $xs % $ys < -$ys := fun h => by
      have := Int.emod_lt_of_pos $xs (Int.neg_pos.mpr h); rwa [Int.emod_neg] at this))
where
  collect (e : Expr) : Array Expr := Id.run do
    let mut acc := #[]
    let mut stack := #[e]
    let mut seen : Std.HashSet Expr := {}
    while !stack.isEmpty do
      let s := stack.back!
      stack := stack.pop
      if seen.contains s then continue
      seen := seen.insert s
      if (s.isAppOfArity ``HDiv.hDiv 6 || s.isAppOfArity ``HMod.hMod 6) && (s.getArg! 0).isConstOf ``Int &&
          !(s.getArg! 5).isAppOfArity ``OfNat.ofNat 3 && !s.hasLooseBVars then
        acc := acc.push s
      match s with
      | .app f a => stack := stack.push f |>.push a
      | .lam _ t b _ | .forallE _ t b _ => stack := stack.push t |>.push b
      | .mdata _ b | .proj _ _ b => stack := stack.push b
      | _ => pure ()
    return acc

syntax (name := blasterCasesNat) "blaster_cases_nat" : tactic

/-- Case analysis (`0` / `n + 1`) on the local variables of type `Nat`. -/
@[tactic blasterCasesNat] def evalBlasterCasesNat : Tactic := fun _ => do
  let vars ← withMainContext do
    let mut vs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← whnfR d.type).isConstOf ``Nat then vs := vs.push d.fvarId
    return vs
  if vars.isEmpty then throwError "blaster_cases_nat: no Nat variable"
  for v in vars do
    let gs ← getGoals
    let mut gs' := #[]
    for g in gs do
      if (← g.getDecl).lctx.contains v then
        let subgoals ← g.cases v
        gs' := gs' ++ subgoals.map (·.mvarId)
      else gs' := gs'.push g
    setGoals gs'.toList

syntax (name := blasterUnfoldLhs) "blaster_unfold_lhs" : tactic

/-- Unfold once the user function at the head of the left-hand side of the equality to prove (e.g., the
    definitional axiom `f x = body[x]` of a recursive function, whose recursive calls must not be unfolded). -/
@[tactic blasterUnfoldLhs] def evalBlasterUnfoldLhs : Tactic := fun _ => withMainContext do
  let some (_, lhs, _) := (← whnfR (← instantiateMVars (← getMainTarget))).eq?
    | throwError "blaster_unfold_lhs: equality expected"
  -- NOTE: through the casts of the interpretation (e.g., `↑(f x)` for a function `f` returning `Nat`)
  let lhs := if lhs.isAppOfArity ``Nat.cast 3 then lhs.appArg! else lhs
  let .const f _ := lhs.getAppFn | throwError "blaster_unfold_lhs: application of a constant expected"
  if !isUserDefinition (← getEnv) f then throwError "blaster_unfold_lhs: {f} is not a user definition"
  evalTactic (← `(tactic| rw [$(mkIdent f):ident]))

syntax (name := blasterUnfoldNonRec) "blaster_unfold_nonrec" : tactic

/-- Unfold the non-recursive user definitions occurring in the main goal and its hypotheses (e.g., the
    functions called by a recursive function whose definitional axiom is proved). -/
@[tactic blasterUnfoldNonRec] def evalBlasterUnfoldNonRec : Tactic := fun _ => withMainContext do
  let env ← getEnv
  let mut t ← instantiateMVars (← getMainTarget)
  for d in ← getLCtx do
    if !d.isImplementationDetail then t := mkApp t (← instantiateMVars d.type)
  let mut defs := #[]
  for n in t.getUsedConstants do
    if isUserDefinition env n && !(← isInstance n) && !(← isRecursiveDefinition n) then defs := defs.push n
  if defs.isEmpty then throwError "blaster_unfold_nonrec: no definition to unfold"
  let lemmas ← defs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  evalTactic (← `(tactic| simp only [$lemmas,*] at *))

/-- Tactics proving the interpretation of asserted formulas (and conclusions of steps that can't be
    replayed) from the negated goal and the definitions of user functions. -/
def bridgeTactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("assumption", ← `(tactic| assumption)),
    -- definitions of lambda terms (β-reduction)
    ("rfl", ← `(tactic| (intros; rfl))),
    -- definitions of functions over `Nat` (see `guardNatQuantifiers`)
    ("nat def", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                              blaster_cases_nat <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_unfold_user) <;> grind))),
    -- definitions by case analysis on datatype arguments
    ("nat def cases", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_cases_nat) <;> blaster_cases_vars <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_unfold_user) <;> (try simp_all) <;> first | done | grind))),
    ("omega", ← `(tactic| (intros; omega))),
    -- Blaster's normal forms (e.g., `Nat.add x y`, `Nat.mod x y`) in the negated goal
    ("denorm+omega", ← `(tactic| (intros; blaster_denorm; omega))),
    ("simp", ← `(tactic| (intros; simp_all [Int.toNat_natCast] <;> done))),
    ("simp+omega", ← `(tactic| (intros; blaster_denorm; simp_all [Int.toNat_natCast] <;> omega))),
    -- casts of `Nat` division and modulo (Blaster's encoding: `ite (0 = y) 0 (div x y)`)
    ("casts", ← `(tactic| (intros; blaster_denorm; simp only [Int.natCast_ediv, Int.natCast_emod, Int.natCast_add, Int.natCast_mul,
                            Int.toNat_natCast, Int.ediv_zero, Int.emod_zero] at * <;> (try split) <;> (try split) <;>
                            first | omega | (simp_all; done) | grind))),
    ("grind", ← `(tactic| (intros; grind))),
    -- definitional axioms of recursive functions (e.g., by well-founded recursion): one unfolding
    ("unfold lhs", ← `(tactic| (intros; blaster_unfold_lhs <;> first | rfl | grind | ((repeat' split) <;> omega)))),
    ("nat unfold lhs", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;> blaster_unfold_lhs <;>
                                   first | rfl | grind | ((repeat' split) <;> (try simp_all) <;> first | done | omega | grind)))),
    -- definitional axioms by case analysis on datatype arguments (with the non-recursive callees unfolded)
    ("nat cases unfold lhs", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                                   (try blaster_cases_vars) <;> blaster_unfold_lhs <;> (try blaster_unfold_nonrec) <;>
                                   (try simp_all) <;> (try split) <;> first | done | omega | grind))),
    ("unfold", ← `(tactic| (intros; blaster_unfold_user <;> (try simp_all [Int.toNat_natCast]) <;>
                            (try split) <;> (try split) <;> first | done | omega | grind))),
    ("cases", ← `(tactic| (intros; blaster_cases_vars <;> blaster_unfold_user <;>
                            (try simp_all [Int.toNat_natCast]) <;> first | done | omega | grind)))
  ]

/-- Tactics proving the equations of the SMT macros of Lean functions (e.g., `↑(x - y) = if x < y then 0 else x - y`). -/
def macroTactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("rfl", ← `(tactic| (intros; rfl))),
    ("split+omega", ← `(tactic| (intros; (repeat' split) <;> omega))),
    ("simp+omega", ← `(tactic| (intros; (repeat' split) <;> simp_all [Int.natCast_ediv, Int.natCast_emod] <;> omega))),
    ("simp", ← `(tactic| (intros; simp [Int.natCast_ediv, Int.natCast_emod]; done))),
    ("grind", ← `(tactic| (intros; grind)))]

theorem toNat_ediv_two (y : Int) : (y / 2).toNat = y.toNat / 2 := by omega

def stepTactics (rule : String) : TermElabM (Array (String × TSyntax `tactic)) := do
  let arith := #[
    ("omega", ← `(tactic| (intros; omega))),
    ("divmod+omega", ← `(tactic| (intros; blaster_divmod; omega))),
    ("propext+omega", ← `(tactic| (intros; apply propext; constructor <;> intro <;> omega))),
    ("split+omega", ← `(tactic| (intros; (repeat' split) <;> omega))),
    -- nonlinear arithmetic (fails quickly on goals without nonlinear terms)
    ("nlarith", ← `(tactic| blaster_nlarith))]
  let simp := #[
    ("rfl", ← `(tactic| (intros; rfl))),
    ("simp", ← `(tactic| (intros; simp_all <;> done))),
    -- associativity of the connectives (e.g., the flattening of n-ary connectives by Z3's rewriter)
    ("simp ac", ← `(tactic| (intros; simp_all [and_assoc, or_assoc] <;> done))),
    ("simp only", ← `(tactic| (intros; simp only [*] <;> done)))]
  let grind := #[("grind", ← `(tactic| (intros; grind)))]
  let quant := #[
    ("forall_congr", ← `(tactic| (intro h; exact forall_congr h))),
    ("forall_imp", ← `(tactic| (intro h h' x; exact h x (h' x))))]
  let unfold := #[
    ("nat def", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_cases_nat) <;> (try simp only [Int.toNat_natCast] at *) <;>
                              (try blaster_unfold_user) <;> grind))),
    -- definitional axioms of recursive functions (e.g., by well-founded recursion): one unfolding
    ("unfold lhs", ← `(tactic| (intros; blaster_unfold_lhs <;> first | rfl | grind | ((repeat' split) <;> omega)))),
    ("nat unfold lhs", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;> blaster_unfold_lhs <;>
                                   first | rfl | grind | ((repeat' split) <;> (try simp_all) <;> first | done | omega | grind)))),
    -- definitional axioms by case analysis on datatype arguments (with the non-recursive callees unfolded)
    ("nat cases unfold lhs", ← `(tactic| (blaster_nat_intros <;> (try simp only [Int.toNat_natCast] at *) <;>
                                   (try blaster_cases_vars) <;> blaster_unfold_lhs <;> (try blaster_unfold_nonrec) <;>
                                   (try simp_all) <;> (try split) <;> first | done | omega | grind))),
    ("unfold", ← `(tactic| (intros; blaster_unfold_user <;> (try simp_all [Int.toNat_natCast]) <;> grind))),
    -- `@Nat.log2` (see `auxiliaryInterp`): one unfolding step
    ("log2", ← `(tactic| (intros; rw [Nat.log2_def] <;> (try simp only [toNat_ediv_two] at *) <;> split <;> omega)))]
  match rule with
  | "th-lemma" => return arith ++ simp ++ grind ++ unfold
  -- datatype lemmas over generalized terms (e.g., `x = C (C.0 x) ∨ ¬ is-C x`)
  | "datatype" => return #[("cases", ← `(tactic| (intros; blaster_cases_vars <;> simp_all <;> done)))] ++ simp ++ grind
  | "quant-intro" => return quant ++ simp ++ grind
  | "def-axiom" | "not-or-elim" | "and-elim" | "iff~" | "nnf-pos" | "nnf-neg" => return simp ++ grind
  | _ => return simp ++ arith ++ grind

/-- Per rule and tactic: number of successes and time spent (ms, including failed attempts), used to
    order the tactic portfolios by efficiency (adaptive, per process). -/
initialize tacticStats : IO.Ref (Std.HashMap (String × String) (Nat × Nat)) ← IO.mkRef {}

/-- Coarse shape of a goal, refining the statistics of the adaptive ordering: `arith` for (in)equalities
    and propositional combinations of linear arithmetic atoms, `nat` for universally quantified formulas
    guarded by `0 ≤ x` (definitions of `Nat` functions), `data` for formulas with constructors or case
    analyses, `other` otherwise. -/
partial def goalShape (e : Expr) : MetaM String := do
  let some kind ← go e 0 | return "other"
  return kind
where
  go (e : Expr) (depth : Nat) : MetaM (Option String) := do
    if depth > 64 then return none
    if e.isForall then
      if let .forallE _ t b _ := e then
        if (← whnfR t).isConstOf ``Int then
          if let .forallE _ g _ _ := b then
            if g.isAppOfArity ``LE.le 4 then return some "nat"
      return none
    let env ← getEnv
    let isData (s : Expr) : Bool := match s with
      | .const n _ =>
          (n.isStr && n.getString!.endsWith "casesOn") ||
          (isCtorName env n && n != ``Int.ofNat && n != ``True && n != ``False && n != ``Int.negSucc)
      | _ => false
    if (e.find? isData).isSome then return some "data"
    let arith := e.find? (fun s => s.isAppOfArity ``LE.le 4 || s.isAppOfArity ``LT.lt 4 || s.isAppOfArity ``HAdd.hAdd 6 || s.isAppOfArity ``HMul.hMul 6) |>.isSome
    return some (if arith then "arith" else "other")
  isCtorName (env : Environment) (n : Name) : Bool := (env.find? n).any (·.isCtor)

def portfolio (tacs : Array (String × TSyntax `tactic)) (goal : Expr) (rule := "") : TermElabM (Option (Expr × String)) := do
  let rule := s!"{rule}/{← goalShape goal}"
  let stats ← tacticStats.get
  -- most efficient tactics first, i.e., highest number of successes per time unit (with a prior
  -- favoring the given order)
  let score (n : String) (i : Nat) : Float :=
    let (succ, ms) := stats.getD (rule, n) (0, 0)
    (succ.toFloat + 1.0 / (i.toFloat + 1.0)) / (ms.toFloat + 50.0)
  let tacs := (tacs.zipIdx.qsort fun ((n₁, _), i₁) ((n₂, _), i₂) => score n₁ i₁ > score n₂ i₂).map (·.1)
  for (name, tac) in tacs do
    let start ← IO.monoMsNow
    let r ← proveWithTactic goal tac
    let ms := (← IO.monoMsNow) - start
    let succ := if r.isSome then 1 else 0
    tacticStats.modify fun m => let (a, b) := m.getD (rule, name) (0, 0); m.insert (rule, name) (a + succ, b + ms)
    if let some p := r then return some (p, name)
  return none

/-! ## Main entry point -/

/-- Split the leading binders of `e` which are neither propositions nor sorts (i.e., data variables). -/
partial def dataBinders (e : Expr) (k : Array Expr → Expr → TermElabM α) (acc : Array Expr := #[]) : TermElabM α := do
  match e with
  | .forallE n t b bi =>
      -- NOTE: sort variables are introduced (see the interpretation of Blaster's polymorphic encoding)
      if (← isProp t) then k acc e
      else withLocalDecl n bi t fun x => dataBinders (b.instantiate1 x) k (acc.push x)
  | _ => k acc e

structure SmtProofResult where
  proof : Expr
  backend : String
  steps : Nat
  stats : ReplayStats

/-- Given `e := ∀ b₁ ... bₙ, C` (leading binders), return `∀ xs, hs → C` where `xs` are the data binders and
    `hs` the propositions among the `bᵢ` (only when no data binder depends on a proposition), together with
    a function turning a proof of the latter into a proof of `e`. Blaster declares the data variables of
    the leading binders as SMT constants, including the ones following hypotheses. -/
def prenex (e : Expr) : MetaM (Option (Expr × (Expr → MetaM Expr))) := do
  forallTelescope e fun bs c => do
    if bs.isEmpty then return none
    let mut data := #[]
    let mut hyps := #[]
    for b in bs do
      let t ← inferType b
      if (← isProp t) then hyps := hyps.push b
      else
        if hyps.any (fun h => t.containsFVar h.fvarId!) then return none
        data := data.push b
    if hyps.isEmpty || data.isEmpty then return none
    -- already in prenex form
    if bs == data ++ hyps then return none
    let e' ← mkForallFVars (data ++ hyps) c
    let back (p : Expr) : MetaM Expr :=
      forallTelescope e fun bs' _ => do
        -- bs' follow the order of `bs`
        let m := (bs.zip bs').toList
        let get (x : Expr) := (m.find? (·.1 == x)).map (·.2) |>.getD x
        mkLambdaFVars bs' (mkAppN p ((data ++ hyps).map get))
    return some (e', back)

/-- Closed quantifications over sorts `∀ (α : Sort u), b` (`u ≠ 0`) in `e` (traversal with sharing). -/
partial def sortQuantifiers (e : Expr) : Array Expr := Id.run do
  let mut acc := #[]
  let mut stack := #[e]
  let mut seen : Std.HashSet Expr := {}
  while !stack.isEmpty do
    let s := stack.back!
    stack := stack.pop
    if seen.contains s then continue
    seen := seen.insert s
    if let .forallE _ (.sort u) _ _ := s then
      if !u.isZero && !s.hasLooseBVars then acc := acc.push s
    match s with
    | .app f a => stack := stack.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => stack := stack.push t |>.push b
    | .letE _ t v b _ => stack := stack.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => stack := stack.push b
    | _ => pure ()
  return acc

/-- Sort variables of the goal `∀ xs, body` (Blaster's polymorphic encoding: sort variables are values of the sort
    `@Type`, and the values of the types they denote are values of the sort `@Instance`): the leading binders and the
    variables of the local context (e.g., auto-bound implicit arguments) whose type is a sort other than `Prop`, and
    whether `body` quantifies over sorts. -/
def sortVariables (xs : Array Expr) (body : Expr) : MetaM (Array Expr × Bool) := do
  let isSortVar (t : Expr) : MetaM Bool := do
    let t ← whnfR t
    return t.isSort && !t.isProp
  let mut sortVars ← xs.filterM fun x => do isSortVar (← inferType x)
  for d in ← getLCtx do
    if d.isImplementationDetail || sortVars.contains d.toExpr then continue
    if ← isSortVar d.type then
      if body.containsFVar d.fvarId || (← xs.anyM fun x => do return (← inferType x).containsFVar d.fvarId) then
        sortVars := sortVars.push d.toExpr
  -- propositions quantifying over sorts (below the leading binders)
  let quantifiedSorts ← (sortQuantifiers body).anyM fun s => isProp s
  return (sortVars, quantifiedSorts)

/-- Interpretations of the polymorphic encoding tried in order (`true`: `Poly`, `false`: `@Instance` as the sort
    variable). With a single sort variable `α`, `@Instance` is first interpreted as `α` and `@Type` as `Unit`
    (membership predicates as `True`), which fails when `α` may be empty (e.g., skolem constants of sort
    `@Instance`). -/
def polyModes (sortVars : Array Expr) (quantifiedSorts : Bool) : Array Bool :=
  if quantifiedSorts then #[true]
  else if sortVars.isEmpty then #[false]
  else if sortVars.size == 1 then #[false, true]
  else #[true, false]

/-- Try to prove `e` (a closed proposition proved valid by the SMT solver) by replaying a proof of the
    SMT backend. The polymorphic encoding is interpreted by `Poly` when `poly?` is `some true`, with `@Instance` as
    the sort variable when `some false`, and with the interpretations of `modes` tried in order otherwise. -/
partial def proveBySmtProof (e : Expr) (sOpts : BlasterOptions) (poly? : Option Bool := none) :
    TermElabM (Except String SmtProofResult) := do
  if let some (e', back) ← prenex e then
    match ← proveBySmtProof e' sOpts poly? with
    | .ok r => return .ok { r with proof := ← back r.proof }
    | .error msg => return .error msg
  if poly?.isNone then
    let modes ← dataBinders e fun xs body => do
      let (sortVars, quantifiedSorts) ← sortVariables xs body
      return polyModes sortVars quantifiedSorts
    if modes.size > 1 then
      let s ← saveState
      let ngen ← getNGen
      let mut msgs := #[]
      for poly in modes do
        s.restore
        -- NOTE: the name generator (not restored by `restore`) is reset too, such that the translations (whose
        -- SMT symbols have fresh names) coincide and the proofs of the backends are reused (see `runBackendCached`)
        setNGen ngen
        match ← proveBySmtProof e sOpts (some poly) with
        | .ok r => return .ok r
        | .error msg => msgs := msgs.push msg
      -- the error of the general interpretation first
      let errs := if modes[0]! then msgs else msgs.reverse
      return .error (String.intercalate "; with the other interpretation of the polymorphic encoding: " errs.toList)
  -- NOTE: each tactic attempt has its own heartbeat budget (see `proveWithTactic`)
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
  dataBinders e fun xs body => do
  try
    -- polymorphic encoding (see `sortVariables`), interpreted by `Poly` when `poly` is set
    let (sortVars, quantifiedSorts) ← sortVariables xs body
    let poly := poly?.getD (polyModes sortVars quantifiedSorts)[0]!
    -- 1. translation
    -- NOTE: commands are only recorded when `dumpSmtLib` is set (nothing is printed)
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := { sOpts with onlySmtLib := true, dumpSmtLib := true }}
    let (goalTerm, tenv) ← (do
        -- NOTE: the optimizer populates the caches used by the translation (e.g., the definitions of
        -- recursive functions); `body` being already optimized, `body'` is expected to be `body` (up to
        -- definitional equality, which the bridge requires).
        let (body', _) ← Optimize.mainPf body (track := false)
        -- NOTE: when the optimizer is not idempotent on `body`, `body` itself is translated, such that the
        -- asserted formula is the translation of the negated goal (see the bridge)
        let reopt := body' == body
        setBlasterProcess
        -- sort variables introduced as free variables: declared as Blaster does for top-level quantifiers
        for α in sortVars do
          updateQuantifiedFVarsCache α.fvarId! true
          -- NOTE: the declarations of sorts are cached on (hash-consed) sort objects
          let decl ← generateSortInstDecl (← hashcons (← inferType α))
          declareConst (← typeParamNameToSmtSymbol α.fvarId!) decl.instSort
        -- the data variables are declared first: their datatypes are then declared before the body refers to
        -- their fields (e.g., the function fields of structures, applied in the body); with sort variables, they
        -- are declared with their membership predicates also when they don't occur in the goal (e.g., `a : α`
        -- witnessing that `α` is inhabited)
        -- NOTE: variables that can't be translated by themselves (e.g., instances of classes) are left to the
        -- translation of the body
        for x in xs do
          let t ← inferType x
          if sortVars.contains x || (← isProp t) || (← isClass? t).isSome then continue
          let saved ← get
          try discard <| translateExpr x catch _ => set saved
        -- NOTE: the unoptimized goal may not be translatable (e.g., terms that only the optimizer normalizes):
        -- its optimized form is then translated, when definitionally equal to it
        let saved ← get
        let (st, goalTerm) ← if reopt then pure (← translateExpr body', body') else
          try pure (← translateExpr body, body) catch ex => do
            set saved
            let defeq ← try withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000 }) <|
                withCurrHeartbeats <| withDefault <| isDefEq body body' catch _ => pure false
            if !defeq then throw ex
            pure (← translateExpr body', body')
        assertTerm (notSmt st)
        return goalTerm : TranslateEnvT Expr).run env
    let cmds ← tenv.smtEnv.smtCommands.mapM fun c => ofExcept (parseSExpr (toString c))
    let cmds := cmds.map guardNatQuantifiers
    -- 2. backend
    -- backends tried in order (environment variable `BLASTER_SMTPROOF_BACKENDS`, e.g., `z3,cvc5`)
    -- (`z3+`: Z3 with the simplifiers of the query, tried after `z3`)
    let names := ((← IO.getEnv "BLASTER_SMTPROOF_BACKENDS").getD "z3,z3+").splitOn ","
    let timeout := ((← IO.getEnv "BLASTER_SMTPROOF_TIMEOUT").bind String.toNat?).getD (sOpts.timeout.getD 20)
    let mut res : Option (Backend × Proof) := none
    let mut errors := #[]
    for n in names do
      let backend ← match n.trim with
        | "z3" => pure (z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout)
        | "z3+" => pure (z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout (simplifiers := true))
        | "cvc5" => pure (cvc5Backend ((← IO.getEnv "BLASTER_SMTPROOF_CVC5").getD "cvc5") timeout)
        | b => throwError "unknown proof backend {b}"
      match ← runBackendCached backend cmds with
      | .error msg => errors := errors.push msg
      | .ok out =>
          match backend.parseProof out with
          | .ok p => res := some (backend, p); break
          | .error msg => errors := errors.push s!"{backend.name}: {msg}"
    let some (backend, sproof) := res | throwError "no proof: {errors}"
    -- 3. interpretation
    -- SMT constants of the free variables of the goal (the introduced variables, as well as the
    -- variables of the local context, e.g., section variables)
    let mut consts : Std.HashMap String Expr := {}
    let lctx ← getLCtx
    for (v, idx) in tenv.smtEnv.fvarsCache.toList do
      if lctx.contains v then consts := consts.insert s!"${idx}" (mkFVar v)
    let tbl ← if poly then polyBuildSymTable cmds tenv consts sortVars else buildSymTable cmds tenv consts sortVars[0]?
    let tbl ← addSkolems sproof tbl
    -- 4. replay
    let bridge ← bridgeTactics
    -- axioms of the polymorphic encoding (see `Poly`)
    let bridge ← if poly then pure (#[("poly", ← `(tactic| blaster_poly))] ++ bridge) else pure bridge
    -- matcher instances optimized by Blaster (whose patterns are the translated ones)
    let mut insts : Std.HashMap Name Expr := {}
    for (k, v) in tenv.optEnv.memCache.isMatcherCache.toList do insts := insts.insert k.name v.instApp
    -- SMT macros of Lean functions (e.g., `@Nat.sub`), expanded by the backends in asserted formulas
    let mut macros : Std.HashMap Name (Array (String × SExpr) × STerm) := {}
    for (k, v) in tenv.smtEnv.funInstCache.toList do
      let nm := match v with
        | .SimpleIdent s => toString s
        | .QualifiedIdent s _ => toString s
      if let .const n _ := k.expr then
        if let some (.macro params body) := tbl.syms.get? nm then macros := macros.insert n (params, body)
    let macroOf (n : Name) : Option (Array Expr → MetaM Expr) := (macros.get? n).map fun (params, body) vals => do
      let locals := (params.zip vals).foldl (fun m ((x, _), v) => m.insert x v) {}
      (interp body).run { table := tbl, locals }
    let macroTacs ← macroTactics
    let bcfg : Bridge.Cfg := {
      matchInst := insts.get?, macroOf
      proveLemma := fun stmt => do return (← portfolio macroTacs stmt "macro").map (·.1) }
    let tacCache : IO.Ref (Std.HashMap String (Array (String × TSyntax `tactic))) ← IO.mkRef {}
    let pf ← withLocalDeclD `hneg (mkNot body) fun hneg => do
      let cfg : ReplayConfig := {
        proveDirect := fun c => do
          if ← withReducible (isDefEq c (mkNot body)) then return some (← mkExpectedTypeHint hneg c)
          -- e.g., projections vs. case analyses, casts of literals (with a budget)
          let defeq (a b : Expr) : TermElabM Bool := do
            try withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 50000 * 1000 }) <|
                  withCurrHeartbeats <| withDefault <| isDefEq a b
            catch _ => return false
          if c.isAppOfArity ``Not 1 then
            if ← defeq c (mkNot body) then return some (← mkExpectedTypeHint hneg c)
          -- the interpretation of the translation of the negated goal: simultaneous traversal (see `Bridge`)
          -- NOTE: the translated goal is definitionally equal to the goal (see the translation above)
          let (r, fails) ← Bridge.prove bcfg (mkNot goalTerm) c
          if let some p := r then
            return some (← mkEqMP p (← mkExpectedTypeHint hneg (mkNot goalTerm)))
          if let some f ← IO.getEnv "BLASTER_SMTPROOF_BRIDGE_DUMP" then
            let h ← IO.FS.Handle.mk f .append
            -- NOTE: only for the translation of the negated goal
            for (a, b) in if c.isAppOfArity ``Not 1 then fails.extract 0 3 else #[] do
              h.putStrLn s!"=== bridge mismatch:\n{← ppExpr a}\n--- interpretation:\n{← ppExpr b}\n"
          let r ← portfolio bridge c "bridge"
          if r.isNone then debugLog m!"bridge failed: {c}"
          if r.isNone then
            if let some f ← IO.getEnv "BLASTER_SMTPROOF_BRIDGE_DUMP" then
              let h ← IO.FS.Handle.mk f .append
              h.putStrLn s!"=== bridge failed:\n{← ppExpr c}\n--- negated goal:\n{← ppExpr (mkNot goalTerm)}\n"
          return r.map (·.1)
        proveStep := fun rule stmt => do
          -- NOTE: the tactic syntax of each rule is built once per replay
          let tacs ← match (← tacCache.get).get? rule with
            | some t => pure t
            | none => do let t ← stepTactics rule; tacCache.modify (·.insert rule t); pure t
          portfolio tacs stmt rule }
      let cache ← IO.mkRef {}
      let deadline := (← IO.monoMsNow) + 1000 * ((← IO.getEnv "BLASTER_SMTPROOF_DEADLINE").bind String.toNat? |>.getD 300)
      let global := (scopedSteps sproof).map (!·)
      let ctx : ReplayCtx := { proof := sproof, interp := { table := tbl, cache := some cache }, cfg, deadline, global,
                               baseLCtx := ← getLCtx, baseInsts := ← getLocalInstances }
      let (p?, st) ← ((do try prepass; return Except.ok (← replay sproof.root)
                            catch ex => return Except.error ex) |>.run ctx).run {}
      let p ← match p? with
        | .ok p => pure p
        | .error ex =>
            -- report the first steps that could not be replayed (i.e., the deepest failures)
            let fs := st.stats.failures.extract 0 3
            let ms := (st.stats.msByRule.toArray.qsort (·.2 > ·.2)).extract 0 6
            let methods := st.stats.byRule.toList.map fun (r, m) => (r, m.toList)
            throwError "{ex.toMessageData}; first failures: {fs}; time per rule: {ms}; methods: {methods}"
      let pt ← inferType p
      if !pt.isConstOf ``False then throwError "smt proof: root does not prove False: {pt}"
      -- NOTE: the proofs of the steps are instantiated once (see `replay`)
      return (← mkLambdaFVars #[hneg] (← instantiateMVars p), st.stats)
    let (pf, stats) := pf
    let proofBody := mkApp2 (mkConst ``Classical.byContradiction) body pf
    let proof ← instantiateMVars (← mkLambdaFVars xs proofBody)
    return .ok { proof, backend := backend.name, steps := sproof.steps.size, stats }
  catch ex =>
    return .error (← ex.toMessageData.toString)

end Blaster.Reconstruct.SmtProof
