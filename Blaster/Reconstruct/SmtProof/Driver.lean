import Lean
import Blaster.Smt.Translate
import Blaster.Reconstruct.Discharge
import Blaster.Reconstruct.SmtProof.Z3
import Blaster.Reconstruct.SmtProof.Alethe
import Blaster.Reconstruct.SmtProof.Replay
import Blaster.Reconstruct.SmtProof.Bridge
import Blaster.Reconstruct.SmtProof.NlArith
import Blaster.Reconstruct.SmtProof.RecFun

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

/-- The input of `backend` for the query `cmds`. -/
def backendInput (backend : Backend) (cmds : Array SExpr) : String :=
  String.intercalate "\n" (backend.preamble.toList ++
    (cmds.filter (!backend.dropCommand ·)).toList.map toString ++ ["(check-sat)", "(get-proof)", "(exit)"])

/-- The proof output of `backend` given its standard output (the output following `unsat`), or the reason of the
    failure. -/
def backendResult (backend : Backend) (stdout stderr : String) : Except String String :=
  -- the first line among `sat`, `unsat` and `unknown` (e.g., after warnings on unsupported options)
  let lines := stdout.splitOn "\n"
  -- errors on the query (e.g., unsupported declarations): its verdict and proof are not used
  let errors := lines.filter (·.trimLeft.startsWith "(error")
  if !errors.isEmpty then
    .error s!"{backend.name}: {String.intercalate " " (errors.take 3) |>.take 600}"
  else match lines.findIdx? (fun l => ["sat", "unsat", "unknown"].contains l.trim) with
    | some i =>
        if lines[i]!.trim == "unsat" then .ok (String.intercalate "\n" (lines.drop (i + 1)))
        else .error s!"{backend.name}: {lines[i]!.trim}"
    | none => .error s!"{backend.name}: {stdout.take 300} {stderr.take 300}"

/-- Run `backend` on the query `cmds`, returning the raw proof output. The query is written to a
    temporary file (no interaction with the solver's pipes during the run). -/
def runBackend (backend : Backend) (cmds : Array SExpr) : IO (Except String String) := do
  let query := backendInput backend cmds
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_DUMP" then IO.FS.writeFile f query
  let (h, path) ← IO.FS.createTempFile
  try
    h.putStr query
    h.flush
    let out ← IO.Process.output { cmd := backend.cmd, args := backend.args.push path.toString }
    return backendResult backend out.stdout out.stderr
  finally
    IO.FS.removeFile path

/-- Whether `c` sets Z3's random seed. -/
def isSeedCommand (c : SExpr) : Bool :=
  match c with
  | .list #[.atom "set-option", .atom o, _] => o == ":smt.random-seed" || o == ":random-seed" || o == ":sat.random_seed"
  | _ => false

/-- Random seed of Z3 set by the query `cmds` (`0` by default). -/
def querySeed (cmds : Array SExpr) : Nat := Id.run do
  for c in cmds do
    if let .list #[.atom "set-option", .atom ":smt.random-seed", .atom n] := c then
      if let some k := n.toNat? then return k
  return 0

/-- The query `cmds` with Z3's random seed set to `seed`. -/
def withSeed (cmds : Array SExpr) (seed : Nat) : Array SExpr :=
  #[SExpr.list #[.atom "set-option", .atom ":smt.random-seed", .atom (toString seed)]] ++ cmds.filter (!isSeedCommand ·)

/-- Standard streams of the solver runs of a portfolio (see `runPortfolio`). -/
abbrev PortfolioStdio : IO.Process.StdioConfig := { stdin := .null, stdout := .piped, stderr := .null }

/-- Run `backend` (Z3, with its timeout given by an argument `-T:n`) on the queries `variants` concurrently (e.g., the
    query with different random seeds, whose time to find a proof may vary by an order of magnitude on the CEK
    evaluation of validators): the variant `i` is started after `i * delayMs` ms when no proof was found yet, with
    the timeout reduced accordingly (the portfolio takes at most the timeout of `backend`). Returns the first proof
    output (the other runs are then killed), or the result of the first variant when no variant finds a proof. -/
def runPortfolio (backend : Backend) (variants : Array (Array SExpr)) (delayMs : Nat) : IO (Except String String) := do
  if variants.size ≤ 1 then return ← runBackend backend (variants.getD 0 #[])
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_DUMP" then IO.FS.writeFile f (backendInput backend variants[0]!)
  let timeoutMs := (backend.args.findSome? fun a => if a.startsWith "-T:" then (a.drop 3).toNat? else none).getD 0 * 1000
  let start ← IO.monoMsNow
  let mut runs : Array (IO.Process.Child PortfolioStdio × Task (Except IO.Error String) × System.FilePath) := #[]
  let mut results : Array (Option (Except String String)) := #[]
  let mut proof := none
  try
    repeat
      let now ← IO.monoMsNow
      -- the next variant, unless its reduced timeout would be less than a second
      let i := runs.size
      if i < variants.size && now - start ≥ i * delayMs && (i == 0 || timeoutMs ≥ i * delayMs + 1000) then
        let (h, path) ← IO.FS.createTempFile
        h.putStr (backendInput backend variants[i]!)
        h.flush
        let args := backend.args.map fun a =>
          if a.startsWith "-T:" && i > 0 then s!"-T:{(timeoutMs - i * delayMs) / 1000}" else a
        let child ← IO.Process.spawn { toStdioConfig := PortfolioStdio, cmd := backend.cmd, args := args.push path.toString }
        let task ← IO.asTask (prio := .dedicated) do
          let out ← child.stdout.readToEnd
          discard <| child.wait
          return out
        runs := runs.push (child, task, path)
        results := results.push none
      for j in [:runs.size] do
        if results[j]!.isSome then continue
        let some (_, task, _) := runs[j]? | continue
        if !(← IO.hasFinished task) then continue
        let r : Except String String := match task.get with
          | Except.ok out => backendResult backend out ""
          | Except.error e => .error s!"{backend.name}: {e}"
        results := results.set! j (some r)
        if r matches .ok _ then proof := some r
      if proof.isSome then break
      if runs.size == variants.size && results.all (·.isSome) then break
      -- no other variant to start (its timeout would be too short): the remaining runs only
      if runs.size < variants.size && results.all (·.isSome) && timeoutMs < runs.size * delayMs + 1000 then break
      IO.sleep 20
  finally
    for (child, task, path) in runs do
      if !(← IO.hasFinished task) then try child.kill catch _ => pure ()
      try IO.FS.removeFile path catch _ => pure ()
  if let some r := proof then return r
  return (results[0]?.bind id).getD (.error s!"{backend.name}: no result")

/-- Results of the backends on the last query, reused by the replays of a goal with the different interpretations
    of the polymorphic encoding (see `proveBySmtProof`). -/
initialize backendRuns : IO.Ref (String × Std.HashMap String (Except String String)) ← IO.mkRef ("", {})

/-- `runBackend`, reusing the result of a previous run of `backend` on the same query. With `seeds > 1`, a portfolio
    of `seeds` runs of Z3 with consecutive random seeds from the seed of the query (see `runPortfolio`). -/
def runBackendCached (backend : Backend) (cmds : Array SExpr) (seeds := 1) (delayMs := 0) :
    IO (Except String String) := do
  let query := String.intercalate "\n" (cmds.toList.map toString)
  let (q, runs) ← backendRuns.get
  let runs := if q == query then runs else {}
  if let some r := runs.get? backend.name then return r
  let r ← if seeds ≤ 1 then runBackend backend cmds else
    let seed := querySeed cmds
    runPortfolio backend ((List.range seeds).toArray.map fun k => if k == 0 then cmds else withSeed cmds (seed + k)) delayMs
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

/-- The definition of a lambda term of the translation (see `Blaster.Smt.translateLambda`):
    `(forall (xs) (! (=> G₁ (=> ... (= (@apply @lambda_n xs) b))) :qid @lambda_n_def_cstr))`, and
    `(forall (ys xs) (! (=> G₁ (=> ... (= (@apply (@apply @global_lambda_n ys) xs) b))) ...))`: its name, the
    parameters `ys` and `xs`, the guards on variables (membership predicates, the guards `0 ≤ x` are removed, see
    `guardNatQuantifiers`) and its body. -/
def guardedLambdaDef? (e : SExpr) :
    Option (String × Array (String × SExpr) × Array (String × SExpr) × Std.HashMap String SExpr × STerm) := Id.run do
  let some #[SExpr.atom "forall", SExpr.list vs, SExpr.list ann] := e.list? | return none
  if ann[0]? != some (SExpr.atom "!") then return none
  let some d₀ := ann[1]? | return none
  let mut d := d₀
  let names := vs.filterMap fun v => match v with
    | .list #[.atom x, _] => some x
    | _ => none
  let mut guards : Std.HashMap String SExpr := {}
  for _ in [0:3 * vs.size] do
    match d with
    | .list #[.atom "=>", .list #[.atom "<=", .atom "0", .atom _], b] => d := b
    | .list #[.atom "=>", g, b] =>
        let some h := g.head? | return none
        if !(unquote h).startsWith "@is" then return none
        -- the guarded parameter (e.g., `(@isInstance x α)`, `(@isList α x)`)
        let some args := g.list? | return none
        let isParam (a : SExpr) : Option String := match a with
          | .atom x => if names.contains x then some x else none
          | _ => none
        let some x := args.findSome? isParam | return none
        guards := guards.insert x g
        d := b
    | _ => break
  let some #[SExpr.atom "=", SExpr.list lhs, body] := d.list? | return none
  let vars := vs.filterMap fun v => match v with
    | .list #[.atom x, s] => some (x, s)
    | _ => none
  let some (SExpr.atom apply) := lhs[0]? | return none
  if !apply.startsWith "@apply" then return none
  let .ok b := STerm.ofSExpr {} body | return none
  match lhs[1]? with
  | some (SExpr.atom l) =>
      if !l.startsWith "@lambda" then return none
      return some (l, #[], vars, guards, b)
  | some (SExpr.list inner) =>
      let some (SExpr.atom g) := inner[1]? | return none
      if !g.startsWith "@global_lambda" then return none
      let k := inner.size - 2
      if k > vars.size then return none
      return some (g, vars.extract 0 k, vars.extract k vars.size, guards, b)
  | _ => return none

/-- Interpretation of a lambda term of the translation (see `guardedLambdaDef?`) of sort `s` in `Poly`: each parameter
    `x` guarded by a membership predicate `Img w x` is bound by `fun x => if Img w x then b else dflt x`, where `dflt`
    is the default of the world of the function (see `Poly.mkWorld`), such that the lambda term is the image of a
    Lean function (see `Poly.lam_world_ite`) whatever its body outside of the domain (e.g., constant functions). The
    definition, guarded by the same predicates, holds. Returns the term and the table with the symbols of the default
    values. -/
def guardedLambda (tbl : SymTable) (n : String) (s : SExpr) (ys xs : Array (String × SExpr))
    (guards : Std.HashMap String SExpr) (body : STerm) : MetaM (STerm × SymTable) := do
  let mut tbl := tbl
  let mut ty ← (sortToType s).run { table := tbl }
  for _ in ys do
    let .forallE _ _ b _ ← whnfR ty | throwError "guardedLambda: function type expected"
    ty := b
  let mut doms := #[]
  for _ in xs do
    let .forallE _ d b _ ← whnfR ty | throwError "guardedLambda: function type expected"
    doms := doms.push (d, b)
    ty := b
  let mut t := body
  for i' in [0:xs.size] do
    let i := xs.size - 1 - i'
    let (x, _) := xs[i]!
    let (d, c) := doms[i]!
    let guarded ← match guards.get? x with
      | some g =>
          let some h := g.head? | pure none
          let some (.lam _) := tbl.syms.get? h | pure none
          let .ok g := STerm.ofSExpr {} g | pure none
          pure (some g)
      | none => pure none
    if let some g := guarded then
      -- the default of the world (see `Poly.mkWorld`): the identity for the functions of a sort into itself
      let dflt ← if c == d || (← withReducible (isDefEq d c)) then pure (STerm.sym x) else do
        let k := s!"@@poly_default_{n}_{i}"
        tbl := { tbl with syms := tbl.syms.insert k (.expr (← Poly.mkDefault c)) }
        pure (STerm.sym k)
      t := .app "ite" #[g, t, dflt]
    t := .quant .lambda #[xs[i]!] t
  return (if ys.isEmpty then t else .quant .lambda ys t, tbl)

/-- Interpretation of Blaster's polymorphic encoding (see `Poly`), given the sort variables of the goal with their
    SMT symbols: the membership predicates of the types with sort variables are the images of their worlds (e.g.,
    `@isFun α β f` is `Img (liftFun (inj α) (inj β) _) f`), the constants of the goal the images of their values
    (e.g., `x : α` is `inj α x`), and the lambda terms are guarded by the membership predicates of their parameters
    (see `guardedLambda`). The sorts `@Type` and `@Instance`, the predicates `@isInstance` and the polymorphic
    functions (at the universe, see `Poly.instantiateUniv`) are interpreted by `buildSymTable`. -/
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
        -- NOTE: the sort parameters are explicit arguments of the predicates (e.g., `{β}` in the cached type)
        withNewBinderInfos (αs.map (·.fvarId!, .default)) do
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
  -- lambda terms, guarded by the membership predicates of their parameters (the first definition, as in
  -- `buildSymTable`)
  let mut sorts : Std.HashMap String SExpr := {}
  for c in cmds do
    if let some #[SExpr.atom "declare-const", SExpr.atom n, s] := c.list? then sorts := sorts.insert n s
  let mut guarded : Std.HashSet String := {}
  for c in cmds do
    let some #[SExpr.atom "assert", a] := c.list? | continue
    let some (n, ys, xs, guards, body) := guardedLambdaDef? a | continue
    let some s := sorts.get? n | continue
    if guarded.contains n then continue
    guarded := guarded.insert n
    try
      let (t, tbl') ← guardedLambda tbl n s ys xs guards body
      tbl := { tbl' with syms := tbl'.syms.insert n (.macro #[] t) }
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
  let arities := if polySortVars?.isSome then funArities cmds else {}
  for (k, v) in env.smtEnv.funInstCache.toList do
    let nm := match v with
      | .SimpleIdent s => toString s
      | .QualifiedIdent s _ => toString s
    let e ← if polySortVars?.isSome then polyInstantiate arities nm k.expr else instantiateSortParams instanceType? k.expr
    funs := funs.insert nm e
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
  /-- Arities of the functions declared by `cmds`. -/
  funArities (cmds : Array SExpr) : Std.HashMap String Nat := Id.run do
    let mut m := {}
    for c in cmds do
      if let some #[SExpr.atom "declare-fun", SExpr.atom n, SExpr.list ss, _] := c.list? then m := m.insert n ss.size
    return m
  /-- Lean functions of the translation abstracted over their generic parameters, interpreted by `Poly`: at the
      universe (see `Poly.instantiateUniv`). -/
  polyInstantiate (arities : Std.HashMap String Nat) (nm : String) (e : Expr) : MetaM Expr := do
    let some arity := arities.get? nm | return e
    try Poly.instantiateUniv e (← Poly.genericParams e arity) catch _ => return e
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
  -- names introduced by `intro-def` (Z3's Tseitin names): `(= t k)` defines `k` as `t`; similarly for the
  -- names introduced by theory lemmas (e.g., `(= pb!2 (or ...))` of Z3's pseudo-Boolean preprocessing)
  for step in proof.steps do
    if !(step.rule == "intro-def" || (step.rule == "th-lemma" && step.premises.isEmpty)) then continue
    match step.concl.stripAnnot with
    | .app "=" #[t, .sym k] | .app "=" #[.sym k, t] =>
        if !tbl.syms.contains k && (findSkolem k t (· == k)).isNone then
          tbl := { tbl with syms := tbl.syms.insert k (.macro #[] t) }
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

theorem ediv_self_of_zero_ne {a : Int} (h : ¬0 = a) : a / a = 1 := Int.ediv_self (Ne.symm h)

syntax (name := blasterDivModSimp) "blaster_divmod_simp" : tactic

/-- The `Int` divisions and modulos by non-literal divisors of the goal normalized by case analyses on the
    conditionals and the signs (e.g., Z3's rewrites of `x % (-y)` into `x % y`, of `x / x` into
    `if x = 0 then 0 / 0 else 1`, of `x % (if c then a else b)` into `if c then x % a else x % b`). -/
@[tactic blasterDivModSimp] def evalBlasterDivModSimp : Tactic := fun _ => withMainContext do
  if (evalBlasterDivMod.collect (← instantiateMVars (← getMainTarget))).isEmpty then
    throwError "blaster_divmod_simp: no division"
  -- NOTE: without case analyses first (e.g., `x % (-1 * y) = x % y` for large conditional terms `x` and `y`)
  evalTactic (← `(tactic| first
    | (intros; simp only [Int.neg_one_mul, Int.emod_neg, Int.ediv_neg, Int.neg_neg]; done)
    | (intros; (repeat' split) <;> (try subst_vars) <;>
        simp_all [Int.emod_neg, Int.ediv_neg, Int.neg_one_mul, Int.ediv_self, ediv_self_of_zero_ne, Int.emod_self] <;> done)))

theorem str_lt_total (a b : String) : a < b ∨ a = b ∨ b < a := by
  by_cases h : a < b
  · exact Or.inl h
  · by_cases h' : b < a
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl (String.le_antisymm h' h))

theorem str_not_lt_empty (a : String) : ¬a < "" := fun h => List.not_lt_nil _ (String.lt_iff.mp h)

syntax (name := blasterStringOrder) "blaster_string_order" : tactic

/-- The order of strings (e.g., Z3's lemmas of the lexicographic order: irreflexivity, transitivity, totality). -/
@[tactic blasterStringOrder] def evalBlasterStringOrder : Tactic := fun _ => withMainContext do
  let isStrLt (e : Expr) : Bool := e.isAppOfArity ``LT.lt 4 && (e.getArg! 0).isConstOf ``String
  if ((← instantiateMVars (← getMainTarget)).find? isStrLt).isNone then throwError "blaster_string_order: no string order"
  evalTactic (← `(tactic| (intros; grind [String.lt_irrefl, String.lt_trans, String.lt_asymm, str_lt_total,
    str_not_lt_empty])))

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
    ("grind", ← `(tactic| (intros; grind))),
    -- the divisions and modulos of `Int` (see `Bridge.tdiv_macro`)
    ("int div", ← `(tactic| first | exact Bridge.tdiv_macro | exact Bridge.tmod_macro | exact Bridge.fdiv_macro |
                                      exact Bridge.fmod_macro | exact Bridge.ediv_macro | exact Bridge.emod_macro))]

theorem toNat_ediv_two (y : Int) : (y / 2).toNat = y.toNat / 2 := by omega

def stepTactics (rule : String) : TermElabM (Array (String × TSyntax `tactic)) := do
  let arith := #[
    ("omega", ← `(tactic| (intros; omega))),
    ("divmod+omega", ← `(tactic| (intros; blaster_divmod; omega))),
    ("divmod simp", ← `(tactic| blaster_divmod_simp)),
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
  let grind := #[("grind", ← `(tactic| (intros; grind))), ("string order", ← `(tactic| blaster_string_order))]
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
    -- 3.-4. interpretation and replay of the proof `sproof` of `backend`
    let replayWith (backend : Backend) (sproof : Proof) (recPairs : Array RecFun.Pair) : TermElabM SmtProofResult := do
      -- 3. interpretation
      -- SMT constants of the free variables of the goal (the introduced variables, as well as the
      -- variables of the local context, e.g., section variables)
      let mut consts : Std.HashMap String Expr := {}
      let lctx ← getLCtx
      for (v, idx) in tenv.smtEnv.fvarsCache.toList do
        if lctx.contains v then consts := consts.insert s!"${idx}" (mkFVar v)
      let tbl ← if poly then polyBuildSymTable cmds tenv consts sortVars else buildSymTable cmds tenv consts sortVars[0]?
      let tbl ← addSkolems sproof tbl
      -- auxiliary functions and case predicates of recursive functions (Z3)
      let (tbl, recAux) ← RecFun.addProofDefs sproof tbl
      -- 4. replay
      let bridge ← bridgeTactics
      -- axioms of the polymorphic encoding (see `Poly`)
      let polyTac := #[("poly", ← `(tactic| blaster_poly))]
      let bridge := if poly then polyTac ++ bridge else bridge
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
        matchInst := insts.get?, macroOf, polyWorld := poly
        proveLemma := fun stmt => do return (← portfolio macroTacs stmt "macro").map (·.1) }
      let tacCache : IO.Ref (Std.HashMap String (Array (String × TSyntax `tactic))) ← IO.mkRef {}
      let proveStep (rule : String) (stmt : Expr) : TermElabM (Option (Expr × String)) := do
        -- NOTE: the tactic syntax of each rule is built once per replay
        let tacs ← match (← tacCache.get).get? rule with
          | some t => pure t
          | none => do let t ← stepTactics rule; tacCache.modify (·.insert rule t); pure t
        -- the axioms of the polymorphic encoding (e.g., Z3's `recfun` lemmas on the definitions of `@isList`)
        let tacs := if poly && (stmt.find? (·.isConstOf ``Poly.Img)).isSome then tacs ++ polyTac else tacs
        portfolio tacs stmt rule
      -- recursive functions (`z3rec`): definitional equations, proved with the bridge tactics in the empty local
      -- context when closed (see `proveClosed`), and differences of normal forms in their unfoldings
      let recCtx ← RecFun.mkCtx tbl recAux recPairs sproof.defs
        (fun stmt => do
          let run : TermElabM (Option Expr) := do return (← portfolio bridge stmt "bridge").map (·.1)
          if stmt.hasFVar then run else withLCtx {} {} run)
        (fun stmt => do return (← proveClosed { proveDirect := fun _ => pure none, proveStep } "th-lemma" stmt).map (·.1))
        (fun a b => do Local.diffEq (localProof { proveDirect := fun _ => pure none, proveStep } "rewrite") (← IO.mkRef 6) a b)
      let recCache : IO.Ref (Std.HashMap Expr (Option Expr)) ← IO.mkRef {}
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
              -- NOTE: the number of failed pairs is given by `BLASTER_SMTPROOF_BRIDGE_DUMP_N` (default 3)
              let n := ((← IO.getEnv "BLASTER_SMTPROOF_BRIDGE_DUMP_N").bind String.toNat?).getD 3
              for (a, b) in if c.isAppOfArity ``Not 1 then fails.extract 0 n else #[] do
                h.putStrLn s!"=== bridge mismatch:\n{← ppExpr a}\n--- interpretation:\n{← ppExpr b}\n"
            -- definitions of Lean functions (e.g., by `match`): the traversal of their unfolding
            if !c.isAppOfArity ``Not 1 then
              if let some p ← (try Bridge.proveDefinition? bcfg c catch _ => pure none) then return some p
            -- definitional axioms of recursive functions (backends without `define-funs-rec`)
            if !c.isAppOfArity ``Not 1 then
              if let some p ← RecFun.proveDefAxiom? c then return some p
            let r ← portfolio bridge c "bridge"
            if r.isNone && (← IO.getEnv "BLASTER_SMTPROOF_DEBUG").isSome then debugLog m!"bridge failed: {← dagString c 4000}"
            if r.isNone then
              if let some f ← IO.getEnv "BLASTER_SMTPROOF_BRIDGE_DUMP" then
                let h ← IO.FS.Handle.mk f .append
                h.putStrLn s!"=== bridge failed:\n{← ppExpr c}\n--- negated goal:\n{← ppExpr (mkNot goalTerm)}\n"
            return r.map (·.1)
          proveStep
          proveRecFun := fun c n => do
            -- NOTE: the lemmas have no premises (a failure is not retried)
            if let some r := (← recCache.get).get? c then return r
            let r ← try RecFun.proveLemma recCtx c n catch _ => pure none
            if r.isNone then debugLog m!"recfun lemma failed: {RecFun.brief c}"
            recCache.modify (·.insert c r)
            return r
          recFunOnly := !recPairs.isEmpty
          recHeads := recCtx.eqs.foldl (fun s eq => s.insert eq.head) {} }
        let cache ← IO.mkRef {}
        let deadline := (← IO.monoMsNow) + 1000 * ((← IO.getEnv "BLASTER_SMTPROOF_DEADLINE").bind String.toNat? |>.getD 300)
        let global := (scopedSteps sproof).map (!·)
        let ctx : ReplayCtx := { proof := sproof, interp := { table := tbl, cache := some cache }, cfg, deadline, global,
                                 openHyps := openHypotheses sproof,
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
      -- NOTE: e.g., type parameters that nothing determines (the other interpretation is then tried)
      if proof.hasMVar then throwError "smt proof: proof term contains metavariables"
      -- debugging: free variables escaping their scopes (environment variable `BLASTER_SMTPROOF_CHECKFINAL`)
      if (← IO.getEnv "BLASTER_SMTPROOF_CHECKFINAL").isSome then reportEscapedFVars proof
      return { proof, backend := backend.name, steps := sproof.steps.size, stats }
    -- 2. backend
    -- backends tried in order (environment variable `BLASTER_SMTPROOF_BACKENDS`, e.g., `z3,cvc5`)
    -- (`z3+`: Z3 with the simplifiers of the query; `z3rec`: Z3 on the query with its recursive functions defined by
    -- `define-funs-rec` (see `RecFun`), skipped when the query has no recursive function)
    -- NOTE: `z3rec` finds proofs when Z3 gets lost in the instantiations of the axioms of recursive functions (e.g., on
    -- the CEK evaluation of validators), but may time out where `z3` succeeds; the next backends are tried when the
    -- replay of a proof fails
    let names := ((← IO.getEnv "BLASTER_SMTPROOF_BACKENDS").getD "z3,z3rec,z3+").splitOn ","
    let timeout := ((← IO.getEnv "BLASTER_SMTPROOF_TIMEOUT").bind String.toNat?).getD (sOpts.timeout.getD 20)
    let mut errors := #[]
    let seedsEnv ← IO.getEnv "BLASTER_SMTPROOF_SEEDS"
    for n in names do
      let recQuery := if n.trim == "z3rec" then (RecFun.rewriteQuery cmds).toOption else none
      if n.trim == "z3rec" && recQuery.isNone then continue
      let backend ← match n.trim with
        | "z3" => pure (z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout)
        | "z3+" => pure (z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout (simplifiers := true))
        | "z3rec" => pure { z3Backend ((← IO.getEnv "BLASTER_SMTPROOF_Z3").getD "z3") timeout with name := "z3rec" }
        | "cvc5" => pure (cvc5Backend ((← IO.getEnv "BLASTER_SMTPROOF_CVC5").getD "cvc5") timeout)
        | b => throwError "unknown proof backend {b}"
      let (query, pairs) := if n.trim == "z3rec" then recQuery.getD (cmds, #[]) else (cmds, #[])
      -- Z3: portfolio of random seeds (environment variable `BLASTER_SMTPROOF_SEEDS`, default 3), started every
      -- `BLASTER_SMTPROOF_SEED_DELAY` ms (default: a quarter of the timeout, at most 10 s) while no proof is found
      -- NOTE: e.g., Z3 finds a proof of a CEK evaluation of a validator in 30 to 170 s depending on the seed
      let seeds := if n.trim == "cvc5" then 1 else (seedsEnv.bind String.toNat?).getD 3
      let delayMs := ((← IO.getEnv "BLASTER_SMTPROOF_SEED_DELAY").bind String.toNat?).getD (min 10000 (timeout * 250))
      match ← runBackendCached backend query seeds delayMs with
      | .error msg => errors := errors.push msg
      | .ok out =>
          match backend.parseProof out with
          | .ok p =>
              -- NOTE: the next backends are tried when the replay fails (e.g., `z3rec` after `z3`)
              let s ← saveState
              try return .ok (← replayWith backend p pairs)
              catch ex =>
                s.restore
                errors := errors.push s!"{backend.name}: {← ex.toMessageData.toString}"
          | .error msg => errors := errors.push s!"{backend.name}: {msg}"
    throwError "no proof: {errors}"
  catch ex =>
    return .error (← ex.toMessageData.toString)

end Blaster.Reconstruct.SmtProof
