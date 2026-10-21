import Lean
import Blaster.Smt.Translate
import Blaster.Reconstruct.Discharge
import Blaster.Reconstruct.SmtProof.Backend
import Blaster.Reconstruct.SmtProof.SymTable
import Blaster.Reconstruct.SmtProof.Tactics
import Blaster.Reconstruct.SmtProof.Replay
import Blaster.Reconstruct.SmtProof.Bridge
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

/-- Quantifications over sorts `∀ (α : Sort u), b` (`u ≠ 0`) in `e` (traversal with sharing), possibly with loose
    bound variables (e.g., `∀ (α : Type), (∀ (_x : α), n > 5) → n > 5` under `∃ n`). -/
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
      if !u.isZero then acc := acc.push s
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
  -- NOTE: a quantification with loose bound variables (e.g., under `∃`) is in a proposition of the goal: its sort
  -- variable is a value of the sort `@Type` as for a closed one
  let quantifiedSorts ← (sortQuantifiers body).anyM fun s => if s.hasLooseBVars then pure true else isProp s
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
        -- NOTE: the replay of the proofs of large goals takes minutes (e.g., about 5 minutes for the validators of
        -- CardanoLedgerApiBlaster's Governance); seconds (environment variable `BLASTER_SMTPROOF_DEADLINE`)
        let deadline := (← IO.monoMsNow) + 1000 * ((← IO.getEnv "BLASTER_SMTPROOF_DEADLINE").bind String.toNat? |>.getD 1800)
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
        let pt ← traceTimed "root type" (inferType p)
        if !pt.isConstOf ``False then throwError "smt proof: root does not prove False: {pt}"
        -- NOTE: the proofs of the steps are instantiated once (see `replay`)
        let p ← traceTimed "instantiation" (instantiateMVars p)
        if (← IO.getEnv "BLASTER_SMTPROOF_TRACE").isSome then
          let (n, d) := dagStats p
          traceTimed s!"proof of {n} distinct subterms, binder depth {d}, metavariables {p.hasMVar}" (pure ())
        -- NOTE: the negated goal only occurs in the proofs of the asserted formulas (see `abstractFVar`)
        let pf ← traceTimed "abstraction of the negated goal" do
          if p.hasMVar then mkLambdaFVars #[hneg] p
          else return .lam `hneg (← inferType hneg) (abstractFVar p hneg.fvarId!) .default
        return (pf, st.stats)
      let (pf, stats) := pf
      let proofBody := mkApp2 (mkConst ``Classical.byContradiction) body pf
      let proof ← traceTimed "abstraction of the variables" (do instantiateMVars (← mkLambdaFVars xs proofBody))
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
