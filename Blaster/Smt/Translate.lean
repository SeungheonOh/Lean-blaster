import Lean
import Blaster.Command.Options
import Blaster.Optimize.Basic
import Blaster.Smt.Env
import Blaster.Smt.Term
import Blaster.Smt.Translate.Application
import Blaster.Reconstruct.Profile

open Lean Elab Command Term Meta Blaster.Optimize Blaster.Options

namespace Blaster.Smt

/-- Translate an optimized Lean4 `Expr` to an SMT term, and invoke the solver. --/
partial def translateExpr (e : Expr) (topLevel := true) : TranslateEnvT SmtTerm := do
  let rec visit (e : Expr) (topLevel := false) : TranslateEnvT SmtTerm := do
    withTranslateEnvCache e fun _ => do
    trace[Translate.expr] "translating {reprStr e}"
    logReprExpr "Translate:" e
    if let some n := isIntValue? e then return intLitSmt n
    if let some n := isNatValue? e then return natLitSmt n
    if let some s := isStrValue? e then
      match strLitSmt s with
      | .ok t => return t
      | .error c =>
          throwEnvError "translateExpr: string literal holds the character with code point \
                         {c.toNat}, above the Smt string alphabet bound {maxSmtCodePoint}"
    -- TODO: consider other sort once supported (e.g., BitVec, Char, etc)
    match e with
     | Expr.fvar .. => translateFreeVar e visit
     | Expr.const .. => translateConst e visit
     | Expr.forallE .. =>
         let qtyEnv := initialQuantifierEnv topLevel
         let t ← translateForAll e visit |>.run' qtyEnv
         trace[Translate.forAll] "translate forall {reprStr e} ==> {t}"
         return t
     | Expr.app .. => translateApp e visit
     | Expr.lam .. => translateLambda e visit
     | Expr.mdata _d me =>
        match toTaggedCtorSelector? e with
        | none => visit me
        | some (Expr.app (Expr.const s _) _) =>
            return mkSimpleSmtAppN (nameToSmtSymbol s) #[smtSimpleVarId (mkReservedSymbol "@x")]
        | some s => throwEnvError "translateExpr: unexpected ctor selector expression {reprStr s}"
     | Expr.proj n idx p => translateProj n idx p visit
     | Expr.lit .. => throwEnvError "translateExpr: unexpected literal expression {reprStr e}"
     | Expr.mvar .. => throwEnvError "translateExpr: unexpected meta variable {reprStr e}"
     | Expr.bvar .. => throwEnvError "translateExpr: unexpected bound variable {reprStr e}"
     | Expr.letE .. => throwEnvError "translateExpr: unexpected let expression {reprStr e}"
     | Expr.sort _ => throwEnvError "translateExpr: unexpected sort type {reprStr e}" -- sort type are handled elsewhere
  visit e topLevel

/-- A cancellation token set when the backend solver's answer `answer` is not `unsat` (i.e., when the goal is not
    valid) or when the enclosing elaboration is interrupted (e.g., the file being edited, see `checkCancelTk?`). The
    token must be set by the caller when no longer used. -/
private def answerToken (answer : Task (Except IO.Error String)) : CoreM IO.CancelToken := do
  let tk ← IO.CancelToken.new
  let _ ← IO.mapTask (t := answer) fun
    | .ok l => unless isUnsatLine l do tk.set
    | .error _ => tk.set
  -- NOTE: the interruption of the enclosing elaboration is forwarded by polling, as tokens cannot be combined
  if let some outer := (← read).cancelTk? then
    let _ ← IO.asTask (prio := .dedicated) do
      while !(← tk.isSet) do
        if ← outer.isSet then tk.set else IO.sleep 50
  return tk

/-- `x` interrupted when `tk` is set, `none` when interrupted. -/
private def interruptible (tk : IO.CancelToken) (x : MetaM α) : MetaM (Option α) :=
  controlAt CoreM fun runInBase => fun ctx s => do
    try (runInBase (some <$> x)) { ctx with cancelTk? := some tk } s
    catch ex => if ex.isInterrupt then (runInBase (pure none)) ctx s else throw ex

/-- `x` without its heartbeats counted, such that the heartbeats consumed in the enclosing declaration are the same
    with and without proof reconstruction. -/
private def uncounted [Monad m] [MonadLiftT BaseIO m] [MonadFinally m] (x : m α) : m α := do
  let heartbeats ← IO.getNumHeartbeats
  try x finally IO.setNumHeartbeats heartbeats

/-- Same as `Translate.main` but also returns the information required to reconstruct a proof
    when the result is `Valid` and proof reconstruction is activated, and the result of `speculate?` on it (e.g., the
    reconstruction itself) when performed while the backend solver checks the query (see `Solve` below).
-/
def Translate.mainWithTaskSpec {α : Type} (e : Expr) (logUndetermined := true)
    (speculate? : Option (Reconstruct.ReconTask → MetaM α) := none) :
  TranslateEnvT (Result × Expr × Option Reconstruct.ReconTask × Option α) := do
    -- set start local context
    updateLocalContext (← mkLocalContext)
    let goal ← toPropExpr e
    let axioms ← findLocalAxiomDecls
    let e' ← addAxioms goal (axioms.map Prod.snd)
    -- NOTE: the verdict is always computed without tracking proof terms, such that proof
    -- reconstruction never alters Blaster's behavior.
    let (optExpr, _) ← profileTask "Optimization" $ Optimize.mainPf e' (track := false) (applyHashCons := false)
    trace[Translate.optExpr] "optimized expression: {← ppExpr optExpr}"
    let sOpts := (← get).optEnv.options.solverOptions
    -- proof run: optimize again while tracking proof terms (see `Blaster.Reconstruct`)
    let proofRun : MetaM (Option ((Expr × Reconstruct.EqPf) × TranslateEnv)) := uncounted do
      let proofEnv := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
      let s ← Meta.saveState
      tryCatchRuntimeEx
        -- NOTE: the proof run starts with an empty hash-consing cache, i.e., `e'` must be hash-consed
        -- such that structural equality checks (e.g., on literals) remain valid.
        (some <$> Reconstruct.withProfile "proofRun" (do
            (Optimize.mainPf e' (track := true) (applyHashCons := true)).run proofEnv))
        (fun _ => do s.restore; return none)
    -- NOTE: the caches only used during the proof run (e.g., `ReconEnv.holeFree`) are dropped, freeing their memory
    let mkTask (bySmt : Bool) (run : Option ((Expr × Reconstruct.EqPf) × TranslateEnv)) : Reconstruct.ReconTask :=
      match run with
      | some ((optExprP, optPf), envP) =>
          { goal, axioms := axioms.map Prod.fst, fullGoal := e', optExpr := optExprP, optPf, bySmt,
            recon := { envP.recon with holeFree := {}, matchCongrs := {} }, smtProof := sOpts.smtProof,
            randomSeed := sOpts.randomSeed, timeout := sOpts.timeout }
      | none => { goal, axioms := axioms.map Prod.fst, fullGoal := e', optExpr, optPf := .unknown, bySmt }
    match (toResult optExpr) with
    | res@(.Undetermined) =>
        if (← get).optEnv.options.solverOptions.onlyOptimize then
          if logUndetermined then logResult res
          return (res, optExpr, none, none)
        else
          -- set backend solver
          setBlasterProcess
          let st ← profileTask "Translation" $ translateExpr optExpr
          -- assert negation for check sat
          profileTask "Submitting Smt Query" $ assertTerm (notSmt st)
          -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
          logSmtQuery
          let (res, task?, spec?) ← match (← get).smtEnv.smtProc with
            | some p =>
                if sOpts.reconstruct == 0 then pure (← profileTask "Solve" checkSat, none, none) else
                -- NOTE: with proof reconstruction, the proof run and then `speculate?` (e.g., the reconstruction
                -- itself) are performed while the backend solver checks the query (e.g., the proof run and most of the
                -- reconstruction during the 15 s of the check of a CEK evaluation). They are interrupted when the
                -- solver answers that the goal is not valid and discarded unless the goal is valid, i.e., the verdict
                -- is unaffected.
                let s ← Meta.saveState
                if sOpts.verbose ≥ 1 then IO.println "[Start]: Solve"
                let start ← IO.monoMsNow
                submitCommand .checkSat
                let answer ← IO.asTask (prio := .dedicated) p.stdout.getLine
                let answered ← BaseIO.mapTask (fun _ => IO.monoMsNow) answer
                let tk ← answerToken answer
                let (run?, spec?) ← try
                    let run? ← interruptible tk proofRun
                    let spec? ← match speculate?, run? with
                      | some speculate, some run => uncounted (interruptible tk (speculate (mkTask true run)))
                      | _, _ => pure none
                    pure (run?, spec?)
                  finally tk.set
                let res ← getSatResult.waitForResult answer
                if sOpts.verbose ≥ 1 then
                  let solveTime := ((← IO.wait answered) - start).toFloat / 1000.0
                  IO.println f!"[End]: Solve ({reprPrec solveTime 2}s)"
                if !res matches .Valid then
                  s.restore
                  pure (res, none, none)
                else
                  -- NOTE: the proof run is performed again when it was interrupted (e.g., by another interrupt)
                  let run ← match run? with
                    | some run => pure run
                    | none => proofRun
                  pure (res, some (mkTask true run), spec?)
            | none => pure (← profileTask "Solve" checkSat, none, none)
          if !isUndeterminedResult res || logUndetermined then logResult res
          discard $ exitSmt
          match res with
          | .Valid => return (res, optExpr, task?, spec?)
          | _ => return (res, optExpr, none, none)
    | res =>
       logResult res
       match res with
       | .Valid =>
           let task? ← if sOpts.reconstruct == 0 then pure none else pure (some (mkTask false (← proofRun)))
           return (res, optExpr, task?, none)
       | _ => return (res, optExpr, none, none)

  where
    isTheoremExpr (e : Expr) : TranslateEnvT (Option Expr) := do
      let Expr.const n _ := e.getAppFn' | return none
      let ConstantInfo.thmInfo info ← getConstEnvInfo n | return none
      hashcons info.type

    toPropExpr (e : Expr) : TranslateEnvT Expr := do
      if let some r ← isTheoremExpr e then return r
      if !(← isTypeCorrect e) || (Expr.hasSorry e) then
         throwEnvError "translate: {← ppExpr e} is not well-formed"
      let e' ← hashcons e
      if (← isPropEnv e') then return e'
         throwEnvError "translate: {← ppExpr e} is not a proposition !!!"

    addAxioms (e : Expr) (axioms : List Expr) : TranslateEnvT Expr := do
      match axioms with
      | [] => return e
      | a :: tl =>
         addAxioms (← mkForallExpr (← Term.mkFreshBinderName) BinderInfo.default (← hashcons a) e) tl

/-- Same as `Translate.mainWithTaskSpec` without speculation. -/
def Translate.mainWithTask (e : Expr) (logUndetermined := true) :
    TranslateEnvT (Result × Expr × Option Reconstruct.ReconTask) := do
  let (res, optExpr, task?, _) ← Translate.mainWithTaskSpec (α := Unit) e logUndetermined none
  return (res, optExpr, task?)

def Translate.main (e : Expr) (logUndetermined := true) : TranslateEnvT (Result × Expr) := do
  let (res, optExpr, _) ← Translate.mainWithTask e logUndetermined
  return (res, optExpr)

def command (sOpts: BlasterOptions) (stx : Syntax) : TermElabM Unit := do
   withRef stx do
     instantiateMVars (← withSynthesize (postpone := .partial) <| elabTerm stx none) >>= fun e => do
       let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
       discard $ Translate.main e|>.run env

initialize
   registerTraceClass `Translate.expr
   registerTraceClass `Translate.forAll
   registerTraceClass `Translate.optExpr

end Blaster.Smt
