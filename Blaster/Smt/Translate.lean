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

/-- `x` with its interrupt exceptions (not caught by `try`/`catch`) as `none`. -/
private def catchInterrupt (x : MetaM α) : MetaM (Option α) :=
  controlAt CoreM fun runInBase => fun ctx s => do
    try (runInBase (some <$> x)) ctx s
    catch ex => if ex.isInterrupt then (runInBase (pure none)) ctx s else throw ex

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
    let proofRun : MetaM (Option ((Expr × Reconstruct.EqPf) × TranslateEnv)) := do
      let proofEnv := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
      let s ← Meta.saveState
      tryCatchRuntimeEx
        -- NOTE: the proof run starts with an empty hash-consing cache, i.e., `e'` must be hash-consed
        -- such that structural equality checks (e.g., on literals) remain valid.
        (some <$> Reconstruct.withProfile "proofRun" (do
            (Optimize.mainPf e' (track := true) (applyHashCons := true)).run proofEnv))
        (fun _ => do s.restore; return none)
    -- `run?`: the result of the proof run when performed beforehand (see `Solve` below)
    let mkTask (bySmt : Bool) (run? : Option (Option ((Expr × Reconstruct.EqPf) × TranslateEnv)) := none) :
        TranslateEnvT (Option Reconstruct.ReconTask) := do
      if sOpts.reconstruct == 0 then return none
      let r ← match run? with
        | some r => pure r
        | none => proofRun
      match r with
      | some ((optExprP, optPf), envP) =>
          return some { goal, axioms := axioms.map Prod.fst, fullGoal := e', optExpr := optExprP, optPf,
                        bySmt, recon := { envP.recon with holeFree := {}, matchCongrs := {} }, smtProof := sOpts.smtProof,
                        randomSeed := sOpts.randomSeed, timeout := sOpts.timeout }
      | none =>
          return some { goal, axioms := axioms.map Prod.fst, fullGoal := e', optExpr, optPf := .unknown, bySmt }
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
          -- NOTE: with proof reconstruction, the proof run is performed while the backend solver checks the
          -- query (e.g., 10 s of the 15 s of the check of a CEK evaluation), the verdict being unaffected; its
          -- result is discarded unless the goal is valid
          let (res, task?, spec?) ← match (← get).smtEnv.smtProc with
            | some p =>
                if sOpts.reconstruct == 0 then pure (← profileTask "Solve" checkSat, none, none) else
                submitCommand .checkSat
                let answer ← IO.asTask p.stdout.getLine
                let s ← Meta.saveState
                let task? ← mkTask true (some (← proofRun))
                -- NOTE: `speculate?` (e.g., the reconstruction) is started when the solver is still checking the query
                -- after the proof run (e.g., 7 of the 15 s of the check of a CEK evaluation), interrupted when the solver
                -- answers that the goal is not valid, and discarded unless the goal is valid
                let mut spec? := none
                if let (some speculate, some task) := (speculate?, task?) then
                  if !(← IO.hasFinished answer) then
                    let tk ← IO.CancelToken.new
                    let _ ← IO.mapTask (t := answer) fun r => do
                      match r with
                      | .ok l => if !isUnsatLine l then tk.set
                      | .error _ => tk.set
                    spec? ← (catchInterrupt (withTheReader Core.Context (fun c => { c with cancelTk? := some tk })
                      (speculate task)) : MetaM _)
                let res ← profileTask "Solve" (getSatResult.getSatResultOf answer)
                if res matches .Valid then pure (res, task?, spec?) else
                  s.restore
                  pure (res, none, none)
            | none => pure (← profileTask "Solve" checkSat, none, none)
          if !isUndeterminedResult res || logUndetermined then logResult res
          discard $ exitSmt
          match res with
          | .Valid => return (res, optExpr, task?, spec?)
          | _ => return (res, optExpr, none, none)
    | res =>
       logResult res
       match res with
       | .Valid => return (res, optExpr, ← mkTask false, none)
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
