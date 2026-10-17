import Lean
import Blaster.Smt.Translate
import Blaster.Reconstruct.Discharge

open Lean Meta Elab Term Blaster.Options Blaster.Optimize Blaster.Smt

namespace Blaster.Reconstruct

/-! # Proof reconstruction

Given a `Valid` verdict, a proof of the original goal `G` is assembled as follows:
  1. Local axioms `ax₁ ... axₙ` are added as hypotheses, i.e., `G' := ∀ (_ : axₙ) ... (_ : ax₁), G`
     (see `Translate.mainWithTask`).
  2. The instrumented optimizer produces `G'' := optimize(G')` together with evidence
     that `G' = G''`, i.e., a proof term possibly containing proof obligations (holes).
  3. A proof of the residual goal `G''` is obtained, i.e.:
       - `True.intro` when `G''` has been reduced to `True` by the optimizer;
       - otherwise (i.e., `G''` proved valid by the SMT solver), via Lean decision procedures.
  4. The proof obligations are discharged (see `dischargeHoles`).
  5. The proof of `G` is obtained by applying the proof of `G'` to the local axioms
     and is checked by the Lean kernel.
-/

/-- Outcome of a proof reconstruction attempt. -/
structure ReconOutcome where
  /-- The kernel-checked proof of the goal (if any). -/
  proof? : Option Expr := none
  /-- Reason of failure (when `proof? = none`). -/
  failure : MessageData := m!""
  /-- Statistics on discharged proof obligations. -/
  stats : DischargeStats := {}
  /-- Number of rewrite steps justified by explicit proof terms. -/
  nbExplicit : Nat := 0
  /-- Number of rewrite steps justified by definitional equality. -/
  nbDefEq : Nat := 0
  /-- Method used to prove the residual goal (if any). -/
  residual : String := "none"
  /-- Time spent on reconstruction (in ms). -/
  elapsedMs : Nat := 0
deriving Inhabited

/-- Return `true` if the reconstruction succeeded. -/
def ReconOutcome.isSuccess (o : ReconOutcome) : Bool := o.proof?.isSome

/-- Create a proof obligation for `lhs = rhs` (used when no evidence has been tracked at all). -/
private def mkTopHole (lhs rhs : Expr) : MetaM Expr := do
  let eqType ← mkEq lhs rhs
  let sorryExpr := mkApp2 (Lean.mkConst ``sorryAx [levelZero]) eqType (toExpr true)
  return mkMData (KVMap.empty.insert holeKey (.ofNat 0)) sorryExpr

/-- Check `proof` against `goal` with the Lean kernel. Fall back to the elaborator's type checker
    when `goal` contains metavariables or free variables.
-/
def kernelCheck (goal : Expr) (proof : Expr) : TermElabM (Option MessageData) := do
  let goal ← instantiateMVars goal
  let proof ← instantiateMVars proof
  if proof.hasMVar then return some m!"proof term contains metavariables"
  if goal.hasMVar || goal.hasFVar || proof.hasFVar then
    try
      Meta.check proof
      if ← isDefEq (← inferType proof) goal then return none
      return some m!"proof term does not have the expected type"
    catch ex => return some ex.toMessageData
  let lvls := (collectLevelParams {} goal).params.toList
  let name ← mkFreshUserName `_blaster_reconstructed
  let decl := Declaration.thmDecl { name, levelParams := lvls, type := goal, value := proof }
  -- NOTE: `addDecl` may perform kernel checking asynchronously, i.e., errors are reported
  -- as messages instead of exceptions. We here call the kernel synchronously.
  match Lean.Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ => return none
  | .error ex => return some m!"kernel rejected the reconstructed proof: {ex.toMessageData (← getOptions)}"

/-- Discharge the proof obligations in `proof` and check it against `goal` with the Lean kernel. -/
def finishProof
  (out : ReconOutcome) (goal proof : Expr) (startTime : Nat) (holes : Array HoleInfo)
  (equivs : Array (Expr × Expr) := #[]) : TermElabM ReconOutcome := do
  let finish (o : ReconOutcome) : TermElabM ReconOutcome := do
    return { o with elapsedMs := (← IO.monoMsNow) - startTime }
  let (proof, stats) ← dischargeHoles proof holes equivs
  let out := { out with stats }
  if !stats.failures.isEmpty || hasHoles proof then
    let shown := stats.failures.extract 0 3
    let msgs := shown.foldl (fun acc m => acc ++ m!"\n  • {m}") m!""
    return ← finish { out with failure := m!"{stats.failures.size} unresolved proof obligation(s) out of {stats.total}:{msgs}" }
  match ← kernelCheck goal proof with
  | some msg => finish { out with failure := msg }
  | none => finish { out with proof? := some proof }

/-- Try to reconstruct a proof for `e = optExpr` given the evidence `pf` obtained by the optimizer. -/
def reconstructRewrite (e optExpr : Expr) (pf : EqPf) (recon : ReconEnv) : TermElabM ReconOutcome := do
  let startTime ← IO.monoMsNow
  let out : ReconOutcome := { nbExplicit := recon.nbExplicit, nbDefEq := recon.nbDefEq, residual := "n/a" }
  let goal ← mkEq e optExpr
  let proof ← match pf with
    | .defeq => mkEqRefl e
    | .proof p => pure p
    | _ => mkTopHole e optExpr
  finishProof out goal proof startTime recon.holes recon.recFunEquivs

/-- Try to reconstruct a proof for `task` given the reconstruction environment `recon`
    obtained after optimization.
-/
def reconstruct (task : ReconTask) (recon : ReconEnv) : TermElabM ReconOutcome := do
  let startTime ← IO.monoMsNow
  let out : ReconOutcome := { nbExplicit := recon.nbExplicit, nbDefEq := recon.nbDefEq }
  let finish := reconstruct.finish startTime
  -- Evidence for `fullGoal = optExpr`
  let optPf? ← match task.optPf with
    | .defeq => pure none
    | .proof p => pure (some p)
    | _ => some <$> mkTopHole task.fullGoal task.optExpr
  -- Proof of the residual goal
  let (residual, residualMethod) ← match task.optExpr with
    | .const ``True _ => pure (some (Lean.mkConst ``True.intro), "optimizer")
    | e =>
        match ← proveResidual e with
        | some (p, m) => pure (some p, s!"smt residual by {m}")
        | none => pure (none, "none")
  let out := { out with residual := residualMethod }
  let some residual := residual
    | finish { out with failure := m!"could not reconstruct a proof for the residual goal proved by the SMT solver{indentExpr task.optExpr}" }
  -- Proof of fullGoal
  let pFull ← match optPf? with
    | none => mkExpectedTypeHint residual task.fullGoal
    | some p =>
        -- NOTE: `Eq.mpr` is built with explicit arguments (`mkEqMPR` unifies the inferred type of `p`
        -- with `task.optExpr`, which may trigger expensive unfolding).
        try pure (mkApp4 (Lean.mkConst ``Eq.mpr [levelZero]) task.fullGoal task.optExpr p residual)
        catch ex => return ← finish { out with failure := m!"ill-formed optimization proof: {ex.toMessageData}" }
  -- Instantiate local axioms
  let axioms ← task.axioms.reverse.mapM fun n => do
    let info ← getConstInfo n
    return Lean.mkConst n (info.levelParams.map mkLevelParam)
  finishProof out task.goal (mkAppN pFull axioms.toArray) startTime recon.holes recon.recFunEquivs

where
  finish (startTime : Nat) (o : ReconOutcome) : TermElabM ReconOutcome := do
    return { o with elapsedMs := (← IO.monoMsNow) - startTime }

/-- Maximum recursion depth used during reconstruction.
    NOTE: `#blaster` sets `maxRecDepth` to `0`, which is not interpreted as "unlimited" by all
    the procedures used during reconstruction (e.g., tactics).
-/
def reconMaxRecDepth : Nat := 100000

@[inline] def withReconRecDepth (x : TermElabM α) : TermElabM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := reconMaxRecDepth }) x

/-- Same as `reconstruct` but any exception (including runtime exceptions such as maximum recursion
    depth or heartbeats) is reported as a reconstruction failure.
-/
def reconstructSafe (task : ReconTask) (recon : ReconEnv) : TermElabM ReconOutcome := do
  let s ← saveState
  let out ← tryCatchRuntimeEx (withReconRecDepth (reconstruct task recon)) fun ex => do
    s.restore
    return { failure := m!"exception: {ex.toMessageData}" }
  if out.proof?.isSome then return out
  -- fallback: prove the original goal directly with Lean's decision procedures
  let startTime ← IO.monoMsNow
  let s ← saveState
  let direct ← tryCatchRuntimeEx (withReconRecDepth (proveDirect task.goal)) fun _ => do
    s.restore
    return none
  match direct with
  | some (p, m) => return { out with proof? := some p, failure := m!"", residual := s!"direct by {m}",
                                     elapsedMs := out.elapsedMs + ((← IO.monoMsNow) - startTime) }
  | none => return out
where
  proveDirect (goal : Expr) : TermElabM (Option (Expr × String)) := do
    let goal ← instantiateMVars goal
    if goal.hasMVar || goal.hasFVar then return none
    let r ← (do
      if let some p ← proveByDefEq goal then return some (p, "rfl")
      if let some p ← proveWithTactic goal (← `(tactic| decide +kernel)) then return some (p, "decide")
      proveResidual goal : TermElabM _)
    let some (p, m) := r | return none
    if (← kernelCheck goal p).isSome then return none
    return some (p, m)

/-- Same as `reconstructRewrite` but any exception is reported as a reconstruction failure. -/
def reconstructRewriteSafe (e optExpr : Expr) (pf : EqPf) (recon : ReconEnv) : TermElabM ReconOutcome := do
  let s ← saveState
  tryCatchRuntimeEx (withReconRecDepth (reconstructRewrite e optExpr pf recon)) fun ex => do
    s.restore
    return { failure := m!"exception: {ex.toMessageData}" }

/-- Lean's standard axioms. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Return the axioms the expression `e` (transitively) depends on. -/
def exprAxioms (e : Expr) : CoreM (Array Name) := do
  let env ← getEnv
  let consts := e.getUsedConstants
  let (_, s) := ((consts.forM fun c => Lean.CollectAxioms.collect c).run env).run {}
  return s.axioms.qsort Name.lt

/-- Check that a proof term only depends on the standard axioms and on `allowed` (e.g., the local
    axioms used as hypotheses). Return the axioms used, or an error message.
-/
def checkProofAxioms (proof : Expr) (allowed : List Name := []) : CoreM (Except MessageData (Array Name)) := do
  let axs ← exprAxioms proof
  let bad := axs.filter fun a => !(standardAxioms.contains a || allowed.contains a)
  if bad.isEmpty then return .ok axs
  return .error m!"the reconstructed proof depends on non-standard axioms: {bad.toList}"

/-- Append a JSON summary of `o` to the file referred by environment variable `BLASTER_RECON_STATS` (if set). -/
def dumpStats (o : ReconOutcome) (label : String) : TermElabM Unit := do
  let some path ← IO.getEnv "BLASTER_RECON_STATS" | return
  let methods := Json.mkObj (o.stats.byMethod.toList.map fun (m, n) => (m, toJson n))
  let pos := (← getRefPos)
  let fileMap ← getFileMap
  let line := (fileMap.toPosition pos).line
  let json := Json.mkObj [
    ("file", toJson (← getFileName)),
    ("line", toJson line),
    ("label", toJson label),
    ("success", toJson o.isSuccess),
    ("residual", toJson o.residual),
    ("explicit", toJson o.nbExplicit),
    ("defeq", toJson o.nbDefEq),
    ("holes", toJson o.stats.total),
    ("unresolved", toJson o.stats.failures.size),
    ("methods", methods),
    ("labels", Json.mkObj (o.stats.byLabel.toList.map fun (l, m) =>
                  (l, Json.mkObj (m.toList.map fun (k, n) => (k, toJson n))))),
    ("ms", toJson o.elapsedMs),
    ("failure", toJson ((← o.failure.toString).take 400))
  ]
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn json.compress

/-- Report the outcome of a proof reconstruction attempt. -/
def reportOutcome (sOpts : BlasterOptions) (o : ReconOutcome) : TermElabM Unit := do
  let details :=
    m!"explicit steps: {o.nbExplicit}, definitional steps: {o.nbDefEq}, " ++
    m!"proof obligations: {o.stats.total} [{o.stats.summary}], residual: {o.residual}, time: {o.elapsedMs}ms"
  if o.isSuccess then
    if sOpts.verbose ≥ 1 then logInfo m!"🔒 Kernel-checked proof reconstructed ({details})"
    else logInfo m!"🔒 Kernel-checked proof reconstructed"
  else
    let msg := m!"Proof reconstruction failed: {o.failure}"
    let msg := if sOpts.verbose ≥ 1 then msg ++ m!"\n({details})" else msg
    if sOpts.reconstruct ≥ 2 then logError m!"❌ {msg}"
    else logWarning m!"⚠️ {msg}\nThe result relies on the trusted Blaster pipeline."

/-- Implementation of the `#blaster` command with proof reconstruction support. -/
def command (sOpts: BlasterOptions) (stx : Syntax) : TermElabM Unit := do
   withRef stx do
     instantiateMVars (← withSynthesize (postpone := .partial) <| elabTerm stx none) >>= fun e => do
       let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
       let ((_, _, task?), _) ← Translate.mainWithTask e |>.run env
       if sOpts.reconstruct == 0 then return
       let some task := task? | return
       let outcome ← reconstructSafe task task.recon
       dumpStats outcome "command"
       reportOutcome sOpts outcome
       if sOpts.genProof then
         if let some p := outcome.proof? then
           match ← checkProofAxioms p task.axioms with
           | .error msg => logError m!"❌ {msg}"
           | .ok axs => logInfo m!"📜 Proof generated (axioms: {axs.toList})"

end Blaster.Reconstruct
