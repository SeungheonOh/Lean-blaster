import Lean
import Blaster.Command.Syntax
import Blaster.Reconstruct.Main

open Lean Elab Command Term Meta Blaster.Options Blaster.Optimize Blaster.Smt

namespace Blaster.Theorem

/--
`blaster_theorem name (options)* : statement` proves `statement` with Blaster and adds `name` to the
environment as a theorem whose proof term has been reconstructed and checked by the Lean kernel.

The generated proof only depends on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) and on the local axioms of the current module used as hypotheses: it never relies on
`sorryAx`. An error is reported when Blaster cannot prove the statement or when no such proof can
be reconstructed.

Example:
  blaster_theorem add_comm' : ∀ (x y : Nat), x + y = y + x
  #print axioms add_comm'
-/
syntax (name := blasterTheorem) "blaster_theorem " ident (solveOption)* " : " term : command

@[command_elab blasterTheorem]
def elabBlasterTheorem : CommandElab := fun stx => do
  let id : Ident := ⟨stx[1]⟩
  let opts := stx[2].getArgs
  let sOpts ← Syntax.parseSolveOptions opts (← BlasterOptions.fromEnv)
  let sOpts := { sOpts with genProof := true, reconstruct := 2 }
  let declName := (← getCurrNamespace) ++ id.getId
  liftTermElabM do
    withRef stx do
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
      let e ← elabType stx[4]
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasMVar then throwError "blaster_theorem: statement contains metavariables{indentExpr e}"
      let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
      let ((result, _, task?), env') ← Translate.mainWithTask e |>.run env
      let .Valid := result | throwError "blaster_theorem: the statement could not be proved"
      let some task := task? | throwError "blaster_theorem: no reconstruction information"
      let outcome ← Reconstruct.reconstructSafe task env'.recon
      Reconstruct.dumpStats outcome "blaster_theorem"
      let some proof := outcome.proof?
        | throwError "blaster_theorem: proof reconstruction failed: {outcome.failure}"
      let axs ← match ← Reconstruct.checkProofAxioms proof task.axioms with
        | .error msg => throwError "blaster_theorem: {msg}"
        | .ok axs => pure axs
      let lvls := (collectLevelParams {} e).params.toList
      addDecl (Declaration.thmDecl { name := declName, levelParams := lvls, type := e, value := proof })
      logInfo m!"📜 Theorem {declName} generated (kernel-checked, axioms: {axs.toList}, \
        explicit steps: {outcome.nbExplicit}, proof obligations: {outcome.stats.total}, time: {outcome.elapsedMs}ms)"

end Blaster.Theorem
