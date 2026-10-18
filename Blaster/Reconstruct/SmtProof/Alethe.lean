import Blaster.Reconstruct.SmtProof.IR

/-!
# Alethe proofs

Adapter for proofs in the Alethe format (produced, e.g., by cvc5 with `--proof-format-mode=alethe`
and by veriT). A proof is a sequence of commands:
 - `(assume id φ)`: an input formula;
 - `(step id (cl l₁ ... lₙ) :rule r :premises (id₁ ... idₖ) :args (a₁ ... aₘ) :discharge (...))`;
 - `(anchor :step id :args (...))`: opens a subproof closed by step `id`, whose steps may use the
   variables (and `(:= x t)` substitutions) introduced by the anchor, and local assumptions.

Clauses are represented as disjunctions (see `IR.lean`). Steps of subproofs are kept with their
local variables free, and the closing step (e.g., `bind`, `subproof`, `sko_ex`) is replayed from its
conclusion (see `Replay.lean`).
-/

namespace Blaster.Reconstruct.SmtProof.Alethe

structure ConvState where
  steps : Array Step := #[]
  ids : Std.HashMap String Nat := {}
  /-- open anchors: identifier of the closing step and index of the first step of the subproof -/
  anchors : Array (String × Nat) := #[]

abbrev ConvM := StateT ConvState (Except String)

/-- Conclusion of a clause `(cl l₁ ... lₙ)`. -/
def clauseToTerm (c : SExpr) : Except String STerm := do
  let some xs := c.list? | throw s!"clause expected: {c}"
  if xs[0]? != some (.atom "cl") then throw s!"clause expected: {c}"
  let lits ← (xs.extract 1 xs.size).mapM (STerm.ofSExpr {})
  match lits.size with
  | 0 => return .sym "false"
  | 1 => return lits[0]!
  | _ => return .app "or" lits

/-- Value of keyword `kw` in the attributes `xs` (e.g., `:rule r`). -/
def attr? (xs : Array SExpr) (kw : String) : Option SExpr := Id.run do
  for i in [:xs.size] do
    if xs[i]! == .atom kw then return xs[i+1]?
  return none

def addStep (id : String) (s : Step) : ConvM Unit :=
  modify fun st => { st with steps := st.steps.push s, ids := st.ids.insert id st.steps.size }

def stepIndex (id : String) : ConvM Nat := do
  match (← get).ids.get? id with
  | some i => return i
  | none => throw s!"unknown step {id}"

def convertCommand (c : SExpr) : ConvM Unit := do
  let some xs := c.list? | throw s!"command expected: {c}"
  match xs[0]?, xs[1]? with
  | some (SExpr.atom "assume"), some (SExpr.atom id) =>
      let some φ := xs[2]? | throw s!"ill-formed assume: {c}"
      -- assumptions of a subproof are local hypotheses (discharged by the closing step)
      let rule := if (← get).anchors.isEmpty then "assume" else "hypothesis"
      addStep id { rule, concl := ← STerm.ofSExpr {} φ }
  | some (SExpr.atom "step"), some (SExpr.atom id) =>
      let some cl := xs[2]? | throw s!"ill-formed step: {c}"
      let concl ← clauseToTerm cl
      let clause? ← match cl.list? with
        | some xs => some <$> (xs.extract 1 xs.size).mapM (fun e => do return (← STerm.ofSExpr {} e))
        | none => pure none
      let attrs := xs.extract 3 xs.size
      let rule := (attr? attrs ":rule" >>= SExpr.atom?).getD "unknown"
      let premises ← match attr? attrs ":premises" with
        | some (SExpr.list ps) => ps.mapM fun p => match p with
            | .atom pid => stepIndex pid
            | _ => throw s!"ill-formed premise: {p}"
        | _ => pure #[]
      let args ← match attr? attrs ":args" with
        | some (SExpr.list as) => as.filterMapM fun a => match a with
            -- `(:= x t)` arguments (e.g., of `forall_inst`): the term `t`
            | .list #[.atom ":=", _, t] => some <$> STerm.ofSExpr {} t
            | a => some <$> STerm.ofSExpr {} a
        | _ => pure #[]
      let discharged ← match attr? attrs ":discharge" with
        | some (SExpr.list ds) => ds.filterMapM fun d => match d with
            | .atom did => some <$> stepIndex did
            | _ => pure none
        | _ => pure #[]
      -- closing step of an anchor: the steps of the subproof are its premises
      let mut premises := premises
      if let some (aid, start) := (← get).anchors.back? then
        if aid == id then
          modify fun st => { st with anchors := st.anchors.pop }
          -- NOTE: the last step of the subproof is the premise of the closing step
          if premises.isEmpty && start < (← get).steps.size then
            premises := #[(← get).steps.size - 1]
      addStep id { rule, premises, args, concl, discharged, clause? }
  | some (SExpr.atom "anchor"), _ =>
      let some (SExpr.atom sid) := attr? xs ":step" | throw s!"ill-formed anchor: {c}"
      modify fun st => { st with anchors := st.anchors.push (sid, st.steps.size) }
  | some (SExpr.atom "define-fun"), _ => pure () -- cvc5 abbreviations are not supported yet
  | _, _ => throw s!"unknown proof command: {c}"

/-- Expand the abbreviations introduced by `(! t :named n)` annotations (as printed by cvc5): later
    occurrences of `n` are replaced by `t` (with sharing). Annotations are removed. -/
partial def expandNamed (e : SExpr) : StateM (Std.HashMap String SExpr) SExpr := do
  match e with
  | .atom a => return (← get).getD a e
  | .str _ => return e
  | .list xs =>
      if xs[0]? == some (.atom "!") && xs.size ≥ 2 then
        let t ← expandNamed xs[1]!
        let attrs := xs.extract 2 xs.size
        for i in [:attrs.size] do
          if attrs[i]! == .atom ":named" then
            if let some (.atom n) := attrs[i+1]? then modify (·.insert n t)
        -- keep other annotations (e.g., patterns)
        let others := (attrs.toList.zip (List.range attrs.size)).filter (fun (a, i) =>
          !(a == .atom ":named" || (i > 0 && attrs[i-1]! == .atom ":named")))
        if others.isEmpty then return t
        return .list (#[.atom "!", t] ++ others.toArray.map (·.1))
      return .list (← xs.mapM expandNamed)

/-- Parse an Alethe proof (the output of `(get-proof)`). -/
def parseProof (out : String) : Except String Proof := do
  let es ← parseSExprs out
  -- cvc5 may wrap the proof commands in a list
  let cmds := match es with
    | #[.list cs] => if cs.all (fun c => c.head?.isSome) then cs else es
    | _ => es
  let cmds := (cmds.mapM expandNamed).run' {}
  let ((), st) ← (cmds.forM convertCommand).run {}
  -- the root is the last step concluding the empty clause
  let some root := (List.range st.steps.size).reverse.find? fun i => st.steps[i]!.concl.isFalse
    | throw "no step concluding the empty clause"
  return { backend := "alethe", steps := st.steps, root }

end Blaster.Reconstruct.SmtProof.Alethe
