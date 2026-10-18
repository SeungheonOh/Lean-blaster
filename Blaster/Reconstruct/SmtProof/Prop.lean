import Lean

/-!
# Propositional reasoning with proof terms

A small refutation procedure used to replay propositional steps of SMT proofs (e.g., Z3's `def-axiom`,
`not-or-elim`, `and-elim`, propositional rewrites, resolution with non-unit literals). Facts (propositions
with proofs) are saturated with unit rules on `¬`, `∧`, `∨`, `→`, `ite` over propositions and equality of
propositions, until a contradiction is found. Atoms are kept opaque, such that the procedure doesn't depend
on the theory of the atoms. No case split is performed (Tseitin axioms are refuted by unit propagation).
-/

open Lean Meta

namespace Blaster.Reconstruct.SmtProof.PropEngine

structure State where
  /-- proved propositions -/
  facts : Std.HashMap Expr Expr := {}
  /-- facts to process -/
  todo : Array Expr := #[]
  conflict : Option Expr := none

abbrev M := StateRefT State MetaM

def isProp' (e : Expr) : MetaM Bool := do
  try isProp e catch _ => return false

/-- Add fact `t` with proof `p`, detecting conflicts with `¬ t` (or `t = ¬ a` with `a`). -/
def addFact (t p : Expr) : M Unit := do
  let s ← get
  if s.conflict.isSome || s.facts.contains t then return
  if t.isConstOf ``False then
    modify fun s => { s with conflict := some p }
    return
  if let some a := t.not? then
    if let some pa := s.facts.get? a then
      modify fun s => { s with conflict := some (mkApp p pa) }
      return
  if let some pn := s.facts.get? (mkNot t) then
    modify fun s => { s with conflict := some (mkApp pn p) }
    return
  modify fun s => { s with facts := s.facts.insert t p, todo := s.todo.push t }

def get? (t : Expr) : M (Option Expr) := return (← get).facts.get? t

/-- Proof of `¬ t` if known (as `¬ t`, or `t := ¬ a` with `a` known). -/
def getNeg? (t : Expr) : M (Option Expr) := do
  if let some p ← get? (mkNot t) then return some p
  if let some a := t.not? then
    if let some pa ← get? a then
      return some (← withLocalDeclD `h t fun h => mkLambdaFVars #[h] (mkApp h pa))
  return none

/-- `propext (Iff.intro ab ba) : a = b`. -/
def mkPropext (a b ab ba : Expr) : MetaM Expr :=
  return mkApp3 (mkConst ``propext) a b (mkApp4 (mkConst ``Iff.intro) a b ab ba)

def byContra (t : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  -- `Classical.byContradiction (fun h : ¬ t => k h)`
  let r ← withLocalDeclD `h (mkNot t) fun h => do mkLambdaFVars #[h] (← k h)
  return mkApp2 (mkConst ``Classical.byContradiction) t r

/-- Derive the consequences of fact `t` (with proof `p`) and of the facts it unlocks. -/
def process (t p : Expr) : M Unit := do
  -- ¬¬a
  if let some na := t.not? then
    if let some a := na.not? then
      addFact a (← byContra a fun h => return mkApp p h)
    -- ¬(a ∧ b)
    if let some (a, b) := na.and? then
      if let some pa ← get? a then
        addFact (mkNot b) (← withLocalDeclD `h b fun h => do mkLambdaFVars #[h] (mkApp p (← mkAppM ``And.intro #[pa, h])))
      if let some pb ← get? b then
        addFact (mkNot a) (← withLocalDeclD `h a fun h => do mkLambdaFVars #[h] (mkApp p (← mkAppM ``And.intro #[h, pb])))
    -- ¬(a ∨ b)
    if let some (a, b) := na.app2? ``Or then
      addFact (mkNot a) (← withLocalDeclD `h a fun h => do mkLambdaFVars #[h] (mkApp p (mkApp3 (mkConst ``Or.inl) a b h)))
      addFact (mkNot b) (← withLocalDeclD `h b fun h => do mkLambdaFVars #[h] (mkApp p (mkApp3 (mkConst ``Or.inr) a b h)))
    -- ¬(a → b)
    if na.isArrow then
      let a := na.bindingDomain!
      let b := na.bindingBody!
      if (← isProp' a) && !b.hasLooseBVars then
        addFact a (← byContra a fun hna => do
          return mkApp p (← withLocalDeclD `ha a fun ha => do
            mkLambdaFVars #[ha] (mkApp2 (mkConst ``False.elim [levelZero]) b (mkApp hna ha))))
        addFact (mkNot b) (← withLocalDeclD `hb b fun hb => do
          mkLambdaFVars #[hb] (mkApp p (← withLocalDeclD `ha a fun ha => mkLambdaFVars #[ha] hb)))
    -- ¬(a = b) for propositions
    if let some (ty, a, b) := na.eq? then
      if ty.isProp then
        if let some pa ← get? a then
          -- b → (a = b)
          let nb ← withLocalDeclD `hb b fun hb => do
            let ab ← withLocalDeclD `x a fun x => mkLambdaFVars #[x] hb
            let ba ← withLocalDeclD `x b fun x => mkLambdaFVars #[x] pa
            mkLambdaFVars #[hb] (mkApp p (← mkPropext a b ab ba))
          addFact (mkNot b) nb
        if let some pna ← getNeg? a then
          -- ¬ b → (a = b)
          let pb ← byContra b fun hnb => do
            let ab ← withLocalDeclD `x a fun x => mkLambdaFVars #[x] (mkApp2 (mkConst ``False.elim [levelZero]) b (mkApp pna x))
            let ba ← withLocalDeclD `x b fun x => mkLambdaFVars #[x] (mkApp2 (mkConst ``False.elim [levelZero]) a (mkApp hnb x))
            return mkApp p (← mkPropext a b ab ba)
          addFact b pb
    return
  -- a ∧ b
  if let some (a, b) := t.and? then
    addFact a (mkApp3 (mkConst ``And.left) a b p)
    addFact b (mkApp3 (mkConst ``And.right) a b p)
    return
  -- a ∨ b
  if let some (a, b) := t.app2? ``Or then
    if let some na ← getNeg? a then addFact b (← mkAppM ``Or.resolve_left #[p, na])
    if let some nb ← getNeg? b then addFact a (← mkAppM ``Or.resolve_right #[p, nb])
    return
  -- a → b
  if t.isArrow then
    let a := t.bindingDomain!
    let b := t.bindingBody!
    if (← isProp' a) && !b.hasLooseBVars then
      if let some pa ← get? a then addFact b (mkApp p pa)
      if let some nb ← getNeg? b then
        addFact (mkNot a) (← withLocalDeclD `h a fun h => do mkLambdaFVars #[h] (mkApp nb (mkApp p h)))
    return
  -- ite c a b (propositions)
  if t.isAppOfArity ``ite 5 then
    let args := t.getAppArgs
    let (c, a, b) := (args[1]!, args[3]!, args[4]!)
    if let some pc ← get? c then
      addFact a (← mkEqMP (← mkAppOptM ``if_pos #[c, args[2]!, pc, none, a, b]) p)
    if let some nc ← getNeg? c then
      addFact b (← mkEqMP (← mkAppOptM ``if_neg #[c, args[2]!, nc, none, a, b]) p)
    return
  -- a = b (propositions)
  if let some (ty, a, b) := t.eq? then
    if ty.isProp then
      if let some pa ← get? a then addFact b (← mkEqMP p pa)
      if let some pb ← get? b then addFact a (← mkEqMPR p pb)
      if let some na ← getNeg? a then
        addFact (mkNot b) (← withLocalDeclD `h b fun h => do mkLambdaFVars #[h] (mkApp na (← mkEqMPR p h)))
      if let some nb ← getNeg? b then
        addFact (mkNot a) (← withLocalDeclD `h a fun h => do mkLambdaFVars #[h] (mkApp nb (← mkEqMP p h)))

/-- Saturate the facts until a conflict is found (at most `fuel` rounds). -/
partial def saturate (fuel : Nat := 8) : M (Option Expr) := do
  for _ in [0:fuel] do
    if let some c := (← get).conflict then return some c
    let todo := (← get).todo
    if todo.isEmpty then
      -- facts may unlock rules on facts processed earlier: process all facts again
      let facts := (← get).facts.toArray
      let before := (← get).facts.size
      for (t, p) in facts do
        process t p
        if (← get).conflict.isSome then break
      if (← get).facts.size == before && (← get).todo.isEmpty then break
      continue
    modify fun s => { s with todo := #[] }
    for t in todo do
      if let some p := (← get).facts.get? t then process t p
      if (← get).conflict.isSome then break
  return (← get).conflict

/-- Prove `goal` from `hyps` (propositions and proofs) by refutation, or return `none`. Propositional
    equalities in the goal are proved with `propext` from both implications. -/
partial def prove (hyps : Array (Expr × Expr)) (goal : Expr) : MetaM (Option Expr) := do
  -- `a = b` between propositions: both directions
  if let some (ty, a, b) := goal.eq? then
    if ty.isProp then
      let some ab ← withLocalDeclD `h a fun h => do
          match ← prove (hyps.push (a, h)) b with
          | some p => some <$> mkLambdaFVars #[h] p
          | none => pure none
        | return none
      let some ba ← withLocalDeclD `h b fun h => do
          match ← prove (hyps.push (b, h)) a with
          | some p => some <$> mkLambdaFVars #[h] p
          | none => pure none
        | return none
      return some (← mkPropext a b ab ba)
  let r ← withLocalDeclD `hn (mkNot goal) fun hn => do
    let act : M (Option Expr) := do
      for (t, p) in hyps do addFact t p
      addFact (mkNot goal) hn
      saturate
    let (c?, _) ← act.run {}
    match c? with
    | some c => some <$> mkLambdaFVars #[hn] c
    | none => pure none
  return r.map fun r => mkApp2 (mkConst ``Classical.byContradiction) goal r

end Blaster.Reconstruct.SmtProof.PropEngine
