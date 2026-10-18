import Lean

/-!
# Local proofs of equalities between large terms

Steps of SMT proofs (e.g., Z3's `rewrite`, `th-lemma`) often relate large terms that differ in a few
places only, and whose validity does not depend on the structure of their common subterms. Instead of
calling tactics on the whole statement:
 - `diffEq` relates the two sides by congruence on their common structure, and proves the remaining
   differences (the smallest subterms whose heads differ) separately;
 - `generalizeCommon` abstracts the maximal subterms common to both sides of a local statement as
   variables, such that the tactics only see the structure relevant to the rewrite.
-/

open Lean Meta Elab Term

namespace Blaster.Reconstruct.SmtProof.Local

/-- Subterms of `e` without loose bound variables (traversal of the DAG, with sharing). -/
partial def closedSubterms (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
  if acc.contains e then acc else
  let acc := if e.hasLooseBVars then acc else acc.insert e
  match e with
  | .app f a => closedSubterms a (closedSubterms f acc)
  | .lam _ t b _ | .forallE _ t b _ => closedSubterms b (closedSubterms t acc)
  | .letE _ t v b _ => closedSubterms b (closedSubterms v (closedSubterms t acc))
  | .mdata _ b | .proj _ _ b => closedSubterms b acc
  | _ => acc

/-- Terms that are never abstracted: atoms, literals, types. -/
def isAtomic (e : Expr) : Bool :=
  match e with
  | .fvar .. | .const .. | .lit .. | .sort .. | .bvar .. | .mvar .. => true
  | _ =>
    e.isAppOfArity ``OfNat.ofNat 3 || e.isAppOfArity ``Nat.cast 3 && (e.getArg! 2).isRawNatLit ||
    e.isAppOfArity ``Int.ofNat 1 || e.isAppOfArity ``Int.negSucc 1 || e.isAppOfArity ``Neg.neg 3 && (e.getArg! 2).isAppOfArity ``OfNat.ofNat 3

/-- Maximal subterms of `l` that also occur in `r` (and are neither atomic nor types). -/
partial def commonSubterms (l r : Expr) : MetaM (Array Expr) := do
  let inR := closedSubterms r {}
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← IO.mkRef (#[] : Array Expr)
  let rec go (e : Expr) : MetaM Unit := do
    if (← visited.get).contains e then return
    visited.modify (·.insert e)
    if !e.hasLooseBVars && !isAtomic e && inR.contains e then
      if !(← isType e) then
        found.modify (·.push e)
        return
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  go l
  found.get

/-- Replace the subterms `ss` (by structural equality) by the free variables `zs` in `e`. -/
partial def replaceAll (m : Std.HashMap Expr Expr) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some z := m.get? e then return z
  if let some e' := (← get).get? e then return e'
  let e' ← match e with
    | .app f a => pure (e.updateApp! (← replaceAll m f) (← replaceAll m a))
    | .lam _ t b _ => pure (e.updateLambdaE! (← replaceAll m t) (← replaceAll m b))
    | .forallE _ t b _ => pure (e.updateForallE! (← replaceAll m t) (← replaceAll m b))
    | .mdata _ b => pure (e.updateMData! (← replaceAll m b))
    | .proj _ _ b => pure (e.updateProj! (← replaceAll m b))
    | _ => pure e
  modify (·.insert e e')
  return e'

/-- `(∀ zs, stmt[zs/ss], ss)` where `ss` are the maximal subterms common to `l` and `r` (the sides of
    `stmt`), or `none` when there is no common subterm or the generalization is not type correct. -/
def generalizeCommon (stmt l r : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let ss ← commonSubterms l r
  if ss.isEmpty then return none
  let types ← ss.mapM inferType
  let decls := (ss.zip types).mapIdx fun i (_, t) => (Name.mkSimple s!"z{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun zs => do
    let m : Std.HashMap Expr Expr := (ss.zip zs).foldl (fun m (s, z) => m.insert s z) {}
    let (stmt', _) := (replaceAll m stmt).run {}
    let g ← mkForallFVars zs stmt'
    if !(← isTypeCorrect g) then return none
    return some (g, ss)

/-- Proof of `l = r` by congruence on the common structure of `l` and `r`, proving the remaining
    differences with `prove` (given the equality to prove, returns a proof). At most `budget` calls of
    `prove`. -/
partial def diffEq (prove : Expr → TermElabM (Option Expr)) (budget : IO.Ref Nat) (l r : Expr) : TermElabM (Option Expr) := do
  if l == r then return some (← mkEqRefl l)
  let whole : TermElabM (Option Expr) := do
    if (← budget.get) == 0 then return none
    budget.modify (· - 1)
    prove (← mkEq l r)
  let fl := l.getAppFn
  let fr := r.getAppFn
  if !l.isApp || !r.isApp || fl != fr || l.getAppNumArgs != r.getAppNumArgs then
    match l, r with
    | .forallE n t b bi, .forallE _ t' b' _ =>
        if t == t' && (b.hasLooseBVars || b'.hasLooseBVars) && (← isProp l) then
          let r? ← withLocalDecl n bi t fun x => do
            let some p ← diffEq prove budget (b.instantiate1 x) (b'.instantiate1 x) | return none
            return some (← mkAppM ``forall_congr #[← mkLambdaFVars #[x] p])
          if r?.isSome then return r?
        else if !b.hasLooseBVars && !b'.hasLooseBVars then
          let some pt ← diffEq prove budget t t' | return ← whole
          let some pb ← diffEq prove budget b b' | return ← whole
          return some (← mkAppM ``implies_congr #[pt, pb])
      | .lam n t b bi, .lam _ t' b' _ =>
        if t == t' then
          let r? ← withLocalDecl n bi t fun x => do
            let some p ← diffEq prove budget (b.instantiate1 x) (b'.instantiate1 x) | return none
            return some (← mkFunExt (← mkLambdaFVars #[x] p))
          if r?.isSome then return r?
      | _, _ => pure ()
    return ← whole
  let as := l.getAppArgs
  let bs := r.getAppArgs
  let info ← getFunInfoNArgs fl as.size
  let mut pf ← mkEqRefl l
  let mut cur := as
  for i in [:as.size] do
    if as[i]! == bs[i]! then continue
    if let some pi := info.paramInfo[i]? then
      if pi.hasFwdDeps then return ← whole
    let ta ← inferType as[i]!
    if !(← isDefEq ta (← inferType bs[i]!)) then return ← whole
    let some p ← diffEq prove budget as[i]! bs[i]! | return ← whole
    let ctx ← withLocalDeclD `z ta fun z => mkLambdaFVars #[z] (mkAppN fl (cur.set! i z))
    pf ← mkEqTrans pf (← mkCongrArg ctx p)
    cur := cur.set! i bs[i]!
  return some pf

end Blaster.Reconstruct.SmtProof.Local

namespace Blaster.Reconstruct.SmtProof.Local

/-- Arithmetic and propositional structure, traversed by `arithAtoms`. -/
def isArithHead (e : Expr) : Bool :=
  let ops := #[(``HAdd.hAdd, 6), (``HSub.hSub, 6), (``HMul.hMul, 6), (``HDiv.hDiv, 6), (``HMod.hMod, 6),
    (``Neg.neg, 3), (``LE.le, 4), (``LT.lt, 4), (``GE.ge, 4), (``GT.gt, 4), (``Nat.cast, 3), (``Int.toNat, 1),
    (``Int.natAbs, 1), (``And, 2), (``Or, 2), (``Not, 1), (``Iff, 2), (``ite, 5), (``Int.add, 2), (``Int.mul, 2),
    (``Int.neg, 1), (``Int.sub, 2), (``Nat.add, 2), (``Nat.mul, 2), (``Nat.sub, 2), (``Int.ediv, 2), (``Int.emod, 2),
    (``Nat.div, 2), (``Nat.mod, 2), (``Nat.succ, 1)]
  ops.any fun (n, k) => e.isAppOfArity n k

/-- Maximal subterms of `e` that are not arithmetic or propositional structure (arithmetic atoms), i.e., the
    terms that linear arithmetic tactics treat as variables. -/
partial def arithAtoms (e : Expr) : MetaM (Array Expr) := do
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← IO.mkRef (#[] : Array Expr)
  let rec go (e : Expr) : MetaM Unit := do
    if (← visited.get).contains e then return
    visited.modify (·.insert e)
    if isAtomic e || e.hasLooseBVars then
      if let .forallE _ t b _ := e then go t; go b
      return
    if e.isAppOfArity ``Eq 3 then
      go (e.getArg! 1); go (e.getArg! 2); return
    if isArithHead e then
      -- instances and types are not traversed
      let args := e.getAppArgs
      let info ← getFunInfoNArgs e.getAppFn args.size
      for i in [:args.size] do
        if info.paramInfo[i]?.any (·.isExplicit) then go args[i]!
      return
    match e with
    | .forallE _ t b _ => go t; go b
    | .mdata _ b => go b
    | _ =>
      if !(← isType e) && !(← isProof e) then found.modify (·.push e)
  go e
  found.get

/-- `(∀ zs, stmt[zs/atoms], atoms)` for the arithmetic atoms of `stmt` (see `arithAtoms`). -/
def generalizeAtoms (stmt : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let ss ← arithAtoms stmt
  if ss.isEmpty then return none
  let types ← ss.mapM inferType
  let decls := (ss.zip types).mapIdx fun i (_, t) => (Name.mkSimple s!"a{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun zs => do
    let m : Std.HashMap Expr Expr := (ss.zip zs).foldl (fun m (s, z) => m.insert s z) {}
    let (stmt', _) := (replaceAll m stmt).run {}
    let g ← mkForallFVars zs stmt'
    if !(← isTypeCorrect g) then return none
    return some (g, ss)

end Blaster.Reconstruct.SmtProof.Local
