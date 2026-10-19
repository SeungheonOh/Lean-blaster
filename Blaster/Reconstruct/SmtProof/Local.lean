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

theorem classical_ite_congr {α : Sort u} {c c' : Prop} {x x' y y' : α} (hc : c = c') (hx : x = x') (hy : y = y') :
    @ite α c (Classical.propDecidable c) x y = @ite α c' (Classical.propDecidable c') x' y' := by
  subst hc hx hy; rfl

theorem classical_decide_congr {p p' : Prop} (h : p = p') :
    @decide p (Classical.propDecidable p) = @decide p' (Classical.propDecidable p') := by
  subst h; rfl

/-- `ite c x y = ite c' x' y'` (with the classical instances of the interpretation, whose argument depends on
    the condition), given the proofs of the equalities of the arguments (`sub`); similarly for `decide`. -/
def iteCongr? [Monad m] [MonadLiftT MetaM m] (l r : Expr) (sub : Expr → Expr → m (Option Expr)) : m (Option Expr) := do
  if l.isAppOfArity ``Decidable.decide 2 && r.isAppOfArity ``Decidable.decide 2 then
    if (l.getArg! 1).isAppOfArity ``Classical.propDecidable 1 && (r.getArg! 1).isAppOfArity ``Classical.propDecidable 1 then
      let some h ← sub (l.getArg! 0) (r.getArg! 0) | return none
      return some (mkApp3 (mkConst ``classical_decide_congr) (l.getArg! 0) (r.getArg! 0) h)
    return none
  if !(l.isAppOfArity ``ite 5 && r.isAppOfArity ``ite 5) then return none
  let la := l.getAppArgs
  let ra := r.getAppArgs
  if !(la[2]!.isAppOfArity ``Classical.propDecidable 1 && ra[2]!.isAppOfArity ``Classical.propDecidable 1) then return none
  if la[0]! != ra[0]! then return none
  let some pc ← (if la[1]! == ra[1]! then liftM (mkEqRefl la[1]!) >>= (pure ∘ some) else sub la[1]! ra[1]!) | return none
  let some px ← (if la[3]! == ra[3]! then liftM (mkEqRefl la[3]!) >>= (pure ∘ some) else sub la[3]! ra[3]!) | return none
  let some py ← (if la[4]! == ra[4]! then liftM (mkEqRefl la[4]!) >>= (pure ∘ some) else sub la[4]! ra[4]!) | return none
  let u ← liftM (getLevel la[0]!)
  return some (mkAppN (mkConst ``classical_ite_congr [u]) #[la[0]!, la[1]!, ra[1]!, la[3]!, ra[3]!, la[4]!, ra[4]!, pc, px, py])

/-- Whether `e` has at most `n` nodes (as a tree), without traversing more than `n` nodes. -/
def sizeLe (e : Expr) (n : Nat) : Bool :=
  (go e n).isSome
where
  go (e : Expr) (fuel : Nat) : Option Nat :=
    if fuel == 0 then none else
    match e with
    | .app f a => go f (fuel - 1) >>= go a
    | .lam _ t b _ | .forallE _ t b _ => go t (fuel - 1) >>= go b
    | .letE _ t v b _ => go t (fuel - 1) >>= go v >>= go b
    | .mdata _ b | .proj _ _ b => go b (fuel - 1)
    | _ => some (fuel - 1)

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

/-- Comparisons of integers and natural numbers, kept visible to the arithmetic tactics (e.g., the conditions
    of conditionals rewritten under these conditions, such as `if 0 = x then 2 + x else ...` into `2`). -/
def isArithComparison (e : Expr) : Bool :=
  let numeric (t : Expr) := t.isConstOf ``Int || t.isConstOf ``Nat
  (e.isAppOfArity ``Eq 3 && numeric (e.getArg! 0)) || (e.isAppOfArity ``LE.le 4 && numeric (e.getArg! 0)) ||
  (e.isAppOfArity ``LT.lt 4 && numeric (e.getArg! 0))

/-- Maximal subterms of `l` that also occur in `r` (and are neither atomic, types nor arithmetic comparisons). -/
partial def commonSubterms (l r : Expr) : MetaM (Array Expr) := do
  let inR := closedSubterms r {}
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← IO.mkRef (#[] : Array Expr)
  let rec go (e : Expr) : MetaM Unit := do
    if (← visited.get).contains e then return
    visited.modify (·.insert e)
    if !e.hasLooseBVars && !isAtomic e && !isArithComparison e && inR.contains e then
      -- values and propositions (not types, partial applications, nor instances, which tactics must see)
      let ty ← whnfR (← inferType e)
      if !(ty.isSort && !ty.isProp) && !ty.isForall && (← isClass? ty).isNone then
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
  -- NOTE: the types are unfolded to their inductive types (e.g., `Value := List (Data × Data)`), such that tactics
  -- can perform case analyses on the variables
  let types ← ss.mapM fun s => do
    let t ← inferType s
    let t' ← whnfD t
    if let .const n _ := t'.getAppFn then
      if (← getEnv).find? n matches some (.inductInfo _) then return t'
    return t
  let decls := (ss.zip types).mapIdx fun i (_, t) => (Name.mkSimple s!"z{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun zs => do
    let m : Std.HashMap Expr Expr := (ss.zip zs).foldl (fun m (s, z) => m.insert s z) {}
    let (stmt', _) := (replaceAll m stmt).run {}
    let g ← mkForallFVars zs stmt'
    if !(← isTypeCorrect g) then return none
    return some (g, ss)

/-- Leaves of the maximal tree of applications of the binary operation `op` (e.g., `And`) at the root of `e`. -/
partial def opLeaves (op : Name) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity op 2 then opLeaves op e.appArg! (opLeaves op e.appFn!.appArg! acc) else acc.push e

/-- Whether the trees of `op` applications at the roots of `l` and `r` have the same shape. -/
partial def sameOpShape (op : Name) (l r : Expr) : Bool :=
  match l.isAppOfArity op 2, r.isAppOfArity op 2 with
  | true, true => sameOpShape op l.appFn!.appArg! r.appFn!.appArg! && sameOpShape op l.appArg! r.appArg!
  | false, false => true
  | _, _ => false

/-- `e` with the leaves of its tree of `op` applications replaced by `f`. -/
partial def mapOpLeaves (op : Name) (f : Expr → Expr) (e : Expr) : Expr :=
  if e.isAppOfArity op 2 then mkApp2 e.appFn!.appFn! (mapOpLeaves op f e.appFn!.appArg!) (mapOpLeaves op f e.appArg!)
  else f e

/-- `e = e'` where `e'` is `e` with the leaves of its tree of `op` applications rewritten with `proofs`. -/
partial def congrLeaves (op : Name) (proofs : Std.HashMap Expr Expr) (e : Expr) : MetaM Expr := do
  if e.isAppOfArity op 2 then
    let pa ← congrLeaves op proofs e.appFn!.appArg!
    let pb ← congrLeaves op proofs e.appArg!
    return ← mkCongr (← mkCongrArg e.appFn!.appFn! pa) pb
  match proofs.get? e with
  | some p => return p
  | none => mkEqRefl e

/-- Arithmetic operations, whose arguments are reordered and combined by the arithmetic normalizations
    of the solvers (e.g., Z3 sorting the summands and folding the constants). -/
def isArithOp (e : Expr) : Bool :=
  e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``HMul.hMul 6 ||
  e.isAppOfArity ``Neg.neg 3

mutual
/-- Proof of `l = r` by congruence on the common structure of `l` and `r`, proving the remaining
    differences with `prove` (given the equality to prove, returns a proof). At most `budget` calls of
    `prove`. Conjunctions and disjunctions are compared modulo associativity and unit elements (e.g., the
    flattening of n-ary connectives by Z3's rewriter). -/
partial def diffEq (prove : Expr → TermElabM (Option Expr)) (budget : IO.Ref Nat) (l r : Expr) : TermElabM (Option Expr) := do
  if l == r then return some (← mkEqRefl l)
  for op in [``And, ``Or] do
    if (l.isAppOfArity op 2 || r.isAppOfArity op 2) && !sameOpShape op l r then
      if let some p ← acEq prove budget op l r then return some p
  let whole : TermElabM (Option Expr) := do
    if (← budget.get) == 0 then return none
    budget.modify (· - 1)
    prove (← mkEq l r)
  -- normalized arithmetic: the congruence on the arguments would mostly produce false differences
  if isArithOp l && isArithOp r && sizeLe l 400 && sizeLe r 400 then return ← whole
  let fl := l.getAppFn
  let fr := r.getAppFn
  if !l.isApp || !r.isApp || fl != fr || l.getAppNumArgs != r.getAppNumArgs then
    match l, r with
    | .forallE n t b bi, .forallE _ t' b' _ =>
        if (t == t' || (← isDefEq t t')) && (b.hasLooseBVars || b'.hasLooseBVars) && (← isProp l) then
          let r? ← withLocalDecl n bi t fun x => do
            let some p ← diffEq prove budget (b.instantiate1 x) (b'.instantiate1 x) | return none
            return some (← mkAppM ``forall_congr #[← mkLambdaFVars #[x] p])
          if r?.isSome then return r?
        else if !b.hasLooseBVars && !b'.hasLooseBVars then
          let some pt ← diffEq prove budget t t' | return ← whole
          let some pb ← diffEq prove budget b b' | return ← whole
          return some (← mkAppM ``implies_congr #[pt, pb])
      | .lam n t b bi, .lam _ t' b' _ =>
        if t == t' || (← isDefEq t t') then
          let r? ← withLocalDecl n bi t fun x => do
            let some p ← diffEq prove budget (b.instantiate1 x) (b'.instantiate1 x) | return none
            return some (← mkFunExt (← mkLambdaFVars #[x] p))
          if r?.isSome then return r?
      | _, _ => pure ()
    return ← whole
  -- conditionals (the instance depends on the condition)
  if let some p ← iteCongr? l r (diffEq prove budget) then return some p
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

/-- `l = r` for trees of `op` applications of different shapes: the leaves of `l` (except the unit
    element, and the duplicates) are paired with the leaves of `r` in order and proved equal (`diffEq`),
    then `l` with the leaves of `r` is proved equal to `r` with the leaves generalized (`prove`). -/
partial def acEq (prove : Expr → TermElabM (Option Expr)) (budget : IO.Ref Nat) (op : Name) (l r : Expr) :
    TermElabM (Option Expr) := do
  let unit := if op == ``And then ``True else ``False
  let dedup (xs : Array Expr) : Array Expr := xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]
  let ls := dedup ((opLeaves op l).filter (!·.isConstOf unit))
  let rs := (opLeaves op r).filter (!·.isConstOf unit)
  if ls.size != rs.size || ls.isEmpty then return none
  -- leaves of `l` rewritten into the leaves of `r`
  let mut m : Std.HashMap Expr Expr := {}
  let mut proofs : Std.HashMap Expr Expr := {}
  for (x, y) in ls.zip rs do
    m := m.insert x y
    if x != y then
      let some p ← diffEq prove budget x y | return none
      proofs := proofs.insert x p
  let l' := mapOpLeaves op (fun x => m.getD x x) l
  -- `l = l'` by congruence (the differences are the leaves)
  let p₁ ← if proofs.isEmpty then mkEqRefl l else congrLeaves op proofs l
  -- `l' = r`: associativity, units and duplicates (the leaves are generalized)
  if l' == r then return some p₁
  if (← budget.get) == 0 then return none
  budget.modify (· - 1)
  let some p₂ ← prove (← mkEq l' r) | return none
  return some (← mkEqTrans p₁ p₂)
end

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
      let ty ← whnfR (← inferType e)
      if !(ty.isSort && !ty.isProp) && !ty.isForall && !(← isProof e) && (← isClass? ty).isNone then
        found.modify (·.push e)
  go e
  found.get

/-- Datatype terms of the propositional structure of `e` examined by a theory lemma: the sides of equalities and the
    arguments of testers (`casesOn` or recursors into propositions), through constructor applications, when they are
    not variables. -/
partial def datatypeAtoms (e : Expr) : MetaM (Array Expr) := do
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← IO.mkRef (#[] : Array Expr)
  let isInductive (t : Expr) : MetaM Bool := do
    let .const n _ := (← whnfD t).getAppFn | return false
    -- NOTE: arithmetic terms are left to the arithmetic tactics
    if n == ``Int || n == ``Nat then return false
    return (← getEnv).find? n matches some (.inductInfo _)
  let rec term (x : Expr) : MetaM Unit := do
    if (← visited.get).contains x || x.hasLooseBVars || isAtomic x then return
    visited.modify (·.insert x)
    if let .const c _ := x.getAppFn then
      if let some (.ctorInfo info) := (← getEnv).find? c then
        for a in x.getAppArgs.extract info.numParams x.getAppNumArgs do term a
        return
    if ← isInductive (← inferType x) then found.modify (·.push x)
  let rec prop (e : Expr) : MetaM Unit := do
    if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 then
      prop e.appFn!.appArg!; prop e.appArg!
    else if e.isAppOfArity ``Not 1 then prop e.appArg!
    else if let .forallE _ t b _ := e then
      if !b.hasLooseBVars then prop t; prop b
    else if e.isAppOfArity ``Eq 3 then
      if (e.getArg! 0).isProp then prop (e.getArg! 1); prop (e.getArg! 2)
      else if ← isInductive (e.getArg! 0) then term (e.getArg! 1); term (e.getArg! 2)
    else if let some m ← matchMatcherApp? e (alsoCasesOn := true) then
      for d in m.discrs do term d
    else if let .const r _ := e.getAppFn then
      if let some (.recInfo info) := (← getEnv).find? r then
        if let some d := e.getAppArgs[info.getMajorIdx]? then term d
  prop e
  found.get

/-- `(∀ zs, stmt[zs/atoms], atoms)` for the datatype terms of `stmt` (see `datatypeAtoms`), e.g., for datatype lemmas
    whose premises relate different terms (`¬ is-nil a → ¬ is-cons b → a = b → False`). -/
def generalizeDatatypeAtoms (stmt : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let ss ← datatypeAtoms stmt
  if ss.isEmpty then return none
  let types ← ss.mapM fun s => do
    let t ← inferType s
    let t' ← whnfD t
    if let .const n _ := t'.getAppFn then
      if (← getEnv).find? n matches some (.inductInfo _) then return t'
    return t
  let decls := (ss.zip types).mapIdx fun i (_, t) => (Name.mkSimple s!"d{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun zs => do
    let m : Std.HashMap Expr Expr := (ss.zip zs).foldl (fun m (s, z) => m.insert s z) {}
    let (stmt', _) := (replaceAll m stmt).run {}
    let g ← mkForallFVars zs stmt'
    if !(← isTypeCorrect g) then return none
    return some (g, ss)

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

namespace Blaster.Reconstruct.SmtProof.Local

/-- Propositional structure, traversed by `propAtoms`. -/
def isPropHead (e : Expr) : Bool :=
  e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Not 1 || e.isAppOfArity ``Iff 2 ||
  e.isConstOf ``True || e.isConstOf ``False ||
  (e.isAppOfArity ``Eq 3 && (e.getArg! 0).isProp) || (e.isAppOfArity ``ite 5 && (e.getArg! 0).isProp)

/-- Maximal subterms of `e` that are not propositional structure (propositional atoms). -/
partial def propAtoms (e : Expr) : MetaM (Array Expr) := do
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← IO.mkRef (#[] : Array Expr)
  let rec go (e : Expr) : MetaM Unit := do
    if (← visited.get).contains e then return
    visited.modify (·.insert e)
    if e.hasLooseBVars then return
    if isPropHead e then
      if e.isAppOfArity ``ite 5 then go (e.getArg! 1); go (e.getArg! 3); go (e.getArg! 4)
      else if e.isAppOfArity ``Eq 3 then go (e.getArg! 1); go (e.getArg! 2)
      else for a in e.getAppArgs do go a
      return
    match e with
    | .forallE _ t b _ => if !b.hasLooseBVars then go t; go b else found.modify (·.push e)
    | .mdata _ b => go b
    | _ => if (← isProp e) then found.modify (·.push e)
  go e
  found.get

/-- `(∀ zs, stmt[zs/atoms], atoms)` for the propositional atoms of `stmt` (see `propAtoms`). -/
def generalizePropAtoms (stmt : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let ss ← propAtoms stmt
  if ss.isEmpty then return none
  let decls := ss.mapIdx fun i _ => (Name.mkSimple s!"p{i}", fun (_ : Array Expr) => pure (mkSort levelZero))
  withLocalDeclsD decls fun zs => do
    let m : Std.HashMap Expr Expr := (ss.zip zs).foldl (fun m (s, z) => m.insert s z) {}
    let (stmt', _) := (replaceAll m stmt).run {}
    let g ← mkForallFVars zs stmt'
    if !(← isTypeCorrect g) then return none
    return some (g, ss)

end Blaster.Reconstruct.SmtProof.Local
