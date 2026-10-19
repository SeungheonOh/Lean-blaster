import Lean
import Blaster.Reconstruct.Proof

open Lean Meta

namespace Blaster.Reconstruct

/-! # Bounding the depth of proof terms

Balanced transitivity chains (see `joinChains`) keep the depth of the evidence of long sequences of
rewrites logarithmic. However, the evidence of a rewrite performed on an argument is nested in a
congruence over the enclosing application (e.g., `congrArg (fun x => n + x) p`). Hence, the evaluation
of a recursive function whose recursive calls are not in tail position (e.g., `f (n+1) := n + f n`)
yields a proof term whose depth is linear in the number of recursive calls.

The proof term is therefore post-processed (before discharging the proof obligations and before kernel
checking) such that subproofs nested too deeply are shared through `let` declarations, i.e., the proof
`C₁[C₂[...Cₙ[p]...]]` becomes `let h₁ := p; let h₂ := Cₙ[h₁]; ...; C₁[hₙ]`. A `let` telescope is
checked iteratively by the kernel and by `Meta.inferType`/`Meta.check` (the value of each declaration
being checked separately), such that the recursion depth needed to check the proof is bounded by the
maximal depth of a value (i.e., `maxProofDepth`) instead of the depth of the original proof.

The declarations are introduced in the innermost binder scope (or fallback region, see `fallbackKey`)
containing the shared subproof, such that free variables of enclosing binders are in scope.
The traversal is iterative within a scope (i.e., it only recurses over binders), such that it does
not overflow the stack itself on deep proof terms.
-/

/-- User name of the `let` declarations introduced by `shareDeepProofs`. -/
def sharedProofName : Name := `_blaster_pf

/-- Maximum nesting depth of proof constructions (i.e., nested proofs) in a shared subproof. -/
def maxProofDepth : Nat := 128

/-- Return `true` if `d` is a declaration introduced by `shareDeepProofs`. -/
@[inline] def isSharedProofDecl (d : LocalDecl) : Bool :=
  d.isLet && d.userName == sharedProofName

/-- Execute `x` in a local context without the declarations introduced by `shareDeepProofs`, i.e., such
    that tactics (e.g., `simp [*]`, `cases`) are not affected by them.
    NOTE: proof obligations never refer to such declarations, as they only bind subproofs.
-/
def withoutSharedProofs [MonadLiftT MetaM m] [MonadControlT MetaM m] [Monad m] (x : m α) : m α := do
  let lctx ← (getLCtx : MetaM _)
  if !lctx.any isSharedProofDecl then return ← x
  let lctx' := lctx.foldl (init := lctx) fun acc d => if isSharedProofDecl d then acc.erase d.fvarId else acc
  withLCtx lctx' (← (getLocalInstances : MetaM _)) x

namespace ShareDeep

/-- Return `true` if `n` is a theorem (i.e., all its applications are proofs). -/
def isTheoremName (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

/-- Return `true` if `e` (an application or metadata node) is known to be a proof, i.e., an application of a
    theorem, a chain node, a proof obligation or a fallback region.
-/
def isProofNode (env : Environment) (e : Expr) : Bool :=
  match e with
  | .mdata d _ => d.contains chainKey || d.contains holeKey || d.contains fallbackKey
  | _ =>
    match e.getAppFn with
    | .const n _ => isTheoremName env n
    | .fvar .. => false
    | _ => false

/-- Return `true` if `e` is a candidate for sharing that requires a type check (i.e., a proof built
    with a definition such as `Eq.mpr` or `id`, or a lambda abstraction over a proof).
-/
def isMaybeProofNode (e : Expr) : Bool :=
  match e with
  | .lam .. => true
  | _ => e.isAppOf ``Eq.mpr || e.isAppOf ``Eq.mp || e.isAppOf ``id

/-- Result of the traversal of a term. -/
structure Result where
  /-- The new term, in which the loose bound variables of the original term have been instantiated. -/
  expr : Expr
  /-- The number of nested proof constructions in `expr` (non-proof terms do not count). -/
  depth : Nat
  /-- `true` when a subproof of the original term has been shared. -/
  shared : Bool := false
deriving Inhabited

/-- A work item of the iterative traversal: a node and whether its children have been visited. -/
abbrev Item := Expr × Bool

/-- Return the number of nested proof constructions of each subterm of `e` (i.e., keyed by pointer),
    where proof obligations are leaves (see `scope`).
    NOTE: The traversal is iterative and each shared subterm is visited once (bound variables are not
    instantiated).
-/
unsafe def proofDepths (env : Environment) (e : Expr) : PtrMap Expr Nat := Id.run do
  let mut done : PtrMap Expr Nat := mkPtrMap
  let mut todo : Array Item := #[(e, false)]
  while !todo.isEmpty do
    let (x, expanded) := todo.back!
    todo := todo.pop
    if done.contains x then continue
    let cs : Array Expr := match x with
      | .app .. => #[x.getAppFn] ++ x.getAppArgs
      | .lam _ t b _ | .forallE _ t b _ => #[t, b]
      | .letE _ _ v b _ => #[v, b]
      | .mdata d b => if d.contains holeKey then #[] else #[b]
      | .proj _ _ b => #[b]
      | _ => #[]
    if !expanded && !cs.isEmpty then
      todo := todo.push (x, true)
      for c in cs do
        if !done.contains c then todo := todo.push (c, false)
      continue
    let d := cs.foldl (fun acc c => max acc ((done.find? c).getD 0)) 0
    done := done.insert x (if isProofNode env x then d + 1 else d)
  return done

/-- Traverse `e`, whose loose bound variables are interpreted by `subst` (i.e., `bvar i ↦ subst[i]!`),
    and share the subproofs whose proof depth exceeds `maxDepth` through `let` declarations placed in
    front of the result (see `shareDeepProofs`). `depths` is the proof depth of the subterms of the
    original term (see `proofDepths`), i.e., subterms that are not deep are not traversed.
    NOTE: The traversal is iterative, except for binders and fallback regions, which are traversed
    recursively as new scopes.
-/
unsafe def scope (env : Environment) (maxDepth : Nat) (depths : PtrMap Expr Nat) (e : Expr)
    (subst : Array Expr) : MetaM Result := do
  let insts ← getLocalInstances
  let mut lctx ← getLCtx
  let mut lets : Array Expr := #[]
  let mut done : PtrMap Expr Result := mkPtrMap
  let mut todo : Array Item := #[(e, false)]
  while !todo.isEmpty do
    let (x, expanded) := todo.back!
    todo := todo.pop
    if done.contains x then continue
    let get (c : Expr) (done : PtrMap Expr Result) : Result := (done.find? c).getD ⟨c, 0, false⟩
    if let some d := depths.find? x then
      if d ≤ maxDepth then
        -- no subproof of `x` has to be shared
        done := done.insert x ⟨x.instantiate subst, d, false⟩
        continue
    match x with
    | .bvar i =>
        let r := if h : i < subst.size then subst[i] else x
        done := done.insert x ⟨r, 0, false⟩
    | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. =>
        done := done.insert x ⟨x, 0, false⟩
    | .app .. =>
        let fn := x.getAppFn
        let args := x.getAppArgs
        if !expanded then
          todo := todo.push (x, true)
          if !done.contains fn then todo := todo.push (fn, false)
          for a in args do
            if !done.contains a then todo := todo.push (a, false)
          continue
        let fn' := get fn done
        let args' := args.map (get · done)
        let unchanged := ptrEq fn'.expr fn && (args'.zip args).all (fun (a', a) => ptrEq a'.expr a)
        let new := if unchanged then x else mkAppN fn'.expr (args'.map (·.expr))
        let d := args'.foldl (fun acc a => max acc a.depth) fn'.depth
        let sh := fn'.shared || args'.any (·.shared)
        let (r, lctx', lets') ← share new (if isProofNode env x then d + 1 else d) sh lctx lets
        lctx := lctx'; lets := lets'
        done := done.insert x r
    | .mdata md b =>
        if md.contains holeKey then
          -- proof obligation: a leaf, i.e., its type never refers to the declarations introduced
          -- here (see `withoutSharedProofs`)
          done := done.insert x ⟨x.instantiate subst, 1, false⟩
        else if md.contains fallbackKey then
          -- fallback region: its subproofs are shared within the region (see `fallbackKey`)
          let r ← withLCtx lctx insts (scope env maxDepth depths b subst)
          let new := if !r.shared && !x.hasLooseBVars then x else mkMData md r.expr
          let (r, lctx', lets') ← share new (r.depth + 1) r.shared lctx lets
          lctx := lctx'; lets := lets'
          done := done.insert x r
        else
          if !expanded then
            todo := todo.push (x, true)
            if !done.contains b then todo := todo.push (b, false)
            continue
          let b' := get b done
          let new := if ptrEq b'.expr b then x else mkMData md b'.expr
          let d := if isProofNode env x then b'.depth + 1 else b'.depth
          let (r, lctx', lets') ← share new d b'.shared lctx lets
          lctx := lctx'; lets := lets'
          done := done.insert x r
    | .proj n i b =>
        if !expanded then
          todo := todo.push (x, true)
          if !done.contains b then todo := todo.push (b, false)
          continue
        let b' := get b done
        let new := if ptrEq b'.expr b then x else mkProj n i b'.expr
        done := done.insert x ⟨new, b'.depth, b'.shared⟩
    | .lam n t b bi | .forallE n t b bi =>
        if !expanded then
          todo := todo.push (x, true)
          if !done.contains t then todo := todo.push (t, false)
          continue
        let t' := get t done
        let isLam := x.isLambda
        let r ← withLCtx lctx insts do
          withLocalDecl n bi t'.expr fun y => do
            let r ← scope env maxDepth depths b (#[y] ++ subst)
            let sh := t'.shared || r.shared
            -- NOTE: the original term is kept when no subproof has been shared
            if !sh && !x.hasLooseBVars then return ({ r with expr := x, depth := max t'.depth r.depth } : Result)
            let e' ← if isLam then mkLambdaFVars #[y] r.expr (usedLetOnly := false)
                     else mkForallFVars #[y] r.expr (usedLetOnly := false)
            return ({ expr := e', depth := max t'.depth r.depth, shared := sh } : Result)
        if isLam then
          let (r, lctx', lets') ← share r.expr r.depth r.shared lctx lets
          lctx := lctx'; lets := lets'
          done := done.insert x r
        else
          done := done.insert x r
    | .letE n t v b nondep =>
        if !expanded then
          todo := todo.push (x, true)
          if !done.contains t then todo := todo.push (t, false)
          if !done.contains v then todo := todo.push (v, false)
          continue
        let t' := get t done
        let v' := get v done
        let r ← withLCtx lctx insts do
          withLetDecl n t'.expr v'.expr (nondep := nondep) fun y => do
            let r ← scope env maxDepth depths b (#[y] ++ subst)
            let sh := t'.shared || v'.shared || r.shared
            if !sh && !x.hasLooseBVars then return ({ r with expr := x, depth := max v'.depth r.depth } : Result)
            let e' ← mkLetFVars #[y] r.expr (usedLetOnly := false) (generalizeNondepLet := false)
            return ({ expr := e', depth := max v'.depth r.depth, shared := sh } : Result)
        done := done.insert x r
  let res := (done.find? e).getD ⟨e, 0, false⟩
  if lets.isEmpty then return res
  let e' ← withLCtx lctx insts (mkLetFVars lets res.expr (usedLetOnly := false) (generalizeNondepLet := false))
  -- NOTE: the depth of the values of the declarations is bounded by `maxDepth`
  return ⟨e', res.depth, true⟩
where
  /-- Share `e` (with proof depth `d`) through a new `let` declaration when `d` exceeds `maxDepth`. -/
  share (e : Expr) (d : Nat) (shared : Bool) (lctx : LocalContext) (lets : Array Expr) :
    MetaM (Result × LocalContext × Array Expr) := do
    if d ≤ maxDepth then return (⟨e, d, shared⟩, lctx, lets)
    let known := isProofNode env e
    if !known && !isMaybeProofNode e then return (⟨e, d, shared⟩, lctx, lets)
    let type? ← withLCtx lctx (← getLocalInstances) do
      try
        let type ← inferType e
        if !known && !(← isProp type) then return none
        return some type
      catch _ => return none
    let some type := type? | return (⟨e, d, shared⟩, lctx, lets)
    let fvarId ← mkFreshFVarId
    let lctx := lctx.mkLetDecl fvarId sharedProofName type e (kind := .implDetail)
    let x := mkFVar fvarId
    return (⟨x, 1, true⟩, lctx, lets.push x)

/-- Implementation of `shareDeepProofs`. -/
unsafe def shareDeepProofsImpl (env : Environment) (maxDepth : Nat) (p : Expr) : MetaM Expr := do
  let depths := proofDepths env p
  -- NOTE: proofs that are not deep are returned unchanged
  if (depths.find? p).getD 0 ≤ maxDepth then return p
  return (← scope env maxDepth depths p #[]).expr

end ShareDeep

@[implemented_by ShareDeep.shareDeepProofsImpl]
opaque shareDeepProofsAux (env : Environment) (maxDepth : Nat) (p : Expr) : MetaM Expr

/-- Share the subproofs of `p` that are nested more than `maxDepth` proof constructions deep through
    `let` declarations (see the module documentation). The result is a proof of the same proposition.
-/
def shareDeepProofs (p : Expr) (maxDepth := maxProofDepth) : MetaM Expr := do
  shareDeepProofsAux (← getEnv) maxDepth p

end Blaster.Reconstruct
