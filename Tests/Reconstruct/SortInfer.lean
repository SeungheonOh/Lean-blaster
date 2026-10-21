import Blaster

/-! # Sort inference on SMT proofs (`Blaster.Reconstruct.SmtProof.SortInfer`)

Z3 prints `List.nil` without its sort, and doesn't always print the occurrences of a term as one object: in the
proof below (the pattern of the replay of the first theorem of CardanoLedgerApiBlaster's `SellNFT`), the three
occurrences of `(List.cons.0 List.nil)` are distinct objects, and the first step (`th-lemma datatype`) determines
none of their instances. The instances are inferred on the whole proof: the occurrence shared with the `asserted`
step is a pair of `Int` and `Bool`, and the two occurrences of the eta-expansion only have one component known.
-/

namespace Tests.Reconstruct.SortInfer

open Blaster.Reconstruct.SmtProof

def query : String := "
(declare-datatype @List (par (|@α|) ((List.nil) (List.cons (List.cons.0 |@α|) (List.cons.1 (@List |@α|))))))
(declare-datatype @Prod (par (|@α| |@β|) ((Prod.mk (Prod.mk.0 |@α|) (Prod.mk.1 |@β|)))))
(declare-fun f (Int) (@List (@Prod Int Bool)))"

def proof : String := "
((proof
(let ((?x1 (Prod.mk (Prod.mk.0 (List.cons.0 List.nil)) (Prod.mk.1 (List.cons.0 List.nil)))))
(let ((?x2 (List.cons.0 List.nil)))
(let ((@p1 ((_ th-lemma datatype) (= ?x2 ?x1))))
(let ((@p2 (asserted (= ?x2 (List.cons.0 (f 0))))))
(let ((@p3 (trans* (symm @p1 (= ?x1 ?x2)) @p2 (= ?x1 (List.cons.0 (f 0))))))
(unit-resolution @p3 (asserted (not (= ?x1 (List.cons.0 (f 0))))) false))))))))"

partial def hintString : SortInfer.Hint → String
  | .unknown => "?"
  | .con n #[] => n
  | .con n args => "(" ++ n ++ " " ++ " ".intercalate (args.toList.map hintString) ++ ")"

/-- The hints of the subterms of `t` (in order). -/
partial def hintsOf (hints : TermCache SortInfer.Hint) (t : STerm) (acc : Array String := #[]) : Array String :=
  let acc := match hints.get? (termAddr t) with
    | some h => acc.push (hintString h)
    | none => acc
  match t with
  | .app _ args | .iapp _ _ args | .qual _ _ args => args.foldl (fun a x => hintsOf hints x a) acc
  | .annot x _ => hintsOf hints x acc
  | .quant _ _ b => hintsOf hints b acc
  | _ => acc

/-- The hints of the conclusion of the `th-lemma` step, which alone doesn't determine any instance. -/
def thLemmaHints : Except String (Array String) := do
  let cmds ← parseSExprs query
  let p ← Z3.parseProof proof
  let (hints, conflicts) := SortInfer.inferHints cmds p
  if conflicts != 0 then throw s!"{conflicts} unification failures"
  let some step := p.steps.find? (·.rule == "th-lemma") | throw "no th-lemma step"
  return hintsOf hints step.concl

/-- info: Except.ok #["(@List (@Prod Int Bool))", "(@List (@Prod Int ?))", "(@List (@Prod ? Bool))"] -/
#guard_msgs in
#eval thLemmaHints

end Tests.Reconstruct.SortInfer
