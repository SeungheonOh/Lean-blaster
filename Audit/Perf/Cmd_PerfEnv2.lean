import Blaster
open Lean Elab Command Blaster.Optimize in
#eval show Lean.Elab.Term.TermElabM Unit from do
  let t0 ← IO.monoMsNow
  for _ in [0:20] do
    let (r, _) ← (findLocalAxioms).run default
    if r.length > 0 then IO.println "x"
  let t1 ← IO.monoMsNow
  IO.println s!"findLocalAxioms avg ms: {(t1 - t0) / 20}"
