# B10cd-asc-gen handoff

Done (WIP commit on this branch, builds green through Rel.Programs.Prelude and Rel.Lang.PreludeOrd):
- Rel/Run/Lang/Elab.lean: new `phVar` (object variable at a generic constant's placeholder) and `rowOrd`
  (just above `symObj`); `build`'s `.leq`/`.lt` take the row path only when `rowOrd objs mc n df.isSome`, so at a
  placeholder with the prelude's `lt`/`le` in scope they go through `ordObj` + `Tm.cmpDef`; `ordObj` skips its
  `ascBad` refusal at a placeholder; the prim-row refusal at a placeholder now calls `phVar`.

Not done:
- `prelude.asc.body` is STILL `Tm (atom i64) (atom i64)` after the change (probe: tmp/Probe.lean).
  `>` has no constant of its own (`prelude.«>»` is a `Decl` with no `.body`): it is expanded into asc's body, so the
  `.lt` node is elaborated inside asc's `once` (Rel/Run/Lang/Expand.lean `once`, ~line 365-425). The run with
  asc's β generic (`fl.set i (true, true)`) must still fail, and its error is swallowed by
  `tryCatch ... fun _ => pure none` (Expand.lean ~line 424). Next step: surface that error (temporarily) to see
  which node refuses β at its placeholder (candidates: `Pre.numsAt` `.lt` at `.base` via `numCheck`/`Use.check`,
  `uniTm` of β, the lt call's `callTm`, `primsFit`).
- Then re-prove `Tm.ascDef_den` (Rel/Lang/PreludeOrd.lean) at every object via `Tm.gt_of_lt` + `Tm.ltDef_den`,
  build DfnLaw, PreludeDfn, PreludeOrd, PreludeDen, Test.Orders, TestAsc, TestCmpMeet, Test.Prelude; update
  doc/tm-minimal-design.zh.typ line 122 (`asc(P)` row) and recompile its PDF.
