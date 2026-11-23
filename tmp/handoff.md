# B10c2 handoff (worktree agent-aaf0133cb02dd7fc4)

Done (committed): RelRun green; Rel/Lang/PreludeDfn.lean (Tm.<sym>Def, Tm.<sym>Def_den for flat foldI dom ran nil front)
imported in PreludeDen (green, gate check passes); Prelude.lean builds (foldI text must be on ONE line: a continuation
line after `≜` is not read); Env.defOf (Elab.lean) finds the fold start's `ran` while the prelude is elaborated;
ranRow's argument form is `none` (read whole, as the old `applied .ran`).

WIP (uncommitted before the WIP commit): Prim.openSrc (Syntax.lean) + Pre.nilSrcs reads `.prim` rows with it, so a
`nil` used as a row still defaults its open source to `1` (settleOpen). `nil(1)` in Programs/Edit.lean and
Programs/Knapsack.lean rewritten to `nil`.
NOTE: `lake build RelRun` did not relink librel_Rel_Run.so (.so older than Syntax.olean), so a `lean` probe
(/data/tmp/hb10c2-open.lean, lists rows with openSrc) still ran the OLD compiled code; first version of openSrc
(no prelude test) also selected asc $ sqrt neg abs ... and broke TestGenericNum (`length`'s target became 1). The
current version (prelude.isSome && no params && source var not in target) must be verified by a full build of
`RelRun Rel` (target the .so: `lake build RelRun:shared` or the lib's facet) and TestGenericNum.

Left (errors of the last full build, build7, with the first openSrc):
- test programs without the prelude use dom/ran now: add `open Rel.Programs.prelude in` before the `rel_program`
  (TestFloatObj 14, 77(#guard_msgs in … open … in); TestFloatArith 10, 36, 77, 143) — "unknown name 'dom'".
- Rel/Programs/Edit.lean:8 (line 71 col 54) and Rel/Lang/Test/Orders.lean:8 (line 17 col 46):
  "⊤'s target: [..] has no universe" — check whether still failing after openSrc is right.
- TestGenericNum (63..141), FrameGroup:39: "length's definition (dfns) has no form at [i64] ⟶ 1", "$ from 1 (no atom) to ψ" —
  caused by the over-broad openSrc; re-check after the fix.
- then `lake build RelRun Rel`, commit `B10c2: …`, re-time Test/Folds Test/Lists Test/Orders TestGenericNum
  (baselines 0.94 1.95 0.64 0.82 s), check TestGenericNum.lean:133 avgS.
Log of the last full build: /data/tmp/hb10c2-build7.log
