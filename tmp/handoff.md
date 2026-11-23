# 8.2e handoff

Branch merged with fb4ab1a (8.2d) with no conflict (auto-merged EmitC, TestNative, Expand, Table).

## Done (RelRun builds green: `lake build RelRun`, 242 jobs)
- `Rel/Run/List.lean`: `Vals.pack` -> `ValsB.pack` generic over `o`; at `o = true` an `arr` keeps its cells and packs only
  its payload (null bounds of the other summand's rows are read by no width/prefix sum); `Tab.pack` calls it.
  `cells/tau/cat/zip` stay `Vals` (only called at `o = false`).
- `Rel/Run/Lang/Plan.lean`: `ColB.toOpt` (new), `cols` generic over `o`.
- `Rel/Run/Lang/Gen.lean`: new `Gen.opt`, `Gen.colB o`; `pairV arrV sumV optV oneV` take `o` first.
- `Rel/Run/Lang/Expand.lean`: `colE` (new), `valsE`/`valsEq` generic over `o` (summand columns rebuilt at `true`);
  `Rel/Run/Lang/TmGen.lean` calls `valsE false`.
- `Rel/Run/Table.lean`: `symIds` states `Arr.enc (t := .sym)` (the abbrev `Vals.enc` defeated `generalize`);
  `readVals`/`encVals` wrap the two summands in `Vals.lift` (ownership mask is the later package).
- `injCols_ok` (master RepStruct:407) users on master: `Tab.inl_holds`, `Tab.inr_holds` only; `Rel.injCols` itself is not
  in the 8.2d `Run/Struct.lean` any more, so restore only if `inl_holds`/`inr_holds` are re-proved via it (not needed by
  the dense `Vals.zeros` design).

## Left (proof side, nothing started)
`lake build Rel.RepCanon` first errors (log /data/tmp/e82e-b6.log):
- `Rel/RepCanon.lean:390:109`, `394:4`, `394:41 Unknown constant Rel.Vals.view_go_cast`, `397`, `398`, `426`, `435
  Unknown constant Rel.Vals.view_ofOpt`, `444`, `468`, `477`, `478`, `491`, `521`, `989`, `998`, `1018`, `1049`, `1082`,
  `1097 Unknown constant Rel.Vals.cols_arr`, `1218`, `1231`, `1408` (lemma names were renamed `Vals.* -> ValsB.*` in Core/Canon;
  the proofs still say `Vals.view_ofOpt`, `Vals.view_go_cast`, `Vals.cols_arr`, and the statements are over `Vals`, not `ValsB o`).
- Plan from the task: `Vals.WF` -> `ValsB.WFOn x P` (Opt leaf: `isNul i <-> ¬P i`; gen sum
  `(forall i, ¬P i -> tag.get i = false) /\ WFOn x (P /\ ¬tag) /\ WFOn y (P /\ tag)`; `Vals.WF x := x.WFOn (fun _ => True)`),
  then RepCols, RepStruct (`Vals.zeros_ok`, `ofGen_wf`, `none_wf`; delete `Arr.dflts_get`; add
  `Opt.fill t n = Opt.nuls t n` for `t != general`), RepTabDiv, RepWF (`pack_wf` filler clauses; `pack_row` in RepTabDiv uses
  the old `Vals.pack`, now `ValsB.pack`).
- Later (as scoped): read-check ownership mask in `readVals`/`encVals`, GenKBits/GenSound, EmitC nullable summands, tests,
  Core.lean test `tsum`.
