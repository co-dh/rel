# 8.2g handoff (worktree-agent-aaaa6a518eeef745f, commit "8.2g (part)")

## Done
- `git merge 088fb5c` (keep-82f) onto master 4854bf8. One conflict, `Rel/RepStruct.lean` ~:497: master's `injCols_ok` is dropped
  (`injCols` no longer exists in `Rel/Run/Struct.lean`: dense design), `Opt.nuls_get` already sits at the top of the file.
- `Rel/RepCanon.lean` builds green (`lake build Rel.RepCanon`):
  - `ValsB.WFOn` band clause strengthened: `.opt _ x => ∀ i, ¬P i → x.get i = none` (a band summand's unowned rows are null);
    `WFOn_congr`, `gather_wf` (opt case via `Opt.gather_row`) follow. At `Vals.WF` (P = True) the clause is vacuous.
  - New: `ColB.enc_wf`, `ValsB.cols_wf` (was `Vals.cols_wf`), `Opt.get_i64`, `ColB.Flat` (no row flagged null),
    `ColB.get_i64`, `ColB.owned_of_flat`, `Opt.get_eq_of_getD`, `noNul_flags`, `Verify.ascCol_cells_flags`
    (`ascCol` of a `cells` key answers only past `noNul` of `lo` and `hi`).
  - Restated over `ValsB o` with an owned set `P`: `ValsB.cell_le`, `ValsB.row_arr`, `Vals.row_empty` (generalised, name kept),
    `ValsB.cols_arr` (now also returns `ColB.Flat lo`, `ColB.Flat hi`, and the cell law only for `P i`, `P i'`),
    `ValsB.row_of_codes x P hw hes hc i i' hp hp' hk`, `ValsB.codes_of_row x P hw ... hp hp' hr`,
    new `ValsB.codes_of_unowned` (two unowned rows of a summand have equal codes; an `arr` summand has none since
    `kasc` needs a null-free `lo`). `Vals.seenKey_iff_row` calls them at `P = fun _ => True`.
  - Removed names that callers must now spell: `Vals.cols_wf` -> `ValsB.cols_wf`, `Vals.row_of_codes` / `Vals.codes_of_row`
    -> `ValsB.row_of_codes x (fun _ => True) hw hes hc i i' trivial trivial`, `Vals.cell_le`/`Vals.row_arr` ->
    `ValsB.cell_le hlo hhi hw i hp` / `ValsB.row_arr hlo hhi i (hw.2.2.1 i hp)`, `ValsB.cols_arr` has a new shape.

## Left (first errors, log /data/tmp/h82g-canon.log from
`CAP_MEM_MB=20000 /home/dh/repo/freyd/scripts/cap lake -d <wt> build Rel.RepCanon Rel.RepCols Rel.RepStruct Rel.RepTabDiv Rel.RepWF`)
- `Rel/RepOrder.lean` (downstream of RepCanon, not in the task's list):
  - `:159` `Unknown constant Rel.Vals.row_of_codes`, `:162` `Unknown constant Rel.Vals.cols_arr`,
    `:240` `Unknown constant Rel.Vals.cols_sum` (it is `ValsB.cols_sum`, `ValsB.cols_arr`): same restatement as
    `ValsB.codes_of_row` (the order law `Vals.lt_of_codes` needs `P` and ownership the same way).
- `Rel/RepCols.lean`:
  - `:604` `cellBad_none.mp h.left` has type `∀ i, 0 ≤ ... ` but `fst✝¹.OwnedOn fun x => True` is expected: the arr `WF`
    triple is now `⟨OwnedOn lo, OwnedOn hi, bounds, WFOn f⟩` (for `o = false` the first two are `True`, so `trivial`),
    i.e. `⟨trivial, trivial, cellBad_none.mp h.left, ...⟩`; `:605` goal `ValsB.WFOn s fun x => True` in the band case:
    `fun i hn => absurd trivial hn`.
  - `:619` `Unknown constant Rel.Vals.gather_wf` -> `ValsB.gather_wf ... (fun _ => True)` then `ValsB.WFOn_congr`.
  - `:663` `concat_row ... hx.right` expects `WF f₁`, gets the arr triple: use `hx.2.2.2`; `:672`, `:680`
    `hx.left ⟨c.1, hc⟩` -> bounds are `hx.2.2.1 i trivial`.
  - `:704`, `:782` `Unknown constant Rel.Vals.view_ofOpt` -> `ValsB.view_ofOpt`; `:794` `Vals.view_ofGen` -> `ValsB.view_ofGen`;
    `:705` `rfl` failed on `Obj.optEl h (x.get c)` vs the `dite` of the concat row; `:718` invalid projection on the sum
    `WF` (now a `match s.view` that must be unfolded with `simp only [Vals.WF, ValsB.WFOn, hv]`); `:761`-`:797`.
- Not started: `Rel/RepStruct.lean` (`zeros_ok`, `ofGen_wf`, `none_wf`, delete `Arr.dflts_get`, `Opt.fill t n = Opt.nuls t n`
  for `t ≠ general`), `Rel/RepWF.lean` (`pack_wf` filler clauses), `Rel/RepTabDiv.lean` (`pack_row` for `ValsB.pack`),
  then `lake build RelRun Rel`.
- Part 2 (native on the dense design: `nativeIO` gmi, gxi, nd, gy, gz, gw; EmitC `ownSideB`/`ownCountsB`/`colsOf`; build
  `Rel.Lang.EmitC Rel.Lang.TestNative relc rel-native`; `/data/tmp/m82g-gate.sh` from `/data/tmp/m8c11-gate.sh`) NOT started.
  Note: master's adf496f rule (a summand `1` count from the tag) was dropped by 8.2f's dense `Plan.cols`; native must read
  and write what the dense in-memory `ValsB true` writes via `Plan.cols`.
