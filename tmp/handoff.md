# perf11 handoff (checkpoint)

Done:
- Kernel-call counts per module: `/data/tmp/perf11/calls.tsv`, by gdb breakpoints on `qlean_k_*`
  (`/data/tmp/perf11/count.sh WORKTREE MODULE_PATH`, `/data/tmp/perf11/count.gdb`; the `while $_isvoid($_exitcode)`
  loop is needed: a hit in a second thread stops all-stop gdb outside `commands`).
- Op-level counts on Knapsack (`/data/tmp/perf11/ops.gdb`, symbols `lp_rel_Rel_*`): colMap 138586, colConst 73676,
  Vals.gather 70742, Vals.concat 45144, catPlan 17244, nub 9395, canon 5863, compOne 2535.
  `colConst` is a `kscatter` of 0 rows: ~40% of all scatters are constant columns.
- perf profile of Bench/MuGrow: `/data/tmp/perf11/mugrow.data`: 86% in librelk (pool::worker 14%, for_meta 12%,
  write_nul 10%, sort 14%, frame_at 6%): per-call fixed cost on many small columns.

Plan (left):
- L1 "a constant operand is a post step": `colMap op n a (colConst n c)` = one `kscan` with `post := [(op, c)]`
  (`colMap_chain`, Rel/RepCanon.lean:109). Sites: `shiftCol` (Rel/Run/Cols.lean:17), `Arr.shift`, `Arr.clampShift`,
  compGroups/compExpand (Rel/Run/Comp.lean), keep `shiftCol_raw` (Rel/RepCols.lean:78) as the interface.
- Re-measure with count.sh into /data/tmp/perf11/cnt-after.
