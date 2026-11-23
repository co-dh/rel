nullband3g2 handoff

GREEN and committed (branch worktree-agent-a676a6321cbdd9688): RelKernel (with ScanTest incl. stream pairs), RelRun.

Design changes beyond the brief:
- `kscan_closed` takes `hS : kscanStream .. = true → (∀ p ∈ es, hasNul p.2 = false) ∧ ∀ p ∈ es, Ext.Enc.WF s p.1 p.2`
  (only a stream reads its sources' null flags); `kscan_lock_closed (hs : kscanStream .. = false)` is the no-hypothesis form;
  `kscanStream_ne (h : op ≠ .first)`; macro `lockstep` (Closure.lean) = the autoParam tactic proving `kscanStream .. = false`.
- `colMap_closed/plain`, `colArr`, `scanArr` take `hs : kscanStream .. = false` (autoParam `by lockstep` on colArr/scanArr);
  `colPrefix_closed/plain` take `ho : op ≠ .first := by decide`.
- `.first` over two sources with no chain is now a STREAM, so `colMap/colArr .first n a a [] []` (identity map) no longer
  works: replaced by one-source `scanArr .first false .i64 .i64 n Option.none [(n, a)]` (Run/List `Vals.cells`, Run/Where
  `positions`), `Arr.pos n` (Run/Struct `injCols`), `kscan .first .. [(n, tag.enc)]` (Run/Cols `tagCount`).
- Plan.srcB n x = `ctorB 0 #[n, x] #[]`; scanB and EmitC.mapB use it.

RED (`lake build Rel`, log /data/tmp/nb3g3.log):
1. Rel/RepCanon.lean:192-204 (`raw_kscan`-style lemma over `kscan ... [a, b]`, now `[(n, a), (n, b)]`; the proof uses `mapM_chain`
   that must become `mapM_pairs`/`kscanCols_lock`, as in KernelSpec/Scan `raw_kscanChain`); 7 errors, all from the es type.
2. Runtime `#guard` failures (value false, no message): Lang/Test/Kern9 (kernT9.ok), TestFrameCols (frameCols.ok,
   frameDescribe.failures), TestFrameSchema, TestGenericN (paramNT/paramPT), TestFrameStat (frameStatT, frameStatFloatT),
   TestPivotDisk (datesT floatsT symsT ...), TestFrameApp, TestFrameBench, TestFrameQuery, TestFrameScale, TestFrameUnbounded.
   Likely one cause: lock-step `kscan` now REFUSES a null source row (`noNul "kscan"` in `kscanCols`) where it used to read
   the null word, e.g. `stepCols` `ne a` / `colMap .ne n x x` over a nullable column (Run/Arith), or a count mismatch
   (`es.any (·.1 != n)`). Next step: run one failing test's pipeline and print the `Except` error text (the first message
   names it: "kscan: row k is null, and a null names no row" or "a source holds a row count other than n"), then fix the
   caller to read the column through the null-aware path, not the kernel.
3. Not done: Concat (`Arr.concat/Opt.concat` as one stream `kscan .first`, deleting scatter+add, `shiftCol`, null refusal);
   Rel/KernelSpec/KGather had no kscan use in this tree (module builds).
