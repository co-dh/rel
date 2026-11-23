nullband3g3 handoff (branch worktree-agent-ae07c0452b66d3bf2)

DONE and committed (9c40b6c): step 1 Rel/RepCanon.lean green (`colMap_chain`/`colMap_get` now take
`hs : kscanStream op [(n,a),(n,b)] pre post = false`; proof uses `kscanCols_lock`, `mapM_chain`).
Index: not built in this worktree (lean-refactor index fails: CsvTest olean mismatch until `lake build Rel.Kernel.Db.CsvTest`).

IN PROGRESS (uncommitted/WIP commit): Rel/RepCols.lean ripple of the `hs` hypothesis.
 Done: colPrefix_raw (takes `ho : op ≠ .first`), colMap_raw (`hk`), colMap_first_chain (`hs`), colMap_post, colMap_const_eq (`hl`),
       clampShift, summandPos_raw, kscan_foR splits (one more `split`, untested).
 Still red (build log /data/tmp/job/nb3g3-b6.log):
  173 Arr.concat_get  — to be replaced by the concat rewrite (step 3).
  374 colPrefix_add_sum calls `colPrefix_raw hP` -> pass `(by decide)`/the op ≠ .first proof.
  402 kscan_foR `simp made no progress` (now fixed by adding a 7th split; re-run).
  491-496,514 tagCount_zero: tagCount is now `kscan .first .. [(n, tag.enc)]`/colPrefix; `unfold colPrefix` block (485-488) and
      `colMap_first_chain` use need re-reading against Run/Cols `tagCount`.
 Callers of colMap_raw / colMap_const_eq / colPrefix_raw / colMap_first_chain outside RepCols (RepSetOps, RepTabDiv, Lang/*) not yet
 built: each needs the new hs/ho argument (`(by lockstep)` / `(by decide)` for a concrete op).

DIAGNOSIS step 2 (from the `lake build Rel` log /data/tmp/job/nb3g3-b5.log, no #eval run):
 Only TestFrameApp:149 prints a message: "withBid: concat: the first 1+i64 column holds a null, and no kernel yet merges two
 columns' null bits" = class (a), fixed by step 3. The other failing `#guard`s (Kern9 87/89, TestFrameCols 68/84, TestFrameSchema 69,
 TestGenericN 108/109, TestFrameStat 122/158, TestPivotDisk 137, TestFrameScale 53, TestFrameApp 101, TestFrameBench 58,
 TestFrameQuery 65/82, TestFrameUnbounded 189/203) are plain false: class (a) presumed (they are Frame programs that union
 nullable columns) but NOT confirmed; class (b) not found. Next: after step 3 rebuild and `#eval` the failures text of any that remain.

NOT DONE step 3 (concat). Design anchors:
 - Rel/Run/Cols.lean 61 `Arr.concat`, 69 `Opt.concat`, 23 `shiftCol`, `catPlan` (~79): replace by
   `kscan .first false t t n none [(n₁, x.enc), (n₂, y.enc)]` (a stream: `kscanStream`, Rel/Kernel/Scan.lean ~230; `kscanCols` joins the
   words and `foRNuls` flags; `n = n₁+n₂` checked inside kscanCols).
 - Missing spec: `kscan_closed` (KernelSpec/Closure.lean ~241) assumes a stream's sources hold NO null (`hasNul = false`) and answers
   `hasNul r.1 = false`; the Opt.concat needs the version with nulls: `Enc.WF t n r.1` of `Coc.encode w words (nulMap flags)` when some
   source holds a null, plus the read law `Opt.isNul`/`Opt.get` of the answer = source row (words: raw_kscanChain at seg = none gives
   out = seed = x.raw ++ y.raw; flags: `nl` fold with `.first`, all rows segment starts, so nl = ns = foRNuls x ++ foRNuls y).
 - Read law to prove: `Opt.get (Opt.concat x y) i = if i < n₁ then x.get i else y.get (i - n₁)`; then fix Arr.concat_valid,
   Vals.concat_wf/row (RepCols 664/728), Tab.concat_wf (RepSetOps 283); delete `Arr.concat_get`, `catPlan_ok`, `shiftCol_raw`.
 - `Opt.concat`/`Vals.concat` callers pass `off` (catPlan's second component): drop the parameter everywhere (Tab.concat in Run/SetOps 30).
