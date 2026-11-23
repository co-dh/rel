nullband3g7 handoff

GREEN and committed (tip 43a7fb3): RepStruct, RepTabArith, RepTabDiv, RepCast, RepBits, and everything they build.
Convention applied: `colMap_closed/colMap_plain (by lockstep) h`; a lemma at a generic `op` takes `op ≠ .first`
(`kscanStream_ne ho _ _ _` gives the `hs`). New: `fverbOne_ne`, `fverbBy_map` (hap takes `o ≠ .first`), `colMap_widen` trailing hs,
`fmapCols_spec` trailing `(ho : o ≠ .first := by decide)`, `Tab.ordOp_ne` (RepTabDiv), `floatOps_ne` (RepCast),
`scanArr_first_word` (RepTabDiv: one-source `scanArr .first` copies its source), `raw_kscan_rev` restated on `es : List (USize × Enc)` + `hs`.

STILL RED after the last full `lake build Rel` (/data/tmp/nb3g7.log), Rel/Lang/GenKBits.lean (all elaboration):
 - 25, 41, 45, 759, 795, 849, 915, 1108?, 1182, 1193, 1234, 1546, 1547: `colMap_plain/colMap_closed h` need `(by lockstep)` first
   (25: `colMap_plain hio` with `hio : shiftCol g 0 = ok io` -- shiftCol is the concat code, NOT colMap: the lemma used there
   is probably a shiftCol lemma that now needs another form; check with the other agent's concat rewrite).
 - 1108, 1151, 1193?: `List.cons c` expected `USize × Enc` (kscan sources now pairs; `raw_kscan`-style statements).
 - 1151:59, 1206:45, 1533:84, 1535:84: "unsolved goals" (the `colPrefix_raw`/`colMap_ok` 1237-1248 region; likely the
   `ho`/`hs` autoParam defaults at generic op). Read the exact goal with `lake build Rel.Lang.GenKBits`.
 - Modules after GenKBits not yet reached.
Runtime #guard: TestFrameApp:149 prints the concat-null error (other agent's concat). No per-module `#eval` text gathered yet;
many `Expression` errors (Kern9 87/89, TestFrameCols 68/84, TestFrameSchema 69, TestGenericN 108/109, TestPivotDisk 137,
TestFrameScale 53, TestFrameStat 122/158, TestFrameApp 101, TestFrameBench 58, TestFrameQuery 65/82, TestFrameUnbounded 189/203)
are failing runtime `#guard`s awaiting the temporary `#eval` of the `Except` text.
