nullband3g4 handoff

GREEN and committed: RepCanon, RepCols (new `kscan_first_chain`: one-source `kscan .first` chain law, used by `tagCount_zero`),
RepSetOps, RepTabComp, RepChecks/Canon, and everything they build.
Convention adopted: `hs`/`ho` of `colMap_chain`, `colMap_get`, `colMap_raw`, `colMap_const_eq`, `colPrefix_raw`,
`colMap_first_chain` is a TRAILING autoParam (`:= by lockstep` / `by decide`), so callers pass nothing; where a
`∀ i` follows, `i hi` precede it (`colMap_first_chain h i hi`). `colMap_closed`/`colMap_plain` (Run/Gather) keep `hs`
FIRST: write `colMap_closed (by lockstep) h`. `sumOn` (RepChecks/Canon) takes the `Obj.band` proof as a trailing autoParam.
`groupFold_ok`/`groupFold_plain` take `(ho : op ≠ .first := by decide)`; `runScan_ok`/`runScanChain_ok` take `hs`.

STILL RED (elaboration), after the last full `lake build Rel` (/data/tmp/nb3g4.log; RepStruct edit not rebuilt):
 - Rel/RepStruct.lean 20, 423, 430: `colMap_first_chain (colArr_ok h) i.1 i.2` — fixed by the reorder, not rebuilt.
 - Rel/RepTabArith.lean:
   * 126 `cm`: `(colMap_raw hc)` for a generic `op` — "could not synthesize default value for parameter 'hk'":
     op may be `.first` (a stream); needs `op ≠ .first`/kscanStream hypothesis threaded into `cm`'s uses.
   * 302, 313 (`colMap_chain h` inside `colMap_widen`-style lemmas, generic op/post): pass `hs` explicitly; give
     `colMap_widen` (line ~308) a trailing `(hs : kscanStream op [(n, x.enc), (n, y.enc)] (widen t) post = false := by lockstep)`
     AFTER `(i : Fin n.toNat)` and use `colMap_chain h hs`.
   * 391, 403, 434 `colMap_closed hc` -> `colMap_closed (by lockstep) hc`.
   * 400 `fverbBy_map (ap := fun o x y => colMap o n x y) … (fun hc => (colMap_raw hc).2.2.2 i i.2)`: `hap` quantifies over
     every `o`, but `colMap .first` is a stream, so the claim is false at `.first`. Fix: `fverbBy_map` (RepTabArith 251) takes
     `hap : ∀ {o x y z}, o ≠ .first → …` and its proof shows every op `fverbBy` applies (from `fverbOne`, as in
     `fverb_one` 323: `repeat' split at h`) is not `.first`.
 - Modules after RepTabArith in build order not yet reached (RepTabDiv, RepSums, RepBits, RepWhere, RepCast, Lang/GenKBits,
   …): expect `colMap_closed`/`colMap_plain` sites needing `(by lockstep)` first, and `colMap_ok`/`colPrefix_raw` in
   GenKBits 1237-1248.
 - Runtime `#guard`s: not reached by the build for the same reason; TestFrameApp:149 still prints the concat-null error
   ("withBid: concat: the first 1+Rel.QAtomicType.i64 column holds a null, and no kernel yet merges two columns' null bits")
   = the other agent's concat. No `#eval` text per module recorded yet.
