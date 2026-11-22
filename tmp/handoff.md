perf11c handoff (checkpoint at 40 calls)

Done (code, Rel/Run/*): every listed colMap-with-colConst site rewritten to `colMap .first n x x .i64 .i64 [] [(op, c)]`
(Bits 10 sites, List 7, Where 2, Comp.compBlock, Div.lamOf 3, SetOps sumTail i64+f64 nul/zero compares, sumsOn
uses `seenSeg` twice and `[(.eq, 0)]`). Rel.Run.* builds.

Left: proofs. First failure: Rel/RepTabComp.lean:953 and :1011 (compBlock proofs, `rewrite` did not find pattern).
Then expected: RepSums sumTail_fold (badWord_spec in RepTabDiv:1074 takes colConst hyps; rewrite it to post-chain
hyps), sums_holds (iterate 6 -> 4; seg is `seenSeg`, unfold then seenSeg_ok), RepBits bitMatrix_spec/ldivBits_holds,
GenKBits colIota_raw/keepBits_law/compTabMat_law/ldivTabMat_spec, RepTabDiv cells/tau/cat/uncons/unsnoc/uncat,
positions (GenSound rowOK_positions), lamOf proofs.
Note: `cap` exits 1 with no output in this worktree; plain `lake -d <wt> build <mods>` works.
