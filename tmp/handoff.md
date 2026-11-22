perf11c handoff (stopped near the 100-call limit)

Landed (code + proofs, edited modules build: RepTabComp RepTabDiv RepBits RepWF RepWhere GenKFold GenSound RepSums):
- List: Vals.cells hi (`colArr .first P P`), Vals.tau, Vals.cat d, uncons, unsnoc, uncat widths (post on the `.sub`)
- Where.positions both sites; Comp.compBlock; Div.lamOf (gt n, lt 0, add (0-n) then max 0)
- Bits: bitMatrix `.mul r w`, ldivBits `.eq cnt 0`
- RepCols.neg_add_word (`0 - b + a = a - b`), replacing RepTabComp's inline copy

Reverted to base (proofs not done):
- Bits colIota, keepBits (3), compTabMat, ldivTabMat (on, vac, p1): GenKBits.lean errors at colIota_raw (19),
  keepBits_law (183), compTabMat_law/wf (315, 481), ldivTabMat_spec (621), ldivTabMat_reads (1582)
- SetOps sumTail (i64 + f64), sumsOn (seenSeg twice, `.eq firsts 0`), List.sumOn `.eq i 0`: RepSums errors at
  sumTail_fold 633/656 (badWord_spec, RepTabDiv:~1074, states colConst hyps), sums_holds 735/745 (iterate 6 -> 4,
  seg via seenSeg), 837/838, sumOn proof 881

Not run: full gate `lake build RelCore RelKernel RelRun Rel RelBench`, kernel-count measurement.
`cap` exits 1 with no output in this worktree (cap -w shows nothing); plain `lake -d <wt> build <mods>` works.
