# f32sum handoff (df-f32sum), round 2

Branch `worktree-agent-ab35a8f73bf595d62` (base `fdf7f8c` + merge of `6bb8b53`). Rule (owner option B): a float atom's
sum widens each element to f64, folds in f64 unrounded, rounds once to V; `sums` rounds each prefix's f64 carry once.

## Done
- Round 1 (see git log of `6bb8b53`): `Lang.sumDen`/`fsumDen` (Den.lean), `sumTailF` (SetOps), `scanArr`/`widen` (Cols).
- `DfnCut.fsum u` (Rel/Run/Lang/Elab.lean, after `DfnCut.sum`): at a float atom the definition IS `F(u) sum u`;
  `uni = some (u, u)`, `fused = .prim sumRow`, `cut` = the term. `dfns "sum"`: float atom -> `.fsum u`, else
  ordered atom -> `.sum`. Law `Tm.dfnCut_den` case `fsum` (DfnLaw.lean): cut part `Iff.rfl`, fused part drops both
  `u` on the universe `𝟙` (`Prim.den_mapRow_corefl`). Built green: Rel.Run.Lang.Elab, Rel.Lang.DfnLaw,
  Rel.Lang.TestFrameTyped, Rel.Lang.TestSums (the f32/f64 universe tests now pass). Commit `2329039`.
- RepSums (WIP commit after it): `sumsDen_rows` and `sumTail_fold` stated with `Lang.sumDen u`; `sumTail_fold`'s
  first conjunct `u = .i64 ∨ u = .f32 ∨ u = .f64`; `sumTail_plain` unfolds `Tab.sumTailF`. `sumsDen_rows`,
  `sumTail_plain`, the i64 case of `sumTail_fold` now check.

## Key fact found
`Enc.raw t n e` on a foR column is `foRBits % 2^(8·width t)` (Rel/Kernel/Value.lean:677), and foRBits holds an
element SIGN-extended to 64 bits. So `Enc.raw .i64` of an f32 column is NOT its f32 word. The general element read
must be `QAtomicType.ofBits u ((Enc.raw u n v)[q]?.getD 0)` (for i64/f64 `raw u = raw .i64`, same width 8). Change
`sumTail_fold`'s statement, `sums_holds`' `hmap` (~803), `sum_holds`' `hvx`/`hmap`/`htot`/`hL1` (~974-1054) to
`Enc.raw u`, and `Arr.get_ofBits` (RepSums ~597) to `(hu : u = .i64 ∨ u = .f32 ∨ u = .f64)` reading `Enc.raw u`
(f32 case from `Arr.get_raw_atom`/`wideCol_word` at width 4).

## Left (current errors of `cap lake build Rel.RepSums`)
- 657:8 / 727:57 `sumTail_fold` float cases: the old f64 proof (kscan .i64 + colArr fto + whereCol) is obsolete;
  sumTail's float branch is now `sumTailF u n seg z v` = `scanArr .fadd false u u n seg [z, v] (widen u)
  [(.fto u, 0)]` then `colMap .first … [(.eq, 2^63)]`. Replace both cases by one proof for `u ∈ {f32, f64}`:
  1. `runScanChain_ok`: generalise `Tab.runScan_ok` (RepSetOps.lean:420) to `kscan` with `pre`/`post` and result
     type `t`, from `raw_kscanChain` (KernelSpec/Scan.lean:156) — `out₀[i]` = foldl `fn` over the run's
     `chain pre`-ed words from `chain pre z`; `raw t n sc [i]` = `chain post out₀[i]` cut to t's width. Make
     `runScan_ok` its specialisation (pre = post = [], `chainAll_nil` Scan.lean:141).
  2. fold lemma for `Lang.fsumDen` (replace `sumsF_fold`/`sumsF_snoc`/`stepF_word`, RepSums 204-271): with
     carry_t = that foldl of `faddW` over `fval`-words, `fsumDen u xs w ↔ (∀ q, bad q = 0) ∧ w = ofBits u
     (ftoWord u carry_t)`, bad_t ↔ `ftoWord u carry_t = 2^63`. Word level only (`Op.fto`, `Op.f32to64`, `fval`),
     never Float arithmetic. Needs `fval u (ofBits u x) = chain (widen u) x` for a raw u word x.
- 806, 989, 1010, 1054: `Arr.get_ofBits hu` with the 3-way `hu` (fix above).
- 975: unsolved goal in `hvx` (follows from the raw-read change).
- 1019:36: empty cell: need `Lang.sumDen u [] c ↔ c = u.ofBits 0` at the three atoms (i64: `Lang.foldDen_nil`;
  float: `fsumDen` = foldDen over pairs from `(0, ofBits u 0)` then `graph Prod.snd`).
- Then `GenSound.rowOK_sums` (Rel/Lang/GenSound.lean:850), `cap lake build Rel.RepSums Rel.Lang.GenSound
  Rel.Lang.TestFrameTyped Rel.Lang.TestSums`, then the full build.
- Another agent (8.5s2p) threads Vals.WF through RepSums callers: keep hunks minimal.
