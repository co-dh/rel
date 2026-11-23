# f32sum handoff (df-f32sum), round 3

Branch `worktree-agent-aa111637125ea8532`: base 037b1e4 + merge 5924d65 (round 2) + merge b10b380 (Vals.WF threading).

## Done (round 3)
- RepSetOps: `runScanChain_ok` (kscan at any read type `s`/answer type `t`, total chains `pre`/`post` as `pw`/`pf`,
  seed words `pw` = `z`); `runScan_ok` is its specialisation. `raw_foR_cut` (a foR read at `t` = its i64 words cut to
  `t`'s width), `kscan_i64` (kscan's answer at a non-u1 `t` with a width is the answer at i64: gives the whole-word
  read the bad column needs).
- Den: `fsumDen` starts from `(fval u (ofBits u 0), ofBits u 0)` (`b.2 = ofBits u 0 ∧ fwideDen u b.2 b.1`), because
  kscan widens the seed through `widen u` and `Op.widen32 0 = 0` is not provable (`Float32.ofBits` is opaque).

## Left (Rel.RepSums)
- Replace `stepF_word`/`sumsF_snoc`/`sumsF_fold` (RepSums ~204-271) by: generic `foldDen` snoc-iff (sumsF_snoc with
  `E V` free, pair carrier), and `fsum_fold`: v q values, `X q` with `fval u (v q) = some (X q)`, `Z` with
  `fval u (ofBits u 0) = some Z`, `C t = (rows t).map X |>.foldl faddW Z`, `R t = ftoWord u (C t)`,
  `bad t = 0 ↔ R t ≠ 2^63` ⟹ `fsumDen u ((rows t).map v) w ↔ (∀ q ∈ rows t, bad q = 0) ∧ w = ofBits u (R t)`.
- `sumTail_fold` float case: unfold `sumTailF`; `scanArr` → kscan; `runScanChain_ok` with s = t = u,
  pw from `widen_fval` (RepTabArith), pf = `ftoWord u`; `kscan_i64` + `runScanChain_ok` at i64 for the bad column
  (`colMap_post`, `eval_eq_word`); seed `raw u` of `colConst n 0` = 0 via `raw_foR_cut` + `colConst_raw`.
  Statement reads values `ofBits u ((Enc.raw u n v)[q]?.getD 0)`.
- `Arr.get_ofBits` is `Arr.get_word` (RepCols:98) at u ∈ {i64,f32,f64}: delete it, use `Arr.get_word`.
- sums_holds hmap, sum_holds hvx/htot/hL1/empty cell (`sumDen u [] c ↔ c = ofBits u 0`).
