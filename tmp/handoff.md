# f32sum handoff (df-f32sum), round 3: done

Branch `worktree-agent-aa111637125ea8532`: base 037b1e4 + merge 5924d65 (round 2) + merge b10b380 (Vals.WF threading).
`lake build RelCore RelKernel RelRun Rel` green (388 jobs). Nothing left for df-f32sum.

- RepSetOps: `runScanChain_ok` (any read type, `pre`/`post` chains); `runScan_ok` its specialisation; `raw_foR_cut`;
  `kscan_i64`.
- Den: `fsumDen` starts from `u`'s `0` paired with its `f64` word (`Op.widen32 0 = 0` is unprovable: `Float32.ofBits`
  is opaque, and kscan widens the seed).
- RepSums: `foldDen_snoc_iff`, `Lang.fsum_fold` (replace `stepF_word`, `sumsF_snoc`, `sumsF_fold`), `sumTailF_fold`,
  `QAtomicType.ofBits_cut`, `Lang.sumDen_nil`; `Arr.get_ofBits` at i64/f32/f64; `sumTail_fold` reads values at `u`.
- TestFrameStat: `avg` at an `f32` object runs (`check m = {(∗,4.0)}`), was a pinned refusal.
