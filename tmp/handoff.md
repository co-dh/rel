# f32sum handoff (df-f32sum)

Branch `worktree-agent-ad5051993708ece68`, base `63b1442`. Rule (owner option B): a float atom's sum widens each
element to f64, folds `⦇0, fadd⦈` in f64 unrounded, rounds once to V; `sums` rounds each prefix's f64 carry once.

## Done (builds: Rel.Run.SetOps Rel.Run.Arith Rel.Run.List Rel.Lang.Den Rel.Lang.DfnLaw)
- `Rel/Lang/Den.lean`: `fwideDen`, `faddDen`, `froundDen`, `fsumDen u` (foldDen over (carry f64, value u) pairs, then
  `π₂`), `sumDen` (`.f32`/`.f64` → `fsumDen`, any other atom → old `foldDen … (stepAt u Ew.add)`); `sumAt (.atom t) =
  sumDen t`; `sumsDen … = … ≫ mapDen T ≫ sumDen u`.
- `Rel/Run/Cols.lean`: `widen` moved here from Arith (SetOps cannot import Arith); new `scanArr` (kscan answer as
  `Arr t n` via `kscan_closed`).
- `Rel/Run/SetOps.lean`: `sumTailF u n seg z v` = `scanArr .fadd false u u n seg [z, v] (widen u) [(.fto u, 0)]`, bad
  = `colMap .first … [(.eq, 2^63)]` read at i64; `sumTail` `.f32`/`.f64` both call it (old f64 `-0` error gone);
  `Tab.sums` accepts `.atom .f32` values.
- `Rel/Run/Lang/Syntax.lean`: `sumAtoms = [.i64, .f32, .f64]`.
- `Rel/Run/Lang/Elab.lean`: `DfnCut.sum` gets `(hf : t ∉ floatAtoms)`; `dfns "sum"` builds it only off float atoms.
- `Rel/Lang/DfnLaw.lean`: `sumDen_fold (hf : t ∉ floatAtoms) : sumDen t = foldDen … (stepAt t Ew.add)`;
  `Prim.den_sumRow … = sumDen t`; `Tm.dfnCut_den` sum case uses `sumDen_fold hf`.
- Tests `Rel/Lang/TestFrameTyped.lean`: `sumsF32T` (prefixes 2^24, 2^24, 2^24+2), `sumF32T` (2^24+2), `sumF32T2`
  (0.1+0.2 = 0.3, `#guard` word 0x3e99999a). `TestSums.lean` i32 refusal pin lists f32.
- Docs: `doc/rel-architecture.zh.typ` §4 `sum`/`sums` rows (typst compiles), `PLAN.md` fsum paragraph.

## Left
1. **dfns at float atoms (blocker found)**: with `dfns` returning none, a float `sum` whose target has a universe now
   fails: `TestFrameTyped.lean:126 (sumFloatT): sum's definition (dfns) has no form at [f64] ⟶ f64`, same for the
   new f32 tests. Fix: a `DfnCut` case for float atoms whose definition IS the row cut to the universe
   (`.comp (.comp (.arg mapRow u) sumRow) u`), `fused = .prim sumRow`, `cut` = that term, law in
   `DfnLaw.Tm.dfnCut_den` by `rfl` (the fold of `plus` rounds each step, so it is not the float meaning).
2. **RepSums proofs** (`Rel/RepSums.lean`, keep the hunk minimal: another agent edits it for Vals.WF):
   - `sumsDen_rows` 455-: statement's `foldDen … (stepAt u Ew.add)` → `Lang.sumDen u`; errors 538:38, 543:22.
   - `sumTail_plain` 604: error 609:44 (float branch is now `sumTailF`: bad is a `colMap .first`, `colMap_plain`).
   - `sumTail_fold` 615: statement → `Lang.sumDen u`, `u = .i64 ∨ u = .f32 ∨ u = .f64`; float case needs a
     run-scan lemma for `kscan` WITH `pre`/`post` chains (generalise `Tab.runScan_ok`, `Rel/RepSetOps.lean:420`, from
     `raw_kscanChain`, `Rel/KernelSpec/Scan.lean:156`: `out₀` is the unrounded carry, `out = chainAll post out₀`),
     then a `fsumDen` fold lemma replacing `sumsF_fold`/`sumsF_snoc`/`stepF_word` (lines 205-270): row t of `W` read at
     u is `ofBits u (ftoWord u carry_t)`, bad_t ↔ `ftoWord u carry_t = 2^63`. Error 657:8 (`rw` pattern), 727:57.
   - `sum_holds` 863-: `hcell` at 1013 and errors 1019:36, 1047:6; `Arr.get_ofBits` (597) needs `u = .f32` too (raw
     at u of a kscan answer is the 8-byte word cut to u's width: `raw_kscanChain` with `t := u`).
   - `GenSound.rowOK_sums` (850) not yet checked (RepSums failed first).
3. Build: `cap lake build Rel.RepSums Rel.Lang.GenSound Rel.Lang.TestFrameTyped Rel.Lang.TestSums`.
