# rq17f handoff (route B: kernel theorems over the null-aware read)

Branch `worktree-agent-ad5dbdf04aa66f661`: base b405ecd + rq17e WIP f55cd2c (merged clean) + rq17f commits.

## State per module

| Module / gate                  | State                                                                                       |
|--------------------------------|---------------------------------------------------------------------------------------------|
| Rel.KernelSpec.Closure         | green: `kscatter_closed` = `repeat' (split at h <;> try (cases h; done))`, then             |
|                                | `wordsFoR_valid _ _ (scatterWords_size ‹scatterWords _ _ _ _ _ = .ok _›)` on every branch   |
| RelKernel (library)            | green (138 jobs)                                                                            |
| Rel.Kernel.Scan/Coc/TestChecks | green                                                                                       |
| Rel.Kernel.AscTest             | 3 new decide/#guard pairs: `cells` null refusal in row words, `lo`, `hi` (`cellsKey`).      |
|                                | FAILS before reaching them: Rust panic, see Blocker 1                                       |
| Rel.Kernel.GatherTest, SeenTest| FAIL: Blocker 1 (`res_pack asked for width 1`)                                              |
| Rel.Kernel.ScatterTest,BitRows | not reached in that run (same null-column tests, expect Blocker 1)                          |
| cargo test --features std      | green, 74 passed, exit 0                                                                    |
| sh crate/build.sh syms         | exit 0                                                                                      |
| Rel.Run.Core                   | green: `foRBytes_wf` passes `(nul := .empty)` to `nblk_encode`                              |
| Rel.Run.Gather                 | FAILING :21 `Arr.kgather_wf`: whnf timeout at :35, `wordsFoR_closed _` (nul = .empty) does  |
|                                | not match `raw_kgather`'s `wordsFoR gw (if hasNul e then nulMap … else .empty)`. Blocker 2  |
| RepCols/RepCanon/RepSetOps/    | not built (behind Run.Gather)                                                               |
| RepTabComp, GenKBits, GenKFix  |                                                                                             |

## Blocker 1: Rust `nul_pack` packs a power-of-two width with `res_pack` (crate/src/enc.rs, off limits to rq17f)

`enc.rs` `nul_pack`'s `go` ends `crate::simd::res_pack(&v, d, nb, p.res)`; `res_pack_scalar` asserts `w >= 3` and not
a power of two. A null block of keys `{0}` plus a null gets `d = 1` -> panic `qlean: res_pack asked for width 1`
(GatherTest, SeenTest), `{0,1}` plus a null `d = 2` (AscTest). `pack_block` (enc.rs:39) already routes a lane width
through `by_width!` and an odd one through `res_pack`; fix: pack the `u64` residuals `v` through `pack_block::<u64>(p.res,
&v[..nb], nb, 0, d as u8)` (base 0, so the residual is unchanged). No cargo test covers `nul_pack` at d ∈ {1,2,4,…}.

## Blocker 2 (design): `Enc.WF` and `raw` read the junk word at a null row

- `raw .i64` reads `foRBits`, which at a null row is the block's top residual plus base, not a q value. So:
  - `Arr.kgather_wf` (Run/Gather.lean:23) at `t = .u1` with `hasNul x.enc`: `Enc.WF .u1` asks every `foRBits < 2`;
    a gathered boolean block `{0,1}` plus a null widens to `d = 2`, the null row reads `3`. Not provable as stated.
    For `t ≠ .u1` `wordsFoR_valid` closes it; for `hasNul x.enc = false` the old proof closes it after
    `simp only [hN]` on the `if`.
  - `ascKeys_row` (KernelSpec/Asc.lean:138) asks equal `raw` words at rows `q`, `q'` in every column. At a null row
    the sorted column's word is its own block's top residual, not the input's, so the RepCanon/RepSetOps callers
    (RepCanon :406, :908, :936; RepSetOps :642) cannot discharge it from `asc_perm` where `hasNul`. Since `nulCodes`
    zeroes a null row's code, the general statement needs equal words only where the flag is `0`.
  - Every readback of `wordsFoR ws nul` with `nul ≠ .empty` goes through `foROpt_encode`, which carries `hmax`
    (rq17g's encoder fix).
- Decision needed: A) `Enc.WF`'s bound reads `Column.foROpt` (bounds only non-null rows) and `ascKeys_row`'s word
  hypothesis is restricted to flag-0 rows; B) `Enc.WF` at a type with no null (`u1`) also asks `hasNul e = false`
  (then `hasNul (wordsFoR ws) = false` must be proved: `planBlock_plain` + width byte < 128).

## Next

1. Blocker 1 fix in enc.rs (by rq17g or with leave), then build the 7 kernel tests.
2. Blocker 2 decision, then Run.Gather `Arr.kgather_wf`, then the Rel callers: `ascKeys_row` (RepCanon ×3,
   RepSetOps), `kasc_ok`/`asc_perm` (RepCanon :398 :845 :872 :899 :924, RepSetOps :634, GenKBits :1338, GenKFix :31),
   `raw_kgather` (RepCanon :211 :419 :948, RepSetOps :108 :144 :661 :774 :775, RepTabComp :393, Run/Gather :26),
   `raw_scatter` (RepCols :130 :131, RepCanon :98, RepSetOps :96 :370 :532; needs `hasNul e = false`: `.pos` gives it
   by `rfl`, `one`/`x.enc` need it or `kscatter_ok`).

# rq17f2 handoff

Branch `worktree-agent-aca6ec9d099a599c9` (base 8852c9a + merge 361c818 + rq17f2 commits).

## Done (built green: RelKernel spec modules through Rel.KernelSpec.Closure, Ids, Raw; Rel.Run.Core; Rel.Run.Gather)

- `foROpt_encode` (KernelSpec/Encoding.lean:1123): `hbig` now asks only at a row that is no null
  (`Column.bitAt nul i = false →`); the proof used it only in that branch. `rawOpt_encodeAt` (Raw.lean) likewise.
- `wordsFoR_nul` (KernelSpec/Closure.lean:55, replaces `wordsFoR_valid`): Valid, raw size, the `foROpt` readback
  (`none` at a null, `ws[i]` elsewhere; hypothesis = `hbig`), and `Enc.WF` at every type, u1 bounded only at non-null
  rows. `wordsFoR_closed` is its `nul = .empty` specialisation; `kscatter_closed`/`kgather_closed` use it.
- `nulMap` (Kernel/Scatter.lean) is `packOf ns.size (ns[i] != 0)`, same bytes as before on 0/1 flags, read back by
  `Verify.bitAt_packOf`.
- `Arr.kgather_wf` (Run/Gather.lean:21) over the null-aware read (decision A): a non-null gathered row reads a
  non-null source row (`hasNul` false: no block flagged; true: its flag via `bitAt_packOf`).
- `foRBits_bools` (KernelSpec/Ids.lean:55) now `foROpt … = some … ∧ foRBits … = …`; `wf_bools`, `boolBits_bools`,
  `bitAt_bools` (Run/Core) use `.1`/`.2`; `get_boolBits` (Run/Core:202) takes `hnn` (row `j` no null), discharged in
  `get_boolsOf` from `foRBits_bools.1`.

## Blocker: kernel `decide` of a kscatter/kgather pair with a null column

Measured with /data/tmp/rq17f2/T1.lean (`env LEAN_PATH=<wt>/.lake/build/lib/lean lean T1.lean`):
- `Coc.encodeAt … nul` alone, null bitmap a small literal (`packIds 1 4 …`): 536 ms for two copies. Encoder is fine.
- `hasNul`, `foRNuls` of an `ncol`: < 150 ms.
- `view (kscatter .last (u 3) (col [2,0,2]) (col [10,11,0]) (u 4) 7) = enc8 [11,7,0,7]`: 1.6 s.
- same with `ncol [10,11,0] [2]` against `lit [11,7,0,7] [2]` (encodeAt with the literal bitmap): fails after 166 s,
  "Decidable instance … did not reduce", stuck at the `match view (kscatter …)`. The model value equals the rhs on
  paper (words `[11,7,0,7]`, flags `[0,0,1,0]`, bitmap byte 4 both ways), so this is cost, not a false pair.
- Hypothesis (not confirmed): the null bitmap reaching `encodeAt` is the unevaluated term
  `nulMap (scatterWords … (foRNuls m e) …)` with `e` itself an encoder term; every `bitAt nul j` the encoder makes
  re-reduces it, and the kernel's whnf cache compares those huge terms (perf: 48% `expr_eq_fn`, 30% its hash cache).
  Next: profile T1's a2 with `perf record -g`; try in T1 a copy of kscatter's body that matches the nul ByteArray
  to a literal first (e.g. `nulMap` built by `ByteArray.mk` of a `List.map`) to see whether a small nul term fixes
  it; the fix must be in the model (all ScatterTest/GatherTest/AscTest/SeenTest null pairs pay it), not per test.
- ScatterTest, GatherTest, AscTest, SeenTest, BitRowsTest not yet built green on this branch; CocTest, ScanTest
  were green on rq17f.

## Left (step 3 of rq17f2, untouched)

`ascKeys_row` (KernelSpec/Asc.lean:157, worktree numbering) restricted to flag-0 rows (decision A); note its `cells`
branch reads raw words unconditionally, so either mask the words at a null there or ask word equality at a cells key
always. Then the callers listed above under Next 2 (RepCanon, RepSetOps, RepTabComp, RepCols, GenKBits, GenKFix),
then `lake build RelKernel RelRun Rel` and `sh crate/build.sh syms`.

# rq17dec handoff

Cause of the slow null pairs (probes under /data/tmp/rq17dec): not the model. Every piece of `kscatter`'s null path
reduces in the kernel in about 2 s (`foROk`/`foRNuls`/`raw` of a null column, `nulMap`, the encoder with a computed
bitmap: R.lean, S.lean). The cost is core's derived `instDecidableEqSum`, the instance every test's
`view … = view …` at `String ⊕ (List UInt8 × List UInt8)` picks: the same pair through `pr` (the `inr` payload, a
`Prod`), through `==`, or under a `Sum.elim`-based instance takes 1.6-2.1 s; with `instDecidableEqSum` it does not
finish (S.lean s0 vs the handoff's 166 s). Fix: `Rel.instDecidableEqSumElim` (Rel/Kernel/Value.lean top), priority
high, decided through `Sum.elim`, whose motive does not mention the two sides.
