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

# rq17f3 handoff

Branch `worktree-agent-ae16f80e7880c5eb6`: base cd3523e + merge 9d8d2ea (rq17f2) + rq17f3 commits.

## Done (Rel.KernelSpec.Asc, Rel.KernelSpec.KSeen check green with `lean`; RelKernel rebuilt through them)

- `nulWords m e c` (Kernel/Asc.lean, before `nulCodes`): `c` with `0` at each null row where `hasNul e`. `nulCodes` is
  now `(if hasNul e then [flags.map (1 - ·)] else []) ++ [nulWords m e c]` (same values as before).
- `ascKey`'s `cells` branch reads `nulWords m e (raw .i64 m e)`: `AscKey × Enc` admits a null in a cells column (only
  `ascCol`'s runtime `noNul` refuses it), so the types do not rule it out; the word is masked instead.
  `nulWords_noNul` (KernelSpec/Asc.lean): `noNul … = .ok _ → nulWords m e c = c`, used in `ascCol_ok`'s cells branch.
- `ascKeys_row`'s word hypothesis is now `(nulWords m K[c].2 (raw .i64 m K[c].2))[q]? = (nulWords m' K'[c].2 …)[q']?`
  (equal words only off nulls); `nulCodes_row` takes that form. `lexLe_pos`, KSeen:150 simp sets gain `nulWords`.
- RepCanon:98 `raw_scatter … rfl h` (`.pos`), RepCanon:872 `kasc_ok` pattern has 10 components now.

## Blocker (design): `ascKeys_row`'s `hasNul K[c].2 = hasNul K'[c].2` cannot be discharged by the callers

The callers (RepCanon `Vals.nub_cover` :406, `kasc_grade` :908, `Vals.nub_sel` :936; RepSetOps :647) compare the
sorted column `v = wordsFoR ws nul` with the input `e`. Instance: `e` a `foR` block of words `{5,6}` whose width byte
has bit 7 set but no row at the top residual: `hasNul e = true`, `foRNuls m e = [0,0]`; `kasc` writes
`nul = nulMap [0,0]`, `planBlock` flags a block only where a row is null (Coc.lean:198), so `hasNul v = false`. Then
`nulCodes` gives `[[1,1], c]` for `e` and `[c]` for `v`: the code lists differ in length, `hkey` is false as stated.
Options: A) a validity conjunct "a flagged block holds a null row" (the encoder meets it; callers get it from the
Vals' encs); B) `nulCodes` keyed on the rows (`(foRNuls m e).any (· != 0)`), Rust `asc` to match; C) `hkey` up to
constant code columns. Also missing for the flag conjunct: a lemma `foRNuls n (wordsFoR ws nul)` at `i` =
`if bitAt nul i then 1 else 0` (from `wordsFoR_nul`'s `foROpt` readback, which carries `hbig`).
DRY note: the four `hkey` proofs are one fact; `kasc_grade` (RepCanon:893) should be the only one, the other three
use it with `asc_perm_grade`.

## Still failing (`lake build Rel.RepCanon`, log /data/tmp/job/rq17f3-4.log), RepCols/RepSetOps/RepTabComp/GenK* not reached

- RepCanon:26 `Enc.WF .u1` now gives `∀ v, foROpt … i = some v → v.toNat < 2`, the proof expects `foRBits … < 2`.
- RepCanon:68, :74 `kscatter` unfolds to the new body (`noNul "scatter: ix"`, `if hasNul e`): proof shape changed.
- RepCanon:205-216 whnf timeout (`raw_kgather` with the new `if hasNul e then nulMap … else .empty` nul).
- RepCanon:406/426/466, 644-675, 775, 908, 936/953: `asc_perm`'s `hcol` has 6 components now (`ws nul hv hws hwq h0 h1`),
  the readback goes through `wordsFoR_nul` where `nul ≠ .empty`, plus the blocker above.
- RepCols:152-153 `raw_scatter n₁ .pos x.enc …` needs `hasNul x.enc = false`: a nullable `x` has none; concat of
  nullable columns needs a null-aware `raw_scatter` (flags scattered beside the words, as `kscatter_ok` states).
- Unchecked: RepSetOps :96 :108 :144 :370 :532 :639-650 :666 :779 :780, RepTabComp :393, GenKBits :1338, GenKFix :31.

# rq17f4 handoff

Branch `worktree-agent-aa582f494541a3b41`: base cd3523e + ff 8495add (rq17f3) + rq17f4 commits.

## Done (green: RelKernel through Rel.KernelSpec.Closure, Rel.Run.Core, Rel.Run.Gather, all of RelRun rebuilt)

- `Ext.Enc.WF` (Kernel/Value.lean, foR branch) has a 5th conjunct (decision A): every block `b < nblk` with `nulAt` holds
  a row `b * blk + j`, `j < blk`, `< n`, with `foRNul`. Decidable as before (bounded ∀/∃, O(blk) per flagged block).
- `nulAt_encodeAt` (KernelSpec/Encoding.lean, before `foRBits_encode`): a flagged block of `encodeAt` holds a row null
  in `nul`. `nulAt_encodeAt_empty` (KernelSpec/Alp.lean, after `nblk_encode`): no flag with an empty bitmap.
- `Enc.Valid.wf` takes the conjunct as `hN`; `wordsFoR_nul` proves it (flag readback via `foROpt_encode`, `hbig`
  vacuous at a null row); `foRBytes_wf`, `wf_bools` (Run/Core) from `nulAt_encodeAt_empty`.
- Closure.lean: `hasNul_flags` (`WF t n e → hasNul e = (foRNuls n e).any (· != 0)`), `foRNuls_wordsFoR` (flag of
  `wordsFoR ws nul` at row `i` = `if bitAt nul i then 1 else 0`, under `hbig`), `hasNul_wordsFoR` (empty bitmap → no
  null), `kgather_plain` (`raw_kgather` when the source has no null: plain `wordsFoR`).
- RepCanon: `foRNuls_bit`, `asc_col_row` (the per-column `ascKeys_row` obligations from `asc_perm`'s 6-part `hcol`:
  masked words, `hasNul`, flags), `kasc_grade` proved over it; `Vals.nub_sel`'s `hri` uses `kgather_plain` (old :953
  fixed).

## Decision taken, report upward: `kasc_grade` now carries `(hwf : ∀ x ∈ es, ∃ t, Ext.Enc.WF t N x.2)
  (hN : N.toNat < 2 ^ 32)`

`hN` is not removable: at `2 ^ 32` rows or more `encodeAt` writes no patch list, so in a block holding a null whose
keys span all `2 ^ 64`, a non-null row keeping `2 ^ 63 - 1` keeps the null's top residual and reads back as null
(`foROpt_encode`'s `hbig`). Instance: sorted column `v`, block with a null and a row `2^63-1` → `foRNuls v` has an
extra `1`, so `nulCodes` differ from the input's and `hkey` is false. Fix options: a u64-offset patch list above
`2 ^ 32` rows (encoder + Rust), or carry `hN` up through the Vals lemmas.

## Still failing (`lake build Rel.RepCanon`, log /data/tmp/job/rq17f4-6.log)

- :1035 `Vals.nub_sel` inline `hkey` (and :406 `Vals.nub_cover`): replace by `kasc_grade ha hwf hN` (+ `asc_perm_grade`);
  needs a lemma "every column of `Vals.cols x` is `Ext.Enc.WF` at `n`" (does not exist; :438 gives only
  `Kernel.Enc.Valid`) and `n < 2 ^ 32` (decision above). Coordinator: master's RepSeen (`kasc_kseen`) should cite
  `kasc_grade` once that lands.
- :26 (u1 bound now through `foROpt`), :68 :74 (`kscatter` body), :205-216 `Arr.gather_row` (whnf timeout on the
  `if hasNul e …` nul; the proof also needs `raw` at a null row, which is junk: the statement must go through
  `foROpt`/`get`, not raw words, where the source has nulls; use `kgather_plain` where `hasNul = false`), :426 :466,
  :644-675, :775.
- Not reached: RepCols :152-153, RepSetOps (:96 :108 :144 :370 :532 :639-650 :666 :779 :780), RepTabComp :393,
  GenKBits :1338, GenKFix :31. RepTabComp `lexLe_congr_right` vs master's `lexLe_congr` not touched.
