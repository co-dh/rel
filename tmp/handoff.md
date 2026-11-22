# rq17e handoff (route B: kernel theorems over the null-aware read)

Branch `worktree-agent-ac58f9733a568196d`: master d8030bc + rq17d (8d0bbba, merged clean, no conflict with 7.4c/perf7).

## Done

- `Rel/KernelSpec/Encoding.lean` (green, `lean` check and `lake build Rel.KernelSpec.Encoding`):
  - `foRMeta_reads`: hypothesis `width byte < 256` (was `< 128`), conclusion `Column.widthByte M b = d` (was
    `widthAt`); `widthAt`/`nulAt` follow by unfolding. Callers fixed: `foROpt_encode`, `Alp.foRWF_encodeAt`.
  - new `any_nul_of`, `planBlock_plain` (a block with no null plans as with `nul = .empty`), `planBlock_nul`
    (`nulBlock`'s frame = base, `128 ≤ byte ≤ 192`, a non-null row fits `byte % 128` and hits the top residual only as
    key `2^63-1`).
  - **`foROpt_encode`** (keystone): `Column.foROpt` of `encodeAt lg w x patch nul` at row `i` is
    `if bitAt nul i then none else some (keyAt w x i).toUInt64`, any `nul`, hypothesis `hmax` only.
  - `foRBits_encode` is now its specialisation at `nul = .empty` (callers unchanged).
- `Rel/KernelSpec/Alp.lean`: two `widthAt` rewrites through `Column.widthAt` (line ~168, and the `pack_blockStart` hd).

## Owner decision needed (encoder)

`hmax` is real: `Coc.nulBlock` does not widen a block whose non-null keys span all `2^64` (doc: "there its top
residual reads as the null"). Instance: w = 8, one block holding keys `Int64.min`, `Int64.max` and a null: `d = 64`,
`Int64.max - Int64.min = 2^64-1 = ones 64`, so the value row reads as null. Every route-B kernel theorem over a
`wordsFoR ws (nulMap ns)` output inherits this side condition. Fix in the encoder (general, removes `hmax`): put a
non-null row whose residual is `ones d` in a null-holding block on the patch list (`foRNul` already requires
`foRExc = none`), in `Coc.encodeAt`'s `exc` filter and `crate/src/enc.rs`. Not done: changes Rust's writer.

## Left (bottom-up)

1. `Rel/KernelSpec/Raw.lean` `raw_encodeAt` (line 105): add the null-aware form over a reader of row `i` as
   `Option UInt64`. Reuse `Kernel.foRNuls` (Rel/Kernel/Scatter.lean) as the flag source: define nothing new beside
   `raw` + `foRNuls`; statement `foRNuls n (.foR (encodeAt … nul)) = flags` and `raw` at non-null rows = key.
2. `KernelSpec/Scatter.lean` `raw_scatter`/`kscatter_pos_ix` still carry rq17d's `(hnul : hasNul e = false)`
   (route A); restate over flags (`foRNuls`) + words, null-free form by specialisation.
3. `KernelSpec/Asc.lean` (failing, first errors, log /data/tmp/job/rq17e-2.log):
   - `:157 ascCol_ok` unsolved `nulCodes m e (Array.map f (raw .i64 m e)) = [Array.map f (raw .i64 m e)]`: fix by
     `ascKey (.atom t, e) := nulCodes m e ((raw .i64 m e).map ((ascOrd t).getD id))` (spec = kernel's codes).
   - `ascKeys_row` (~:128) then needs per column `hasNul K[c].2 = hasNul K'[c].2` and equal `foRNuls` at q/q'
     (nulCodes emits the flag column only when `hasNul`). Callers: RepCanon 405/907/935, RepSetOps 641.
   - `:262 kasc_ok`: `vs = wss.map wordsFoR` must become `vs = wss.zipWith wordsFoR ns` with `ns` the `mapM` of
     `nulMap <$> scatterWords .last r (foRNuls m e) …` (kasc body, Rel/Kernel/Asc.lean:151-156).
   - `:373 kasc_pos_key`, `#guard_msgs` 503/507/511 follow.
4. Then KGather (`raw_kgather` :~, `kgather_pos_e/ix`), KSeen (`kseen_keys` :19/40, `kseen_pos` :149), Closure
   (`kgather_closed` :158, `wordsFoR_closed` :74), BitRows, and Rel downstream (use_site list: RepCanon, RepSetOps,
   RepCols, RepTabComp, RepOrder, RepSums, RepBits, GenKBits, GenKFix, GenKFold, Run.Gather).
5. Open edge (not done): `ascCol`'s `cells` index column is read by `foRWords` without `noNul`.
