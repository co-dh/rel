# rq17e handoff (route B: kernel theorems over the null-aware read)

Branch `worktree-agent-ac58f9733a568196d`: master d8030bc + rq17d (8d0bbba, merged clean).

## State per module (RelKernel; Rel downstream not built yet)

| Module                    | State                                                                                          |
|---------------------------|------------------------------------------------------------------------------------------------|
| Rel.KernelSpec.Encoding   | green: `foROpt_encode` (null-aware round trip, hyp `hmax`), `foRBits_encode` its `.empty` case, |
|                           | new `planBlock_plain/_nul/_byte/_inside`, `any_nul_of`                                          |
| Rel.KernelSpec.Alp        | green: `nblk_encode`, `foRWF_encodeAt` now for every `nul` (layout holds with null blocks)     |
| Rel.KernelSpec.Raw        | green (unchanged; `raw_encodeAt` still `.empty` only)                                          |
| Rel.KernelSpec.Scatter    | green: `kscatter_ok` (all inputs: words `ws` + flags `fl`, encoded with `nulMap fl`);          |
|                           | `raw_scatter` = its `hasNul e = false` case; Law S1 `kscatter_pos_ix` restated (answer = e's   |
|                           | words and flags re-encoded); `foRNuls_size` lives here                                         |
| Rel.KernelSpec.Asc        | green: `ascKey` atom = `nulCodes`; `nulCodes_row`; `ascKeys_row` takes equal `hasNul` and      |
|                           | flags; `kasc_ok`/`asc_perm`/`kasc_pos_key`/`kasc_pos_first` carry the scattered flags `ns`     |
| Rel.Kernel.Asc + Rust     | `ascCol` cells: `noNul` on ix, lo, hi (Lean body and crate/src/ffi/asc.rs, same order)          |
| Rel.KernelSpec.KGather    | green: `raw_kgather` answer `wordsFoR gathered (if hasNul e then nulMap gatheredFlags else ∅)`;|
|                           | G1 `kgather_pos_ix` restated with flags, G2 unchanged                                          |
| Rel.KernelSpec.KSeen      | green (pos case unfolds `nulCodes`)                                                            |
| Rel.KernelSpec.EwEnc      | green; 2 `#print axioms` pins now include `Classical.choice` (via `foRBits_encode`)            |
| Rel.KernelSpec.Closure    | FAILING :171 `kscatter_closed`: the `split at h` chain no longer matches the kscatter body     |
|                           | (noNul ix, op match, scatterWords, nul `if`). New `wordsFoR_valid ws nul` (green) is the lemma |
|                           | to close it with: get `ws`, `nul` with `scatterWords_size` and `exact wordsFoR_valid ws nul _`.|
|                           | `kgather_closed` already uses `wordsFoR_valid`.                                                |
| BitRows, kernel tests     | not reached (blocked behind Closure)                                                           |
| Rel (RepCanon, RepSetOps, | not built. Callers to update: `ascKeys_row` (new 3rd hyp), `kasc_ok`/`asc_perm` (new `ns`/nul  |
| RepCols, RepTabComp, …)   | outputs), `raw_kgather` (nul arg of `wordsFoR`), `raw_scatter` (needs `hasNul e = false` where |
|                           | they had none: derive it, or move them to `kscatter_ok`)                                        |

Gates not yet run: `cargo test --features std`, `sh crate/build.sh syms`, kernel tests' #guard/decide, full build.

## Owner decision needed (encoder)

`hmax` in `foROpt_encode` is real: `Coc.nulBlock` does not widen a block whose non-null keys span all `2^64`.
Instance: w = 8, one block holding `Int64.min`, `Int64.max` and a null: `d = 64`, `Int64.max - Int64.min = ones 64`, so
the `Int64.max` row reads as null. Fix that removes `hmax` (general): put a non-null row whose residual is `ones d` in
a null-holding block on the patch list, in `Coc.encodeAt`'s `exc` filter and `crate/src/enc.rs`. Not done (Rust writer).
The route-B kernel laws above avoid it by describing answers as `Coc.encode ws (nulMap fl)` rather than by `raw`.

## Next

1. Closure `kscatter_closed` (above), then `lake build RelKernel`, kernel tests.
2. Null-aware `raw_encodeAt` (Raw.lean:105) from `foROpt_encode` once `hmax` is decided.
3. Rel downstream callers (list above).

# rq17g (null code never denotes a value)

Done: `Coc.patched lst f d k = outside f d k || lst && 128 ≤ d && (k - f) == ones (d % 128)` is the one patch test of
`Coc.encodeAt` (pack and patch list); `lst = decide (n < 2 ^ 32)` (a column that can carry a patch list). Rust
`enc::nul_meta` counts and `nul_pack` writes the same patches (`nul_pack` now packs through `pack_block`, which also
fixes a panic at power-of-two widths: `res_pack` refuses them). `hmax` gone; `foROpt_encode` keeps `hbig` only for
`2 ^ 32 ≤ n` (no patch list there, so a null block spanning all 2^64 keys is unrepresentable). New `rawOpt_encodeAt`
(Raw). CocTest pair `readN [Int64.min, Int64.max, 0] [2]`; cargo test `encode_nul_patches_a_value_at_the_null_code`.
Green: Coc, Encoding, Alp, Raw, KernelSpec.Scatter, KernelSpec.Asc; cargo 75 passed; `build.sh syms` 0.
Not run: CocTest's `#guard`s (need the RelKernel dynlib, blocked by Closure :171, rq17f); its `decide +kernel` passed.
Proof note: generalize `decide (n < 2 ^ 32) = lst` right after `pl`; without it `generalize (Array.foldl _ …).1 = pack`
times out in `whnf`.
