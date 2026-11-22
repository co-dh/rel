# rq17d handoff

## Done (committed on branch worktree-agent-adbee1ddf5bc8bcdd)

- Lean kernel bodies (compile: `Rel.Kernel.Gather`, `Rel.Kernel.Seen` build):
  - `Rel/Kernel/Scatter.lean`: `hasNul` (width bytes only), `foRNuls` (row null flag as a word, `Column.foRNul`),
    `noNul what m e` (error `"{what}: row k is null, and a null names no row"`), `nulMap`, `wordsFoR ws (nul := .empty)`.
    `kscatter`: `noNul ix`; op other than `.last` refuses a null of `e` (`"scatter: e under op {ctorIdx}: row k ..."`);
    `.last` scatters `foRNuls e` with the same indices into the answer's null bitmap.
  - `Rel/Kernel/Gather.lean`: `kgather` refuses a null index, gathers `foRNuls e` with the same indices.
  - `Rel/Kernel/Asc.lean`: `nulCodes m e c` (`[c]` without a null; else `[1 - flag, c with 0 at a null]`), used by the
    `atom` branch of `ascCol`; `kasc` carries each column's null bits through `r`. `kseen` unchanged (reads `ascCol`).
  - Without a null every path is the old one: `if hasNul e` guards each null computation, so existing bytes and
    `decide` cost are unchanged.
- Tests added (not yet run — they need the RelKernel shared library, which needs all of KernelSpec to build):
  `GatherTest` (null gathered, null index error), `ScatterTest` (null under last, value overwrites null, null under
  add error, null index error), `AscTest` (`bview`, nulls first), `SeenTest` (nulls one group, null with residual
  word 7 vs value 7 two groups, value-before-null unsorted).
- Rust (`cargo test --features std`: 74 passed): `cocops.rs` `Coc::patch`/`res`/`is_nul`/`nuls`; `ffi/scatter.rs`
  `no_nul`, `qlean_k_scatter` null checks; `scatter.rs` `LAST`, `blocks(.., nul)` writes the answer's null bits in
  pass 1 and `Sink::write_nul`; `gather.rs` `enc` gathers `e.nuls()` by `ix` a block at a time; `ffi/gather.rs` order
  ix view, e view, `no_nul ix`; `asc.rs` `Col::Nul(Key, bitmap)`, `work` returns `Vec<Vec<u64>>` (Nul: two columns),
  `rank`/`grade_cols` flat_map; `ffi/asc.rs` key → `Col::Nul` when `c.nuls()`, `kasc` sorts the null bits by `p`;
  `seen.rs` reads every code column (`src`), Nul/Cells through `asc::work`.
- `KernelSpec/Scatter.lean`: `raw_scatter`, `kscatter_pos_ix` take `(hnul : hasNul e = false)`; builds.

## Not run yet

- `sh crate/build.sh syms`, the `#guard`/`decide` pairs, full `lake build RelCore RelKernel RelRun Rel`.

## Left: the proof migration (design fork, needs the owner)

Every raw-level kernel theorem is false for an input holding a null (its re-encoded null row does not read back the
input's residual word). Current failures (`lake build RelKernel`, log /data/tmp/job/rq17d-8.log):

- `Rel/KernelSpec/Asc.lean:157` `ascCol_ok` (`ascKey` must become `nulCodes m e (...)`), `:262` `kasc_ok` (`vs =
  wss.map wordsFoR` now `wss.zipWith wordsFoR ns`), `:373` `kasc_pos_key`, and `#guard_msgs` at 503/507/511 follow.
  `ascKeys_row` (line ~120) says a row's codes depend only on its raw words: false with nulls (needs the flags too).
- Then expected: `KGather` (`raw_kgather`, `kgather_pos_e/ix`), `KSeen`, `Closure` (`k*_closed`), `BitRows`, and in
  `Rel` ~50 uses (`GenKBits` 12, `RepCanon` 16, `RepSetOps` 13, `RepTabComp` 3, `RepCols` 2, `Run.Gather`, …; query
  `use_site` for `raw_kgather raw_scatter kasc_ok kseen_ok asc_perm asc_sorted k*_closed ascCol_ok`).

Two routes:
- A: each theorem takes `hasNul e = false` (as `raw_scatter` now does); discharge it downstream by adding
  `hasNul e = false` to `Ext.Enc.WF t n e`'s `foR` case for every current type (no type has a `1` until step 2), and
  proving `hasNul (wordsFoR ws) = false` in `wordsFoR_closed` (width byte = `planOf` width ≤ 64 < 128 when `nul` is
  empty). Step 2 (`Vals (.sum (.atom t) .one)`) then adds the null-aware statements.
- B: restate the kernel theorems over a null-aware read (`foROpt`) now; larger, but it is what step 2 needs anyway.

Open edge: a `cells` key's own column (cell indices) is read by `foRWords` in `ascCol`; a null there is not refused.
