# Vortex as relk's kernels: not adopted

Decision (owner, 2026-11-18): relk keeps its own kernels and file format; PLAN 6 continues. Vortex 0.93.0
(c1de7e80d7df) was read, not linked.

| Question                         | Finding                                                                                         |
|----------------------------------|-------------------------------------------------------------------------------------------------|
| PLAN 6 primitives                | only `gather` has a counterpart (`take`, lazy, no bounds check); no scan, scatter, sort, distinct |
| relk's 77 exports                | direct 0, adapter 27, keep ours 50                                                              |
| `packed`                         | no byte-exact counterpart; FoR+BitPacked fix 1024-element blocks and fall back to canonical      |
| Load = mmap                      | data buffers mmap zero-copy, but every array is decoded into an `ArrayRef` tree from a flatbuffer |
| Toolchain, deps                  | MSRV 1.95 (relk 1.93.1), no `no_std`, arrow and async in the workspace                           |
| FastLanes layout (spike, below)  | take 0.8–1.5×, compare 1.4–4.6× (median ≈ 2.4×) of relk's AVX-512 coc kernels on the same payload |
| Code size                        | `fastlanes` adds 682 KB `.text`; relk is 115 KB                                                  |

The spike (`/data/tmp/vortex-spike.md`, bench in `/data/tmp/fl-spike/`) compared `fastlanes` 0.8.1 with relk on
u64 columns of 1M and 64M rows at widths 1–32. `pack.rs`'s scalar per-element `res_at` is 40–100× slower than
either; that gap is the scalar loop, not the layout, and relk's existing AVX-512 codec closes most of it.

Follow-up: `pack.rs` reads `packed` through the AVX-512 coc/codec kernels instead of `res_at`; compare-to-constant is
the one op where FastLanes' lane order may pay, so it is re-measured after that change before any layout is copied.
