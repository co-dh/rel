# Benchmarks and gates of the relk kernels

Moved from qlean `rust/BENCH.md` (the sections about the crate that now lives in `crate/`); paths rewritten to this repo.
The qlean-side harnesses (`bench-own`, `bench-kernel`, `bench-coc`, `reach.sh`, `qlean-test`) are qlean binaries and stay
there, so a `qlean-test` or `W/.lake/build/bin/...` mention below is a qlean command, not one of this repo. `T` is a
scratch directory under `/data/tmp`. This repo's own gates are the `Makefile` targets (`make check`).

## Unit gate

`crate/build.sh` compiles `relk.o` with `-C target-cpu=native`, so the unit gate runs `cargo test` twice, once per build the
SIMD paths take: `cd crate; env CAP_MEM_MB=8000 RUSTFLAGS="-C target-cpu=native" CAP cargo test` and the same without
`RUSTFLAGS`. Both exit 0.

## Rel gate

Generated once by `relc-1a` from leetq at 3c08990 (the binary of `.claude/worktrees/agent-aa50fde7c3332431d`,
clean at that commit): `/data/tmp/qrs/rel/c.c` (`relc-1a c`), `/data/tmp/qrs/rel/g.c` (`relc-1a g`). Baseline
exes and the baseline `out` directory, linked against the unported C: `/data/tmp/qrs/rel/base/{c,g}`,
`/data/tmp/qrs/rel/base/run/out`. Per task, with `T` = `/data/tmp/qrs/<task>`:

```
env CAP_MEM_MB=8000 CAP sh crate/build.sh rt                  # once per crate/rt change: T0 = $CARGO_TARGET_DIR, writes T0/qrt.o
cc -O2 -I $(lean --print-prefix)/include -o T/rel-c /data/tmp/qrs/rel/c.c $CARGO_TARGET_DIR/qrt.o W/.lake/build/lib/libqleankernel.a .lake/build/lib/librelk.a -lm -lpthread
cc -O2 -I $(lean --print-prefix)/include -o T/rel-g /data/tmp/qrs/rel/g.c $CARGO_TARGET_DIR/qrt.o W/.lake/build/lib/libqleankernel.a .lake/build/lib/librelk.a -lm -lpthread
mkdir -p T/run/out; T/rel-c T/run; T/rel-g          # both exit 0 (`c` writes into an existing `out`)
nm -u T/rel-c T/rel-g | grep lean_                  # no output
ldd T/rel-c T/rel-g                                 # libc, libm, libpthread, the loader, vdso only
cmp T/run/out/key /data/tmp/qrs/rel/base/run/out/key; cmp T/run/out/val /data/tmp/qrs/rel/base/run/out/val
```

Task B3 (`T` = `/data/tmp/qrs/B3`): both exes built, both exit 0, `nm -u` has no `lean_` name, `ldd` shows libm, libc,
the loader and vdso only, and `key`/`val` are `cmp`-identical to the baseline.

Task RT (`c/rt.c` gone; `crate/rt`, a crate of its own, built by `build.sh rt` into `$CARGO_TARGET_DIR/qrt.o`): rel gate built the new way (recipe above), `T` = `/data/tmp/qrs/RT`: both exes exit 0, `key`/`val` `cmp`-identical to the exes built with rt.c at 4a3ae22 and to the baseline, no `lean_` in `nm -u`, `ldd` libm/libc/loader/vdso, no symbol defined in both `libqleankernel.a` and `qrt.o`, `qrt.o` defines exactly the 18 names rt.c defined (`diff` of the two `nm -g --defined-only` lists empty). Differential `T/rtdiff.c` (every symbol, 20000 random object trees of ctor/array/sarray/string, rc 1 and 2, rc -1/-2, io results, errno texts, 4095-byte truncation) over rt.c and over qrt.o: identical trace hash, 14 die paths identical stderr and exit status, ASan+UBSan clean on both. R/C (15 runs interleaved, min/median, load 0.6): `T/rtmicro.c` ctor+sarray alloc/dec 20M `0.1527/0.1551` (rt.c) vs `0.1457/0.1632`, 2M `mk_string` `0.0153/0.0154` vs `0.0145/0.0150`, 2M `copy_byte_array` `0.0152/0.0155` vs `0.0149/0.0166`; rel-c / rel-g (`perf stat -r 200`, sub-millisecond runs) `279 us` vs `281 us` and `253 us` vs `261 us`. First build was 1.3x slower on `copy_byte_array` (cycles 1.18G vs 0.86G of 20M calls): rustc's default `call *malloc@GOT` against C's `call malloc@plt`, fixed by `-Z plt=yes` in `build.sh rt` (`RUSTC_BOOTSTRAP=1`, as build.sh already does for cbindgen). `rust/testdata/rtcount.c` no longer includes rt.c: it counts `qrt_malloc`/`qrt_free`, which `qrt-count.o` (qrt.o with `malloc`/`free` renamed, also from `build.sh rt`) calls, so every harness that linked `rtcount.c` in place of rt.c now links `rtcount.c qrt-count.o`. The one `exit(1)` rt.c had (`qlean_rt_io`) is libc `exit(1)` still; the aborts keep their `qlean rt: ...` texts.

Pending: `bench-zip` and `bench-coc` baselines (they compile since 8665576; nothing on column (b) reads them).


## Behaviour change: abort instead of exit(1)

Where C printed a message and called `exit(1)`, the ported Rust `panic!`s (the crate is `panic = "abort"`): the message text
is the same, the exit status is 134 (SIGABRT) instead of 1. Found by comparing every `exit(1)` of `master:c/*.c` with
the C now in the tree; one row per site whose `exit(1)` left the C.

| C function (master)                     | message                                          | Rust site                      |
|-----------------------------------------|--------------------------------------------------|--------------------------------|
| coc.c `qlean_coc_encode_raw` (width `default`) | a Frame of Reference element of N bytes   | `enc.rs:218`                   |
| coc.h `res_pack`                        | res_pack asked for width W                       | `res.rs:39` (`assert!`)        |
| scan.c `qlean_scan` (kind)              | element kind K is not one of the N               | `scan.rs:152`                  |
| scan.c `qlean_scan` (verb)              | verb V is not one of the N                       | `scan.rs:229`                  |
| search.c hashed-table macro             | a hashed table numbers its keys in 32 bits       | `search.rs:178`                |
| coc.h `cocf_meta_view` (via the 18 exports) | read blindly (undefined behaviour); Rust: the metadata array is not a column's 33 * nblk + 16 bytes, or the alp array is misaligned or shorter than its header says; exit 1 | `ffi/coc.rs:135` (`fview`) |
| coc.c `coc_val_vv` (verb)               | verb V is not one of the three in QLean.Kernel.Ew; `exit(1)` before and after, status 1 | `ffi/coc.rs:144` (`die`) |
| coc.c scratch buffer (`pod::with_kept`) | out of memory for a N-byte scratch buffer; C eprint + `abort`, Rust eprint + `handle_alloc_error`, status 134 | `pod.rs:85` |
| search.c `kind_of`                      | W got element width ... instantiated at 1, 2, 4, 8 and 16 | `search.rs:72`        |
| sort.c `sk_*` dense-kind check          | element kind K is not one of the N               | `sort.rs:55` (`assert!`)       |
| sort.c `group_bound`                    | group cuts at most 4294967295 rows               | `sort.rs:665`, called by C through `qrs_group_bound` |
| sort.c `pair_ids`                       | groupIdsPair over M rows: X x Y codes do not fit | `sort.rs:698`                  |
| sort.c `grade_narrow` (`qlean_priv_alloc`) | N narrow histograms of B buckets failed to allocate | no message: the `Vec` allocation in `sort.rs:356` `hist_narrow` aborts in Rust's allocator |
| reduce.c `qlean_group_cells` (short `m`) | qlean_group_cells: B slot bytes for N groups at width W | `ffi/reduce.rs:85` (B6) |
| structural.c `unequal blocks` gather at width 16 (A37) | none: C misread its decode buffer (undefined behaviour), no `exit(1)` | `structural.rs:481` `assert!(W <= 8)` |
| elementwise.c `ew_width` (`qlean_ew_val`, `qlean_coc_ew_val_atom`, `qlean_coc_ew_val`, B11) | qlean_ew: storage class C has no dense element width | `ew.rs:24` via `ffi/ew.rs` |
| sym.h `off_at` (`qlean_ew_rank_pair`, `qlean_ew_cmp_ids_key`, B11) | qlean: symbol offset I is a bignum; an offset is bounded by the blob's byte count and cannot reach 2^63 | `sym.rs:22` `Syms::off`, a bignum read as an even word by `ffi.rs` `syms_of` |
| elementwise.c `qlean_ew_fixed_hits`, `qlean_ew_ssr` (`xalloc` of the match buffer, B13) | the ss hits / the ssr hits: out of memory | Rust allocation failure of `pod::uninit` in `ffi/ew.rs` (no message text; `abort`) |
| elementwise.c `ew_unsupported` (`qlean_ew_mon`, `_coc_ew_mon[_enc]`, `_floor`, `_cast`, `_widen`, `_bit`, B13-B14) | qlean_ew_X: no case for verb V at storage class C. ... | `ew.rs:12` via `ffi/ew.rs` |
| sort.c `xalloc` scratch of the symbol, id and group exports (`qlean_sort_grade_syms` .. `qlean_sort_group_syms`, S2) | qlean: malloc of N x S bytes for the first-occurrence indices / the id group table / the group of each row ... failed | Rust allocation failure of `pod::uninit` / `vec!` in `ffi/symsort.rs` (no message text; `abort`) |
| sym.h `off_at` (the symbol and id exports of `ffi/symsort.rs`, S2) | qlean: symbol offset I is a bignum ... | `sym.rs:22` `Syms::off` through `syms_of` |

| sort.c `sk_dense_width` via `distinct_foR`/`group_foR`/`group_ids_foR`/`parted_foR` (S1), kind bit or outside the eight | element kind K has no dense width (impossible: an encoded column is never a bit or key payload); C: the longer text naming Scan.lean, `exit(1)` | `kwin.rs:25` (`panic!`), status 134 |
| structural.c `xalloc` in `qlean_structural_gauss_jordan` ("the augmented matrix"), `qlean_structural_concat_ids` ("the parts of concatIds", "the part sizes of concatIds", "the widths of concatIds"), `qlean_symdict_concat` ("the concat parts") (T1) | out of memory for a N-byte buffer: the name above | no message: the `Vec` allocation of the Rust export aborts (`alloc_error`) |
| sym.h `off_at` (`qlean_match_syms`, `qlean_search_match_ids`, `qlean_search_match_syms_ids`, `qlean_search_run_starts_syms`, Q1) | qlean: symbol offset I is a bignum; an offset is bounded by the blob's byte count and cannot reach 2^63 | `sym.rs:22` `Syms::off` via `ffi::syms_of`, in `ffi/search.rs` |
| elementwise.c `qlean_ew_chain_enc` (result width vs the last stage's bits, E) | qlean_ew_chain_enc: the result type is W bytes wide and the chain's last stage answers B bits. ... | `ew.rs` `enc_cls` via `ffi.rs` `chain_enc` |
| elementwise.c `ew_width` (chain stages: `ew_val_run`, `qlean_ew_chain*`, E) | qlean_ew: storage class C has no dense element width | `ew.rs:23` `ew_width` |

C sites that still carry their own `exit(1)` are unchanged (env.c, sym.h, structural.c, the rest of
coc.c/scan.c/sort.c); where a Rust duplicate of the same text exists (`ew.rs:15,24`, `structural.rs:73,427,606,616,860`,
`sym.rs:16`, `unpack.rs:32`) it fires only for a Rust caller that C's own check does not reach first.

## Task K5 (`ew_val_run` and its helpers, float `pow`)

Symbols gate, allowed undefined (design §6): the 12 libc names of §1 and, since K5, the libm names the crate calls:
`pow` (`c::pow`, the one `extern "C"` libm declaration, in `c.rs` where `unsafe` is already allowed, so the unsafe set
stays `c.rs ffi.rs lib.rs pod.rs rt.rs simd.rs`). Each later libm name (K9's nine float maps) is added here and
declared next to `pow`. `ew_val_run` in C is now the thin adapter over `qrs_ew_val` (serial runner) that the chain stage
and the two encoded runs (K6) call; `qlean_ew_val` calls `qrs_ew_val` for every verb. Reach (`bench-kernel 10000000 5`,
run directly under gdb, no `cap`, since gdb does not follow `cap`'s exec): `qrs_ew_val hit 1171930`; `qlean-test`:
`qrs_ew_val hit 904260`, `ew_val_run hit 904260`, `qrs_ew_val` with `op = 9` (pow) hit.

## Task K9 (the nine float maps, `ew_serial`, the chain's widen/decode/alp/ids/pack/enc workers)

Symbols gate, allowed undefined: K5's list plus the libm names the nine maps call, `acos asin atan cos exp log sin tan`
(`sqrt` is the instruction `sqrtsd`, so it is not an undefined name). All ten libm names are declared by one `libm!`
macro in `c.rs` (the unsafe set stays `c.rs ffi.rs lib.rs pod.rs rt.rs simd.rs`, plus `lean.rs`/`os.rs` of phase 2);
there is no `m.rs`. The libm loops are `ew::mon_map`, one straight loop per map (the `op` switch is outside it), the
same call an element as C's `__builtin_*`. `qlean_ew_mon` and the chain's `ew_mon_stage` call `qrs_ew_mon` for every verb.
`ew_serial` is `c::serial`, exported as `qrs_serial` for the C adapters that hand it to a `qrs_ew_*` entry as the runner.
The chain workers in C are one-line adapters over `qrs_ew_{widen,decode,alp,ids,pack}_stage`, `qrs_enc_for_meta/pack`;
their pool entry (`ew_stage_worker`, `ew_chain_build`) is K10's. `ew_val_run` keeps its callers (the chain's `EW_E_VAL`
worker and the two foR runs), so it stays. Differential: `/data/tmp/qrs/K9/diff.c`, elementwise.c of b95e0b7 (every
global renamed `old_*`) against the library, entries `qlean_ew_mon`, `qlean_ew_widen`, `qlean_ew_chain`,
`qlean_ew_chain_enc`.

Task K14 (`dedup` family to `rust/src/group.rs`, `qrs_dedup`, `qrs_sort_gather`): reach under `qlean-test`: `qrs_dedup` 803
hits, `qrs_sort_gather` 395; `qrs::group::part` 101 hits against 101 for the old `part_dedup`. Differential against the base
`sort.c` (0 mismatches over 15842 `dedup` calls, all 8 kinds, foR and ALP sources). C helpers kept for K15: `group_probe`,
`SK_EACH` (`parted_of`), `range_of`, `key_at`, `key_flip`, `kwin_*` (`parted_foR`, the `dfill` callers), `sk_write_width`.

K14p (perf fix before merge). The one-thread harness `/data/tmp/qrs/K14/pb.c` (the base `dedup` against `qrs_dedup`, -O3 -march=native,
min of 7 whole-process cycles by `perf stat`, `pbmin.sh`; `allrows.sh` runs every row) showed `distinct til 1e7` at 1.18 and `group 1e7 mod 1000`
at 1.06. The range pass was not the cost (`key::Range` already compiles to `vpminuq`/`vpmaxuq`, and the harness times only `dedup`); the cost
was the bitmap and direct loops, which `perf annotate` showed carrying a bounds test per index and a worse block layout:
- `bitmap` (the `distinct til` row, 17 instructions an element in C): `n.min(k.len())` and a cut `first` drop the key and `first` tests;
  `first` is walked as a shrinking slice (`rest`), which also drops the second copy of `ng`; the word switch is marked unlikely by calling a
  `#[cold]` function (rustc 1.93 has no stable `cold_path`), which leaves the same-word path with one taken branch where it had three.
- `direct`: `&mut tab[..]` taken once and held (one test of `tab` an element, not two), `n.min(k.len())` and a cut `first`.
- `hashed`: `gkey` is an `uninit` slice and a counter, not a `Vec::push` (a capacity test and a grow call in the loop); `slot` is
  indexed `& mask`, which is the shift's own range, so LLVM drops that test; one load of `slot[s]` per probe.
- `part`: the bucket index `& (nb - 1)`, each bucket cut once as `run`.
Whole-process cycles C / R, min of 7 (instructions in G): see the table in the task report; every row within 1.05 except `group 1e6 wide` (1.05 to
1.08 over three repeats; `part`'s `rank`/`cnt` indexes are values, not bounded by a mask, so their tests stay).
`bench-kernel 10000000 5`, `group i64`, interleaved C (`base/bench-kernel-p0`) and R, `QLEAN_THREADS=8 taskset -c 0-7`: C 43.1, 44.3, 62.5 ms against R 43.7,
55.5, 60.4 ms (the machine was loaded by other builds from the third pair on; a second batch under load read R 92.0, C 77.5, R 71.4). Min C 43.1, min R 43.7 (1.014).

## Task G1R — per-column block size (`lg` in the 24-byte metadata trailer)

Differential (`/data/tmp/qrs/G1R/diff.c`, base 531a1b9 as `old_*` against HEAD over `qrt-count.o`/`rtcount.c`; 2000 random columns of widths
2/4/8 and 7 value shapes at n in {0, 1, 63 .. 3072, random < 5000}, plus 2000 ALP columns): 150350 comparisons, 0 mismatches, live objects
steady. Metadata equal after inserting `lg = 10` at `32n + 16`; every other answer by `objeq` or equal bits. Families: coc encode and
encode_below, decode, over (add, mul, min, max, all, any), count_lt, any_null, mask_cmp and mask_cmp_vv, shift, val_vv, val_prior, scale,
ew val/val_atom/mon, ew chain enc, find_scalar/find_vec/member_vec, gather_foR and gather_foR_idx, reverse/cycle/shift/concat_foR, and ALP
encode f64/f32, decode, sum, min, max, gather, mask_lt, reverse.
R/C (`/data/tmp/qrs/G1R/micro.c`, old = 531a1b9, same process, alternated, 15 runs, n = 4e6, load average 5-7 from other agents' builds):
`QLEAN_THREADS=8 taskset -c 0-7` reads are noisy (ratios 0.8 .. 1.3 between repeats), so the verdicts come from `QLEAN_THREADS=1 taskset -c 3`,
three repeats, min ratio: sum 1.00-1.04, decode 0.97-1.01, find foR 0.94-0.97, gather foR 1.00, count_lt 1.03-1.06, chain enc 1.07-1.09,
encode 1.09-1.11, group_ids foR (the `Kwin` path) 1.11-1.13. Fixed by perf: `count_lt` re-derived `blk` per block (hoisted, 1.11 -> 1.05),
`Scr::new` moved an 8 KB struct (now `inline(always)`), `pack_exc_blk` filled its scratch twice and dereferenced it per element
(`Scr::filled`, one slice; instructions +13% -> +2%). Left above 1.03: encode, chain enc, group_ids and count_lt, whose per-block loops now run to
a runtime `blk` where the old ones ran to the constant 1024 (`c::slice` and `res_unpack_add` +8-12% cycles at equal instruction counts);
a `blk == 1024` instantiation of those loops is the next step if G2 keeps the default.
