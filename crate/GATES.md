# Gates of the relk crate

Moved from qlean `rust/GATES.md` (the parts about the crate that now lives in `crate/`); paths rewritten to this repo.
This repo's own gates are the `Makefile` targets (`make check`); `make syms` is `sh crate/build.sh syms` below.
`CAP` = `/home/dh/repo/freyd/scripts/cap`, `T` = a scratch directory under `/data/tmp`,
`CARGO_TARGET_DIR` defaults to `/data/tmp/relk/target/<checkout name>` in `crate/build.sh`. Never piped into `tail`,
never `|| true`.

## symbols

`crate/RELK.txt` lists the `qlean_*` exports of this crate (no copy anywhere else). `sh crate/build.sh syms` builds the
crate alone and requires its defined `qlean_*` to equal `RELK.txt` exactly (an extra name and a missing name both fail,
exit 1), that the extern_lib object has no `DW.ref.rust_eh_personality`, and that `--no-default-features` defines no
`qlean_*`.

Every runtime name a downstream Rust object (qlean's `qrs.o`) leaves undefined must be one that `crate/rt` (`qrt.o`)
defines:

```
env CAP_MEM_MB=8000 CAP sh crate/build.sh rt         # $CARGO_TARGET_DIR/qrt.o (and qrt-count.o)
nm -u --format=just-symbols QRS.o | grep '^lean_\|^mi_' | sort > T/rt-need.txt
nm -g --defined-only --format=just-symbols $CARGO_TARGET_DIR/qrt.o | sort | comm -23 T/rt-need.txt -   # empty
```

`QRS.o` is qlean's object, so that check is run from qlean.

## unsafe

```
grep -L 'forbid(unsafe_code)\|deny(unsafe_code)' crate/src/*.rs      # relk: c ffi lean lib os pod pool rt simd
grep -l 'allow(unsafe_code)' crate/src/*.rs crate/src/ffi/*.rs       # crate/src/lean.rs only
grep -cw unsafe crate/src/ffi/*.rs                                   # 0 for every file (`unsafe_code` is not the word)
grep -L "deny(unsafe_op_in_unsafe_fn)" crate/rt/src/lib.rs           # empty: crate/rt is its own crate, `allow(unsafe_code)` in one file, lean.rs shared by path
```

## G1R — golden metadata at the 24-byte trailer

`crate/testdata/alp.bin` keeps the C encoder's old trailer: the stream's records are parsed only by
`alp::tests::differential`, so the 24-byte trailer insertion is done there by `old_trailer` while it reads each metadata
blob (regenerating the file means a second copy of that parser). The `testdata/col{1,2,4,8}.meta` goldens are qlean's.
