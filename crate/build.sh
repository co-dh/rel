#!/bin/sh
# Builds relk's link objects from crate/ alone.
#   build.sh OUT.o  relk's staticlib partial-linked into ONE object OUT.o with only the `qlean_*` Lean externs global,
#                   everything else local, so `libleanshared`'s and the C library's names cannot collide with relk's
#                   internals. The lakefile's `extern_lib relk` archives it as `librelk.a`.
#   build.sh rt     $CARGO_TARGET_DIR/qrt.o: the Lean runtime a Rel native program links instead of `libleanshared`.
#   build.sh syms   builds relk ALONE and diffs its staticlib's defined `qlean_*` against RELK.txt (kernels)
#                   + RELIO.txt (IO), which must be disjoint, then builds it with
#                   --no-default-features (no `ffi`) and requires zero `qlean_*` defined.
# Any failing step stops the script.
set -eu
# Two Rust objects in one link share the COMDAT signed by DW.ref.rust_eh_personality and the linker keeps one copy, which
# breaks the other's unwind references; each object renames its own signature, so no downstream Rust object has to.
eh=DW.ref.rust_eh_personality
# (the group signature and the symbol; the member sections keep their .data.DW.ref.* names, which collide with nothing)
noeh() { if { readelf -g "$1" | grep -F "[$eh]"; nm "$1" | grep -F " $eh"; } >&2; then echo "build.sh: $1 still has $eh" >&2; exit 1; fi; }
here=$(cd "$(dirname "$0")" && pwd)
# one target dir per checkout: parallel worktrees would otherwise take turns on cargo's lock and rebuild each other
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-/data/tmp/relk/target/$(basename "$(dirname "$here")")}"
cd "$here"

if [ "${1:-}" = rt ]; then
    # Never linked into librelk.a, which a Lean build pairs with the real runtime.
    # plt=yes: the default GOT-indirect `call *malloc@GOT` ran copy_byte_array 1.3x slower than rt.c's `call malloc@plt` (perf stat)
    RUSTC_BOOTSTRAP=1 RUSTFLAGS="-D warnings -Z plt=yes" cargo build --release --manifest-path "$here/rt/Cargo.toml" --target-dir "$CARGO_TARGET_DIR/rt"
    lib="$CARGO_TARGET_DIR/rt/release/libqrt.a"
    syms=$(nm -g --defined-only --format=just-symbols "$lib" | grep '^lean_\|^mi_\|^qlean_rt_io$' | sed 's/^/-u /')
    [ -n "$syms" ] || { echo "build.sh: no lean_*, mi_* or qlean_rt_io symbol defined in $lib" >&2; exit 1; }
    # shellcheck disable=SC2086 # one `-u sym` word pair per export
    ld -r $syms -o "$CARGO_TARGET_DIR/qrt.o.r" "$lib"
    objcopy --wildcard -G 'lean_*' -G 'mi_*' -G qlean_rt_io --redefine-sym $eh=DW.ref.relk_eh_personality "$CARGO_TARGET_DIR/qrt.o.r" "$CARGO_TARGET_DIR/qrt.o"
    rm "$CARGO_TARGET_DIR/qrt.o.r"
    noeh "$CARGO_TARGET_DIR/qrt.o"
    exit 0
fi

RUSTFLAGS="-C target-cpu=native -D warnings" cargo build --release --lib
lib="$CARGO_TARGET_DIR/release/librelk.a"

if [ "${1:-}" = syms ]; then
    nm -g --defined-only --format=just-symbols "$lib" | grep '^qlean_' | sort -u > "$CARGO_TARGET_DIR/relk.have"
    sort -u "$here/RELK.txt" > "$CARGO_TARGET_DIR/relk.kernels"
    sort -u "$here/RELIO.txt" > "$CARGO_TARGET_DIR/relk.io"
    # a name in both files would be counted twice as "wanted" and hide that the lists overlap
    comm -12 "$CARGO_TARGET_DIR/relk.kernels" "$CARGO_TARGET_DIR/relk.io" > "$CARGO_TARGET_DIR/relk.both"
    [ ! -s "$CARGO_TARGET_DIR/relk.both" ] || { echo "build.sh syms: listed in both RELK.txt and RELIO.txt:" >&2; cat "$CARGO_TARGET_DIR/relk.both" >&2; exit 1; }
    sort -u "$CARGO_TARGET_DIR/relk.kernels" "$CARGO_TARGET_DIR/relk.io" > "$CARGO_TARGET_DIR/relk.want"
    diff "$CARGO_TARGET_DIR/relk.want" "$CARGO_TARGET_DIR/relk.have" || { echo "build.sh syms: relk's defined qlean_* differ from RELK.txt + RELIO.txt (< wanted, > defined)" >&2; exit 1; }
    echo "build.sh syms: $(wc -l < "$CARGO_TARGET_DIR/relk.have") qlean_* defined = $(wc -l < "$CARGO_TARGET_DIR/relk.kernels") in RELK.txt + $(wc -l < "$CARGO_TARGET_DIR/relk.io") in RELIO.txt, disjoint"
    sh "$here/build.sh" "$CARGO_TARGET_DIR/relk.syms.o"
    echo "build.sh syms: no $eh in the extern_lib object"
    # a crate that links beside the rel package's object (which defines every qlean_*) must define none
    # no export is a root here, so every item is dead: the default build above, with -D warnings, is the dead-code gate.
    # Every other warning (an import or variable only this configuration leaves unused) still fails here.
    RUSTFLAGS="-C target-cpu=native -D warnings -A dead_code" cargo build --release --lib --no-default-features
    nm -g --defined-only --format=just-symbols "$lib" | { grep '^qlean_' || true; } | sort -u > "$CARGO_TARGET_DIR/relk.nofeat"
    [ ! -s "$CARGO_TARGET_DIR/relk.nofeat" ] || { echo "build.sh syms: --no-default-features still defines qlean_*:" >&2; cat "$CARGO_TARGET_DIR/relk.nofeat" >&2; exit 1; }
    echo "build.sh syms: --no-default-features defines 0 qlean_*"
    exit 0
fi

out="${1:?usage: build.sh OUT.o | rt | syms}"
syms=$(nm -g --defined-only --format=just-symbols "$lib" | grep '^qlean_' | sed 's/^/-u /')
[ -n "$syms" ] || { echo "build.sh: no qlean_* symbol defined in $lib" >&2; exit 1; }
# shellcheck disable=SC2086 # one `-u sym` word pair per export
ld -r $syms -o "$out.r" "$lib"
objcopy --wildcard -G 'qlean_*' --redefine-sym $eh=DW.ref.relk_eh_personality "$out.r" "$out"
rm "$out.r"
noeh "$out"
