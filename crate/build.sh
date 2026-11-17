#!/bin/sh
# Builds rust/relk.o and rust/qrs.o (the two crates partial-linked) and regenerates c/rs.h from both with the cbindgen CLI.
#   relk.o: every symbol of relk's own object stays global (qrs.o calls them) except what the crate pulled from core/alloc;
#           the Lean externs it defines are the 94 `qlean_*` of relk.
#   qrs.o:  libqrs.a bundles the relk object too; that member is deleted first, so qrs.o defines only its own `qrs_*` and
#           `qlean_*` and leaves relk's names undefined, to be resolved by relk.o. Everything else in it is local.
# Lake's `qrs.o` target runs this before any C object is compiled, so no C file ever compiles against a header older than
# the Rust. Any failing step stops the script.
# `build.sh symbols` compares what the two objects leave undefined (less what they define) with UNDEF.txt, exactly, and
# fails when both define a name.
# `build.sh abi` instead builds $CARGO_TARGET_DIR/qrs-abi.o: both crates with feature `abi` (the lean.rs twins test/abi.c
# calls) as ONE object, never part of the library.
# `build.sh relk-syms` builds relk ALONE and prints the diff between its staticlib's defined `qlean_*` and rust/RELK.txt.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
# one target dir per worktree: parallel tasks would otherwise take turns on cargo's lock and rebuild each other
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-/data/tmp/qrs/target/$(basename "$root")}"
cd "$here"

# partial-links the staticlib $1 into $2 with only the exported names global
link() {
    syms=$(nm -g --defined-only --format=just-symbols "$1" | grep '^qrs_\|^qlean_' | sed 's/^/-u /')
    [ -n "$syms" ] || { echo "build.sh: no qrs_* or qlean_* symbol defined in $1" >&2; exit 1; }
    # shellcheck disable=SC2086 # one `-u sym` word pair per export
    ld -r $syms -o "$2.r" "$1"
    objcopy --wildcard -G 'qrs_*' -G 'qlean_*' "$2.r" "$2"
    rm "$2.r"
}

# the archive member holding crate $2 of staticlib $1
member() { ar t "$1" | grep "^$2-"; }

if [ "${1:-}" = rt ]; then
    # $CARGO_TARGET_DIR/qrt.o: the Lean runtime a program linked WITHOUT libleanshared needs (the Rel native backend),
    # replacing the C runtime. Never linked into libqleankernel.a, which a Lean build pairs with the real runtime.
    # plt=yes: the default GOT-indirect `call *malloc@GOT` ran copy_byte_array 1.3x slower than rt.c's `call malloc@plt` (perf stat)
    RUSTC_BOOTSTRAP=1 RUSTFLAGS="-D warnings -Z plt=yes" cargo build --release --manifest-path "$here/relk/rt/Cargo.toml" --target-dir "$CARGO_TARGET_DIR/rt"
    lib="$CARGO_TARGET_DIR/rt/release/libqrt.a"
    syms=$(nm -g --defined-only --format=just-symbols "$lib" | grep '^lean_\|^mi_\|^qlean_rt_io$' | sed 's/^/-u /')
    [ -n "$syms" ] || { echo "build.sh: no lean_*, mi_* or qlean_rt_io symbol defined in $lib" >&2; exit 1; }
    # shellcheck disable=SC2086 # one `-u sym` word pair per export
    ld -r $syms -o "$CARGO_TARGET_DIR/qrt.o.r" "$lib"
    objcopy --wildcard -G 'lean_*' -G 'mi_*' -G qlean_rt_io "$CARGO_TARGET_DIR/qrt.o.r" "$CARGO_TARGET_DIR/qrt.o"
    rm "$CARGO_TARGET_DIR/qrt.o.r"
    # the counted twin testdata/rtcount.c wraps: the runtime's own malloc and free renamed, nothing else
    objcopy --redefine-sym malloc=qrt_malloc --redefine-sym free=qrt_free "$CARGO_TARGET_DIR/qrt.o" "$CARGO_TARGET_DIR/qrt-count.o"
    exit 0
fi

if [ "${1:-}" = abi ]; then
    RUSTFLAGS="-C target-cpu=native -D warnings" cargo build --release --lib -p qrs --features abi --target-dir "$CARGO_TARGET_DIR/abi"
    link "$CARGO_TARGET_DIR/abi/release/libqrs.a" "$CARGO_TARGET_DIR/qrs-abi.o"
    exit 0
fi

if [ "${1:-}" = relk-syms ]; then
    RUSTFLAGS="-C target-cpu=native -D warnings" cargo build --release --lib -p relk --target-dir "$CARGO_TARGET_DIR/relk-alone"
    nm -g --defined-only --format=just-symbols "$CARGO_TARGET_DIR/relk-alone/release/librelk.a" | grep '^qlean_' | sort -u > "$CARGO_TARGET_DIR/relk.have"
    sort -u "$here/RELK.txt" > "$CARGO_TARGET_DIR/relk.want"
    diff "$CARGO_TARGET_DIR/relk.want" "$CARGO_TARGET_DIR/relk.have" || { echo "build.sh relk-syms: relk's defined qlean_* differ from RELK.txt (< wanted, > defined)" >&2; exit 1; }
    echo "build.sh relk-syms: $(wc -l < "$CARGO_TARGET_DIR/relk.have") qlean_* defined, equal to RELK.txt"
    exit 0
fi

if [ "${1:-}" = symbols ]; then
    for o in qrs; do [ -f "$here/$o.o" ] || { echo "build.sh: $here/$o.o is not built; run: sh $here/build.sh" >&2; exit 1; }; done
    for o in qrs; do nm -g --defined-only --format=just-symbols "$here/$o.o" | sort -u > "$CARGO_TARGET_DIR/def.$o"; done
    cp "$CARGO_TARGET_DIR/def.qrs" "$CARGO_TARGET_DIR/def.all"
    nm -u --format=just-symbols "$here/qrs.o" | sort -u > "$CARGO_TARGET_DIR/undef.nm"
    comm -23 "$CARGO_TARGET_DIR/undef.nm" "$CARGO_TARGET_DIR/def.all" > "$CARGO_TARGET_DIR/undef.have"
    sed -e '/^#/d' -e '/^[[:space:]]*$/d' "$here/UNDEF.txt" > "$CARGO_TARGET_DIR/undef.rows"
    cut -d' ' -f1 "$CARGO_TARGET_DIR/undef.rows" | sort -u > "$CARGO_TARGET_DIR/undef.want"
    extra=$(comm -23 "$CARGO_TARGET_DIR/undef.have" "$CARGO_TARGET_DIR/undef.want")
    missing=$(comm -13 "$CARGO_TARGET_DIR/undef.have" "$CARGO_TARGET_DIR/undef.want")
    [ -z "$extra" ] || echo "build.sh symbols: relk.o and qrs.o leave these undefined and UNDEF.txt does not list them: $extra" >&2
    [ -z "$missing" ] || echo "build.sh symbols: UNDEF.txt lists these and the objects no longer need them: $missing" >&2
    [ -z "$extra$missing" ] || exit 1
    echo "build.sh symbols: $(wc -l < "$CARGO_TARGET_DIR/undef.have") undefined names, all in UNDEF.txt; nothing defined twice"
    exit 0
fi

RUSTFLAGS="-C target-cpu=native -D warnings" cargo build --release --lib -p relk -p qrs
command -v cbindgen > /dev/null || { echo "build.sh: cbindgen not on PATH; run: cargo install --locked cbindgen" >&2; exit 1; }
# the Lean externs are macro output, which cbindgen reads from the expanded crates (`-Zunpretty=expanded`); a crate's
# header is its own prototypes, so rs.h is relk's (with the mirrors and constants) followed by the prototypes of qrs
for c in relk qrs; do
    CARGO_PROFILE_DEV_PANIC=abort RUSTC_BOOTSTRAP=1 cbindgen --quiet --config "$here/cbindgen.toml" --crate "$c" --output "$CARGO_TARGET_DIR/rs-$c.h" "$here/$c"
done
{ sed '$d' "$CARGO_TARGET_DIR/rs-relk.h"
  awk 'BEGIN { RS = ""; ORS = "\n\n" } NR == FNR { n = split($0, l, "\n"); for (i = 1; i <= n; i++) if (l[i] ~ /^#define /) { split(l[i], w, " "); seen[w[2]] = 1 }; next } { if (/(^|\n)[a-z_0-9 ]+ \*?(qlean|qrs)_[a-z0-9_]+\(/) print; else if (match($0, /#define RS_[A-Z_0-9]+/)) { d = substr($0, RSTART + 8, RLENGTH - 8); if (!(d in seen)) print } }' "$CARGO_TARGET_DIR/rs-relk.h" "$CARGO_TARGET_DIR/rs-qrs.h"
  echo '#endif  /* QLEAN_RS_H */'; } > "$CARGO_TARGET_DIR/rs.h"
# written only on a change, so lake's hash of c/rs.h moves only when the interface does
cmp -s "$CARGO_TARGET_DIR/rs.h" "$root/c/rs.h" || cp "$CARGO_TARGET_DIR/rs.h" "$root/c/rs.h"

link "$CARGO_TARGET_DIR/release/libqrs.a" "$here/qrs.o"
