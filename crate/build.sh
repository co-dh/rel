#!/bin/sh
# Builds rust/qrs.o (the crate partial-linked, every symbol but qrs_* and the qlean_* Lean externs made local) and
# regenerates c/rs.h from the crate with the cbindgen CLI. Lake's `qrs.o` target runs this before any C object is
# compiled, so no C file ever compiles against a header older than the Rust. Any failing step stops the script.
# `build.sh abi` instead builds $CARGO_TARGET_DIR/qrs-abi.o: the same crate with feature `abi` (the lean.rs twins
# test/abi.c calls), never part of the library.
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

if [ "${1:-}" = abi ]; then
    RUSTFLAGS="-C target-cpu=native -D warnings" cargo build --release --lib --features abi --target-dir "$CARGO_TARGET_DIR/abi"
    link "$CARGO_TARGET_DIR/abi/release/libqrs.a" "$CARGO_TARGET_DIR/qrs-abi.o"
    exit 0
fi

RUSTFLAGS="-C target-cpu=native -D warnings" cargo build --release --lib
command -v cbindgen > /dev/null || { echo "build.sh: cbindgen not on PATH; run: cargo install --locked cbindgen" >&2; exit 1; }
# the Lean externs are macro output, which cbindgen reads from the expanded crate (`-Zunpretty=expanded`)
RUSTC_BOOTSTRAP=1 cbindgen --quiet --config "$here/cbindgen.toml" --crate qrs --output "$CARGO_TARGET_DIR/rs.h" "$here"
# written only on a change, so lake's hash of c/rs.h moves only when the interface does
cmp -s "$CARGO_TARGET_DIR/rs.h" "$root/c/rs.h" || cp "$CARGO_TARGET_DIR/rs.h" "$root/c/rs.h"
link "$CARGO_TARGET_DIR/release/libqrs.a" "$here/qrs.o"
