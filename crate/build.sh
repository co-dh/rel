#!/bin/sh
# Builds rust/qrs.o (the crate partial-linked, every symbol but qrs_* made local) and regenerates c/rs.h from the
# crate's `ffi` module with the cbindgen CLI. Lake's `qrs.o` target runs this before any C object is compiled,
# so no C file ever compiles against a header older than ffi.rs. Any failing step stops the script.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
# one target dir per worktree: parallel tasks would otherwise take turns on cargo's lock and rebuild each other
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-/data/tmp/qrs/target/$(basename "$root")}"
cd "$here"
RUSTFLAGS="-C target-cpu=native -D warnings" cargo build --release --lib
command -v cbindgen > /dev/null || { echo "build.sh: cbindgen not on PATH; run: cargo install --locked cbindgen" >&2; exit 1; }
cbindgen --quiet --config "$here/cbindgen.toml" --crate qrs --output "$CARGO_TARGET_DIR/rs.h" "$here"
# written only on a change, so lake's hash of c/rs.h moves only when the interface does
cmp -s "$CARGO_TARGET_DIR/rs.h" "$root/c/rs.h" || cp "$CARGO_TARGET_DIR/rs.h" "$root/c/rs.h"
a="$CARGO_TARGET_DIR/release/libqrs.a"
syms=$(nm -g --defined-only --format=just-symbols "$a" | grep '^qrs_' | sed 's/^/-u /')
[ -n "$syms" ] || { echo "build.sh: no qrs_* symbol defined in $a" >&2; exit 1; }
# shellcheck disable=SC2086 # one `-u sym` word pair per export
ld -r $syms -o "$CARGO_TARGET_DIR/qrs-r.o" "$a"
objcopy --wildcard -G 'qrs_*' "$CARGO_TARGET_DIR/qrs-r.o" "$here/qrs.o"
