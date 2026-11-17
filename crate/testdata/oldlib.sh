#!/bin/sh
# oldlib.sh BASE_LIB OUT SYM... -- the old side of the Lean-level differential (phase-2 §2.8). Cuts the base sha's
# libqleankernel.a down to the members SYM... reach (the old C exports, the qrs_* shims and C pool they call, the base
# qrs.o), partial-links them into OUT, and prefixes every global OUT defines with `old_`. OUT then links beside the
# task's own library and rust/testdata/rtcount.c without a clash: call `old_qlean_x` against `qlean_x`.
set -eu
[ $# -ge 3 ] || { echo "usage: oldlib.sh BASE_LIB OUT SYM..." >&2; exit 2; }
lib=$1 out=$2
shift 2
us=$(printf -- '-u %s ' "$@")
# shellcheck disable=SC2086 # one `-u sym` word pair per symbol
ld -r $us -o "$out.r" "$lib"
for s in "$@"; do nm -g --defined-only --format=just-symbols "$out.r" | grep -qx "$s" || { echo "oldlib.sh: $s is not defined in $lib" >&2; exit 1; }; done
nm -g --defined-only --format=just-symbols "$out.r" | sed 's/.*/& old_&/' > "$out.map"
objcopy --redefine-syms="$out.map" "$out.r" "$out"
rm "$out.r" "$out.map"
