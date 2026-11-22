//! qlean's kernels in Rust, linked into `libqleankernel.a` as the rel package's object. The Lean externs of `ffi/*.rs` leave the
//! object (`qrs_abi_*` beside them with feature `abi`). `unsafe` is confined to c.rs, ffi.rs, lean.rs, lib.rs, os.rs, pod.rs, pool.rs,
//! rt.rs, simd.rs; every other module refuses it, and `ffi/*.rs` denies it (their one `allow` comes from `lean::export!`).
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![deny(unsafe_op_in_unsafe_fn)]
extern crate alloc;

/// The block size every encoder writes, as `lg` in a column's metadata trailer (`blk = 1 << lg`, `MIN_LG <= lg <= MAX_LG`):
/// the one place 10 is written.
pub(crate) const DEFAULT_LG: u32 = 10;
/// tests that name the default block by its size
#[cfg(any(test, feature = "std"))]
pub(crate) const BLK: usize = 1 << DEFAULT_LG;
pub(crate) const MIN_LG: u32 = 6;
pub(crate) const MAX_LG: u32 = 16;

/// a straight-line move, no arithmetic. 3, not 2: a move writes a fresh answer and its page faults are the cost, so
/// at 2 a 4 MB answer ran on one thread -- `prev` on 1M reals or 500k floats 120-148us serial against 22-33 split
pub(crate) const QLEAN_COST_COPY: u32 = 3;
/// the element-wise verbs and the comparisons
pub(crate) const QLEAN_COST_ARITH: u32 = 4;
/// a libm call
pub(crate) const QLEAN_COST_MATH: u32 = 12;

// the runtime and the C declarations are not interface: cbindgen skips both
/// cbindgen:ignore
#[cfg(not(any(test, feature = "std")))]
mod rt;
/// cbindgen:ignore
mod c;
/// cbindgen:ignore
mod ffi;
// `pub`: `crate/rt` includes this file by path and uses items no export here reaches, so dead-code analysis of
// this crate alone must not prune it
pub mod lean;
mod os;
/// The Lean externs, one file per C file they replace. Not under `cargo test`: they call the Lean runtime, which only
/// a Lean link (or rust/rt) provides. A module of its own, not `ffi::`, because ffi.rs imports the kernel modules of
/// the same names.
#[path = "ffi"]
mod exports {
    mod asc;
    mod coc;
    mod csv;
    mod seen;
    mod env;
    mod gather;
    mod own;
    mod reduce;
    mod scan;
    mod scatter;
}
/// cbindgen:ignore
mod pod;
/// cbindgen:ignore
mod simd;
/// cbindgen:ignore
mod pool;

/// cbindgen:ignore
mod bits;
/// cbindgen:ignore
mod blocks;
/// cbindgen:ignore
mod bitblk;
/// cbindgen:ignore
mod alp;
/// cbindgen:ignore
mod asc;
/// cbindgen:ignore
mod coc;
/// cbindgen:ignore
mod cocops;
/// cbindgen:ignore
mod csv;
/// cbindgen:ignore
mod gather;
/// cbindgen:ignore
mod codec;
/// cbindgen:ignore
mod seen;
/// cbindgen:ignore
mod enc;
/// cbindgen:ignore
mod ew;
/// cbindgen:ignore
mod reduce;
/// cbindgen:ignore
mod res;
/// cbindgen:ignore
mod scan;
/// cbindgen:ignore
mod scatter;
/// cbindgen:ignore
mod sort;
/// cbindgen:ignore
mod structural;
/// cbindgen:ignore
mod sym;
/// cbindgen:ignore
mod group;
/// cbindgen:ignore
mod ids;
/// cbindgen:ignore
mod key;
/// cbindgen:ignore
mod kwin;
/// cbindgen:ignore
mod layout;
/// cbindgen:ignore
mod own;
/// cbindgen:ignore
mod unpack;
/// cbindgen:ignore
mod why;
#[cfg(test)]
mod testutil;
