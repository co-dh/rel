//! qlean's kernels in Rust, linked into `libqleankernel.a` as the rel package's object. The Lean externs of `ffi/*.rs` leave the
//! object (`qrs_abi_*` beside them with feature `abi`). `unsafe` is confined to c.rs, ffi.rs, lean.rs, lib.rs, os.rs, pod.rs, pool.rs,
//! rt.rs, simd.rs; every other module refuses it, and `ffi/*.rs` denies it (their one `allow` comes from `lean::export!`).
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![deny(unsafe_op_in_unsafe_fn)]
extern crate alloc;

/// The block size every encoder writes, as `lg` in a column's metadata trailer (`blk = 1 << lg`, `MIN_LG <= lg <= MAX_LG`):
/// the one place 10 is written.
pub const DEFAULT_LG: u32 = 10;
/// tests that name the default block by its size
#[cfg(any(test, feature = "std"))]
pub const BLK: usize = 1 << DEFAULT_LG;
pub const MIN_LG: u32 = 6;
pub const MAX_LG: u32 = 16;

/// Costs per element, named so a call site says why rather than what; the one definition.
/// one indexed load and one store
pub const QLEAN_COST_GATHER: u32 = 1;
/// a straight-line move, no arithmetic. 3, not 2: a move writes a fresh answer and its page faults are the cost, so
/// at 2 a 4 MB answer ran on one thread -- `prev` on 1M reals or 500k floats 120-148us serial against 22-33 split
pub const QLEAN_COST_COPY: u32 = 3;
/// the element-wise verbs and the comparisons
pub const QLEAN_COST_ARITH: u32 = 4;
/// a conversion, a rounding and a range test
pub const QLEAN_COST_CAST: u32 = 6;
/// a libm call
pub const QLEAN_COST_MATH: u32 = 12;

// the runtime and the C declarations are not interface: cbindgen skips both
/// cbindgen:ignore
#[cfg(not(any(test, feature = "std")))]
mod rt;
/// cbindgen:ignore
pub mod c;
/// cbindgen:ignore
pub mod ffi;
pub mod lean;
pub mod os;
/// The Lean externs, one file per C file they replace. Not under `cargo test`: they call the Lean runtime, which only
/// a Lean link (or rust/rt) provides. A module of its own, not `ffi::`, because ffi.rs imports the kernel modules of
/// the same names.
#[path = "ffi"]
pub mod exports {
    pub mod asc;
    pub mod coc;
    pub mod distinct;
    pub mod env;
    pub mod gather;
    pub mod group;
    pub mod ew;
    pub mod own;
    pub mod reduce;
    pub mod scan;
    pub mod scatter;
    pub mod search;
    pub mod sort;
    pub mod structural;
    pub mod symsort;
}
/// cbindgen:ignore
pub mod pod;
/// cbindgen:ignore
pub mod simd;
/// cbindgen:ignore
pub mod pool;

/// cbindgen:ignore
pub mod bits;
/// cbindgen:ignore
pub mod blocks;
/// cbindgen:ignore
pub mod bitblk;
/// cbindgen:ignore
pub mod alp;
/// cbindgen:ignore
pub mod asc;
/// cbindgen:ignore
pub mod coc;
/// cbindgen:ignore
pub mod cocops;
/// cbindgen:ignore
pub mod gather;
/// cbindgen:ignore
pub mod codec;
/// cbindgen:ignore
pub mod distinct;
/// cbindgen:ignore
pub mod enc;
/// cbindgen:ignore
pub mod ew;
/// cbindgen:ignore
pub mod reduce;
/// cbindgen:ignore
pub mod res;
/// cbindgen:ignore
pub mod scan;
/// cbindgen:ignore
pub mod scatter;
/// cbindgen:ignore
pub mod search;
/// cbindgen:ignore
pub mod sort;
/// cbindgen:ignore
pub mod structural;
/// cbindgen:ignore
pub mod sym;
/// cbindgen:ignore
pub mod group;
/// cbindgen:ignore
pub mod ids;
/// cbindgen:ignore
pub mod key;
/// cbindgen:ignore
pub mod kwin;
/// cbindgen:ignore
pub mod layout;
/// cbindgen:ignore
pub mod own;
/// cbindgen:ignore
pub mod unpack;
/// cbindgen:ignore
pub mod why;
