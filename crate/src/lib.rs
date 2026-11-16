//! qlean's kernels in Rust, linked into `libqleankernel.a` as `rust/qrs.o`. Only `qrs_*` (ffi.rs) leave the
//! object, beside the Lean externs of `ffi/*.rs`. `unsafe` is confined to c.rs, ffi.rs, lean.rs, lib.rs, os.rs, pod.rs, pool.rs,
//! rt.rs, simd.rs; every other module refuses it, and `ffi/*.rs` denies it (their one `allow` comes from `lean::export!`).
#![cfg_attr(not(test), no_std)]
#![deny(unsafe_op_in_unsafe_fn)]
extern crate alloc;

pub const BLK: usize = 1024;

/// Costs per element, named so a call site says why rather than what; the one definition, C reads it through rs.h.
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
#[cfg(not(test))]
mod rt;
/// cbindgen:ignore
pub mod c;
pub mod ffi;
pub mod lean;
pub mod os;
/// The Lean externs, one file per C file they replace. Not under `cargo test`: they call the Lean runtime, which only
/// a Lean link (or c/rt.c) provides. A module of its own, not `ffi::`, because ffi.rs imports the kernel modules of
/// the same names.
#[cfg(not(test))]
#[path = "ffi"]
pub mod exports {
    pub mod env;
    pub mod interp;
    pub mod handle;
    pub mod pool;
    pub mod search;
    pub mod structural;
    pub mod time;
    pub mod zip;
}
pub mod pod;
pub mod simd;
/// cbindgen:ignore
pub mod pool;

pub mod bits;
pub mod alp;
pub mod coc;
pub mod cocops;
pub mod codec;
pub mod enc;
pub mod ew;
pub mod reduce;
pub mod res;
pub mod scan;
pub mod search;
pub mod sort;
pub mod structural;
pub mod sym;
pub mod group;
pub mod ids;
pub mod interp;
pub mod key;
pub mod kwin;
pub mod layout;
pub mod own;
pub mod unpack;
pub mod why;
pub mod zip;
