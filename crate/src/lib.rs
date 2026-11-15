//! qlean's kernels in Rust, linked into `libqleankernel.a` as `rust/qrs.o`. Only `qrs_*` (ffi.rs) leave the
//! object. `unsafe` is confined to c.rs, ffi.rs, pod.rs, rt.rs, simd.rs; every other module refuses it.
#![cfg_attr(not(test), no_std)]
#![deny(unsafe_op_in_unsafe_fn)]
extern crate alloc;

pub const BLK: usize = 1024;

#[cfg(not(test))]
mod rt;
pub mod c;
pub mod ffi;
pub mod pod;
pub mod simd;

pub mod bits;
pub mod coc;
pub mod ids;
pub mod layout;
pub mod own;
pub mod unpack;
pub mod why;
pub mod zip;
