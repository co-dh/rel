//! qlean's kernels in Rust, linked into `libqleankernel.a` as `rust/qrs.o`. Only `qrs_*` (ffi.rs) leave the
//! object. `unsafe` is confined to c.rs, ffi.rs, pod.rs, rt.rs, simd.rs; every other module refuses it.
#![cfg_attr(not(test), no_std)]
#![deny(unsafe_op_in_unsafe_fn)]
extern crate alloc;

pub const BLK: usize = 1024;

// the runtime and the C declarations are not interface: cbindgen skips both
/// cbindgen:ignore
#[cfg(not(test))]
mod rt;
/// cbindgen:ignore
pub mod c;
pub mod ffi;
pub mod pod;
pub mod simd;

pub mod bits;
pub mod coc;
pub mod group;
pub mod ids;
pub mod key;
pub mod kwin;
pub mod layout;
pub mod own;
pub mod unpack;
pub mod why;
pub mod zip;
