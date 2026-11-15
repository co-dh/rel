#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! The one checked reinterpretation of bytes as a slice of numbers.

pub trait Pod: Copy {}
impl Pod for u8 {}
impl Pod for i8 {}
impl Pod for u16 {}
impl Pod for i16 {}
impl Pod for u32 {}
impl Pod for i32 {}
impl Pod for u64 {}
impl Pod for i64 {}
impl Pod for f32 {}
impl Pod for f64 {}

/// An element type a residual becomes (`COC_T` of coc.h's `decode_blk`): `base + residual` truncated, wrapping.
pub trait Lane: Pod { fn wrap(v: u64) -> Self; }
impl Lane for u8 { fn wrap(v: u64) -> Self { v as u8 } }
impl Lane for i16 { fn wrap(v: u64) -> Self { v as i16 } }
impl Lane for i32 { fn wrap(v: u64) -> Self { v as i32 } }
impl Lane for i64 { fn wrap(v: u64) -> Self { v as i64 } }

/// None when `b` is misaligned for `T` or `b.len() % size_of::<T>() != 0`.
pub fn cast<T: Pod>(b: &[u8]) -> Option<&[T]> { unimplemented!() }
pub fn cast_mut<T: Pod>(b: &mut [u8]) -> Option<&mut [T]> { unimplemented!() }
