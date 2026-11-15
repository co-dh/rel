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

/// None when `b` is misaligned for `T` or `b.len() % size_of::<T>() != 0`.
pub fn cast<T: Pod>(b: &[u8]) -> Option<&[T]> { unimplemented!() }
pub fn cast_mut<T: Pod>(b: &mut [u8]) -> Option<&mut [T]> { unimplemented!() }
