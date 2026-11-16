//! The one checked reinterpretation of bytes as a slice of numbers.

pub trait Pod: Copy {}
impl Pod for u8 {}
impl Pod for i8 {}
impl Pod for u16 {}
impl Pod for i16 {}
impl Pod for u32 {}
impl Pod for i32 {}
impl Pod for u64 {}
impl Pod for usize {}
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
pub fn cast<T: Pod>(b: &[u8]) -> Option<&[T]> {
    if b.is_empty() { return Some(&[]) } // no element is read, so the dangling pointer of `&[]` is no misalignment
    if b.as_ptr() as usize % align_of::<T>() != 0 || b.len() % size_of::<T>() != 0 { return None }
    // Safety: aligned and a whole number of elements, both tested above; `Pod` is valid for any bit pattern
    Some(unsafe { core::slice::from_raw_parts(b.as_ptr().cast::<T>(), b.len() / size_of::<T>()) })
}
/// As `cast`, for writing.
pub fn cast_mut<T: Pod>(b: &mut [u8]) -> Option<&mut [T]> {
    if b.is_empty() { return Some(&mut []) }
    if b.as_ptr() as usize % align_of::<T>() != 0 || b.len() % size_of::<T>() != 0 { return None }
    // Safety: aligned and a whole number of elements, both tested above; `Pod` is valid for any bit pattern
    Some(unsafe { core::slice::from_raw_parts_mut(b.as_mut_ptr().cast::<T>(), b.len() / size_of::<T>()) })
}
/// A slice of numbers as its bytes.
pub fn bytes<T: Pod>(s: &[T]) -> &[u8] {
    // Safety: a `Pod` has no padding, so every byte is initialised
    unsafe { core::slice::from_raw_parts(s.as_ptr().cast::<u8>(), size_of_val(s)) }
}
/// `s` as atomics, so workers whose indices are disjoint but not contiguous (a scatter) share one output: a relaxed
/// store is a plain store on the targets we ship, and overlapping indices stay defined (last writer wins).
pub fn atomics(s: &mut [i64]) -> &[core::sync::atomic::AtomicI64] {
    // Safety: `AtomicI64` has the size and alignment of `i64` on this target, and the `&mut` borrow means nothing
    // else touches `s` for as long as the atomic view lives
    unsafe { core::slice::from_raw_parts(s.as_ptr().cast::<core::sync::atomic::AtomicI64>(), s.len()) }
}
/// A slice of numbers as its bytes, for writing.
pub fn bytes_mut<T: Pod>(s: &mut [T]) -> &mut [u8] {
    // Safety: a `Pod` has no padding, so every byte is initialised, and any byte pattern written back is a valid `T`
    unsafe { core::slice::from_raw_parts_mut(s.as_mut_ptr().cast::<u8>(), size_of_val(s)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn cast_rejects_misaligned_and_ragged() {
        let a = [0u64; 4];
        let b: &[u8] = unsafe { core::slice::from_raw_parts(a.as_ptr().cast::<u8>(), 32) };
        assert_eq!(cast::<u32>(&b[..8]).map(|s| s.len()), Some(2));
        assert!(cast::<u32>(&b[1..9]).is_none(), "misaligned");
        assert!(cast::<u32>(&b[..7]).is_none(), "ragged length");
        assert_eq!(cast::<u64>(&b[..0]).map(|s| s.len()), Some(0));
    }
    #[test] fn cast_mut_rejects_misaligned_and_ragged() {
        let mut a = [0u64; 4];
        let b: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(a.as_mut_ptr().cast::<u8>(), 32) };
        assert!(cast_mut::<u32>(&mut b[1..9]).is_none(), "misaligned");
        assert!(cast_mut::<u32>(&mut b[..7]).is_none(), "ragged length");
        assert_eq!(cast_mut::<u64>(&mut b[..0]).map(|s| s.len()), Some(0));
        cast_mut::<u32>(&mut b[..8]).unwrap()[1] = 7;
        assert_eq!(a[0] >> 32, 7);
    }
}
