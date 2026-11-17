//! The one checked reinterpretation of bytes as a slice of numbers.

/// # Safety
/// No padding bytes and every bit pattern a valid value: `cast`, `cast_mut` and `bytes` reinterpret memory as `Self`.
pub unsafe trait Pod: Copy {}
unsafe impl Pod for u8 {}
unsafe impl Pod for i8 {}
unsafe impl Pod for u16 {}
unsafe impl Pod for i16 {}
unsafe impl Pod for u32 {}
unsafe impl Pod for i32 {}
unsafe impl Pod for u64 {}
unsafe impl Pod for usize {}
unsafe impl Pod for i64 {}
unsafe impl Pod for f32 {}
unsafe impl Pod for f64 {}
// packed: no padding, and a key with its element index is any twelve bytes
unsafe impl Pod for crate::group::KeyAt {}

/// An element type a residual becomes (`COC_T` of coc.rs's `decode_blk`): `base + residual` truncated, wrapping.
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
/// `n` elements with no initialisation, as C's `xalloc`: for a buffer every slot of which is written before it is read,
/// where `vec![0; n]` would write it twice.
pub fn uninit<T: Pod>(n: usize) -> alloc::vec::Vec<T> {
    let mut v = alloc::vec::Vec::with_capacity(n);
    // Safety: capacity `n` was just reserved, and a `Pod` is valid for any bit pattern; the caller writes before it reads
    unsafe { v.set_len(n) };
    v
}
/// A slice of numbers as its bytes, for writing.
pub fn bytes_mut<T: Pod>(s: &mut [T]) -> &mut [u8] {
    // Safety: a `Pod` has no padding, so every byte is initialised, and any byte pattern written back is a valid `T`
    unsafe { core::slice::from_raw_parts_mut(s.as_mut_ptr().cast::<u8>(), size_of_val(s)) }
}

/// A zeroed scratch of `len` elements: inline up to `N` (the default block of 1024, so a column at `DEFAULT_LG` pays what a
/// stack array did), on the heap above it. One per call, never per block.
pub struct Scr<T: Pod + Default, const N: usize = 1024> { inl: [T; N], heap: alloc::vec::Vec<T>, len: usize }
impl<T: Pod + Default, const N: usize> Scr<T, N> {
    pub fn new(len: usize) -> Self {
        Scr { inl: [T::default(); N], heap: if len > N { alloc::vec![T::default(); len] } else { alloc::vec::Vec::new() }, len }
    }
}
impl<T: Pod + Default, const N: usize> core::ops::Deref for Scr<T, N> {
    type Target = [T];
    fn deref(&self) -> &[T] { if self.len > N { &self.heap } else { &self.inl[..self.len] } }
}
impl<T: Pod + Default, const N: usize> core::ops::DerefMut for Scr<T, N> {
    fn deref_mut(&mut self) -> &mut [T] { if self.len > N { &mut self.heap } else { &mut self.inl[..self.len] } }
}
impl<'a, T: Pod + Default, const N: usize> IntoIterator for &'a Scr<T, N> {
    type Item = &'a T; type IntoIter = core::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter { (**self).iter() }
}
impl<'a, T: Pod + Default, const N: usize> IntoIterator for &'a mut Scr<T, N> {
    type Item = &'a mut T; type IntoIter = core::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter { (**self).iter_mut() }
}

/// `bytes` bytes of 64-byte aligned scratch with no initialisation, kept for the next call so that faulting a large buffer in
/// is paid once (C's `static __thread` chunk of `qlean_alp_sum_f64`). A call takes the kept buffer or allocates one, and puts
/// it back unless another call already has; the buffer one call asks for is the size every call asks for.
pub fn with_kept<R>(bytes: usize, f: impl FnOnce(&mut [u8]) -> R) -> R {
    use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering::{AcqRel, Acquire, Release}};
    static KEEP: AtomicPtr<u8> = AtomicPtr::new(core::ptr::null_mut());
    static SIZE: AtomicUsize = AtomicUsize::new(0);
    let lay = |n: usize| alloc::alloc::Layout::from_size_align(n.max(1), 64).expect("pod::with_kept: layout");
    let mut p = KEEP.swap(core::ptr::null_mut(), AcqRel);
    // the holder of the pointer is the only writer of SIZE until it publishes the pointer again
    if !p.is_null() && SIZE.load(Acquire) != bytes {
        unsafe { alloc::alloc::dealloc(p, lay(SIZE.load(Acquire))) };
        p = core::ptr::null_mut();
    }
    if p.is_null() {
        p = unsafe { alloc::alloc::alloc(lay(bytes)) };
        if p.is_null() {
            crate::os::eprint(format_args!("qlean: out of memory for a {bytes}-byte scratch buffer\n")).expect("qlean: stderr");
            alloc::alloc::handle_alloc_error(lay(bytes))
        }
    }
    // Safety: `p` is a live allocation of `bytes` bytes that nothing else holds until it is put back below
    let r = f(unsafe { core::slice::from_raw_parts_mut(p, bytes) });
    SIZE.store(bytes, Release);
    if KEEP.compare_exchange(core::ptr::null_mut(), p, Release, Acquire).is_err() { unsafe { alloc::alloc::dealloc(p, lay(bytes)) } }
    r
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
