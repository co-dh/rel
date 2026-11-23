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

/// The one element trait: every number a column, a lane or a counter holds, so a kernel is generic over `T: Elt` and
/// `by_width!` picks `T` once per column. An op's own per-type code (a SIMD register) is a subtrait, never a second one.
pub trait Elt: Pod + Default + PartialOrd + Send + Sync + 'static {
    /// bytes an element
    const W: usize;
    /// the element whose bits are the low `8·W` of `v`: `base + residual` truncated, wrapping (`COC_T` of `decode_blk`)
    fn wrap(v: u64) -> Self;
    /// the bits, zero-extended: `wrap(x.bits()) == x`
    fn bits(self) -> u64;
    /// the element as q reads it, C's `(int64_t)` cast: zero-extended at an unsigned type, sign-extended at a signed one
    fn i(self) -> i64;
}
macro_rules! elt { ($($t:ty: $u:ty),*) => {$(impl Elt for $t {
    const W: usize = size_of::<$t>();
    #[inline(always)] fn wrap(v: u64) -> $t { <$t>::from_ne_bytes((v as $u).to_ne_bytes()) }
    #[inline(always)] fn bits(self) -> u64 { <$u>::from_ne_bytes(self.to_ne_bytes()) as u64 }
    #[inline(always)] fn i(self) -> i64 { self as i64 }
})*} }
elt!(u8: u8, u16: u16, i16: u16, u32: u32, i32: u32, u64: u64, i64: u64, usize: usize);
elt!(f32: u32, f64: u64);

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
/// `n` elements with no initialisation, as C's `xalloc`: for a buffer every slot of which is written before it is read,
/// where `vec![0; n]` would write it twice.
pub fn uninit<T: Pod>(n: usize) -> alloc::vec::Vec<T> {
    let mut v = alloc::vec::Vec::with_capacity(n);
    // Safety: capacity `n` was just reserved, and a `Pod` is valid for any bit pattern; the caller writes before it reads
    unsafe { v.set_len(n) };
    v
}
/// `n` copies of `x` for kernel `k`'s `what`, or the error naming the three and the bytes asked: the one way a kernel
/// makes a vector whose size its input decides, so an allocation that fails reaches Lean as `Except.error`, not an abort.
pub fn vec_of<T: Clone>(k: &str, what: &str, n: usize, x: T) -> Result<alloc::vec::Vec<T>, alloc::string::String> {
    let mut v = room(k, what, n)?;
    v.resize(n, x);
    Ok(v)
}
/// The `n` items of `it` (it must yield exactly `n`) reserved as `vec_of` reserves: `collect` with the error, not the abort.
pub fn collect_of<T>(k: &str, what: &str, n: usize, it: impl Iterator<Item = T>) -> Result<alloc::vec::Vec<T>, alloc::string::String> {
    let mut v = room(k, what, n)?;
    v.extend(it);
    Ok(v)
}
/// `uninit` reserved as `vec_of` reserves: no initialisation, the error where the allocator has not got the bytes.
pub fn try_uninit<T: Pod>(k: &str, what: &str, n: usize) -> Result<alloc::vec::Vec<T>, alloc::string::String> {
    let mut v = room(k, what, n)?;
    // Safety: capacity `n` was just reserved, and a `Pod` is valid for any bit pattern; the caller writes before it reads
    unsafe { v.set_len(n) };
    Ok(v)
}
/// An empty vector with room for exactly `n`, by the fallible reserve.
fn room<T>(k: &str, what: &str, n: usize) -> Result<alloc::vec::Vec<T>, alloc::string::String> {
    let mut v = alloc::vec::Vec::new();
    v.try_reserve_exact(n).map_err(|_| alloc::format!("{k}: cannot allocate {} bytes for {what} ({n} elements)", n.saturating_mul(size_of::<T>())))?;
    Ok(v)
}
/// A slice of numbers as its bytes, for writing.
pub fn bytes_mut<T: Pod>(s: &mut [T]) -> &mut [u8] {
    // Safety: a `Pod` has no padding, so every byte is initialised, and any byte pattern written back is a valid `T`
    unsafe { core::slice::from_raw_parts_mut(s.as_mut_ptr().cast::<u8>(), size_of_val(s)) }
}

/// A zeroed scratch of `len` elements: inline up to `N` (the default block of 1024, so a column at `DEFAULT_LG` pays what a
/// stack array did), on the heap above it. One per call, never per block.
/// Only `inl[..len]` is ever written: initialising all `N` made every small kernel call pay `N` elements of memset.
pub struct Scr<T: Pod + Default, const N: usize = 1024> { inl: core::mem::MaybeUninit<[T; N]>, heap: alloc::vec::Vec<T>, len: usize }
impl<T: Pod + Default, const N: usize> Scr<T, N> {
    #[inline]
    pub fn new(len: usize) -> Self { Self::filled(len, T::default()) }
    /// `len` copies of `x`, written once. Not `inline(always)`: unoptimised, a kernel expanded at every op (`by_op!`)
    /// then holds this frame's copy of the inline array once per op, which overflowed a test thread's stack
    #[inline]
    pub fn filled(len: usize, x: T) -> Self {
        let mut s = Scr { inl: core::mem::MaybeUninit::uninit(), heap: alloc::vec::Vec::new(), len };
        // Safety: `i < len <= N`
        if len > N { s.heap = alloc::vec![x; len] } else { let p = s.inl.as_mut_ptr().cast::<T>(); for i in 0..len { unsafe { p.add(i).write(x) } } }
        s
    }
}
impl<T: Pod + Default, const N: usize> core::ops::Deref for Scr<T, N> {
    type Target = [T];
    // Safety: `filled` wrote `inl[..len]` whenever `len <= N`
    fn deref(&self) -> &[T] { if self.len > N { &self.heap } else { unsafe { core::slice::from_raw_parts(self.inl.as_ptr().cast::<T>(), self.len) } } }
}
impl<T: Pod + Default, const N: usize> core::ops::DerefMut for Scr<T, N> {
    // Safety: as `deref`
    fn deref_mut(&mut self) -> &mut [T] { if self.len > N { &mut self.heap } else { unsafe { core::slice::from_raw_parts_mut(self.inl.as_mut_ptr().cast::<T>(), self.len) } } }
}
impl<'a, T: Pod + Default, const N: usize> IntoIterator for &'a Scr<T, N> {
    type Item = &'a T; type IntoIter = core::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter { (**self).iter() }
}
impl<'a, T: Pod + Default, const N: usize> IntoIterator for &'a mut Scr<T, N> {
    type Item = &'a mut T; type IntoIter = core::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter { (**self).iter_mut() }
}


#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn vec_of_fails_as_an_error() {
        let n = usize::MAX / 16;
        assert_eq!(vec_of("gather", "the output", n, 0u64).err(),
            Some(alloc::format!("gather: cannot allocate {} bytes for the output ({n} elements)", n * 8)));
        assert!(try_uninit::<u64>("scatter", "the values", n).is_err());
        assert_eq!(vec_of("k", "x", 3, 7u8), Ok(alloc::vec![7, 7, 7]));
    }
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
