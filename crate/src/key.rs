#![forbid(unsafe_code)]
//! `key_at` (sort.c:132) with the kind switch hoisted by monomorphisation (`SK_EACH`, sort.c:1697): `each` switches
//! once and hands the pass a `Keys` of one concrete type, so the element loop has no switch.

/// The kinds `key_at` switches on; c/rs.h defines them from here. `SK_C8` reads as `SK_U8`; `SK_KEY` is a payload
/// of keys already biased; `SK_WIN` is an encoded column read through `kwin::Kwin`, never a byte payload.
pub const SK_BIT: u8 = 0;
pub const SK_U8: u8 = 1;
pub const SK_I16: u8 = 2;
pub const SK_I32: u8 = 3;
pub const SK_I64: u8 = 4;
pub const SK_F32: u8 = 5;
pub const SK_F64: u8 = 6;
pub const SK_C8: u8 = 7;
pub const SK_KINDS_N: u8 = SK_C8 + 1;
pub const SK_KEY: u8 = SK_KINDS_N;
pub const SK_WIN: u8 = SK_KINDS_N + 1;

/// Element `i`'s key, in the unsigned order q sorts by. `at` takes `&mut self` because a window decodes a block
/// on first touch; `fork` is a worker's own copy (a fresh window over the same column).
pub trait Keys: Sync {
    fn at(&mut self, i: usize) -> u64;
    fn fork(&self) -> Self where Self: Sized;
}

/// A loop over keys, written once and instantiated per key type by `each`.
pub trait Pass { type Out; fn run<K: Keys>(self, k: K, n: usize) -> Self::Out; }

macro_rules! dense {
    ($($(#[$d:meta])* $name:ident($t:ty) |$s:ident, $i:ident| $e:expr;)*) => {$(
        $(#[$d])*
        #[derive(Clone, Copy)]
        pub struct $name<'a>(pub &'a [$t]);
        impl Keys for $name<'_> {
            #[inline(always)]
            fn at(&mut self, $i: usize) -> u64 { let $s = self.0; $e }
            fn fork(&self) -> Self { *self }
        }
    )*};
}
dense! {
    /// `SK_BIT`: bit `i` of the bytes, low bit first.
    Bit(u8) |s, i| ((s[i >> 3] >> (i & 7)) & 1) as u64;
    /// `SK_U8`, `SK_C8`: the byte is its own key.
    U8(u8) |s, i| s[i] as u64;
    /// `SK_I16`: the sign bit flipped within 16 bits.
    I16(u16) |s, i| (s[i] ^ 0x8000) as u64;
    I32(u32) |s, i| (s[i] ^ 0x8000_0000) as u64;
    I64(u64) |s, i| s[i] ^ 0x8000_0000_0000_0000;
    /// `SK_F32`: `rank32` of the bits.
    F32(u32) |s, i| rank32(s[i]);
    F64(u64) |s, i| rank64(s[i]);
    /// `SK_KEY`: the payload is the key.
    Key(u64) |s, i| s[i];
}

/// sort.c:100; NaN payloads to 0, `-0.0` to `+0.0`'s key.
pub fn rank32(b: u32) -> u64 {
    if (b >> 23) & 0xff == 0xff && b & 0x7f_ffff != 0 { 0 }
    else if b == 0x8000_0000 { 0x8000_0000 }
    else if b >> 31 != 0 { (!b) as u64 } else { (b | 0x8000_0000) as u64 }
}
/// sort.c:106
pub fn rank64(b: u64) -> u64 {
    if (b >> 52) & 0x7ff == 0x7ff && b & 0xf_ffff_ffff_ffff != 0 { 0 }
    else if b == 0x8000_0000_0000_0000 { b }
    else if b >> 63 != 0 { !b } else { b | 0x8000_0000_0000_0000 }
}

/// The payload bytes `n` elements of a dense `kind` occupy; None for `SK_WIN` and an unknown kind.
pub fn bytes(kind: u8, n: usize) -> Option<usize> {
    match kind {
        SK_BIT => Some(n.div_ceil(8)),
        SK_U8 | SK_C8 => Some(n),
        SK_I16 => n.checked_mul(2),
        SK_I32 | SK_F32 => n.checked_mul(4),
        SK_I64 | SK_F64 | SK_KEY => n.checked_mul(8),
        _ => None,
    }
}

/// `SK_EACH`: `pass` over the keys of `p`; None = `SK_WIN`, an unknown kind, or `p` misaligned or short.
pub fn each<P: Pass>(kind: u8, p: &[u8], n: usize, pass: P) -> Option<P::Out> {
    use crate::pod::cast;
    if p.len() != bytes(kind, n)? { return None }
    Some(match kind {
        SK_BIT => pass.run(Bit(p), n),
        SK_U8 | SK_C8 => pass.run(U8(p), n),
        SK_I16 => pass.run(I16(cast(p)?), n),
        SK_I32 => pass.run(I32(cast(p)?), n),
        SK_I64 => pass.run(I64(cast(p)?), n),
        SK_F32 => pass.run(F32(cast(p)?), n),
        SK_F64 => pass.run(F64(cast(p)?), n),
        _ => pass.run(Key(cast(p)?), n),
    })
}

/// `SK_RANGE`: the least and greatest key, in the one pass `SK_EACH` instantiates per kind.
pub struct Range;
impl Pass for Range {
    type Out = (u64, u64);
    #[inline(always)]
    fn run<K: Keys>(self, mut k: K, n: usize) -> (u64, u64) {
        if n == 0 { return (0, 0) }
        let a = k.at(0);
        let (mut lo, mut hi) = (a, a);
        for i in 1..n { let v = k.at(i); lo = lo.min(v); hi = hi.max(v); }
        (lo, hi)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    // expected values: /data/tmp/qrs/B3/drv.c, drv2.c (sort.c's rank32, rank64, key_at, SK_RANGE), run
    #[test]
    fn rank32_c() {
        for (b, r) in [(0u32, 0x8000_0000u64), (1, 0x8000_0001), (0x8000_0000, 0x8000_0000), (0x8000_0001, 0x7fff_fffe),
                       (0x7f80_0000, 0xff80_0000), (0x7f80_0001, 0), (0xff80_0000, 0x7f_ffff), (0xffc0_0000, 0),
                       (0x7fff_ffff, 0), (0xffff_ffff, 0), (0x3f80_0000, 0xbf80_0000), (0xbf80_0000, 0x407f_ffff)] {
            assert_eq!(rank32(b), r, "{b:#x}");
        }
    }
    #[test]
    fn rank64_c() {
        for (b, r) in [(0u64, 1 << 63), (1, (1 << 63) | 1), (1 << 63, 1 << 63), ((1 << 63) | 1, 0x7fff_ffff_ffff_fffe),
                       (0x7ff0 << 48, 0xfff0 << 48), (0x7ff0_0000_0000_0001, 0), (0xfff0 << 48, 0xf_ffff_ffff_ffff),
                       (0x7ff8 << 48, 0), (u64::MAX, 0), (0x3ff0 << 48, 0xbff0 << 48),
                       (0xbff0 << 48, 0x400f_ffff_ffff_ffff)] {
            assert_eq!(rank64(b), r, "{b:#x}");
        }
    }
    fn bytes_of<T: Copy>(v: &[T], f: impl Fn(T) -> Vec<u8>) -> Vec<u8> { v.iter().flat_map(|&x| f(x)).collect() }
    #[test]
    fn range_c() {
        let s = bytes_of(&[3i16, -5, 7, -32768, 32767], |x| x.to_ne_bytes().to_vec());
        assert_eq!(each(SK_I16, &s, 5, Range), Some((0, 0xffff)));
        assert_eq!(each(SK_BIT, &[0xa4, 0x01], 10, Range), Some((0, 1)));
        let l = bytes_of(&[5i64, -1, 9], |x| x.to_ne_bytes().to_vec());
        assert_eq!(each(SK_I64, &l, 3, Range), Some((0x7fff_ffff_ffff_ffff, 0x8000_0000_0000_0009)));
        assert_eq!(each(SK_I64, &[], 0, Range), Some((0, 0)));
        assert_eq!(each(SK_WIN, &[], 0, Range), None);
        assert_eq!(each(SK_I32, &[0; 7], 2, Range), None);
    }
}
