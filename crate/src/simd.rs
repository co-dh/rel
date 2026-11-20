//! The AVX-512 kernels: coc.rs, 646; reduce.rs. Each picks its path by `cfg`, as the C picks by `#if`.
// a build without the vector features takes the scalar arm of each function and ignores what only the vector arm reads
#![cfg_attr(not(all(target_arch = "x86_64", target_feature = "avx512bw")), allow(unused_variables))]



/// `__builtin_prefetch(r, 1)`: starts the line of `r` loading; a hint, it never faults.
#[inline(always)]
pub fn prefetch<T>(r: &T) {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: a prefetch reads no memory architecturally and `r` is a live reference.
    unsafe { core::arch::x86_64::_mm_prefetch::<{ core::arch::x86_64::_MM_HINT_T0 }>((r as *const T).cast()) }
}

pub fn res_unpack(p: &[u8], w: u8, nb: usize, out: &mut [u8]) {
    // coc.rs's `#if`: the vector path only where the build enables every feature it needs (target-cpu=native)
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "avx512vbmi2",
              target_feature = "avx512bw", target_feature = "avx512dq"))]
    {
        if w & w.wrapping_sub(1) == 0 || w > 64 { crate::unpack::res_unpack_scalar(p, w, nb, out) } // refuses, naming w
        // SAFETY: the cfg above is the build enabling every feature the v:: kernels are compiled for
        else { unsafe {
            if w < 8 { v::unpack16_u8(p, w, nb, out) }
            else if w < 16 { v::unpack16(p, w, nb, out) }
            else if w < 32 { v::unpack32(p, w, nb, out) }
            else { v::unpack64(p, w, nb, out) }
        } }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "avx512vbmi2",
                  target_feature = "avx512bw", target_feature = "avx512dq")))]
    crate::unpack::res_unpack_scalar(p, w, nb, out)
}
/// coc.rs's `res_unpack_add`: block residuals widened to `tw`-byte elements with `base` added, wrapping, the first `nb`
/// stored and nothing after; false (nothing written) at a power-of-two width, an element narrower than the lane, or
/// a build without the vector path.
pub fn res_unpack_add(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8], tw: u32) -> bool {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "avx512vbmi2",
              target_feature = "avx512bw", target_feature = "avx512dq"))]
    {
        if w & w.wrapping_sub(1) == 0 || w > 64 { return false }
        // SAFETY: the cfg above is the build enabling every feature the v:: kernels are compiled for
        unsafe { match (w, tw) {
            (..16, 1) => v::add16_u8(p, w, nb, base, out),
            (..16, 2) => v::add16_i16(p, w, nb, base, out),
            (..16, 4) => v::add16_i32(p, w, nb, base, out),
            (..16, 8) => v::add16_i64(p, w, nb, base, out),
            (16..32, 4) => v::add32_i32(p, w, nb, base, out),
            (16..32, 8) => v::add32_i64(p, w, nb, base, out),
            (32.., 8) => v::add64_i64(p, w, nb, base, out),
            _ => return false,
        } }
        true
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "avx512vbmi2",
                  target_feature = "avx512bw", target_feature = "avx512dq")))]
    false
}

/// coc.rs's `res_vcmp`: `r - lo <= span` (unsigned, flipped when `inv`) of an odd-width block's residuals, in register, ORed
/// into the bitmap `out` (bit `i` of its word `i / 64`), the lanes never stored. Only when [lo, lo + span] lies inside the
/// L-bit lane, where the lane's wrapping subtraction agrees with the 64-bit one; false (nothing written) otherwise, at a
/// power-of-two width, or in a build without the vector path.
pub fn res_vcmp(p: &[u8], w: u8, nb: usize, lo: u64, span: u64, inv: bool, out: &mut [u64]) -> bool {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "avx512vbmi2",
              target_feature = "avx512bw", target_feature = "avx512dq"))]
    {
        let lmax = match w { ..16 => 0xffff, 16..32 => 0xffff_ffff, _ => u64::MAX };
        if w & w.wrapping_sub(1) == 0 || w > 64 || span > lmax || lo > lmax - span { return false }
        let flip = if inv { u64::MAX } else { 0 };
        // SAFETY: the cfg above is the build enabling every feature the v:: kernels are compiled for
        unsafe { match w { ..16 => v::vcmp16(p, w, nb, lo, span, flip, out), 16..32 => v::vcmp32(p, w, nb, lo, span, flip, out),
                           _ => v::vcmp64(p, w, nb, lo, span, flip, out) } }
        true
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "avx512vbmi2",
                  target_feature = "avx512bw", target_feature = "avx512dq")))]
    false
}

/// One function per `RES_VUNPACK` instance of coc.rs (`res_unpack`: B9; `res_unpack_add`: B10). Each names
/// every intrinsic its C instance uses, so this file compiling on the pinned toolchain is the check that all of
/// them are stable; the bodies are B9's and B10's.
#[cfg(target_arch = "x86_64")]
pub mod v {
    #![allow(clippy::let_unit_value)]
    use core::arch::x86_64::*;

    /// `res_span`: the first `r` bytes of a 64-byte window, none when `r <= 0`.
    fn span(r: isize) -> __mmask64 { if r >= 64 { !0 } else if r <= 0 { 0 } else { (1u64 << r) - 1 } }
    /// RES_IOTA8: byte i holds i.
    macro_rules! iota8 { () => { _mm512_set_epi8(63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
        47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24,
        23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0) } }
    /// RES_VUNPACK: a group of 512 / L residuals spans G * w / 8 bytes; lane k's field starts at bit k * w, its two
    /// L-bit byte windows gathered by vpermi2b from the group's 128 bytes and shifted right by (k * w) & 7 by vpshrdv.
    /// Loads are masked to the block's bytes (`p.len()`), so nothing past `p` is read.
    macro_rules! vunpack {
        ($p:ident, $w:ident, $nb:ident, $l:literal, $mullo:ident, $set1:ident, $add:ident, $srli:ident, $shrdv:ident,
         $iota:expr, $ones:expr, $ramp:expr, |$g:ident, $v:ident| $store:expr) => {{
            let w = $w as usize;
            let (gn, span_) = (512 / $l, $p.len());
            let gb = gn * w / 8;
            let bit = $mullo($iota, $set1($w as _));
            let sh = _mm512_and_si512(bit, $set1(7));
            let lo = $add($mullo($srli::<3>(bit), $set1($ones)), $set1($ramp));
            let hi = _mm512_add_epi8(lo, _mm512_set1_epi8(($l / 8) as i8));
            let m = $set1(((1u64 << w) - 1) as _);
            let mut $g = 0;
            while $g * gn < $nb {
                let (q, r) = ($p.as_ptr().wrapping_add($g * gb) as *const i8, span_ as isize - ($g * gb) as isize);
                // SAFETY: a masked load touches only the bytes its mask selects, the first r of p[g * gb..span_)
                let (a, b) = unsafe { (_mm512_maskz_loadu_epi8(span(r), q),
                                       _mm512_maskz_loadu_epi8(span(r - 64), q.wrapping_add(64))) };
                let $v = _mm512_and_si512(m, $shrdv(_mm512_permutex2var_epi8(a, lo, b),
                                                    _mm512_permutex2var_epi8(a, hi, b), sh));
                $store;
                $g += 1;
            }
        }};
    }

    /// `res_unpack`, `w < 8`: unpacked at 16 bits, narrowed to bytes.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn unpack16_u8(p: &[u8], w: u8, nb: usize, out: &mut [u8]) {
        vunpack!(p, w, nb, 16, _mm512_mullo_epi16, _mm512_set1_epi16, _mm512_add_epi16, _mm512_srli_epi16,
                 _mm512_shrdv_epi16, _mm512_cvtepu8_epi16(_mm512_castsi512_si256(iota8!())), 0x0101, 0x0100,
                 |g, v| { let o = &mut out[g * 32..g * 32 + 32];
                          // SAFETY: o is 32 bytes
                          unsafe { _mm256_storeu_si256(o.as_mut_ptr() as *mut __m256i, _mm512_cvtepi16_epi8(v)) } })
    }
    /// `res_unpack`, `8 < w < 16`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn unpack16(p: &[u8], w: u8, nb: usize, out: &mut [u8]) {
        vunpack!(p, w, nb, 16, _mm512_mullo_epi16, _mm512_set1_epi16, _mm512_add_epi16, _mm512_srli_epi16,
                 _mm512_shrdv_epi16, _mm512_cvtepu8_epi16(_mm512_castsi512_si256(iota8!())), 0x0101, 0x0100,
                 |g, v| { let o = &mut out[g * 64..g * 64 + 64];
                          // SAFETY: o is 64 bytes
                          unsafe { _mm512_storeu_si512(o.as_mut_ptr() as *mut _, v) } })
    }
    /// `res_unpack`, `16 < w < 32`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn unpack32(p: &[u8], w: u8, nb: usize, out: &mut [u8]) {
        vunpack!(p, w, nb, 32, _mm512_mullo_epi32, _mm512_set1_epi32, _mm512_add_epi32, _mm512_srli_epi32,
                 _mm512_shrdv_epi32, _mm512_cvtepu8_epi32(_mm512_castsi512_si128(iota8!())), 0x01010101, 0x03020100,
                 |g, v| { let o = &mut out[g * 64..g * 64 + 64];
                          // SAFETY: o is 64 bytes
                          unsafe { _mm512_storeu_si512(o.as_mut_ptr() as *mut _, v) } })
    }
    /// `res_unpack`, `32 < w < 64`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn unpack64(p: &[u8], w: u8, nb: usize, out: &mut [u8]) {
        vunpack!(p, w, nb, 64, _mm512_mullo_epi64, _mm512_set1_epi64, _mm512_add_epi64, _mm512_srli_epi64,
                 _mm512_shrdv_epi64, _mm512_cvtepu8_epi64(_mm512_castsi512_si128(iota8!())), 0x0101010101010101, 0x0706050403020100,
                 |g, v| { let o = &mut out[g * 64..g * 64 + 64];
                          // SAFETY: o is 64 bytes
                          unsafe { _mm512_storeu_si512(o.as_mut_ptr() as *mut _, v) } })
    }

    /// `res_unpack_add`'s ST: the first `n` (at most `$k`) `$e`-byte elements of `$x` stored masked at byte `$off`,
    /// none when `n <= 0`; the slice taken is exactly the bytes the mask selects.
    macro_rules! st {
        ($out:ident, $off:expr, $n:expr, $e:literal, $k:literal, $mt:ty, $store:ident, $pt:ty, $x:expr) => {{
            let n: isize = $n;
            if n > 0 {
                let n = (n as usize).min($k);
                let o = &mut $out[$off..$off + n * $e];
                // SAFETY: the mask selects the first n elements, the n * e bytes of o
                unsafe { $store(o.as_mut_ptr() as *mut $pt, span(n as isize) as $mt, $x) }
            }
        }};
    }
    /// `res_unpack_add`, `w < 16`, one-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add16_u8(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        let b8 = _mm256_set1_epi8(base as i8);
        vunpack!(p, w, nb, 16, _mm512_mullo_epi16, _mm512_set1_epi16, _mm512_add_epi16, _mm512_srli_epi16,
                 _mm512_shrdv_epi16, _mm512_cvtepu8_epi16(_mm512_castsi512_si256(iota8!())), 0x0101, 0x0100,
                 |g, v| st!(out, g * 32, nb as isize - (g * 32) as isize, 1, 32, __mmask32, _mm256_mask_storeu_epi8,
                            i8, _mm256_add_epi8(_mm512_cvtepi16_epi8(v), b8)))
    }
    /// `res_unpack_add`, `w < 16`, two-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add16_i16(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        let b16 = _mm512_set1_epi16(base as i16);
        vunpack!(p, w, nb, 16, _mm512_mullo_epi16, _mm512_set1_epi16, _mm512_add_epi16, _mm512_srli_epi16,
                 _mm512_shrdv_epi16, _mm512_cvtepu8_epi16(_mm512_castsi512_si256(iota8!())), 0x0101, 0x0100,
                 |g, v| st!(out, g * 64, nb as isize - (g * 32) as isize, 2, 32, __mmask32, _mm512_mask_storeu_epi16,
                            i16, _mm512_add_epi16(v, b16)))
    }
    /// `res_unpack_add`, `w < 16`, four-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add16_i32(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        let b32 = _mm512_set1_epi32(base as i32);
        vunpack!(p, w, nb, 16, _mm512_mullo_epi16, _mm512_set1_epi16, _mm512_add_epi16, _mm512_srli_epi16,
                 _mm512_shrdv_epi16, _mm512_cvtepu8_epi16(_mm512_castsi512_si256(iota8!())), 0x0101, 0x0100,
                 |g, v| { let n = nb as isize - (g * 32) as isize;
                   st!(out, g * 128, n, 4, 16, __mmask16, _mm512_mask_storeu_epi32, i32,
                       _mm512_add_epi32(_mm512_cvtepu16_epi32(_mm512_extracti64x4_epi64::<0>(v)), b32));
                   st!(out, g * 128 + 64, n - 16, 4, 16, __mmask16, _mm512_mask_storeu_epi32, i32,
                       _mm512_add_epi32(_mm512_cvtepu16_epi32(_mm512_extracti64x4_epi64::<1>(v)), b32)) })
    }
    /// `res_unpack_add`, `w < 16`, eight-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add16_i64(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        let b64 = _mm512_set1_epi64(base as i64);
        vunpack!(p, w, nb, 16, _mm512_mullo_epi16, _mm512_set1_epi16, _mm512_add_epi16, _mm512_srli_epi16,
                 _mm512_shrdv_epi16, _mm512_cvtepu8_epi16(_mm512_castsi512_si256(iota8!())), 0x0101, 0x0100,
                 |g, v| { let n = nb as isize - (g * 32) as isize;
                   st!(out, g * 256, n, 8, 8, __mmask8, _mm512_mask_storeu_epi64, i64,
                       _mm512_add_epi64(_mm512_cvtepu16_epi64(_mm512_extracti32x4_epi32::<0>(v)), b64));
                   st!(out, g * 256 + 64, n - 8, 8, 8, __mmask8, _mm512_mask_storeu_epi64, i64,
                       _mm512_add_epi64(_mm512_cvtepu16_epi64(_mm512_extracti32x4_epi32::<1>(v)), b64));
                   st!(out, g * 256 + 128, n - 16, 8, 8, __mmask8, _mm512_mask_storeu_epi64, i64,
                       _mm512_add_epi64(_mm512_cvtepu16_epi64(_mm512_extracti32x4_epi32::<2>(v)), b64));
                   st!(out, g * 256 + 192, n - 24, 8, 8, __mmask8, _mm512_mask_storeu_epi64, i64,
                       _mm512_add_epi64(_mm512_cvtepu16_epi64(_mm512_extracti32x4_epi32::<3>(v)), b64)) })
    }
    /// `res_unpack_add`, `16 < w < 32`, four-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add32_i32(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        let b32 = _mm512_set1_epi32(base as i32);
        vunpack!(p, w, nb, 32, _mm512_mullo_epi32, _mm512_set1_epi32, _mm512_add_epi32, _mm512_srli_epi32,
                 _mm512_shrdv_epi32, _mm512_cvtepu8_epi32(_mm512_castsi512_si128(iota8!())), 0x01010101, 0x03020100,
                 |g, v| st!(out, g * 64, nb as isize - (g * 16) as isize, 4, 16, __mmask16, _mm512_mask_storeu_epi32,
                            i32, _mm512_add_epi32(v, b32)))
    }
    /// `res_unpack_add`, `16 < w < 32`, eight-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add32_i64(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        let b64 = _mm512_set1_epi64(base as i64);
        vunpack!(p, w, nb, 32, _mm512_mullo_epi32, _mm512_set1_epi32, _mm512_add_epi32, _mm512_srli_epi32,
                 _mm512_shrdv_epi32, _mm512_cvtepu8_epi32(_mm512_castsi512_si128(iota8!())), 0x01010101, 0x03020100,
                 |g, v| { let n = nb as isize - (g * 16) as isize;
                   st!(out, g * 128, n, 8, 8, __mmask8, _mm512_mask_storeu_epi64, i64,
                       _mm512_add_epi64(_mm512_cvtepu32_epi64(_mm512_extracti64x4_epi64::<0>(v)), b64));
                   st!(out, g * 128 + 64, n - 8, 8, 8, __mmask8, _mm512_mask_storeu_epi64, i64,
                       _mm512_add_epi64(_mm512_cvtepu32_epi64(_mm512_extracti64x4_epi64::<1>(v)), b64)) })
    }
    /// `res_unpack_add`, `32 < w < 64`, eight-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add64_i64(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        let b64 = _mm512_set1_epi64(base as i64);
        vunpack!(p, w, nb, 64, _mm512_mullo_epi64, _mm512_set1_epi64, _mm512_add_epi64, _mm512_srli_epi64,
                 _mm512_shrdv_epi64, _mm512_cvtepu8_epi64(_mm512_castsi512_si128(iota8!())), 0x0101010101010101, 0x0706050403020100,
                 |g, v| st!(out, g * 64, nb as isize - (g * 8) as isize, 8, 8, __mmask8, _mm512_mask_storeu_epi64,
                            i64, _mm512_add_epi64(v, b64)))
    }

    /// `res_vcmp`'s RES_VCMP: the group's lanes `r - lo <= span` at the lane's width as a mask, flipped by `flip`, its
    /// first `n` bits ORed into `out` at bit `at`. Only entered when [lo, lo + span] lies inside the lane.
    macro_rules! vcmp {
        ($p:ident, $w:ident, $nb:ident, $l:literal, $mullo:ident, $set1:ident, $add:ident, $srli:ident, $shrdv:ident,
         $iota:expr, $ones:expr, $ramp:expr, $sub:ident, $cmp:ident, $lo:ident, $span:ident, $flip:ident, $out:ident) => {
            vunpack!($p, $w, $nb, $l, $mullo, $set1, $add, $srli, $shrdv, $iota, $ones, $ramp, |g, v| {
                let (at, n) = (g * (512 / $l), ($nb - g * (512 / $l)).min(512 / $l));
                let k = $cmp($sub(v, $set1($lo as _)), $set1($span as _)) as u64;
                $out[at / 64] |= ((k ^ $flip) & ((1u64 << n) - 1)) << (at % 64);
            })
        };
    }
    /// `res_vcmp`, `w < 16`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn vcmp16(p: &[u8], w: u8, nb: usize, lo: u64, span: u64, flip: u64, out: &mut [u64]) {
        vcmp!(p, w, nb, 16, _mm512_mullo_epi16, _mm512_set1_epi16, _mm512_add_epi16, _mm512_srli_epi16, _mm512_shrdv_epi16,
              _mm512_cvtepu8_epi16(_mm512_castsi512_si256(iota8!())), 0x0101, 0x0100,
              _mm512_sub_epi16, _mm512_cmple_epu16_mask, lo, span, flip, out)
    }
    /// `res_vcmp`, `16 < w < 32`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn vcmp32(p: &[u8], w: u8, nb: usize, lo: u64, span: u64, flip: u64, out: &mut [u64]) {
        vcmp!(p, w, nb, 32, _mm512_mullo_epi32, _mm512_set1_epi32, _mm512_add_epi32, _mm512_srli_epi32, _mm512_shrdv_epi32,
              _mm512_cvtepu8_epi32(_mm512_castsi512_si128(iota8!())), 0x01010101, 0x03020100,
              _mm512_sub_epi32, _mm512_cmple_epu32_mask, lo, span, flip, out)
    }
    /// `res_vcmp`, `32 < w < 64`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn vcmp64(p: &[u8], w: u8, nb: usize, lo: u64, span: u64, flip: u64, out: &mut [u64]) {
        vcmp!(p, w, nb, 64, _mm512_mullo_epi64, _mm512_set1_epi64, _mm512_add_epi64, _mm512_srli_epi64, _mm512_shrdv_epi64,
              _mm512_cvtepu8_epi64(_mm512_castsi512_si128(iota8!())), 0x0101010101010101, 0x0706050403020100,
              _mm512_sub_epi64, _mm512_cmple_epu64_mask, lo, span, flip, out)
    }

    /// The first `n` of the lanes of `v` that fit 64 bits, narrowed; lanes past `n` are zero (res_lanes64).
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    fn lanes64(v: &[u64], at: usize, n: usize) -> __m512i {
        let n = n.min(8);
        // SAFETY: the mask selects lanes at - at + n of v only, and v[at..at + n] exists (caller: at + n <= nb <= v.len())
        unsafe { _mm512_maskz_loadu_epi64(((1u16 << n) - 1) as __mmask8, v.as_ptr().wrapping_add(at) as *const i64) }
    }
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    fn lanes32(v: &[u64], at: usize, n: usize) -> __m512i {
        _mm512_inserti64x4::<1>(_mm512_castsi256_si512(_mm512_cvtepi64_epi32(lanes64(v, at, n))),
                                _mm512_cvtepi64_epi32(lanes64(v, at + 8, n.saturating_sub(8))))
    }
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    fn lanes16(v: &[u64], at: usize, n: usize) -> __m512i {
        _mm512_inserti64x4::<1>(_mm512_castsi256_si512(_mm512_cvtepi32_epi16(lanes32(v, at, n))),
                                _mm512_cvtepi32_epi16(lanes32(v, at + 16, n.saturating_sub(16))))
    }
    /// RES_VPACK's index setup for lane width `8 << LG`... `LG` is log2 of the lane bytes: output byte k takes, per
    /// parity c, the byte of the one lane of that parity whose field reaches it; which lane is floor(8k / w) or the
    /// next, by a multiply with ceil(2^16 / w), exact for 8k < 512.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    fn pack_idx<const LG: u32>(w: u8) -> ([__m512i; 2], [__mmask64; 2]) {
        let lb = (1i16 << LG) - 1; // L / 8 - 1
        let mut ix = [_mm512_setzero_si512(); 2];
        let mut ok = [0 as __mmask64; 2];
        for c in 0..2 {
            let mut h = [_mm256_setzero_si256(); 2];
            let mut k = [0 as __mmask32; 2];
            for half in 0..2 {
                let (ww, one) = (_mm512_set1_epi16(w as i16), _mm512_set1_epi16(1));
                let x = _mm512_slli_epi16::<3>(_mm512_add_epi16(_mm512_cvtepu8_epi16(_mm512_castsi512_si256(iota8!())),
                                                                _mm512_set1_epi16(32 * half)));
                let j0 = _mm512_mulhi_epu16(x, _mm512_set1_epi16(((65536 + w as i32 - 1) / w as i32) as i16));
                let j1 = _mm512_add_epi16(j0, one);
                let even = _mm512_cmpeq_epi16_mask(_mm512_and_si512(j0, one), _mm512_set1_epi16(c));
                let t1 = _mm512_cmple_epu16_mask(_mm512_mullo_epi16(j1, ww), _mm512_add_epi16(x, _mm512_set1_epi16(7)));
                let j = _mm512_mask_blend_epi16(even, j1, j0);
                let b = _mm512_sub_epi16(_mm512_srli_epi16::<3>(x), _mm512_srli_epi16::<3>(_mm512_mullo_epi16(j, ww)));
                let i = _mm512_add_epi16(_mm512_add_epi16(_mm512_slli_epi16::<LG>(j), _mm512_and_si512(b, _mm512_set1_epi16(lb))),
                                         _mm512_slli_epi16::<6>(_mm512_srli_epi16::<LG>(b)));
                h[half as usize] = _mm512_cvtepi16_epi8(i);
                k[half as usize] = even | t1;
            }
            ix[c as usize] = _mm512_inserti64x4::<1>(_mm512_castsi256_si512(h[0]), h[1]);
            ok[c as usize] = k[0] as __mmask64 | (k[1] as __mmask64) << 32;
        }
        (ix, ok)
    }
    /// RES_VPACK: each lane is shifted into the pair of L-bit windows at byte (j * w) >> 3, and the even and odd
    /// lanes' bytes are gathered by vpermi2b and ORed; the group's ⌈n*w/8⌉ bytes are stored masked.
    macro_rules! vpack {
        ($v:ident, $w:ident, $nb:ident, $dst:ident, $l:literal, $lg:literal, $set1:ident, $sllv:ident, $srlv:ident,
         $mullo:ident, $sub:ident, $iota:expr, $load:ident) => {{
            let wu = $w as usize;
            let (gn, gb) = (512 / $l, 512 / $l * wu / 8);
            assert!($v.len() >= $nb && $dst.len() >= ($nb * wu + 7) / 8, "res_pack: {} values / {} bytes for nb {}, width {wu}", $v.len(), $dst.len(), $nb);
            let bit = $mullo($iota, $set1($w as _));
            let sh = _mm512_and_si512(bit, $set1(7));
            let rsh = $sub($set1($l), sh);
            let m = $set1(((1u64 << wu) - 1) as _);
            let (ix, ok) = pack_idx::<$lg>($w);
            let mut g = 0;
            while g * gn < $nb {
                let n = ($nb - g * gn).min(gn);
                let v_ = _mm512_and_si512(m, $load($v, g * gn, n));
                let (lo, hi) = ($sllv(v_, sh), $srlv(v_, rsh));
                let o = _mm512_or_si512(_mm512_maskz_permutex2var_epi8(ok[0], lo, ix[0], hi),
                                        _mm512_maskz_permutex2var_epi8(ok[1], lo, ix[1], hi));
                let bytes = (n * wu + 7) / 8;
                // SAFETY: the mask selects the first `bytes` bytes of dst[g * gb..], inside the length asserted above
                unsafe { _mm512_mask_storeu_epi8($dst.as_mut_ptr().wrapping_add(g * gb) as *mut i8, span(bytes as isize), o) }
                g += 1;
            }
        }};
    }
    /// `res_pack`, `9 < w < 16`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn pack16(v: &[u64], w: u8, nb: usize, dst: &mut [u8]) {
        vpack!(v, w, nb, dst, 16, 1, _mm512_set1_epi16, _mm512_sllv_epi16, _mm512_srlv_epi16, _mm512_mullo_epi16, _mm512_sub_epi16,
               _mm512_cvtepu8_epi16(_mm512_castsi512_si256(iota8!())), lanes16)
    }
    /// `res_pack`, `16 < w < 32`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn pack32(v: &[u64], w: u8, nb: usize, dst: &mut [u8]) {
        vpack!(v, w, nb, dst, 32, 2, _mm512_set1_epi32, _mm512_sllv_epi32, _mm512_srlv_epi32, _mm512_mullo_epi32, _mm512_sub_epi32,
               _mm512_cvtepu8_epi32(_mm512_castsi512_si128(iota8!())), lanes32)
    }
    /// `res_pack`, `32 < w < 64`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn pack64(v: &[u64], w: u8, nb: usize, dst: &mut [u8]) {
        vpack!(v, w, nb, dst, 64, 3, _mm512_set1_epi64, _mm512_sllv_epi64, _mm512_srlv_epi64, _mm512_mullo_epi64, _mm512_sub_epi64,
               _mm512_cvtepu8_epi64(_mm512_castsi512_si128(iota8!())), lanes64)
    }
}

#[cfg(test)]
mod tests {
    use crate::{BLK, unpack::res_unpack_scalar};
    // the vector path against B8's scalar port at every odd width, on random blocks (target-cpu=native runs it)
    #[test] fn res_unpack_matches_scalar() {
        let mut s = 0x2545F4914F6CDD1Du64;
        for w in 1..64u8 {
            if w.is_power_of_two() { continue }
            let p: Vec<u8> = (0..BLK * w as usize / 8).map(|_| { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s as u8 }).collect();
            let l = if w < 8 { 1 } else { crate::bits::lane_width(w) as usize / 8 };
            for nb in [1, 7, 63, 64, 1023, 1024] {
                let (mut a, mut b) = (vec![0xA5u8; BLK * 8], vec![0x5Au8; BLK * 8]);
                res_unpack_scalar(&p, w, nb, &mut a); super::res_unpack(&p, w, nb, &mut b);
                assert_eq!(a[..nb * l], b[..nb * l], "w {w} nb {nb}");
            }
        }
    }
    // res_pack against the scalar port at every odd width: same bytes, none written past ⌈nb*w/8⌉
    #[test] fn res_pack_matches_scalar() {
        let mut s = 0x1234567899ABCDEFu64;
        for w in 1..64u8 {
            if w.is_power_of_two() { continue }
            let v: Vec<u64> = (0..BLK).map(|_| { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s }).collect();
            for nb in [1, 7, 8, 9, 15, 16, 17, 31, 33, 63, 64, 65, 1000, 1023, 1024] {
                if w < 3 { continue }
                let (mut a, mut b) = (vec![0xA5u8; BLK * 8], vec![0x5Au8; BLK * 8]);
                crate::res::res_pack_scalar(&v, w, nb, &mut a); super::res_pack(&v, w, nb, &mut b);
                let len = (nb * w as usize + 7) / 8;
                assert_eq!(a[..len], b[..len], "w {w} nb {nb}");
                assert!(b[len..].iter().all(|&x| x == 0x5A), "w {w} nb {nb} wrote past {len}");
            }
        }
    }
    // res_unpack_add against the scalar unpack plus base, truncated to tw bytes; the bytes after nb untouched
    #[test] fn res_unpack_add_matches_scalar() {
        let mut s = 0x9E3779B97F4A7C15u64;
        let vec_path = cfg!(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "avx512vbmi2",
                                target_feature = "avx512bw", target_feature = "avx512dq"));
        for w in 1..64u8 {
            if w.is_power_of_two() { continue }
            let p: Vec<u8> = (0..BLK * w as usize / 8).map(|_| { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s as u8 }).collect();
            let l = if w < 8 { 1 } else { crate::bits::lane_width(w) as usize / 8 };
            let base = 0x8000000000000123u64 ^ (w as u64) << 40;
            for nb in [1, 7, 63, 64, 1023, 1024] {
                let mut r = vec![0u8; BLK * 8];
                res_unpack_scalar(&p, w, nb, &mut r);
                for tw in [1u32, 2, 4, 8] {
                    let t = tw as usize;
                    let mut d = vec![0xEEu8; nb * t + 64];
                    let ok = super::res_unpack_add(&p, w, nb, base, &mut d[..nb * t], tw);
                    assert_eq!(ok, vec_path && (w < 16 || t >= l), "accepted w {w} tw {tw}");
                    if !ok { assert!(d.iter().all(|&x| x == 0xEE), "refused yet wrote, w {w} tw {tw}"); continue }
                    for i in 0..nb {
                        let mut v = [0u8; 8]; v[..l].copy_from_slice(&r[i * l..i * l + l]);
                        let x = base.wrapping_add(u64::from_le_bytes(v)).to_le_bytes();
                        assert_eq!(d[i * t..i * t + t], x[..t], "w {w} nb {nb} tw {tw} i {i}");
                    }
                    assert!(d[nb * t..].iter().all(|&x| x == 0xEE), "wrote past nb: w {w} nb {nb} tw {tw}");
                }
            }
        }
    }
}

/// coc.rs `res_pack`: the vector pack at an odd width from 9 to 63 where the build enables the vector path (as
/// `res_unpack`), `res::res_pack_scalar` otherwise. Writes the first ⌈nb*w/8⌉ bytes of `dst`, no more.
pub fn res_pack(v: &[u64], w: u8, nb: usize, dst: &mut [u8]) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "avx512vbmi2",
              target_feature = "avx512bw", target_feature = "avx512dq"))]
    if !(w < 9 || w & w.wrapping_sub(1) == 0 || w > 64) {
        // SAFETY: the cfg above is the build enabling every feature the v:: kernels are compiled for
        unsafe { if w < 16 { v::pack16(v, w, nb, dst) } else if w < 32 { v::pack32(v, w, nb, dst) } else { v::pack64(v, w, nb, dst) } }
        return;
    }
    crate::res::res_pack_scalar(v, w, nb, dst)
}
/// scan.rs `SCG_*`: whether a 64-byte group holds the kind's null, one `cmp` to a mask. `byte` has none.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw"))]
mod sc {
    
    


}

/// ew.rs: the mask-register kernels. A comparison's result is a mask, so packing the bits is one store;
/// q's NaN rule is two mask blends over the arithmetic.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw"))]
mod ev {
    
    







}

/// `(int64_t)nearbyint(s)` for |s| < 2^53 (coc.rs `dat`): `cvtsd2si` rounds in the current mode, to nearest even, in one
/// instruction and without libm.
#[inline(always)]
pub fn cvt_nearest(s: f64) -> i64 {
    // SAFETY: SSE2 is the x86_64 baseline and the intrinsic works on a register.
    unsafe { core::arch::x86_64::_mm_cvtsd_si64(core::arch::x86_64::_mm_set_sd(s)) }
}


// ---- the moving-window extremes (scan.rs `MW_EXT`) ----
// The carried `ex = better(v, ex) ? v : ex` is a one-register chain. LLVM lowers a scalar select there to a cmov and its
// cmov converter turns that into a branch, which mispredicts on random data; gcc keeps the chain in an xmm register as a
// one-cycle `vpmin`, so the integral kinds do the same, and a float is a branch only because the running extreme is
// rarely replaced at a wide window (`ucomis` then `ja`, as gcc's own loop), written as asm so LLVM cannot turn it back
// into selects.

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx512vl")))]
pub type VReg = i64;



