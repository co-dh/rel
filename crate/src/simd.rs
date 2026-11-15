#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! The AVX-512 kernels: coc.h:598, 646; reduce.c:261. Each picks its path by `cfg`, as the C picks by `#if`.

/// `__builtin_prefetch(r, 1)`: starts the line of `r` loading; a hint, it never faults.
#[inline(always)]
pub fn prefetch<T>(r: &T) {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: a prefetch reads no memory architecturally and `r` is a live reference.
    unsafe { core::arch::x86_64::_mm_prefetch::<{ core::arch::x86_64::_MM_HINT_T0 }>((r as *const T).cast()) }
}

/// Dispatches by cfg.
pub fn u8_sum(p: &[u8]) -> i64 { unimplemented!() }
pub fn res_unpack(p: &[u8], w: u8, nb: usize, out: &mut [u8]) {
    // coc.h:598's `#if`: the vector path only where the build enables every feature it needs (target-cpu=native)
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
/// coc.h's `res_unpack_add`: block residuals widened to `tw`-byte elements with `base` added, wrapping, the first `nb`
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

/// One function per `RES_VUNPACK` instance of coc.h:589-695 (`res_unpack`: B9; `res_unpack_add`: B10). Each names
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
    /// Loads are masked to the block's BLK * w / 8 bytes, so nothing past `p` is read.
    macro_rules! vunpack {
        ($p:ident, $w:ident, $nb:ident, $l:literal, $mullo:ident, $set1:ident, $add:ident, $srli:ident, $shrdv:ident,
         $iota:expr, $ones:expr, $ramp:expr, |$g:ident, $v:ident| $store:expr) => {{
            let w = $w as usize;
            let (gn, span_) = (512 / $l, crate::BLK * w / 8);
            let gb = gn * w / 8;
            assert!($p.len() >= span_, "res_unpack: block of {} bytes, width {w} needs {span_}", $p.len());
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

/// A2: coc.h:690 `res_pack`'s vector arm (scalar: `res::res_pack_scalar`).
pub fn res_pack(v: &[u64], w: u8, nb: usize, dst: &mut [u8]) { unimplemented!("A2: res_pack avx512") }
/// A3: coc.h:820 `res_sum8`, the vector residual sum.
pub fn res_sum8(p: &[u8], nb: usize, w: u8) -> u64 { unimplemented!("A3: res_sum8") }
/// A14: scan.c's vector `scan_fill`.
pub fn scan_fill(kind: i32, p: &[u8], out: &mut [u8], n: usize) { unimplemented!("A14: scan_fill avx512") }
/// A14: scan.c's vector `scan_any_null`.
pub fn any_null(kind: i32, p: &[u8], n: usize) -> bool { unimplemented!("A14: scan_any_null avx512") }
/// A43: elementwise.c `ew_val_avx`.
pub fn ew_val(op: u8, cls: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A43: ew_val_avx") }
/// A43: elementwise.c `ew_cmp_avx`.
pub fn ew_cmp(op: u8, cls: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A43: ew_cmp_avx") }
