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
pub fn res_unpack(p: &[u8], w: u8, nb: usize, out: &mut [u8]) { unimplemented!() }
pub fn res_unpack_add(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8], tw: u32) -> bool { unimplemented!() }

/// One function per `RES_VUNPACK` instance of coc.h:589-695 (`res_unpack`: B9; `res_unpack_add`: B10). Each names
/// every intrinsic its C instance uses, so this file compiling on the pinned toolchain is the check that all of
/// them are stable; the bodies are B9's and B10's.
#[cfg(target_arch = "x86_64")]
pub mod v {
    #![allow(clippy::let_unit_value)]
    use core::arch::x86_64::*;

    // RES_VUNPACK's own intrinsics at lane width 16, 32, 64, and the iota it is fed
    macro_rules! vunpack16 { () => { let _ = (_mm512_mullo_epi16, _mm512_set1_epi16, _mm512_and_si512,
        _mm512_add_epi16, _mm512_srli_epi16::<3>, _mm512_add_epi8, _mm512_set1_epi8, _mm512_maskz_loadu_epi8,
        _mm512_shrdv_epi16, _mm512_permutex2var_epi8, _mm512_set_epi8, _mm512_cvtepu8_epi16,
        _mm512_castsi512_si256); } }
    macro_rules! vunpack32 { () => { let _ = (_mm512_mullo_epi32, _mm512_set1_epi32, _mm512_and_si512,
        _mm512_add_epi32, _mm512_srli_epi32::<3>, _mm512_add_epi8, _mm512_set1_epi8, _mm512_maskz_loadu_epi8,
        _mm512_shrdv_epi32, _mm512_permutex2var_epi8, _mm512_set_epi8, _mm512_cvtepu8_epi32,
        _mm512_castsi512_si128); } }
    macro_rules! vunpack64 { () => { let _ = (_mm512_mullo_epi64, _mm512_set1_epi64, _mm512_and_si512,
        _mm512_add_epi64, _mm512_srli_epi64::<3>, _mm512_add_epi8, _mm512_set1_epi8, _mm512_maskz_loadu_epi8,
        _mm512_shrdv_epi64, _mm512_permutex2var_epi8, _mm512_set_epi8, _mm512_cvtepu8_epi64,
        _mm512_castsi512_si128); } }

    /// `res_unpack`, `w < 8`: unpacked at 16 bits, narrowed to bytes.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn unpack16_u8(p: &[u8], w: u8, nb: usize, out: &mut [u8]) {
        vunpack16!(); let _ = (_mm256_storeu_si256, _mm512_cvtepi16_epi8); unimplemented!()
    }
    /// `res_unpack`, `8 < w < 16`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn unpack16(p: &[u8], w: u8, nb: usize, out: &mut [u8]) { vunpack16!(); let _ = _mm512_storeu_si512; unimplemented!() }
    /// `res_unpack`, `16 < w < 32`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn unpack32(p: &[u8], w: u8, nb: usize, out: &mut [u8]) { vunpack32!(); let _ = _mm512_storeu_si512; unimplemented!() }
    /// `res_unpack`, `32 < w < 64`
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn unpack64(p: &[u8], w: u8, nb: usize, out: &mut [u8]) { vunpack64!(); let _ = _mm512_storeu_si512; unimplemented!() }

    /// `res_unpack_add`, `w < 16`, one-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add16_u8(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        vunpack16!(); let _ = (_mm256_mask_storeu_epi8, _mm256_add_epi8, _mm512_cvtepi16_epi8, _mm256_set1_epi8);
        unimplemented!()
    }
    /// `res_unpack_add`, `w < 16`, two-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add16_i16(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        vunpack16!(); let _ = (_mm512_mask_storeu_epi16, _mm512_add_epi16); unimplemented!()
    }
    /// `res_unpack_add`, `w < 16`, four-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add16_i32(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        vunpack16!();
        let _ = (_mm512_mask_storeu_epi32, _mm512_add_epi32, _mm512_cvtepu16_epi32, _mm512_extracti64x4_epi64::<0>,
                 _mm512_extracti64x4_epi64::<1>);
        unimplemented!()
    }
    /// `res_unpack_add`, `w < 16`, eight-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add16_i64(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        vunpack16!();
        let _ = (_mm512_mask_storeu_epi64, _mm512_add_epi64, _mm512_cvtepu16_epi64, _mm512_extracti32x4_epi32::<0>,
                 _mm512_extracti32x4_epi32::<1>, _mm512_extracti32x4_epi32::<2>, _mm512_extracti32x4_epi32::<3>);
        unimplemented!()
    }
    /// `res_unpack_add`, `16 < w < 32`, four-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add32_i32(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        vunpack32!(); let _ = (_mm512_mask_storeu_epi32, _mm512_add_epi32); unimplemented!()
    }
    /// `res_unpack_add`, `16 < w < 32`, eight-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add32_i64(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        vunpack32!();
        let _ = (_mm512_mask_storeu_epi64, _mm512_add_epi64, _mm512_cvtepu32_epi64, _mm512_extracti64x4_epi64::<0>,
                 _mm512_extracti64x4_epi64::<1>);
        unimplemented!()
    }
    /// `res_unpack_add`, `32 < w < 64`, eight-byte elements.
    #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")]
    pub fn add64_i64(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]) {
        vunpack64!(); let _ = (_mm512_mask_storeu_epi64, _mm512_add_epi64); unimplemented!()
    }
}
