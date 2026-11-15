#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a): the Frame of Reference encoder's per-block steps — coc.h's FoR encode (A7), its patch list and the
//! whole-column decode (A8), coc.c's block steps of `coc_enc` (A16) and of the fill/move sources (A17).
//!
//! `coc_enc` (coc.h:1956) owns three `lean_object*` and calls the source's C callbacks, so its orchestration —
//! `coc_enc_open/plan/layout/pair/free`, `src_pass`, `qlean_coc_encode_src`, `fill_*` — stays C in phase 1 (§1, Lean
//! boundary), as the pool does. Rust gets one block at a time: `EncMeta` is what the meta pass may write for block
//! `b`, `EncPack` what the pack pass may write; `ffi::CEnc` cuts them, so parallel blocks hold disjoint borrows.
use core::sync::atomic::{AtomicI32, AtomicUsize};

use crate::coc::Coc;
use crate::pod::Lane;

/// An element type the encoder reads (`COC_T` of coc.h's encode template): `u8 i16 i32 i64`.
pub trait Elt: Lane { fn widen(self) -> i64; }
impl Elt for u8 { fn widen(self) -> i64 { self as i64 } }
impl Elt for i16 { fn widen(self) -> i64 { self as i64 } }
impl Elt for i32 { fn widen(self) -> i64 { self as i64 } }
impl Elt for i64 { fn widen(self) -> i64 { self } }

/// Block `b`'s metadata slots in a column being written: the meta pass's whole output for that block.
pub struct EncMeta<'a> {
    pub b: usize,
    pub base: &'a mut i64, pub maxv: &'a mut i64, pub width: &'a mut u8, pub bsum: &'a mut i64,
    /// the frame above `base` (coc.h `fdelta`), when the column keeps frames
    pub frm: Option<&'a mut u64>,
    /// the block's patch count, `exc_off[b + 1]` before the prefix sum
    pub nexc: &'a mut u32,
    /// ALP: the block's exponent
    pub exp: Option<&'a mut i8>,
    /// `coc_enc`'s early decline: the byte budget (0 = none), the bound reached, whether it was passed
    pub below: usize, pub lb: &'a AtomicUsize, pub over: &'a AtomicI32,
}
/// Block `b`'s output region in a column being written: residuals and patch slots, from the layout's offsets.
pub struct EncPack<'a> {
    pub b: usize, pub nb: usize,
    pub base: i64, pub frame: u64, pub width: u8, pub exp: i8,
    /// `BLK * width / 8` bytes at `off[b]`
    pub res: &'a mut [u8],
    /// `exc_off[b] .. exc_off[b + 1]`
    pub pos: &'a mut [u16], pub raw: &'a mut [u8],
}
/// `frame_pick`'s answer: the frame, the residual width, the patch count at it.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Frame { pub fo: i64, pub wo: u8, pub neo: u32 }

// ---- A7: coc.h:2191-2312 ----
/// `COC_NUL` of the element type: `INT16_MIN`, `INT32_MIN`, `INT64_MIN`; `u8` has none, so `INT64_MIN` there never matches.
fn nul<T: Elt>() -> i64 { if size_of::<T>() == 1 { i64::MIN } else { i64::MIN >> (64 - 8 * size_of::<T>()) } }
/// coc.h:2191 `pack_block`: `nb` elements of `src` minus `base` into `dst` at `w` bits, the first ⌈nb*w/8⌉ bytes of it.
pub fn pack_block<T: Elt>(dst: &mut [u8], src: &[T], nb: usize, base: i64, w: u8) {
    let r = |v: &T| (v.widen() as u64).wrapping_sub(base as u64);
    let src = &src[..nb];
    match w {
        0 => {}
        8 => for (o, v) in dst.iter_mut().zip(src) { *o = r(v) as u8 },
        16 => for (o, v) in dst.chunks_exact_mut(2).zip(src) { o.copy_from_slice(&(r(v) as u16).to_le_bytes()) },
        32 => for (o, v) in dst.chunks_exact_mut(4).zip(src) { o.copy_from_slice(&(r(v) as u32).to_le_bytes()) },
        64 => for (o, v) in dst.chunks_exact_mut(8).zip(src) { o.copy_from_slice(&r(v).to_le_bytes()) },
        // 1, 2, 4: 8/w residuals to a byte, built then stored so the buffer needs no zeroing
        1 | 2 | 4 => for (o, g) in dst.iter_mut().zip(src.chunks(8 / w as usize)) {
            *o = g.iter().enumerate().fold(0u8, |a, (t, v)| a | ((r(v) & ((1 << w) - 1)) << (t * w as usize)) as u8)
        },
        _ => {
            let mut v = [0u64; crate::BLK];
            for (o, x) in v.iter_mut().zip(src) { *o = r(x) }
            crate::simd::res_pack(&v, w, nb, dst)
        }
    }
}
/// coc.h:2240 `encode_meta_blk`: block metadata with no patch list.
pub fn encode_meta_blk<T: Elt>(m: &mut EncMeta, x: &[T], nb: usize) {
    let x = &x[..nb];
    let (mn, mx) = x.iter().fold((x[0].widen(), x[0].widen()), |(a, b), v| (a.min(v.widen()), b.max(v.widen())));
    let s = if mn == nul::<T>() { x.iter().map(|v| v.widen()).filter(|&v| v != nul::<T>()).fold(0i64, i64::wrapping_add) }
            else { x.iter().fold(0i64, |a, v| a.wrapping_add(v.widen())) };
    *m.base = mn; *m.maxv = mx; *m.bsum = s;
    *m.width = crate::bits::width_for((mx as u64).wrapping_sub(mn as u64));
}
/// coc.h:2275 `frame_pick`: from the sorted sample `smp`, the frame and width minimising bytes at `cost` per patch;
/// `None` = keep the plain frame.
pub fn frame_pick<T: Elt>(smp: &mut [i64], nb: usize, nnul: usize, cost: usize, mn: i64, x: &[T]) -> Option<Frame> {
    let (k, esz, bl) = (smp.len(), size_of::<T>(), |r: i64| crate::bits::width_for(r as u64) as usize);
    if k == 0 { return None }
    smp.sort_unstable();
    let c = smp[k / 2];
    // lifting the frame pays only when the minimum lies far below the bulk
    if bl(c.wrapping_sub(mn)) <= bl(smp[k * 3 / 4].wrapping_sub(smp[k / 4])) + 2 { return None }
    let v = || x[..nb].iter().map(|v| v.widen()).filter(|&v| v != nul::<T>());
    let (mut lo, mut hi) = ([0u32; 65], [0u32; 65]);
    for v in v() { if v < c { lo[bl(c.wrapping_sub(v))] += 1 } else { hi[bl(v.wrapping_sub(c))] += 1 } }
    for i in 1..=64 { lo[i] += lo[i - 1]; hi[i] += hi[i - 1] }
    let (mut best, mut ba) = (cost, 65);
    for w in 0..64usize {
        let m = w.saturating_sub(1);
        for (pa, pb) in [(0, w), (m, m), (w, 0)] {
            let bytes = (nb * w + 7) / 8 + (nb - lo[pa] as usize - hi[pb] as usize) * (2 + esz);
            if bytes < best { best = bytes; ba = pa }
        }
    }
    if ba == 65 { return None }
    let f = v().filter(|&v| v >= c || bl(c.wrapping_sub(v)) <= ba).fold(i64::MAX, i64::min);
    let (mut h, mut below) = ([0u32; 65], 0usize);
    for v in v() { if v < f { below += 1 } else { h[bl(v.wrapping_sub(f))] += 1 } }
    let (w, ne) = crate::cocops::width_exc(&h, nnul + below, esz, nb);
    if (nb * w as usize + 7) / 8 + ne as usize * (2 + esz) >= cost { return None }
    Some(Frame { fo: f, wo: w, neo: ne })
}

// ---- A8: coc.h:2452-2546 ----
/// coc.h:2452 `encode_meta_exc_blk`: block metadata with patches; answers the patch count.
pub fn encode_meta_exc_blk<T: Elt>(m: &mut EncMeta, x: &[T], nb: usize) -> u32 { unimplemented!("A8: encode_meta_exc_blk") }
/// coc.h:2489 `pack_exc_blk`: residuals and the block's `ne` patches.
pub fn pack_exc_blk<T: Elt>(p: &mut EncPack, x: &[T], ne: u32) { unimplemented!("A8: pack_exc_blk") }
/// coc.h:2546 `decode`: the whole column into `out` (`n` long).
pub fn decode<T: Lane>(c: &Coc, out: &mut [T]) { unimplemented!("A8: decode") }

// ---- A16: coc.c:165-210, the block steps of `coc_enc` ----
/// coc.c:165 `coc_enc_for_meta`: the FoR meta step over block `b`'s `nb` elements `x` at `width` bytes each.
pub fn for_meta(m: &mut EncMeta, x: &[u8], width: usize, nb: usize) { unimplemented!("A16: coc_enc_for_meta") }
/// coc.c:174 `coc_enc_for_pack`
pub fn for_pack(p: &mut EncPack, x: &[u8], width: usize) { unimplemented!("A16: coc_enc_for_pack") }
/// coc.c:186 `coc_enc_alp_meta`: `x` is `f32` (`width` 4) or `f64`.
pub fn alp_meta(m: &mut EncMeta, x: &[u8], width: usize, nb: usize) { unimplemented!("A16: coc_enc_alp_meta") }
/// coc.c:191 `coc_enc_alp_pack`
pub fn alp_pack(p: &mut EncPack, x: &[u8], width: usize) { unimplemented!("A16: coc_enc_alp_pack") }
/// coc.c:197 `src_copy`: a dense column's block `b` copied into the dense output `out`.
pub fn src_copy(out: &mut [u8], x: &[u8]) { unimplemented!("A16: src_copy") }
/// coc.c:203 `src_bits`: block `b`'s bytes (0/1) packed into the bitmap `out` at bit `b * BLK`.
pub fn src_bits(out: &mut [u8], b: usize, x: &[u8]) { unimplemented!("A16: src_bits") }

// ---- A17: coc.c:363-490 ----
/// coc.c:363 `coc_narrow`: `v` narrowed to `width` bytes into `out` (`v` itself when `width` is 8).
pub fn narrow<'b>(width: usize, v: &'b [i64], out: &'b mut [u8]) -> &'b [u8] { unimplemented!("A17: coc_narrow") }
/// coc.c:375 `coc_enc_blk_meta`: block metadata from decoded `v`; answers the patch count.
pub fn blk_meta(m: &mut EncMeta, v: &[i64], width: usize) -> u32 { unimplemented!("A17: coc_enc_blk_meta") }
/// coc.c:418 `move_meta`: the meta step of a column moved from another encoding (`x` the decoded block).
pub fn move_meta(m: &mut EncMeta, x: &[u8], width: usize, nb: usize) { unimplemented!("A17: move_meta") }
/// coc.c:450 `move_pack`
pub fn move_pack(p: &mut EncPack, x: &[u8], width: usize) { unimplemented!("A17: move_pack") }

#[cfg(test)]
mod a7_tests {
    use super::*;
    // Expected values come from running the original C (pack_block_i16, frame_pick_i64) on these inputs; the 8M-check
    // comparison over every width, nulls and frames is /data/tmp/qrs/A7/diff.c.
    #[test] fn pack_block_widths() {
        let x: [i16; 10] = [5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        for (w, want) in [(1u8, &[170u8, 2][..]), (2, &[228, 228, 4]), (3, &[136, 198, 250, 8]), (4, &[16, 50, 84, 118, 152]),
                          (5, &[32, 136, 65, 138, 57, 40, 1])] {
            let mut d = [0u8; 8];
            pack_block(&mut d[..want.len()], &x, 10, 5, w);
            assert_eq!(&d[..want.len()], want, "w {w}");
        }
        let mut d = [0u8; 20];
        pack_block(&mut d, &x, 10, 5, 16);
        assert_eq!(d, [0, 0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 6, 0, 7, 0, 8, 0, 9, 0]);
    }
    #[test] fn frame_pick_lifts_over_low_outliers() {
        let x: [i64; 1000] = core::array::from_fn(|i| if i < 24 { 0 } else { 100000 + (i & 255) as i64 });
        let mut smp = [100001, 100130, 100200, 100050, 100100];
        // plain frame at the minimum 0: width 17, no patches
        let cost = (1000 * 17 + 7) / 8;
        assert_eq!(frame_pick(&mut smp, 1000, 0, cost, 0, &x), Some(Frame { fo: 100000, wo: 8, neo: 24 }));
        assert_eq!(smp, [100001, 100050, 100100, 100130, 100200]);
    }
    #[test] fn encode_meta_blk_nulls() {
        let x: [i16; 4] = [i16::MIN, 3, 9, -2];
        let (mut base, mut maxv, mut width, mut bsum, mut nexc) = (0, 0, 0, 0, 0);
        let (lb, over) = (AtomicUsize::new(0), AtomicI32::new(0));
        let mut m = EncMeta { b: 0, base: &mut base, maxv: &mut maxv, width: &mut width, bsum: &mut bsum, frm: None, nexc: &mut nexc,
                              exp: None, below: 0, lb: &lb, over: &over };
        encode_meta_blk(&mut m, &x, 4);
        // the null is the minimum, so the sum skips it
        assert_eq!((base, maxv, width, bsum), (i16::MIN as i64, 9, 16, 10));
    }
}
