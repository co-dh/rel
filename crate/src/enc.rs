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

use crate::alp::Cocf;
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

// ---- A8: coc.h:2226-2310 ----
/// coc.h:2226 `encode_meta_exc_blk`: block metadata with patches; answers the patch count. The frame goes to `frm`.
pub fn encode_meta_exc_blk<T: Elt>(m: &mut EncMeta, x: &[T], nb: usize) -> u32 {
    let (x, nul, esz) = (&x[..nb], nul::<T>(), size_of::<T>());
    let frm = m.frm.as_deref_mut().expect("encode_meta_exc_blk: the column keeps no frames");
    let v = || x.iter().map(|v| v.widen()).filter(|&v| v != nul);
    let nnul = x.len() - v().count();
    *frm = 0;
    if nnul == nb { // all null: the null is the frame at width 0, and nothing is patched
        (*m.base, *m.maxv, *m.bsum, *m.width, *m.nexc) = (nul, nul, 0, 0, 0);
        return 0;
    }
    let (mn, mx) = v().fold((i64::MAX, i64::MIN), |(a, b), v| (a.min(v), b.max(v)));
    let mut h = [0u32; 65];
    for v in v() { h[crate::bits::width_for((v as u64).wrapping_sub(mn as u64)) as usize] += 1 }
    (*m.base, *m.maxv, *m.bsum) = (mn, mx, v().fold(0i64, i64::wrapping_add));
    let (mut w, mut ne) = crate::cocops::width_exc(&h, nnul, esz, nb);
    if w > 1 { // frame_pick is asked only where the median sits high in the window
        let mut smp = [0i64; 5];
        let mut k = 0;
        for q in 0..5 { let v = x[q * (nb - 1) / 4].widen(); if v != nul { smp[k] = v; k += 1 } }
        if let Some(f) = frame_pick(&mut smp[..k], nb, nnul, (nb * w as usize + 7) / 8 + ne as usize * (2 + esz), mn, x) {
            (w, ne, *frm) = (f.wo, f.neo, (f.fo as u64).wrapping_sub(mn as u64));
        }
    }
    (*m.width, *m.nexc) = (w, ne);
    ne
}
/// coc.h:2263 `pack_exc_blk`: residuals and the block's `ne` patches (an element the frame and width cannot hold, or a
/// null), their slots set to the frame.
pub fn pack_exc_blk<T: Elt>(p: &mut EncPack, x: &[T], ne: u32) {
    let (nul, base, w, x) = (nul::<T>(), p.frame as i64, p.width, &x[..p.nb]);
    if ne == 0 { return pack_block(p.res, x, p.nb, base, w) }
    let (mut y, mut k) = ([T::wrap(base as u64); crate::BLK], 0);
    for (i, &v) in x.iter().enumerate() {
        let r = (v.widen() as u64).wrapping_sub(base as u64);
        if v.widen() == nul || (w < 64 && r >> w != 0) {
            let mut e = [v];
            p.raw[k * size_of::<T>()..][..size_of::<T>()].copy_from_slice(crate::pod::bytes_mut(&mut e));
            p.pos[k] = i as u16;
            k += 1;
        } else { y[i] = v }
    }
    pack_block(p.res, &y[..p.nb], p.nb, base, w)
}
/// coc.h:2320 `decode`: the whole column into `out` (`n` long).
pub fn decode<T: Lane>(c: &Coc, out: &mut [T]) {
    for (b, o) in out[..c.meta.n].chunks_mut(crate::BLK).enumerate() { c.decode_blk(b, o.len(), o) }
}

// ---- A16: coc.c:165-210, the block steps of `coc_enc` ----
/// `x` as `nb` elements of `T`; C read them through a typed pointer, so a misaligned source is a bug there too.
fn elts<'b, T: crate::pod::Pod>(x: &'b [u8], what: &str) -> &'b [T] {
    crate::pod::cast::<T>(x).unwrap_or_else(|| panic!("qlean {what}: a block of {} bytes is misaligned for {}-byte elements", x.len(), size_of::<T>()))
}
/// coc.c:165 `coc_enc_for_meta`: the FoR meta step over block `b`'s `nb` elements `x` at `width` bytes each.
pub fn for_meta(m: &mut EncMeta, x: &[u8], width: usize, nb: usize) {
    fn go<T: Elt>(m: &mut EncMeta, x: &[u8], nb: usize) { let ne = encode_meta_exc_blk(m, elts::<T>(x, "coc_enc_for_meta"), nb); *m.nexc = ne }
    match width { 1 => go::<u8>(m, x, nb), 2 => go::<i16>(m, x, nb), 4 => go::<i32>(m, x, nb), _ => go::<i64>(m, x, nb) }
}
/// coc.c:174 `coc_enc_for_pack`: `p.pos` holds the block's patches, `exc_off[b + 1] - exc_off[b]` of them.
pub fn for_pack(p: &mut EncPack, x: &[u8], width: usize) {
    fn go<T: Elt>(p: &mut EncPack, x: &[u8]) { let ne = p.pos.len() as u32; pack_exc_blk(p, elts::<T>(x, "coc_enc_for_pack"), ne) }
    match width { 1 => go::<u8>(p, x), 2 => go::<i16>(p, x), 4 => go::<i32>(p, x), _ => go::<i64>(p, x) }
}
/// coc.c:186 `coc_enc_alp_meta`: `x` is `f32` (`width` 4) or `f64`.
pub fn alp_meta(m: &mut EncMeta, x: &[u8], width: usize, nb: usize) {
    use crate::alp::alp_meta_blk;
    let ne = if width == 4 { alp_meta_blk(m, elts::<f32>(x, "coc_enc_alp_meta"), nb) } else { alp_meta_blk(m, elts::<f64>(x, "coc_enc_alp_meta"), nb) };
    *m.nexc = ne
}
/// coc.c:191 `coc_enc_alp_pack`: the block exponent is `p.exp`, its patches' bits go to `p.raw`.
pub fn alp_pack(p: &mut EncPack, x: &[u8], width: usize) {
    use crate::alp::alp_pack_blk;
    let (be, raw) = (p.exp as i32, core::mem::take(&mut p.raw));
    if width == 4 { alp_pack_blk(p, be, elts::<f32>(x, "coc_enc_alp_pack"), crate::pod::cast_mut::<f32>(raw).expect("qlean coc_enc_alp_pack: misaligned f32 patch bits")) }
    else { alp_pack_blk(p, be, elts::<f64>(x, "coc_enc_alp_pack"), crate::pod::cast_mut::<f64>(raw).expect("qlean coc_enc_alp_pack: misaligned f64 patch bits")) }
}
/// coc.c:197 `src_copy`: a dense column's block copied into its place in the dense output `out`.
pub fn src_copy(out: &mut [u8], x: &[u8]) { out[..x.len()].copy_from_slice(x) }
/// coc.c:203 `src_bits`: block `b`'s bytes (0/1) packed into the bitmap `out` at bit `b * BLK`, bit `i % 8` of byte
/// `i / 8`, a non-zero byte reading as set (`Wire.booleanColumn`'s packing).
pub fn src_bits(out: &mut [u8], b: usize, x: &[u8]) {
    for (o, c) in out[b * (crate::BLK / 8)..].iter_mut().zip(x.chunks(8)) {
        *o = c.iter().enumerate().fold(0, |w, (j, &v)| w | ((v != 0) as u8) << j)
    }
}
/// coc.h:1845 `coc_sumnul`: the null the writer's block sums skip, which its trailer records: the element type's own,
/// and a float's integers are an `i64` column.
pub fn coc_sumnul(width: usize, alp: bool) -> i64 {
    if alp || width == 1 || width == 8 { i64::MIN } else if width == 2 { i16::MIN as i64 } else { i32::MIN as i64 }
}

// ---- A17: coc.c:363-490 ----
/// coc.c:363 `coc_narrow`: `v` narrowed to `width` bytes into `out` (`v` itself when `width` is 8).
pub fn narrow<'b>(width: usize, v: &'b [i64], out: &'b mut [u8]) -> &'b [u8] {
    fn put<'b, const W: usize>(v: &[i64], out: &'b mut [u8], f: fn(i64) -> [u8; W]) -> &'b [u8] {
        let out = &mut out[..W * v.len()];
        for (o, &x) in out.chunks_exact_mut(W).zip(v) { o.copy_from_slice(&f(x)) }
        out
    }
    match width {
        1 => put(v, out, |x| (x as u8).to_ne_bytes()),
        2 => put(v, out, |x| (x as i16).to_ne_bytes()),
        4 => put(v, out, |x| (x as i32).to_ne_bytes()),
        8 => crate::pod::bytes(v),
        _ => panic!("qlean: a Frame of Reference element of {width} bytes; the writer has 1, 2, 4 and 8"),
    }
}
/// coc.c:375 `coc_enc_blk_meta`: block metadata from decoded `v`; answers the patch count.
pub fn blk_meta(m: &mut EncMeta, v: &[i64], width: usize) -> u32 {
    fn go<T: Elt>(m: &mut EncMeta, x: &[u8], nb: usize) -> u32 {
        encode_meta_exc_blk(m, crate::pod::cast::<T>(x).expect("qlean: narrowed block misaligned"), nb)
    }
    let mut buf = [0i64; crate::BLK]; // i64 lanes, so the narrowed bytes are aligned for every `T`
    let x = narrow(width, v, crate::pod::bytes_mut(&mut buf));
    match width { 1 => go::<u8>(m, x, v.len()), 2 => go::<i16>(m, x, v.len()), 4 => go::<i32>(m, x, v.len()), _ => go::<i64>(m, x, v.len()) }
}
/// coc.c:418 `move_meta`, the branch where block `pb` of the column `f` is taken whole: its metadata is the block's,
/// and its patch count is what the layout prefix-sums. Answers it, and leaves it in `m.nexc`. The branches that call
/// back into the source (`ints`, `hint`, `fill`) stay C.
pub fn move_meta(m: &mut EncMeta, f: &Cocf, pb: usize) -> u32 {
    let p = &f.c;
    (*m.base, *m.maxv, *m.bsum, *m.width) = (p.meta.base[pb], p.meta.maxv[pb], p.meta.bsum[pb], p.meta.width[pb]);
    let ne = if let Some(e) = m.exp.as_deref_mut() {
        *e = f.exp[pb];
        f.exc_off[pb + 1] - f.exc_off[pb]
    } else {
        if let Some(fr) = m.frm.as_deref_mut() { *fr = p.fdelta.map_or(0, |d| d[pb]) }
        p.blk_nexc(pb) as u32
    };
    *m.nexc = ne;
    ne
}
/// coc.c:450 `move_pack`, the taken branch: block `pb` of `f`'s residuals (`p.res` is the whole `BLK * width / 8`
/// bytes, a pack shorter than its widths claim reading zeros past its end, `Column.resAt`'s convention) and its patch
/// list, whose positions move unchanged. `esz` is the written column's element size, `alp` its form.
pub fn move_pack(p: &mut EncPack, f: &Cocf, pb: usize, alp: bool, esz: usize) {
    let c = &f.c;
    let (bytes, so) = (crate::BLK * c.meta.width[pb] as usize / 8, c.meta.off[pb] as usize);
    let src = c.pack.get(so..).unwrap_or(&[]);
    let avail = src.len().min(bytes);
    p.res[..avail].copy_from_slice(&src[..avail]);
    p.res[avail..bytes].fill(0);
    if alp {
        let (from, to) = (f.exc_off[pb] as usize, f.exc_off[pb + 1] as usize);
        p.pos[..to - from].copy_from_slice(&f.exc_pos[from..to]);
        p.raw[..(to - from) * esz].copy_from_slice(&f.exc_raw[from * esz..to * esz]);
    } else if let Some(e) = c.exc.filter(|e| !e.pos.is_empty()) {
        // the element's first `esz` bytes: a patch of a wider column is truncated as the written column is
        for (q, j) in (e.off[pb] as usize..e.off[pb + 1] as usize).enumerate() {
            p.pos[q] = e.pos[j];
            p.raw[q * esz..(q + 1) * esz].copy_from_slice(&e.raw[j * e.esz..j * e.esz + esz]);
        }
    }
}

#[cfg(test)]
mod a17_tests {
    use super::*;
    // Expected values come from running the original C (coc_narrow, coc_enc_blk_meta) on these vectors, /data/tmp/qrs/A17/one.c;
    // the random comparison of those and of move_meta, move_pack, alp_patch_blk is /data/tmp/qrs/A17/diff.c.
    #[test] fn narrow_truncates() {
        let v = [1, -1, 0x1_0000_0001, i64::MIN, i64::MAX];
        let mut o = [0u8; 40];
        assert_eq!(narrow(1, &v, &mut o), [1, 255, 1, 0, 255]);
        assert_eq!(narrow(2, &v, &mut o), [1, 0, 255, 255, 1, 0, 0, 0, 255, 255]);
        assert_eq!(narrow(4, &v, &mut o), [1, 0, 0, 0, 255, 255, 255, 255, 1, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255]);
        assert_eq!(narrow(8, &v, &mut o).as_ptr(), v.as_ptr().cast::<u8>());
    }
    #[test] #[should_panic(expected = "a Frame of Reference element of 3 bytes; the writer has 1, 2, 4 and 8")]
    fn narrow_refuses_an_odd_width() { narrow(3, &[0], &mut [0; 8]); }
    fn meta(v: &[i64], width: usize) -> (u32, i64, i64, i64, u8, u64) {
        let (mut base, mut maxv, mut width_, mut bsum, mut nexc, mut frm) = (0, 0, 0, 0, 0, 7u64);
        let (lb, over) = (AtomicUsize::new(0), AtomicI32::new(0));
        let mut m = EncMeta { b: 0, base: &mut base, maxv: &mut maxv, width: &mut width_, bsum: &mut bsum, frm: Some(&mut frm),
                              nexc: &mut nexc, exp: None, below: 0, lb: &lb, over: &over };
        let ne = blk_meta(&mut m, v, width);
        (ne, base, maxv, bsum, width_, frm)
    }
    #[test] fn blk_meta_at_each_width() {
        let u = [i16::MIN as i64, 3, 9, -2];
        assert_eq!(meta(&u, 2), (1, -2, 9, 10, 4, 0)); // the null is a patch
        assert_eq!(meta(&[500, 100000, 100003], 4), (0, 500, 100003, 200503, 18, 0));
        assert_eq!(meta(&u, 8), (0, -32768, 9, -32758, 16, 0));
    }
    #[test] fn move_pack_zero_pads_a_short_pack() {
        // block 0 of width 8 whose pack holds 3 of its 1024 bytes: the rest reads as zeros, `Column.resAt`'s convention
        let (base, z, off, width) = ([5i64], [0i64], [0u64], [8u8]);
        let meta = crate::coc::Meta { base: &base, maxv: &z, off: &off, bsum: &z, width: &width, sumnul: 0, sumn: 0, n: 3, nblk: 1, mblk: 1 };
        let f = Cocf { c: Coc { meta, pack: &[1, 2, 3], exc: None, fdelta: None }, exp: &[], exc_off: &[], exc_pos: &[], exc_raw: &[], f32: false };
        let mut res = [0xa5u8; crate::BLK];
        let mut p = EncPack { b: 0, nb: 3, base: 5, frame: 5, width: 8, exp: 0, res: &mut res, pos: &mut [], raw: &mut [] };
        move_pack(&mut p, &f, 0, false, 2);
        assert_eq!(&res[..4], [1, 2, 3, 0]);
        assert!(res[3..].iter().all(|&x| x == 0));
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BLK;
    // encode with patches, decode the whole column: the round trip, for a column of low outliers and nulls, so the
    // frame is lifted and the patch list is non-empty; the C comparison is /data/tmp/qrs/A8/diff.c
    fn round<T: Elt + PartialEq + core::fmt::Debug>(x: &[T]) -> u32 {
        let n = x.len();
        let (mut base, mut maxv, mut bsum, mut width, mut frm) = (vec![0i64; 2], vec![0i64; 2], vec![0i64; 2], vec![0u8; 2], vec![0u64; 2]);
        let (lb, over) = (AtomicUsize::new(0), AtomicI32::new(0));
        let mut ne = vec![0u32; 2];
        for b in 0..n.div_ceil(BLK) {
            let mut nx = 0;
            let mut m = EncMeta { b, base: &mut base[b], maxv: &mut maxv[b], width: &mut width[b], bsum: &mut bsum[b],
                                  frm: Some(&mut frm[b]), nexc: &mut nx, exp: None, below: 0, lb: &lb, over: &over };
            let nb = BLK.min(n - b * BLK);
            ne[b] = encode_meta_exc_blk(&mut m, &x[b * BLK..], nb);
        }
        let (mut off, mut pack, mut at) = (vec![0u64; 2], vec![0u8; 2 * BLK * 8], 0usize);
        let (mut pos, mut raw) = (vec![0u16; ne.iter().sum::<u32>() as usize], vec![0u8; ne.iter().sum::<u32>() as usize * size_of::<T>()]);
        let mut eo = vec![0u32; 3];
        for b in 0..n.div_ceil(BLK) {
            off[b] = at as u64;
            let nb = BLK.min(n - b * BLK);
            let (e0, e1) = (eo[b] as usize, (eo[b] + ne[b]) as usize);
            eo[b + 1] = eo[b] + ne[b];
            let mut p = EncPack { b, nb, base: base[b], frame: (base[b] as u64).wrapping_add(frm[b]), width: width[b], exp: 0,
                                  res: &mut pack[at..at + (nb * width[b] as usize).div_ceil(8)],
                                  pos: &mut pos[e0..e1], raw: &mut raw[e0 * size_of::<T>()..e1 * size_of::<T>()] };
            pack_exc_blk(&mut p, &x[b * BLK..], ne[b]);
            at += BLK * width[b] as usize / 8;
        }
        let nbk = n.div_ceil(BLK);
        let c = Coc { meta: crate::coc::Meta { base: &base, maxv: &maxv, off: &off, bsum: &bsum, width: &width, sumnul: 0, sumn: 0,
                                                n, nblk: nbk, mblk: 2 },
                      pack: &pack, exc: Some(crate::coc::Exc { off: &eo, pos: &pos, raw: &raw, esz: size_of::<T>() }),
                      fdelta: Some(&frm) };
        let mut out = vec![T::wrap(0); n];
        decode(&c, &mut out);
        assert_eq!(out, x);
        ne.iter().sum()
    }
    #[test] fn decode_round_trip_with_patches() {
        let mut x: Vec<i64> = (0..BLK as i64 + 300).map(|i| 1_000_000 + (i * 37) % 500).collect();
        x[3] = -5; x[900] = 1 << 40; x[1100] = i64::MIN; x[1200] = 7;
        assert!(round(&x) >= 4);
        let y: Vec<i16> = (0..2000).map(|i| if i % 97 == 0 { i16::MIN } else { 300 + (i % 11) as i16 }).collect();
        assert!(round(&y) > 0);
        let z: Vec<u8> = (0..BLK as u32 + 5).map(|i| if i == 5 { 0 } else { 200 + (i % 5) as u8 }).collect();
        round(&z);
        round(&[i32::MIN; 7]);
    }
}

#[cfg(test)]
mod a16_tests {
    use super::*;
    // Expected values come from running the original C loops of coc.c:197-210 and coc.h:1845 (/data/tmp/qrs/A16/diff.c
    // compares the block steps over 12,000 columns).
    #[test] fn src_bits_packs_bit_i_of_byte_i_div_8() {
        let x = [1u8, 0, 7, 0, 0, 0, 0, 0, 255, 0, 0, 1];
        let mut o = [0xffu8; 3 + 130];
        src_bits(&mut o[..], 0, &x);
        assert_eq!(&o[..2], &[0b101, 0b1001]);
        // block 1 starts at byte BLK / 8, and a short block writes only its ceil(nb / 8) bytes
        let mut o = [0u8; 130];
        src_bits(&mut o, 1, &x[..9]);
        assert_eq!((o[127], o[128], o[129]), (0, 0b101, 1));
    }
    #[test] fn src_copy_and_sumnul() {
        let mut o = [9u8; 6];
        src_copy(&mut o, &[1, 2, 3]);
        assert_eq!(o, [1, 2, 3, 9, 9, 9]);
        assert_eq!([(1, false), (2, false), (4, false), (8, false), (4, true)].map(|(w, a)| coc_sumnul(w, a)),
                   [i64::MIN, i16::MIN as i64, i32::MIN as i64, i64::MIN, i64::MIN]);
    }
}
