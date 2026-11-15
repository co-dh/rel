#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), coc.h: the whole-column reads of a `Coc` (A1), its sums (A3), product, any/all, min and max (A4)
//! and the in-place shift (A6), plus `CocMut`, the writable form of the same `coc`.
use crate::coc::{Coc, Meta};
use crate::res::res_get_in;
use crate::simd::prefetch;
use crate::BLK;

/// coc.h:987, the comparison codes in QLean.Kernel.Ew's constructor order
const EQ: i32 = 0;
const NE: i32 = 1;
const LT: i32 = 2;
const LE: i32 = 3;
const GT: i32 = 4;

/// The writable form of coc.h:103 `coc`, for the operations that rewrite a column in place: `coc_offsets` (A1),
/// `coc_sums_drop` (A3), `coc_shift` (A6). Lengths as `Coc`'s; the per-block writers of the encoder take
/// `enc::EncMeta`/`enc::EncPack` instead, which split this by block.
pub struct CocMut<'a> {
    pub base: &'a mut [i64], pub maxv: &'a mut [i64], pub off: &'a mut [u64], pub bsum: &'a mut [i64],
    pub width: &'a mut [u8],
    /// null in C = no sums stored
    pub sumnul: Option<&'a mut i64>, pub sumn: Option<&'a mut u64>,
    pub pack: &'a mut [u8],
    pub n: usize, pub nblk: usize, pub mblk: usize,
}

// ---- A1: coc.h:139-303, 2043-2165 ----

/// `coc_meta_view` (coc.h:139) and `coc_attach` (coc.h:251) are `Meta::new` and `Coc::attach`; `coc_blocks`
/// (coc.h:162) is `Coc::blocks`; `coc_res_end`, `coc_grid`, `coc_std` are `Meta::res_end`, `Meta::grid`, `Coc::std`.
impl<'a> Coc<'a> {
    /// coc.h:2043 `coc_get`: element `i`, its patch applied. Per element: C keeps its body while a C caller remains.
    pub fn get(&self, i: usize) -> i64 {
        let (b, j) = (i / BLK, i % BLK);
        if let Some(e) = self.exc.filter(|e| !e.pos.is_empty()) {
            for x in e.off[b] as usize..e.off[b + 1] as usize { if e.pos[x] as usize == j { return self.exc(x) } }
        }
        let p = self.pack.get(self.meta.off[b] as usize..).unwrap_or(&[]);
        self.frame(b).wrapping_add(res_get_in(p, self.meta.width[b], j, p.len())) as i64
    }
    /// coc.h:2078 `coc_get_w`: `get` for a column whose every block has residual width `uw` (`one_width`).
    pub fn get_w(&self, uw: u8, i: usize) -> i64 {
        let (base, p) = (self.meta.base[i / BLK] as u64, self.pack);
        let at = |k: usize, n: usize| &p[k..k + n];
        if self.exc.is_some_and(|e| !e.pos.is_empty()) { return self.get(i) }
        base.wrapping_add(match uw {
            0 => 0,
            1 => (p[i >> 3] >> (i & 7) & 1) as u64,
            2 => (p[i >> 2] >> ((i & 3) * 2) & 3) as u64,
            4 => (p[i >> 1] >> ((i & 1) * 4) & 15) as u64,
            8 => p[i] as u64,
            16 => u16::from_ne_bytes(at(2 * i, 2).try_into().unwrap()) as u64,
            32 => u32::from_ne_bytes(at(4 * i, 4).try_into().unwrap()) as u64,
            64 => u64::from_ne_bytes(at(8 * i, 8).try_into().unwrap()),
            255 => return self.get(i),
            // an odd width is flat too, so the residual is read at `i * uw` bits of the whole pack
            _ => res_get_in(p, uw, i, p.len()),
        }) as i64
    }
    /// coc.h:2052 `coc_prefetch`: element `i`'s residual into cache.
    pub fn prefetch(&self, i: usize) {
        if i >= self.meta.n { return }
        let b = i / BLK;
        // a hint: an address the pack does not hold is skipped, where C's never faults
        if let Some(r) = self.pack.get(self.meta.off[b] as usize + (i % BLK) * self.meta.width[b] as usize / 8) { prefetch(r) }
    }
    /// coc.h:2062 `coc_one_width`: the width every block shares, as C answers when they differ.
    pub fn one_width(&self) -> u8 {
        let w = &self.meta.width[..self.meta.nblk];
        if self.exc.is_some_and(|e| !e.pos.is_empty()) { return 255 } // a flat read would miss the patch list
        match w.first() { None => 0, Some(&w0) if w.iter().all(|&x| x == w0) => w0, _ => 255 }
    }
    /// coc.h:2165 `coc_load_run`: elements `from .. from + out.len()` into `out`; positions outside `0..n` are `fill`.
    pub fn load_run(&self, from: i64, fill: i64, out: &mut [i64]) {
        let (n, end) = (self.meta.n as i64, from + out.len() as i64);
        let lo = from.max(0).min(end);
        let hi = end.min(n).max(lo);
        out[..(lo - from) as usize].fill(fill);
        out[(hi - from) as usize..].fill(fill);
        if lo >= hi { return }
        let (b0, b1) = (lo as usize / BLK, (hi - 1) as usize / BLK);
        let g = if b1 != b0 && hi as usize - b1 * BLK > b1 * BLK - lo as usize { b1 } else { b0 };
        let bs = (g * BLK) as i64;
        let cnt = if (g + 1) * BLK < self.meta.n { BLK } else { self.meta.n - g * BLK };
        let (s, e) = (bs.max(lo), (bs + BLK as i64).min(hi));
        if bs >= from && bs + cnt as i64 <= end {
            self.decode_blk(g, cnt, &mut out[(bs - from) as usize..][..cnt]);
        } else {
            let mut tmp = [0i64; BLK];
            self.decode_blk(g, (e - bs) as usize, &mut tmp);
            out[(s - from) as usize..(e - from) as usize].copy_from_slice(&tmp[(s - bs) as usize..(e - bs) as usize]);
        }
        for j in (lo..s).chain(e..hi) { out[(j - from) as usize] = self.get(j as usize) }
    }
}
impl<'a> Meta<'a> {
    /// coc.h:176 `coc_offsets` over the metadata alone: `off[b]` from the widths; answers the residuals' end.
    pub fn offsets(width: &[u8], nblk: usize, off: &mut [u64]) -> u64 {
        let mut at = 0u64;
        for (o, &w) in off[..nblk].iter_mut().zip(&width[..nblk]) { *o = at; at += (BLK as u64 * w as u64) / 8 }
        at
    }
}
/// coc.h:303 `width_exc`: from the histogram `h` of the block's residual bit lengths, the width that minimises
/// residual plus patch bytes, and the patch count at it.
pub fn width_exc(h: &[u32], nnul: usize, esz: usize, nb: usize) -> (u8, u32) {
    let (mut best, mut e, mut bw, mut ne) = (usize::MAX, nnul + h[1..=64].iter().map(|&x| x as usize).sum::<usize>(), 64u8, 0u32);
    for w in 0..=64usize {
        if w > 0 { e -= h[w] as usize } // e: the residuals wider than w, and the nulls
        let cost = (nb * w).div_ceil(8) + e * (2 + esz);
        if cost <= best { (best, bw, ne) = (cost, w as u8, e as u32) }
    }
    (bw, ne)
}
/// coc.h:2102 `res_cmp2`: `nb` decoded pairs compared by `op` into the bit mask `out`.
pub fn res_cmp2(x: &[i64], y: &[i64], op: i32, out: &mut [u64]) {
    let nb = x.len();
    for (k, o) in out[..nb.div_ceil(64)].iter_mut().enumerate() {
        let (a, b) = (&x[k * 64..nb.min(k * 64 + 64)], &y[k * 64..nb.min(k * 64 + 64)]);
        let bit = |f: fn(&i64, &i64) -> bool| a.iter().zip(b).enumerate().fold(0u64, |w, (i, (p, q))| w | (f(p, q) as u64) << i);
        *o = match op { EQ => bit(i64::eq), NE => bit(i64::ne), LT => bit(i64::lt), LE => bit(i64::le), GT => bit(i64::gt), _ => bit(i64::ge) };
    }
}
/// coc.h:2129 `coc_cmp2_res`: blocks `lo .. hi` of `a op b` into `out`; `deep` lists the blocks whose frames do not
/// decide the answer.
pub fn cmp2_res(a: &Coc, b: &Coc, op: i32, out: &mut [u64], deep: &[u32], lo: usize, hi: usize) {
    let (mut xa, mut xb) = ([0i64; BLK], [0i64; BLK]);
    for &k in &deep[lo..hi] {
        let (k, n) = (k as usize, a.meta.n);
        let (at, nb) = (k * BLK, if k * BLK + BLK < n { BLK } else { n - k * BLK });
        a.decode_blk(k, nb, &mut xa);
        b.decode_blk(k, nb, &mut xb);
        res_cmp2(&xa[..nb], &xb[..nb], op, &mut out[at >> 6..]); // BLK=1024 -> 16 u64 per block
    }
}

// ---- A3: coc.h:858-930 (the residual sums are res.rs) ----
impl<'a> Coc<'a> {
    /// coc.h:858 `coc_sum_blk`: block `b`'s first `nb` elements summed, wrapping.
    pub fn sum_blk(&self, b: usize, nb: usize) -> u64 { unimplemented!("A3: coc_sum_blk") }
    /// coc.h:878 `coc_sum_blk_nulls`: as `sum_blk`, nulls skipped.
    pub fn sum_blk_nulls(&self, b: usize, nb: usize) -> u64 { unimplemented!("A3: coc_sum_blk_nulls") }
    /// coc.h:893 `coc_sums_ok`: the stored block sums were taken at `nul` and the current `n`.
    pub fn sums_ok(&self, nul: i64) -> bool { unimplemented!("A3: coc_sums_ok") }
    /// coc.h:910 `coc_sum`: the column's sum, nulls `nul` skipped, wrapping.
    pub fn sum(&self, nul: i64) -> u64 { unimplemented!("A3: coc_sum") }
}
impl<'a> CocMut<'a> {
    /// coc.h:901 `coc_sums_drop`: mark the stored sums stale.
    pub fn sums_drop(&mut self) { unimplemented!("A3: coc_sums_drop") }
}

// ---- A4: coc.h:934-1050 ----
impl<'a> Coc<'a> {
    /// coc.h:934 `coc_prd`: product, nulls skipped, wrapping.
    pub fn prd(&self, nul: i64) -> u64 { unimplemented!("A4: coc_prd") }
    /// coc.h:964 `coc_any`
    pub fn any(&self) -> bool { unimplemented!("A4: coc_any") }
    /// coc.h:970 `coc_all`
    pub fn all(&self) -> bool { unimplemented!("A4: coc_all") }
    /// coc.h:1007 `coc_min`: nulls skipped; `nul` when every element is null.
    pub fn min(&self, nul: i64) -> i64 { unimplemented!("A4: coc_min") }
    /// coc.h:1031 `coc_max`
    pub fn max(&self, nul: i64) -> i64 { unimplemented!("A4: coc_max") }
}

// ---- A6: coc.h:1304-1400 ----
impl<'a> Coc<'a> {
    /// coc.h:1304 `coc_blk_allnul`
    pub fn blk_allnul(&self, b: usize) -> bool { unimplemented!("A6: coc_blk_allnul") }
    /// coc.h:1311 `coc_shift_ok`: `x + k` (`neg`: `k - x`) cannot overflow any block's frame.
    pub fn shift_ok(&self, k: i64, neg: bool) -> bool { unimplemented!("A6: coc_shift_ok") }
    /// coc.h:1330 `coc_negate_res`: every block's residuals negated into `out` (`packbytes` long).
    pub fn negate_res(&self, out: &mut [u8]) { unimplemented!("A6: coc_negate_res") }
}
impl<'a> CocMut<'a> {
    /// coc.h:1382 `coc_shift`: `x + k` (or `k - x`) by rewriting the metadata; sums dropped.
    pub fn shift(&mut self, k: i64, neg: bool) { unimplemented!("A6: coc_shift") }
}

#[cfg(test)]
mod tests {
    use super::*;
    // expected values: /data/tmp/qrs/A1/ex.c (coc.h's own functions at 152d98f), run; the 24600-case C differential
    // is /data/tmp/qrs/A1/{gen.c,diff_test.rs}
    #[test] fn width_exc_matches_c() {
        let mut h = [0u32; 65];
        assert_eq!(width_exc(&h, 0, 8, 1024), (0, 0));
        h[3] = 1024;
        assert_eq!(width_exc(&h, 0, 8, 1024), (3, 0));
        h = [0; 65]; h[8] = 1;
        assert_eq!(width_exc(&h, 0, 1, 8), (0, 1));
        h = [0; 65]; h[2] = 3; h[40] = 1;
        assert_eq!(width_exc(&h, 2, 2, 100), (0, 6));
    }
    #[test] fn load_run_fills_both_ends_and_a_run_off_one_end() {
        let (z, base, off, width) = ([0i64], [7i64], [0u64], [0u8]);
        let meta = Meta { base: &base, maxv: &z, off: &off, bsum: &z, width: &width, sumnul: 0, sumn: 0, n: 3, nblk: 1, mblk: 1 };
        let c = Coc { meta, pack: &[], exc: None, fdelta: None };
        let mut out = [0i64; 8];
        c.load_run(-2, 99, &mut out);
        assert_eq!(out, [99, 99, 7, 7, 7, 99, 99, 99]);
        c.load_run(5, 99, &mut out[..3]);
        assert_eq!(out[..3], [99, 99, 99]);
        assert_eq!((c.std(3), c.std(1025), c.std(0)), (true, false, false));
        assert_eq!(c.one_width(), 0);
    }
    #[test] fn res_cmp2_puts_null_least() {
        let mut out = [0u64; 1];
        res_cmp2(&[i64::MIN, 1, 2], &[0, 1, i64::MIN], LT, &mut out);
        assert_eq!(out[0], 0b001);
        res_cmp2(&[i64::MIN, 1, 2], &[i64::MIN, 1, 5], EQ, &mut out);
        assert_eq!(out[0], 0b011);
    }
}
