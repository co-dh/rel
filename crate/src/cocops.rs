#![forbid(unsafe_code)]
//! Column (a), coc.h: the whole-column reads of a `Coc` (A1), its sums (A3), product, any/all, min and max (A4)
//! and the in-place shift (A6), plus `CocMut`, the writable form of the same `coc`.
use crate::coc::{Coc, Meta};
use crate::coc::lanes;
use crate::res::{res_get, res_get_in, res_min_nonzero, res_pack_scalar, res_sum};
use crate::simd::prefetch;
use crate::BLK;

/// coc.h:987, the comparison codes in QLean.Kernel.Ew's constructor order
pub(crate) const EQ: i32 = 0;
pub(crate) const NE: i32 = 1;
pub(crate) const LT: i32 = 2;
pub(crate) const LE: i32 = 3;
pub(crate) const GT: i32 = 4;
pub(crate) const GE: i32 = 5;

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
/// decide the answer. `out[0]` is word `w0` of the whole bitmap (0 for the whole of it).
pub fn cmp2_res(a: &Coc, b: &Coc, op: i32, out: &mut [u64], deep: &[u32], lo: usize, hi: usize, w0: usize) {
    let (mut xa, mut xb) = ([0i64; BLK], [0i64; BLK]);
    for &k in &deep[lo..hi] {
        let (k, n) = (k as usize, a.meta.n);
        let (at, nb) = (k * BLK, if k * BLK + BLK < n { BLK } else { n - k * BLK });
        a.decode_blk(k, nb, &mut xa);
        b.decode_blk(k, nb, &mut xb);
        res_cmp2(&xa[..nb], &xb[..nb], op, &mut out[(at >> 6) - w0..]); // BLK=1024 -> 16 u64 per block
    }
}

// ---- A3: coc.h:858-930 (the residual sums are res.rs) ----
impl<'a> Coc<'a> {
    /// coc.h:858 `coc_sum_blk`: block `b`'s first `nb` elements summed, wrapping.
    pub fn sum_blk(&self, b: usize, nb: usize) -> u64 {
        let (mut w, at) = (self.meta.width[b], self.meta.off[b] as usize);
        let p = &self.pack[at..at + BLK * w as usize / 8];
        let s = if w & w.wrapping_sub(1) == 0 { res_sum(p, nb, w) } else {
            let mut buf = [0u8; BLK * 8]; // the lanes of an odd width, summed at the lane width `lanes` leaves in `w`
            let q = lanes(p, &mut w, nb, &mut buf);
            res_sum(q, nb, w)
        };
        (nb as u64).wrapping_mul(self.frame(b)).wrapping_add(s)
    }
    /// coc.h:878 `coc_sum_blk_nulls`: as `sum_blk`, nulls skipped. A null is the residual 0, which neither the
    /// residual sum nor the count `k` of elements takes in.
    pub fn sum_blk_nulls(&self, b: usize, nb: usize) -> u64 {
        let (w, at) = (self.meta.width[b], self.meta.off[b] as usize);
        let p = &self.pack[at..at + BLK * w as usize / 8];
        let (mut s, mut k) = (0u64, 0u64);
        for j in 0..nb { let r = res_get(p, w, j); if r != 0 { s = s.wrapping_add(r); k += 1 } }
        k.wrapping_mul(self.frame(b)).wrapping_add(s)
    }
    /// coc.h:893 `coc_sums_ok`: the stored block sums were taken at `nul` and the current `n`. 0 is no type's null,
    /// so "no sums stored" and "taken at another null" are one test.
    pub fn sums_ok(&self, nul: i64) -> bool { self.meta.sumnul == nul && self.meta.sumn == self.meta.n as u64 && nul != 0 }
    /// coc.h:910 `coc_sum`: the column's sum, nulls `nul` skipped, wrapping.
    pub fn sum(&self, nul: i64) -> u64 {
        let m = &self.meta;
        // the stored sums are the numbers `sum_blk` and `sum_blk_nulls` compute, at nblk reads rather than n
        if self.sums_ok(nul) { return m.bsum[..m.nblk].iter().fold(0u64, |a, &s| a.wrapping_add(s as u64)) }
        let mut acc = 0u64;
        for b in 0..m.nblk {
            let nb = if b * BLK + BLK < m.n { BLK } else { m.n - b * BLK };
            acc = acc.wrapping_add(if m.base[b] == nul { self.sum_blk_nulls(b, nb) } else { self.sum_blk(b, nb) });
            // each exception's slot added the frame: take it back and add the element, a null adding nothing
            let Some(e) = self.exc.filter(|e| !e.pos.is_empty()) else { continue };
            for j in (e.off[b] as usize..e.off[b + 1] as usize).filter(|&j| (e.pos[j] as usize) < nb) {
                let v = self.exc(j);
                acc = acc.wrapping_add(if v == nul { 0 } else { v as u64 }).wrapping_sub(self.frame(b));
            }
        }
        acc
    }
}
impl<'a> CocMut<'a> {
    /// coc.h:901 `coc_sums_drop`: mark the stored sums stale. `bsum` is zeroed with the trailer, so two columns of the
    /// same elements hold the same bytes.
    pub fn sums_drop(&mut self) {
        self.bsum[..self.nblk].fill(0);
        if let Some(s) = self.sumnul.as_deref_mut() { *s = 0 }
        if let Some(s) = self.sumn.as_deref_mut() { *s = 0 }
    }
}

// ---- A4: coc.h:934-1050 ----
impl<'a> Coc<'a> {
    /// Block `b`'s residual bytes and its element count.
    fn blk(&self, b: usize) -> (&'a [u8], usize) {
        let m = &self.meta;
        let at = m.off[b] as usize;
        (&self.pack[at..at + BLK * m.width[b] as usize / 8], if b * BLK + BLK < m.n { BLK } else { m.n - b * BLK })
    }
    /// coc.h:934 `coc_prd`: product, nulls skipped, wrapping. Every element is read; the accumulator reaching 0
    /// ends the column, a wrapping product being absorbing at 0 as an exact one is.
    pub fn prd(&self, nul: i64) -> u64 {
        let (mut acc, m) = (1u64, &self.meta);
        for b in 0..m.nblk {
            if acc == 0 { break }
            let ((p, nb), base, w) = (self.blk(b), m.base[b] as u64, m.width[b]);
            if self.blk_nexc(b) != 0 {
                let mut x = [0i64; BLK];
                self.decode_blk(b, nb, &mut x);
                for &v in x[..nb].iter().filter(|&&v| v != nul) { acc = acc.wrapping_mul(v as u64) }
            } else if m.base[b] == nul {
                for r in (0..nb).map(|j| res_get(p, w, j)).filter(|&r| r != 0) { acc = acc.wrapping_mul(base.wrapping_add(r)) }
            } else {
                for j in 0..nb { acc = acc.wrapping_mul(base.wrapping_add(res_get(p, w, j))) }
            }
        }
        acc
    }
    /// coc.h:964 `coc_any`: base and maxv are attained values, so only a patched block's exceptions need asking too.
    pub fn any(&self) -> bool {
        let m = &self.meta;
        (0..m.nblk).any(|b| m.base[b] != 0 || m.maxv[b] != 0) || (0..self.exc.map_or(0, |e| e.pos.len())).any(|j| self.exc(j) != 0)
    }
    /// coc.h:970 `coc_all`: descends only into a block that could hold a zero (base <= 0 <= maxv), where a zero has
    /// the residual `0 - base`.
    pub fn all(&self) -> bool {
        let m = &self.meta;
        (0..m.nblk).filter(|&b| !(m.base[b] > 0 || m.maxv[b] < 0)).all(|b| {
            let (p, nb) = self.blk(b);
            if self.blk_nexc(b) != 0 { // a slot reads as base, which may be the zero it is not
                let mut x = [0i64; BLK];
                self.decode_blk(b, nb, &mut x);
                return x[..nb].iter().all(|&v| v != 0)
            }
            let t = 0u64.wrapping_sub(m.base[b] as u64);
            (0..nb).all(|j| res_get(p, m.width[b], j) != t)
        })
    }
    /// coc.h:1007 `coc_min`: nulls skipped; `!nul` (q's 0W) when every element is null. The first phase is a plain
    /// running minimum that vectorises; the null test is asked once afterwards.
    pub fn min(&self, nul: i64) -> i64 {
        let m = &self.meta;
        let lo = m.base[..m.nblk].iter().fold(!nul, |a, &b| a.min(b));
        if lo != nul { return lo }
        (0..m.nblk).filter_map(|b| if m.base[b] != nul { Some(m.base[b]) } else {
            let (p, nb) = self.blk(b);
            let r = res_min_nonzero(p, nb, m.width[b]);
            (r != 0).then(|| self.frame(b).wrapping_add(r) as i64) // r = 0: every element of the block is null
        }).fold(!nul, i64::min)
    }
    /// coc.h:1031 `coc_max`: a null is the smallest element, so `maxv` is the answer unless every block is null,
    /// which is q's -0W.
    pub fn max(&self, nul: i64) -> i64 {
        let m = self.meta.maxv[..self.meta.nblk].iter().fold(nul, |a, &b| a.max(b));
        if m == nul { nul.wrapping_add(1) } else { m }
    }
}

// ---- A6: coc.h:945-1035 ----
impl<'a> Coc<'a> {
    /// coc.h:945 `coc_blk_allnul`: the writer's whole block of nulls, `base == maxv ==` the null. A `base` alone at the
    /// null is a kernel's own answer from before the writer, and every whole-column verb refuses it.
    pub fn blk_allnul(&self, b: usize) -> bool { self.meta.base[b] == i64::MIN && self.meta.maxv[b] == i64::MIN }
    /// coc.h:952 `coc_shift_ok`: 0 when `x + k` (`neg`: `k - x`) must be refused (the null as `k`, a block holding a
    /// pre-writer null, a frame leaving `i64`), 1 when it rides the metadata, 2 when it needs `coc_fill_nul`.
    pub fn shift_ok(&self, k: i64, neg: bool) -> i32 {
        let m = &self.meta;
        let mut path = if neg || self.exc.is_some_and(|e| !e.pos.is_empty()) { 2 } else { 1 };
        if k == i64::MIN { return 0 }
        for b in 0..m.nblk {
            if self.blk_allnul(b) { path = 2; continue }
            if m.base[b] == i64::MIN { return 0 }
            let (lo, hi) = if neg { (k.checked_sub(m.maxv[b]), k.checked_sub(m.base[b])) }
                           else { (m.base[b].checked_add(k), m.maxv[b].checked_add(k)) };
            let (Some(lo), Some(_)) = (lo, hi) else { return 0 };
            // a minimum landing on the null makes a null the writer would patch, so the frame is not its
            if lo == i64::MIN { path = 2 }
        }
        path
    }
    /// coc.h:971 `coc_negate_res`: the residuals of `k - x` into `out`, a pack of the same size. The block turns round,
    /// its minimum becoming `k - maxv`, so an element's residual is `R - r` for the block's range `R`; the width and
    /// the offsets stay. Bytes of a block past its last element are written 0.
    pub fn negate_res(&self, out: &mut [u8]) {
        let m = &self.meta;
        for b in 0..m.nblk {
            let (lo, w) = (b * BLK, m.width[b]);
            let nb = if lo + BLK < m.n { BLK } else { m.n - lo };
            let r = (m.maxv[b] as u64).wrapping_sub(m.base[b] as u64);
            let (at, bytes) = (m.off[b] as usize, BLK * w as usize / 8);
            let (p, o) = (&self.pack[at..at + bytes], &mut out[at..at + bytes]);
            let done = (nb * w as usize).div_ceil(8);
            match w {
                0 => {}
                8 => for (d, &s) in o.iter_mut().zip(p).take(nb) { *d = (r as u8).wrapping_sub(s) },
                16 => for (d, s) in o.chunks_exact_mut(2).zip(p.chunks_exact(2)).take(nb) {
                    d.copy_from_slice(&(r as u16).wrapping_sub(u16::from_le_bytes([s[0], s[1]])).to_le_bytes())
                },
                32 => for (d, s) in o.chunks_exact_mut(4).zip(p.chunks_exact(4)).take(nb) {
                    d.copy_from_slice(&(r as u32).wrapping_sub(u32::from_le_bytes(s.try_into().unwrap())).to_le_bytes())
                },
                64 => for (d, s) in o.chunks_exact_mut(8).zip(p.chunks_exact(8)).take(nb) {
                    d.copy_from_slice(&r.wrapping_sub(u64::from_le_bytes(s.try_into().unwrap())).to_le_bytes())
                },
                // 1, 2 and 4 bits: no field borrows into the next, every residual being at most R, so one byte-wide
                // subtraction from R replicated in each field does 8 / width of them at once
                1 | 2 | 4 => {
                    let per = 8 / w as usize;
                    let rep = (r.wrapping_mul(0xff / ((1u64 << w) - 1))) as u8;
                    for (d, &s) in o.iter_mut().zip(p).take(nb.div_ceil(per)) { *d = rep.wrapping_sub(s) }
                    // the fields of the last byte that no element owns
                    if nb % per != 0 { o[nb.div_ceil(per) - 1] &= ((1u32 << ((nb % per) * w as usize)) - 1) as u8 }
                }
                _ => {
                    let mut v = [0u64; BLK];
                    for (j, x) in v[..nb].iter_mut().enumerate() { *x = r.wrapping_sub(res_get(p, w, j)) }
                    res_pack_scalar(&v, w, nb, &mut o[..done]);
                }
            }
            o[done..].fill(0);
        }
    }
}
impl<'a> CocMut<'a> {
    /// coc.h:1023 `coc_shift`: `k + x` (`neg`: `k - x`) on base, maxv and the block sums, in unsigned arithmetic. The
    /// guard is `shift_ok`'s, not this function's. The sums come along only where they still say what they said: a block
    /// whose minimum is the null held a null the stored sum left out, and one whose minimum lands on it has made one.
    pub fn shift(&mut self, k: i64, neg: bool) {
        let mut keep = self.sumnul.as_deref().is_some_and(|&s| s == i64::MIN) && self.sumn.as_deref().is_some_and(|&s| s == self.n as u64);
        for b in 0..self.nblk {
            let (bs, mx) = (self.base[b] as u64, self.maxv[b] as u64);
            let (lo, hi) = if neg { ((k as u64).wrapping_sub(mx), (k as u64).wrapping_sub(bs)) }
                           else { (bs.wrapping_add(k as u64), mx.wrapping_add(k as u64)) };
            let at = b * BLK;
            let nb = if at + BLK < self.n { BLK } else { self.n - at };
            let s = (nb as u64).wrapping_mul(k as u64);
            if self.base[b] == i64::MIN || lo as i64 == i64::MIN { keep = false }
            (self.base[b], self.maxv[b]) = (lo as i64, hi as i64);
            let old = self.bsum[b] as u64;
            self.bsum[b] = (if neg { s.wrapping_sub(old) } else { s.wrapping_add(old) }) as i64;
        }
        if !keep { self.sums_drop() }
    }
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
    // expected values: the C of 7091572 (/data/tmp/qrs/A4/diff.c: 312000 checks, 0 mismatches)
    #[test] fn folds_of_a_column_with_no_element_are_q_seeds() {
        let meta = Meta { base: &[], maxv: &[], off: &[], bsum: &[], width: &[], sumnul: 0, sumn: 0, n: 0, nblk: 0, mblk: 0 };
        let c = Coc { meta, pack: &[], exc: None, fdelta: None };
        assert_eq!((c.prd(i64::MIN), c.min(i64::MIN), c.max(i64::MIN)), (1, i64::MAX, i64::MIN + 1));
        assert_eq!((c.all(), c.any()), (true, false));
    }
    #[test] fn all_null_block_and_all_zero_block() {
        fn mk(v: &[i64; 1]) -> Coc<'_> {
            Coc { meta: Meta { base: v, maxv: v, off: &[0], bsum: &[0], width: &[0], sumnul: 0, sumn: 0, n: 3, nblk: 1, mblk: 1 }, pack: &[], exc: None, fdelta: None }
        }
        let n = mk(&[i64::MIN]);
        assert_eq!((n.min(i64::MIN), n.max(i64::MIN), n.prd(i64::MIN)), (i64::MAX, i64::MIN + 1, 1));
        let z = mk(&[0]);
        assert_eq!((z.any(), z.all(), z.prd(i64::MIN)), (false, false, 0));
    }
    // expected values: the C of d995c59 (/data/tmp/qrs/A3/diff.c: 185232 checks, 0 mismatches)
    #[test] fn sums_wrap_skip_nulls_and_drop() {
        let mut base = [i64::MAX];
        let mut bsum = [5i64];
        let (mut sn, mut ss) = (i64::MIN, 3u64);
        fn mk<'a>(base: &'a [i64], bsum: &'a [i64], sumnul: i64, sumn: u64) -> Coc<'a> {
            let meta = Meta { base, maxv: &[0], off: &[0], bsum, width: &[0], sumnul, sumn, n: 3, nblk: 1, mblk: 1 };
            Coc { meta, pack: &[], exc: None, fdelta: None }
        }
        // 3 * i64::MAX wraps; a block whose base is the null sums to 0
        let c = mk(&base, &bsum, 0, 0);
        assert_eq!(c.sum(i64::MIN), i64::MAX.wrapping_mul(3) as u64);
        assert_eq!(c.sum(i64::MAX), 0);
        assert!(!c.sums_ok(i64::MIN));
        // stored sums answer only at their own null and n; 0 is never a null
        assert_eq!(mk(&base, &bsum, i64::MIN, 3).sum(i64::MIN), 5);
        assert!(mk(&base, &bsum, i64::MIN, 3).sums_ok(i64::MIN));
        assert!(!mk(&base, &bsum, i64::MIN, 4).sums_ok(i64::MIN) && !mk(&base, &bsum, 0, 3).sums_ok(0));
        let mut m = CocMut { base: &mut base, maxv: &mut [0], off: &mut [0], bsum: &mut bsum, width: &mut [0], sumnul: Some(&mut sn),
                             sumn: Some(&mut ss), pack: &mut [], n: 3, nblk: 1, mblk: 1 };
        m.sums_drop();
        assert_eq!((m.bsum[0], *m.sumnul.unwrap(), *m.sumn.unwrap()), (0, 0, 0));
    }
    #[test] fn res_cmp2_puts_null_least() {
        let mut out = [0u64; 1];
        res_cmp2(&[i64::MIN, 1, 2], &[0, 1, i64::MIN], LT, &mut out);
        assert_eq!(out[0], 0b001);
        res_cmp2(&[i64::MIN, 1, 2], &[i64::MIN, 1, 5], EQ, &mut out);
        assert_eq!(out[0], 0b011);
    }
    // expected values: the C of 336b87b (/data/tmp/qrs/A6b/gen.c: 3000 columns, 63000 comparisons, 0 mismatches)
    #[test] fn shift_refusals_paths_and_sums() {
        let cm = |base: &[i64], maxv: &[i64]| Coc { meta: Meta { base: &base.to_vec().leak()[..], maxv: &maxv.to_vec().leak()[..], off: &[0; 2],
            bsum: &[0; 2], width: &[0; 2], sumnul: i64::MIN, sumn: 2048, n: 2048, nblk: 2, mblk: 2 }, pack: &[], exc: None, fdelta: None };
        let c = cm(&[1, 5], &[9, 9]);
        assert_eq!((c.shift_ok(1, false), c.shift_ok(1, true), c.shift_ok(i64::MIN, false)), (1, 2, 0));
        assert_eq!((c.shift_ok(i64::MAX - 8, false), c.shift_ok(i64::MAX - 9, false)), (0, 1));
        assert_eq!(c.shift_ok(i64::MIN + 9, true), 2); // k - maxv lands on the null: the writer patches it
        assert_eq!(cm(&[i64::MIN, 0], &[3, 3]).shift_ok(1, false), 0); // a pre-writer null
        assert_eq!(cm(&[i64::MIN, 0], &[i64::MIN, 3]).shift_ok(1, false), 2); // an all-null block goes through the writer
        let (mut base, mut maxv, mut off, mut bsum, mut width) = ([1i64, 5], [9i64, 9], [0u64; 2], [10i64, 20], [0u8; 2]);
        let (mut sn, mut sc) = (i64::MIN, 2048u64);
        let mut m = CocMut { base: &mut base, maxv: &mut maxv, off: &mut off, bsum: &mut bsum, width: &mut width,
                             sumnul: Some(&mut sn), sumn: Some(&mut sc), pack: &mut [], n: 2048, nblk: 2, mblk: 2 };
        m.shift(3, false);
        assert_eq!((m.base.to_vec(), m.maxv.to_vec(), m.bsum.to_vec()), (vec![4, 8], vec![12, 12], vec![3082, 3092]));
        m.shift(0, true); // `0 - x` turns the blocks round; the sums are told so
        assert_eq!((m.base.to_vec(), m.bsum.to_vec(), *m.sumnul.as_deref().unwrap()), (vec![-12, -12], vec![-3082, -3092], i64::MIN));
        m.shift(i64::MIN.wrapping_add(-8), true); // block 1's minimum lands on the null: the sums go
        assert_eq!((*m.sumnul.as_deref().unwrap(), *m.sumn.as_deref().unwrap()), (0, 0));
    }
    #[test] fn negate_res_turns_each_block_round_at_every_width() {
        let pack: Vec<u8> = (0..BLK as u32 * 8).map(|i| (i * 37 + 11) as u8).collect();
        for w in [0u8, 1, 2, 3, 4, 7, 8, 13, 16, 32, 63, 64] {
            let m = |n: usize| Meta { base: &[10], maxv: &[10 + 200], off: &[0], bsum: &[0], width: &*vec![w].leak(), sumnul: 0, sumn: 0, n, nblk: 1, mblk: 1 };
            let nb = BLK * w as usize / 8;
            for n in [BLK, 100] {
                let c = Coc { meta: m(n), pack: &pack[..nb], exc: None, fdelta: None };
                let (mut once, mut twice) = (vec![0xabu8; nb], vec![0xabu8; nb]);
                c.negate_res(&mut once);
                let c2 = Coc { pack: &once, ..c };
                c2.negate_res(&mut twice);
                // R - (R - r) = r on the n elements, and the bytes past them are 0
                for j in 0..n { assert_eq!(res_get(&twice, w, j), res_get(&pack[..nb], w, j), "w {w} n {n} j {j}") }
                assert!(twice[(n * w as usize).div_ceil(8)..].iter().all(|&x| x == 0));
            }
        }
    }
}
