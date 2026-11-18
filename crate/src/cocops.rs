#![forbid(unsafe_code)]
//! Column (a), coc.rs: the whole-column reads of a `Coc` (A1), its sums (A3), product, any/all, min and max (A4)
//! and the in-place shift (A6), plus `CocMut`, the writable form of the same `coc`.
use crate::blocks::{Blocks, Res};
use crate::coc::{Coc, Meta};
use crate::coc::lanes;
use crate::pod;
use crate::res::{res_get, res_get_in, res_min_nonzero, res_sum};
use crate::simd::prefetch;

/// coc.rs, the comparison codes in QLean.Kernel.Ew's constructor order
pub const EQ: i32 = 0;
pub const NE: i32 = 1;
pub const LT: i32 = 2;
pub const LE: i32 = 3;
pub const GT: i32 = 4;
pub const GE: i32 = 5;

/// The writable form of coc.rs `coc`, for the operations that rewrite a column in place: `coc_offsets` (A1),
/// `coc_sums_drop` (A3), `coc_shift` (A6). Lengths as `Coc`'s; the per-block writers of the encoder take
/// `enc::EncMeta`/`enc::EncPack` instead, which split this by block.
pub struct CocMut<'a> {
    pub base: &'a mut [i64], pub maxv: &'a mut [i64], pub bsum: &'a mut [i64],
    /// null in C = no sums stored
    pub sumnul: Option<&'a mut i64>, pub sumn: Option<&'a mut u64>,
    pub n: usize, pub nblk: usize, pub lg: u32,
}

impl<'a> CocMut<'a> {
    /// `coc_meta_view` (coc.rs) over writable metadata bytes and no pack, the view `coc_shift` rides the metadata
    /// through: None where `Meta::new` is, misaligned or shorter than its sections.
    pub fn meta_only(m: &'a mut [u8], n: usize) -> Option<Self> {
        let nb = m.len() / 33;
        if m.len() < 33 * nb + 24 { return None }
        let (head, tail) = m.split_at_mut(32 * nb);
        let (base, rest) = head.split_at_mut(8 * nb);
        let (maxv, rest) = rest.split_at_mut(8 * nb);
        let (_, bsum) = rest.split_at_mut(8 * nb);
        let (sumnul, rest) = tail[..24].split_at_mut(8);
        let (sumn, lg) = rest.split_at_mut(8);
        let lg = pod::cast_mut::<u64>(lg)?[0];
        if !(crate::MIN_LG as u64..=crate::MAX_LG as u64).contains(&lg) { return None }
        let (lg, n) = (lg as u32, n.min(nb << lg));
        Some(CocMut {
            base: pod::cast_mut(base)?, maxv: pod::cast_mut(maxv)?, bsum: pod::cast_mut(bsum)?,
            sumnul: Some(&mut pod::cast_mut::<i64>(sumnul)?[0]), sumn: Some(&mut pod::cast_mut::<u64>(sumn)?[0]), n, nblk: n.div_ceil(1 << lg), lg,
        })
    }
}

// ---- A1: coc.rs, 2043-2165 ----

/// `coc_meta_view` (coc.rs) and `coc_attach` (coc.rs) are `Meta::new` and `Coc::attach`; `coc_blocks`
/// (coc.rs) is `Coc::blocks`; `coc_res_end`, `coc_grid`, `coc_std` are `Meta::res_end`, `Meta::grid`, `Coc::std`.
impl<'a> Coc<'a> {
    /// coc.rs `coc_get`: element `i`, its patch applied. Per element: C keeps its body while a C caller remains.
    pub fn get(&self, i: usize) -> i64 {
        let (b, j) = (i >> self.meta.lg, i & (self.meta.blk() - 1));
        if let Some(e) = self.exc.filter(|e| !e.pos.is_empty()) {
            for x in e.off[b] as usize..e.off[b + 1] as usize { if e.pos[x] as usize == j { return self.exc(x) } }
        }
        let p = self.pack.get(self.meta.off[b] as usize..).unwrap_or(&[]);
        self.frame(b).wrapping_add(res_get_in(p, self.meta.width[b], j, p.len())) as i64
    }
    /// coc.rs `coc_get_w`: `get` for a column whose every block has residual width `uw` (`one_width`).
    pub fn get_w(&self, uw: u8, i: usize) -> i64 {
        let (base, p) = (self.meta.base[i >> self.meta.lg] as u64, self.pack);
        if uw == 255 || self.exc.is_some_and(|e| !e.pos.is_empty()) { return self.get(i) }
        // a lane width through `by_width!`; an odd width is flat too, so the residual is read at `i * uw` bits of the pack
        base.wrapping_add(if uw <= 64 && uw & uw.wrapping_sub(1) == 0 { use crate::ids::lane; crate::by_width!(uw, lane(p, i)) }
            else { res_get_in(p, uw, i, p.len()) }) as i64
    }
    /// coc.rs `coc_prefetch`: element `i`'s residual into cache.
    pub fn prefetch(&self, i: usize) {
        if i >= self.meta.n { return }
        let b = i >> self.meta.lg;
        // a hint: an address the pack does not hold is skipped, where C's never faults
        if let Some(r) = self.pack.get(self.meta.off[b] as usize + (i & (self.meta.blk() - 1)) * self.meta.width[b] as usize / 8) { prefetch(r) }
    }
    /// coc.rs `coc_one_width`: the width every block shares, as C answers when they differ.
    pub fn one_width(&self) -> u8 {
        let w = &self.meta.width[..self.meta.nblk];
        if self.exc.is_some_and(|e| !e.pos.is_empty()) { return 255 } // a flat read would miss the patch list
        match w.first() { None => 0, Some(&w0) if w.iter().all(|&x| x == w0) => w0, _ => 255 }
    }
    /// coc.rs `coc_load_run`: elements `from .. from + out.len()` into `out`; positions outside `0..n` are `fill`.
    pub fn load_run(&self, from: i64, fill: i64, out: &mut [i64]) {
        let (n, end) = (self.meta.n as i64, from + out.len() as i64);
        let lo = from.max(0).min(end);
        let hi = end.min(n).max(lo);
        out[..(lo - from) as usize].fill(fill);
        out[(hi - from) as usize..].fill(fill);
        if lo >= hi { return }
        let (lg, blk) = (self.meta.lg, self.meta.blk());
        let (b0, b1) = (lo as usize >> lg, (hi - 1) as usize >> lg);
        let g = if b1 != b0 && hi as usize - (b1 << lg) > (b1 << lg) - lo as usize { b1 } else { b0 };
        let bs = (g << lg) as i64;
        let cnt = Blocks::from(*self).span(g).1;
        let (s, e) = (bs.max(lo), (bs + blk as i64).min(hi));
        if bs >= from && bs + cnt as i64 <= end {
            self.decode_blk(g, cnt, &mut out[(bs - from) as usize..][..cnt]);
        } else {
            let mut tmp = pod::Scr::<i64>::new(blk);
            self.decode_blk(g, (e - bs) as usize, &mut tmp);
            out[(s - from) as usize..(e - from) as usize].copy_from_slice(&tmp[(s - bs) as usize..(e - bs) as usize]);
        }
        for j in (lo..s).chain(e..hi) { out[(j - from) as usize] = self.get(j as usize) }
    }
}
impl<'a> Meta<'a> {
    /// coc.rs `coc_offsets` over the metadata alone: `off[b]` from the widths; answers the residuals' end.
    pub fn offsets(lg: u32, width: &[u8], nblk: usize, off: &mut [u64]) -> u64 {
        let mut at = 0u64;
        for (o, &w) in off[..nblk].iter_mut().zip(&width[..nblk]) { *o = at; at += ((1u64 << lg) * w as u64) / 8 }
        at
    }
}
/// coc.rs `res_cmp2`: `nb` decoded pairs compared by `op` into the bit mask `out`.
pub fn res_cmp2(x: &[i64], y: &[i64], op: i32, out: &mut [u64]) {
    let nb = x.len();
    for (k, o) in out[..nb.div_ceil(64)].iter_mut().enumerate() {
        let (a, b) = (&x[k * 64..nb.min(k * 64 + 64)], &y[k * 64..nb.min(k * 64 + 64)]);
        let bit = |f: fn(&i64, &i64) -> bool| a.iter().zip(b).enumerate().fold(0u64, |w, (i, (p, q))| w | (f(p, q) as u64) << i);
        *o = match op { EQ => bit(i64::eq), NE => bit(i64::ne), LT => bit(i64::lt), LE => bit(i64::le), GT => bit(i64::gt), _ => bit(i64::ge) };
    }
}
/// coc.rs `coc_cmp2_res`: blocks `lo .. hi` of `a op b` into `out`; `deep` lists the blocks whose frames do not
/// decide the answer. `out[0]` is word `w0` of the whole bitmap (0 for the whole of it).
pub fn cmp2_res(a: &Coc, b: &Coc, op: i32, out: &mut [u64], deep: &[u32], lo: usize, hi: usize, w0: usize) {
    assert_eq!(a.meta.lg, b.meta.lg, "coc cmp2: columns of different block sizes");
    let blk = a.meta.blk();
    let (mut xa, mut xb) = (pod::Scr::<i64>::new(blk), pod::Scr::<i64>::new(blk));
    for &k in &deep[lo..hi] {
        let k = k as usize;
        let (at, nb) = Blocks::from(*a).span(k);
        if let (Some(pa), Some(pb)) = (a.bit_blk(k), b.bit_blk(k)) { crate::bitblk::cmp2(pa, pb, nb, op, &mut out[(at >> 6) - w0..]); continue }
        a.decode_blk(k, nb, &mut xa);
        b.decode_blk(k, nb, &mut xb);
        res_cmp2(&xa[..nb], &xb[..nb], op, &mut out[(at >> 6) - w0..]); // blk / 64 u64 per block
    }
}

// ---- A3: coc.rs (the residual sums are res.rs) ----
impl<'a> Coc<'a> {
    /// coc.rs `coc_sum_blk`: block `b`'s first `nb` elements summed, wrapping.
    pub fn sum_blk(&self, b: usize, nb: usize) -> u64 {
        if let Some(p) = self.bit_blk(b) { return crate::bitblk::ones(p, nb) as u64 }
        let (mut w, at) = (self.meta.width[b], self.meta.off[b] as usize);
        let p = &self.pack[at..at + self.meta.blk() * w as usize / 8];
        let s = if w &w.wrapping_sub(1) == 0 { res_sum(p, nb, w) } else {
            let mut buf = pod::Scr::<u8, 8192>::new(self.meta.blk() * 8); // the lanes of an odd width, summed at the lane width `lanes` leaves in `w`
            let q = lanes(p, &mut w, nb, &mut buf);
            res_sum(q, nb, w)
        };
        (nb as u64).wrapping_mul(self.frame(b)).wrapping_add(s)
    }
    /// coc.rs `coc_sum_blk_nulls`: as `sum_blk`, nulls skipped. A null is the residual 0, which neither the
    /// residual sum nor the count `k` of elements takes in.
    pub fn sum_blk_nulls(&self, b: usize, nb: usize) -> u64 {
        let (w, at) = (self.meta.width[b], self.meta.off[b] as usize);
        let p = &self.pack[at..at + self.meta.blk() * w as usize / 8];
        let (mut s, mut k) = (0u64, 0u64);
        for j in 0..nb { let r = res_get(p, w, j); if r != 0 { s = s.wrapping_add(r); k += 1 } }
        k.wrapping_mul(self.frame(b)).wrapping_add(s)
    }
    /// coc.rs `coc_sums_ok`: the stored block sums were taken at `nul` and the current `n`. 0 is no type's null,
    /// so "no sums stored" and "taken at another null" are one test.
    pub fn sums_ok(&self, nul: i64) -> bool { self.meta.sumnul == nul && self.meta.sumn == self.meta.n as u64 && nul != 0 }
    /// coc.rs `coc_sum`: the column's sum, nulls `nul` skipped, wrapping.
    pub fn sum(&self, nul: i64) -> u64 {
        let m = &self.meta;
        // the stored sums are the numbers `sum_blk` and `sum_blk_nulls` compute, at nblk reads rather than n
        if self.sums_ok(nul) { return m.bsum[..m.nblk].iter().fold(0u64, |a, &s| a.wrapping_add(s as u64)) }
        let mut acc = 0u64;
        let blk = m.blk();
        for b in 0..m.nblk {
            let nb = if (b + 1) << m.lg < m.n { blk } else { m.n - (b << m.lg) };
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
    /// coc.rs `coc_sums_drop`: mark the stored sums stale. `bsum` is zeroed with the trailer, so two columns of the
    /// same elements hold the same bytes.
    pub fn sums_drop(&mut self) {
        self.bsum[..self.nblk].fill(0);
        if let Some(s) = self.sumnul.as_deref_mut() { *s = 0 }
        if let Some(s) = self.sumn.as_deref_mut() { *s = 0 }
    }
}

// ---- A4: coc.rs ----
impl<'a> Coc<'a> {
    /// coc.rs `coc_prd`: product, nulls skipped, wrapping. Every element is read; the accumulator reaching 0
    /// ends the column, a wrapping product being absorbing at 0 as an exact one is.
    pub fn prd(&self, nul: i64) -> u64 {
        let (mut acc, m) = (1u64, &self.meta);
        for b in 0..m.nblk {
            if acc == 0 { break }
            let (Res { pack: p, nb, .. }, base, w) = (Blocks::from(*self).res(b), m.base[b] as u64, m.width[b]);
            if self.blk_nexc(b) != 0 {
                let mut x = pod::Scr::<i64>::new(m.blk());
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
    /// coc.rs `coc_any`: base and maxv are attained values, so only a patched block's exceptions need asking too.
    pub fn any(&self) -> bool {
        let m = &self.meta;
        (0..m.nblk).any(|b| m.base[b] != 0 || m.maxv[b] != 0) || (0..self.exc.map_or(0, |e| e.pos.len())).any(|j| self.exc(j) != 0)
    }
    /// coc.rs `coc_all`: descends only into a block that could hold a zero (base <= 0 <= maxv), where a zero has
    /// the residual `0 - base`.
    pub fn all(&self) -> bool {
        let m = &self.meta;
        (0..m.nblk).filter(|&b| !(m.base[b] > 0 || m.maxv[b] < 0)).all(|b| {
            let Res { pack: p, nb, .. } = Blocks::from(*self).res(b);
            if self.blk_nexc(b) != 0 { // a slot reads as base, which may be the zero it is not
                let mut x = pod::Scr::<i64>::new(m.blk());
                self.decode_blk(b, nb, &mut x);
                return x[..nb].iter().all(|&v| v != 0)
            }
            if let Some(p) = self.bit_blk(b) { return crate::bitblk::all_set(p, nb) }
            let t = 0u64.wrapping_sub(m.base[b] as u64);
            (0..nb).all(|j| res_get(p, m.width[b], j) != t)
        })
    }
    /// coc.rs `coc_min`: nulls skipped; `!nul` (q's 0W) when every element is null. The first phase is a plain
    /// running minimum that vectorises; the null test is asked once afterwards.
    pub fn min(&self, nul: i64) -> i64 {
        let m = &self.meta;
        let lo = m.base[..m.nblk].iter().fold(!nul, |a, &b| a.min(b));
        if lo != nul { return lo }
        (0..m.nblk).filter_map(|b| if m.base[b] != nul { Some(m.base[b]) } else {
            let Res { pack: p, nb, .. } = Blocks::from(*self).res(b);
            let r = res_min_nonzero(p, nb, m.width[b]);
            (r != 0).then(|| self.frame(b).wrapping_add(r) as i64) // r = 0: every element of the block is null
        }).fold(!nul, i64::min)
    }
    /// coc.rs `coc_max`: a null is the smallest element, so `maxv` is the answer unless every block is null,
    /// which is q's -0W.
    pub fn max(&self, nul: i64) -> i64 {
        let m = self.meta.maxv[..self.meta.nblk].iter().fold(nul, |a, &b| a.max(b));
        if m == nul { nul.wrapping_add(1) } else { m }
    }
}

// ---- A6: coc.rs ----
impl<'a> Coc<'a> {
    /// coc.rs `coc_blk_allnul`: the writer's whole block of nulls, `base == maxv ==` the null. A `base` alone at the
    /// null is a kernel's own answer from before the writer, and every whole-column verb refuses it.
    pub fn blk_allnul(&self, b: usize) -> bool { self.meta.base[b] == i64::MIN && self.meta.maxv[b] == i64::MIN }
    /// coc.rs `coc_shift_ok`: 0 when `x + k` (`neg`: `k - x`) must be refused (the null as `k`, a block holding a
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
    /// coc.rs `coc_shift_bounds`: an outer bound on what `load_run(lo - s, fill)` of `nb` answers: the extremes of every source
    /// block it touches, and `fill` where it runs off an end. A null, filled or stored, answers a null, so it bounds
    /// nothing. `(MAX, MIN)` = every operand a null. `lo - s` wraps, as C's does when `s` is at `i64`'s ends.
    pub fn shift_bounds(&self, lo: usize, nb: usize, s: i64, fill: i64) -> (i64, i64) {
        let m = &self.meta;
        let (from, n) = ((lo as i64).wrapping_sub(s), m.n as i64);
        let end = from.wrapping_add(nb as i64);
        let (l, h) = (from.max(0), end.min(n));
        let (mut a, mut z) = (i64::MAX, i64::MIN);
        if (from < 0 || end > n) && fill != i64::MIN { (a, z) = (fill, fill) }
        if l < h {
            for g in l as usize >> m.lg..=(h - 1) as usize >> m.lg {
                if self.blk_allnul(g) { continue }
                (a, z) = (a.min(m.base[g]), z.max(m.maxv[g]));
            }
        }
        (a, z)
    }
    /// coc.rs `coc_vv_ok`: whether `self op (b shifted by s, fill off its ends)` rides the encoded form (`op` 0 `+`, 1 `-`,
    /// else `*`). The bounds are the non-null extremes, a patch list's outliers included, and the fill keeps every null a
    /// null, so only an overflow or a pre-writer null frame is refused.
    pub fn vv_ok(&self, b: &Coc, op: i32, s: i64, fill: i64) -> bool {
        let m = &self.meta;
        if m.nblk != b.meta.nblk || m.lg != b.meta.lg { return false }
        for k in 0..m.nblk {
            let lo = k << m.lg;
            let nb = if lo + m.blk() < m.n { m.blk() } else { m.n - lo };
            if self.blk_allnul(k) { continue }
            let (ba, ma) = (m.base[k], m.maxv[k]);
            let (bb, mb) = b.shift_bounds(lo, nb, s, fill);
            if bb > mb { continue } // every operand a null
            if ba == i64::MIN || bb == i64::MIN { return false }
            let ok = match op {
                0 => ba.checked_add(bb).is_some() && ma.checked_add(mb).is_some(),
                1 => ba.checked_sub(mb).is_some() && ma.checked_sub(bb).is_some(),
                _ => ba.checked_mul(bb).is_some() && ba.checked_mul(mb).is_some() && ma.checked_mul(bb).is_some() && ma.checked_mul(mb).is_some(),
            };
            if !ok { return false }
        }
        true
    }
    /// coc.rs `coc_scale_ok`: whether `x * k` rides the encoded form. q's `x*0N` and `0N*0` are `0N`, so a pre-writer null
    /// frame and `k` at the null are refused, and so is an overflow of either end of a block.
    pub fn scale_ok(&self, k: i64) -> bool {
        let m = &self.meta;
        k != i64::MIN && (0..m.nblk).all(|b| self.blk_allnul(b)
            || (m.base[b] != i64::MIN && m.base[b].checked_mul(k).is_some() && m.maxv[b].checked_mul(k).is_some()))
    }
}
impl<'a> CocMut<'a> {
    /// coc.rs `coc_shift`: `k + x` (`neg`: `k - x`) on base, maxv and the block sums, in unsigned arithmetic. The
    /// guard is `shift_ok`'s, not this function's. The sums come along only where they still say what they said: a block
    /// whose minimum is the null held a null the stored sum left out, and one whose minimum lands on it has made one.
    pub fn shift(&mut self, k: i64, neg: bool) {
        let mut keep = self.sumnul.as_deref().is_some_and(|&s| s == i64::MIN) && self.sumn.as_deref().is_some_and(|&s| s == self.n as u64);
        for b in 0..self.nblk {
            let (bs, mx) = (self.base[b] as u64, self.maxv[b] as u64);
            let (lo, hi) = if neg { ((k as u64).wrapping_sub(mx), (k as u64).wrapping_sub(bs)) }
                           else { (bs.wrapping_add(k as u64), mx.wrapping_add(k as u64)) };
            let at = b << self.lg;
            let nb = if at + (1 << self.lg) < self.n { 1 << self.lg } else { self.n - at };
            let s = (nb as u64).wrapping_mul(k as u64);
            if self.base[b] == i64::MIN || lo as i64 == i64::MIN { keep = false }
            (self.base[b], self.maxv[b]) = (lo as i64, hi as i64);
            let old = self.bsum[b] as u64;
            self.bsum[b] = (if neg { s.wrapping_sub(old) } else { s.wrapping_add(old) }) as i64;
        }
        if !keep { self.sums_drop() }
    }
}

// ---- K24b: coc.rs `vv_fill` and `scale_fill`, the producers of `x op y` and `x * k` ----
/// coc.rs `vv_fill`: the answer block of `x op y` from `i0`, a block start, into `xa` (`op` 0 `+`, 1 `-`, else `*`): `a` decoded
/// there, `b` read from `i0 - s` with `fill` outside it, and a null on either side is the null.
pub fn vv_fill(a: &Coc, b: &Coc, op: i32, s: i64, fill: i64, i0: usize, xa: &mut [i64]) {
    fn go(xa: &mut [i64], xb: &[i64], f: impl Fn(u64, u64) -> u64) {
        for (a, &b) in xa.iter_mut().zip(xb) { *a = if *a == i64::MIN || b == i64::MIN { i64::MIN } else { f(*a as u64, b as u64) as i64 } }
    }
    assert_eq!(a.meta.lg, b.meta.lg, "coc vv: columns of different block sizes");
    let mut xb = pod::Scr::<i64>::new(xa.len());
    a.decode_blk(i0 >> a.meta.lg, xa.len(), xa);
    b.load_run(i0 as i64 - s, fill, &mut xb);
    // unsigned arithmetic throughout: signed overflow is UB in C even where `coc_vv_ok` has refused it
    match op { 0 => go(xa, &xb, u64::wrapping_add), 1 => go(xa, &xb, u64::wrapping_sub), _ => go(xa, &xb, u64::wrapping_mul) }
}
/// coc.rs `scale_fill`: the answer block of `x * k` from `i0` into `buf`, nulls staying the null.
pub fn scale_fill(a: &Coc, k: i64, i0: usize, buf: &mut [i64]) {
    a.decode_blk(i0 >> a.meta.lg, buf.len(), buf);
    for v in buf { if *v != i64::MIN { *v = (*v as u64).wrapping_mul(k as u64) as i64 } }
}

#[cfg(test)]
mod tests {
    use super::*;
    // expected values: /data/tmp/qrs/A1/ex.c (coc.rs's own functions at 152d98f), run; the 24600-case C differential
    // is /data/tmp/qrs/A1/{gen.c,diff_test.rs}
    #[test] fn load_run_fills_both_ends_and_a_run_off_one_end() {
        let (z, base, off, width) = ([0i64], [7i64], [0u64], [0u8]);
        let meta = Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &z, off: &off, bsum: &z, width: &width, sumnul: 0, sumn: 0, n: 3, nblk: 1, mblk: 1 };
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
        let meta = Meta { lg: crate::DEFAULT_LG, base: &[], maxv: &[], off: &[], bsum: &[], width: &[], sumnul: 0, sumn: 0, n: 0, nblk: 0, mblk: 0 };
        let c = Coc { meta, pack: &[], exc: None, fdelta: None };
        assert_eq!((c.prd(i64::MIN), c.min(i64::MIN), c.max(i64::MIN)), (1, i64::MAX, i64::MIN + 1));
        assert_eq!((c.all(), c.any()), (true, false));
    }
    #[test] fn all_null_block_and_all_zero_block() {
        fn mk(v: &[i64; 1]) -> Coc<'_> {
            Coc { meta: Meta { lg: crate::DEFAULT_LG, base: v, maxv: v, off: &[0], bsum: &[0], width: &[0], sumnul: 0, sumn: 0, n: 3, nblk: 1, mblk: 1 }, pack: &[], exc: None, fdelta: None }
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
            let meta = Meta { lg: crate::DEFAULT_LG, base, maxv: &[0], off: &[0], bsum, width: &[0], sumnul, sumn, n: 3, nblk: 1, mblk: 1 };
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
        let mut m = CocMut { lg: crate::DEFAULT_LG, base: &mut base, maxv: &mut [0], bsum: &mut bsum, sumnul: Some(&mut sn),
                             sumn: Some(&mut ss), n: 3, nblk: 1 };
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
    // expected values: the C of e16b3fd (/data/tmp/qrs/K26/diff.c: 720000 vv/scale checks, shifts at i64's ends included, 0 mismatches)
    #[test] fn vv_scale_refusals_and_shift_bounds() {
        let cm = |base: &[i64], maxv: &[i64]| Coc { meta: Meta { lg: crate::DEFAULT_LG, base: &base.to_vec().leak()[..], maxv: &maxv.to_vec().leak()[..], off: &[0; 2],
            bsum: &[0; 2], width: &[0; 2], sumnul: i64::MIN, sumn: 2048, n: 2048, nblk: 2, mblk: 2 }, pack: &[], exc: None, fdelta: None };
        let (a, b) = (cm(&[i64::MAX - 1, 0], &[i64::MAX, 0]), cm(&[2, 2], &[8, 8]));
        assert_eq!((a.vv_ok(&b, 0, 0, 0), a.vv_ok(&b, 1, 0, 0), a.vv_ok(&b, 2, 0, 0)), (false, true, false));
        assert_eq!((b.shift_bounds(0, 1024, 0, 0), b.shift_bounds(0, 1024, 1, 7)), ((2, 8), (2, 8)));
        assert_eq!(b.shift_bounds(1024, 1024, 2048, 100), (100, 100)); // runs off the front: the fill alone
        assert_eq!(b.shift_bounds(0, 1024, 5000, i64::MIN), (i64::MAX, i64::MIN)); // off the end with a null fill: bounds nothing
        assert_eq!(b.shift_bounds(0, 1024, i64::MIN, 3), (3, 3)); // `lo - s` wraps, as C's does
        assert!(b.vv_ok(&b, 2, 0, 0) && !b.vv_ok(&cm(&[i64::MIN, 0], &[3, 3]), 0, 0, 0)); // a pre-writer null on either side
        let s = cm(&[1, 5], &[9, 9]);
        assert_eq!((s.scale_ok(0), s.scale_ok(i64::MAX / 9), s.scale_ok(i64::MAX / 9 + 1), s.scale_ok(i64::MIN)), (true, true, false, false));
        assert_eq!((cm(&[i64::MIN, 0], &[i64::MIN, 3]).scale_ok(7), cm(&[i64::MIN, 0], &[3, 3]).scale_ok(7)), (true, false));
    }
    // expected values: the C of 336b87b (/data/tmp/qrs/A6b/gen.c: 3000 columns, 63000 comparisons, 0 mismatches)
    #[test] fn shift_refusals_paths_and_sums() {
        let cm = |base: &[i64], maxv: &[i64]| Coc { meta: Meta { lg: crate::DEFAULT_LG, base: &base.to_vec().leak()[..], maxv: &maxv.to_vec().leak()[..], off: &[0; 2],
            bsum: &[0; 2], width: &[0; 2], sumnul: i64::MIN, sumn: 2048, n: 2048, nblk: 2, mblk: 2 }, pack: &[], exc: None, fdelta: None };
        let c = cm(&[1, 5], &[9, 9]);
        assert_eq!((c.shift_ok(1, false), c.shift_ok(1, true), c.shift_ok(i64::MIN, false)), (1, 2, 0));
        assert_eq!((c.shift_ok(i64::MAX - 8, false), c.shift_ok(i64::MAX - 9, false)), (0, 1));
        assert_eq!(c.shift_ok(i64::MIN + 9, true), 2); // k - maxv lands on the null: the writer patches it
        assert_eq!(cm(&[i64::MIN, 0], &[3, 3]).shift_ok(1, false), 0); // a pre-writer null
        assert_eq!(cm(&[i64::MIN, 0], &[i64::MIN, 3]).shift_ok(1, false), 2); // an all-null block goes through the writer
        let (mut base, mut maxv, mut bsum) = ([1i64, 5], [9i64, 9], [10i64, 20]);
        let (mut sn, mut sc) = (i64::MIN, 2048u64);
        let mut m = CocMut { lg: crate::DEFAULT_LG, base: &mut base, maxv: &mut maxv, bsum: &mut bsum,
                             sumnul: Some(&mut sn), sumn: Some(&mut sc), n: 2048, nblk: 2 };
        m.shift(3, false);
        assert_eq!((m.base.to_vec(), m.maxv.to_vec(), m.bsum.to_vec()), (vec![4, 8], vec![12, 12], vec![3082, 3092]));
        m.shift(0, true); // `0 - x` turns the blocks round; the sums are told so
        assert_eq!((m.base.to_vec(), m.bsum.to_vec(), *m.sumnul.as_deref().unwrap()), (vec![-12, -12], vec![-3082, -3092], i64::MIN));
        m.shift(i64::MIN.wrapping_add(-8), true); // block 1's minimum lands on the null: the sums go
        assert_eq!((*m.sumnul.as_deref().unwrap(), *m.sumn.as_deref().unwrap()), (0, 0));
    }
}
