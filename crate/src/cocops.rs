#![forbid(unsafe_code)]
//! Column (a), coc.rs: the whole-column reads of a `Coc` (A1), its sums (A3), product, any/all, min and max (A4)
//! and the in-place shift (A6), plus `CocMut`, the writable form of the same `coc`.
use alloc::{vec, vec::Vec};
use crate::coc::{Coc, Meta};
use crate::res::res_get_in;
use crate::simd::prefetch;

/// coc.rs, the comparison codes in QLean.Kernel.Ew's constructor order
pub const EQ: i32 = 0;
pub const NE: i32 = 1;
pub const LT: i32 = 2;
pub const LE: i32 = 3;
pub const GT: i32 = 4;
pub const GE: i32 = 5;



// ---- A1: coc.rs, 2043-2165 ----

/// `coc_meta_view` (coc.rs) and `coc_attach` (coc.rs) are `Meta::new` and `Coc::attach`; `coc_blocks`
/// (coc.rs) is `Coc::blocks`; `coc_res_end`, `coc_grid`, `coc_std` are `Meta::res_end`, `Meta::grid`, `Coc::std`.
impl<'a> Coc<'a> {
    /// coc.rs `coc_get`: element `i`, its patch applied. Per element: C keeps its body while a C caller remains.
    pub fn get(&self, i: usize) -> i64 {
        let (b, j) = (i >> self.meta.lg, i & (self.meta.blk() - 1));
        if let Some(x) = self.patch(b, j) { return self.exc(x) }
        self.frame(b).wrapping_add(self.res(b, j)) as i64
    }
    /// The patch of row `j` of block `b`, if any: the first at `j`, Lean `foRExc`'s `find?`; in ascending positions it
    /// is the only one.
    fn patch(&self, b: usize, j: usize) -> Option<usize> {
        let e = self.exc.filter(|e| !e.pos.is_empty())?;
        let r = e.off[b] as usize..e.off[b + 1] as usize;
        if e.asc { e.pos[r.clone()].binary_search(&(j as u16)).ok().map(|k| r.start + k) } else { r.clone().find(|&x| e.pos[x] as usize == j) }
    }
    /// The residual of row `j` of block `b`, Lean `resAt`.
    fn res(&self, b: usize, j: usize) -> u64 {
        let p = self.pack.get(self.meta.off[b] as usize..).unwrap_or(&[]);
        res_get_in(p, self.meta.w(b), j, p.len())
    }
    /// Lean `foRNul`: row `i` is the null of a nullable column, tested on the encoding and never decoded: its block
    /// flagged (`Meta::nul`), no patch holding it, its residual the block's top one `2^w - 1`.
    pub fn is_nul(&self, i: usize) -> bool {
        let (b, j) = (i >> self.meta.lg, i & (self.meta.blk() - 1));
        let w = self.meta.w(b);
        self.meta.nul(b) && self.patch(b, j).is_none() && self.res(b, j) == if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
    }
    /// The null bitmap of rows `0 .. n`, bit `i` (LSB first) row `i`, the form `Sink::write_nul` takes; `None` where no
    /// block is flagged (Lean `hasNul`). Only flagged blocks are read, one width byte each for the rest.
    pub fn nuls(&self) -> Option<Vec<u8>> {
        let (lg, n) = (self.meta.lg, self.meta.n);
        let fl = |b: &usize| self.meta.nul(*b);
        if !(0..self.meta.mblk).any(|b| fl(&b)) { return None }
        let mut o = vec![0u8; n.div_ceil(8)];
        for b in (0..self.meta.mblk).filter(fl) {
            for i in (b << lg..((b + 1) << lg).min(n)).filter(|&i| self.is_nul(i)) { o[i >> 3] |= 1 << (i & 7) }
        }
        Some(o)
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
        if let Some(r) = self.pack.get(self.meta.off[b] as usize + (i & (self.meta.blk() - 1)) * self.meta.w(b) as usize / 8) { prefetch(r) }
    }
    /// coc.rs `coc_one_width`: the width every block shares, as C answers when they differ.
    pub fn one_width(&self) -> u8 {
        if self.exc.is_some_and(|e| !e.pos.is_empty()) { return 255 } // a flat read would miss the patch list
        let mut w = (0..self.meta.nblk).map(|b| self.meta.w(b));
        match w.next() { None => 0, Some(w0) if w.all(|x| x == w0) => w0, _ => 255 }
    }
}
impl<'a> Meta<'a> {
    /// coc.rs `coc_offsets` over the metadata alone: `off[b]` from the widths; answers the residuals' end.
    pub fn offsets(lg: u32, width: &[u8], nblk: usize, off: &mut [u64]) -> u64 {
        let mut at = 0u64;
        for (o, &w) in off[..nblk].iter_mut().zip(&width[..nblk]) { *o = at; at += ((1u64 << lg) * (w & crate::coc::WIDTH_MASK) as u64) / 8 }
        at
    }
}

// ---- A3: coc.rs (the residual sums are res.rs) ----
impl<'a> Coc<'a> {
}

// ---- A4: coc.rs ----
impl<'a> Coc<'a> {
}

// ---- A6: coc.rs ----
impl<'a> Coc<'a> {
}

// ---- K24b: coc.rs `vv_fill` and `scale_fill`, the producers of `x op y` and `x * k` ----

#[cfg(test)]
mod tests {
    use super::*;
    // expected values: /data/tmp/qrs/A1/ex.c (coc.rs's own functions at 152d98f), run; the 24600-case C differential
    // is /data/tmp/qrs/A1/{gen.c,diff_test.rs}; only the `std` and `one_width` assertions of that test have a live subject
    #[test] fn std_grid_and_one_width_of_a_constant_column() {
        let (z, base, off, width) = ([0i64], [7i64], [0u64], [0u8]);
        let meta = Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &z, off: &off, bsum: &z, width: &width, n: 3, nblk: 1, mblk: 1 };
        let c = Coc { meta, pack: &[], exc: None, fdelta: None };
        assert_eq!((c.std(3), c.std(1025), c.std(0)), (true, false, false));
        assert_eq!(c.one_width(), 0);
    }
    // the architecture note's example: a 6-bit block, base 100, flagged; residual 63 (`111111`) is the null, the
    // other residuals read as values, and the flag leaves the width, the offsets and `get` of a value unchanged
    #[test] fn in_band_null_is_the_flagged_top_residual() {
        let (z, base, off, width) = ([0i64], [100i64], [0u64], [6u8 | crate::coc::NUL_FLAG]);
        let mut pack = [0u8; (1 << crate::DEFAULT_LG) * 6 / 8];
        (pack[0], pack[1]) = (63 | 1 << 6, 1); // residuals 63, 5 (bits 6..12), 0
        let meta = Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &z, off: &off, bsum: &z, width: &width, n: 3, nblk: 1, mblk: 1 };
        let c = Coc { meta, pack: &pack, exc: None, fdelta: None };
        assert_eq!((c.meta.w(0), c.meta.nul(0), c.meta.res_end(), c.one_width()), (6, true, pack.len(), 6));
        let top = |i| res_get_in(&pack, c.meta.w(0), i, pack.len()) == (1 << c.meta.w(0)) - 1;
        assert_eq!((top(0), top(1), top(2), c.get(1)), (true, false, false, 105));
        let plain = Coc { meta: Meta { width: &[6u8], ..meta }, ..c };
        assert_eq!((plain.meta.nul(0), plain.get(0)), (false, 163));
    }
    // the writer (`Sink::write_nul`) over three blocks — mixed, all null, no null — read back through `coc::view`: a
    // flagged block's null rows hold its top residual, every other row `get`s its value, and an unflagged block is plain
    #[test] fn encode_nul_puts_nulls_in_band() {
        let bk = 1usize << crate::DEFAULT_LG;
        let n = 2 * bk + 5;
        let val = |i: usize| (i % 7) as i64 * 3 - 4;
        let nulr = |i: usize| i < bk && i % 5 == 1 || (bk..2 * bk).contains(&i);
        let x: alloc::vec::Vec<i64> = (0..n).map(val).collect();
        let mut nul = alloc::vec![0u8; n.div_ceil(8)];
        for i in (0..n).filter(|&i| nulr(i)) { nul[i >> 3] |= 1 << (i & 7) }
        let o = crate::ffi::Sink::new(n, 8).write_nul(&crate::blocks::Blocks::dense(crate::pod::bytes(&x), 8), false, &nul)
            .expect("encode_nul: a write with no size test has an answer");
        let [m, p] = [0, 1].map(|i| o.borrow().field(i).bytes().to_vec());
        let c = crate::coc::view(&m, &p, n).unwrap_or_else(|e| panic!("encode_nul: {e}"));
        assert_eq!((c.meta.nul(0), c.meta.nul(1), c.meta.nul(2)), (true, true, false));
        assert_eq!((c.meta.w(0), c.meta.w(1), c.meta.w(2)), (5, 0, 5));
        for i in (0..n).filter(|&i| !nulr(i)) { assert_eq!(c.get(i), val(i), "row {i}") }
        let w = c.meta.w(0);
        for i in (0..bk).filter(|&i| nulr(i)) { assert_eq!(res_get_in(&p, w, i, p.len()), (1 << w) - 1, "row {i}") }
    }
}
