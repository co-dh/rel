#![forbid(unsafe_code)]
//! Column (a), coc.rs: the whole-column reads of a `Coc` (A1), its sums (A3), product, any/all, min and max (A4)
//! and the in-place shift (A6), plus `CocMut`, the writable form of the same `coc`.
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
        if let Some(e) = self.exc.filter(|e| !e.pos.is_empty()) {
            let r = e.off[b] as usize..e.off[b + 1] as usize;
            // the first patch at `j`, Lean `foRExc`'s `find?`: in ascending positions it is the only one
            let x = if e.asc { e.pos[r.clone()].binary_search(&(j as u16)).ok().map(|k| r.start + k) } else { r.clone().find(|&x| e.pos[x] as usize == j) };
            if let Some(x) = x { return self.exc(x) }
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
}
impl<'a> Meta<'a> {
    /// coc.rs `coc_offsets` over the metadata alone: `off[b]` from the widths; answers the residuals' end.
    pub fn offsets(lg: u32, width: &[u8], nblk: usize, off: &mut [u64]) -> u64 {
        let mut at = 0u64;
        for (o, &w) in off[..nblk].iter_mut().zip(&width[..nblk]) { *o = at; at += ((1u64 << lg) * w as u64) / 8 }
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
