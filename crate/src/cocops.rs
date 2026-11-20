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
    // is /data/tmp/qrs/A1/{gen.c,diff_test.rs}; only the `std` and `one_width` assertions of that test have a live subject
    #[test] fn std_grid_and_one_width_of_a_constant_column() {
        let (z, base, off, width) = ([0i64], [7i64], [0u64], [0u8]);
        let meta = Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &z, off: &off, bsum: &z, width: &width, n: 3, nblk: 1, mblk: 1 };
        let c = Coc { meta, pack: &[], exc: None, fdelta: None };
        assert_eq!((c.std(3), c.std(1025), c.std(0)), (true, false, false));
        assert_eq!(c.one_width(), 0);
    }
}
