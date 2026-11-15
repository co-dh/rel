#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), coc.h: the whole-column reads of a `Coc` (A1), its sums (A3), product, any/all, min and max (A4)
//! and the in-place shift (A6), plus `CocMut`, the writable form of the same `coc`.
use crate::coc::{Coc, Meta};

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
    pub fn get(&self, i: usize) -> i64 { unimplemented!("A1: coc_get") }
    /// coc.h:2078 `coc_get_w`: `get` for a column whose every block has residual width `uw` (`one_width`).
    pub fn get_w(&self, uw: u8, i: usize) -> i64 { unimplemented!("A1: coc_get_w") }
    /// coc.h:2052 `coc_prefetch`: element `i`'s residual into cache.
    pub fn prefetch(&self, i: usize) { unimplemented!("A1: coc_prefetch") }
    /// coc.h:2062 `coc_one_width`: the width every block shares, as C answers when they differ.
    pub fn one_width(&self) -> u8 { unimplemented!("A1: coc_one_width") }
    /// coc.h:2165 `coc_load_run`: elements `from .. from + out.len()` into `out`; positions outside `0..n` are `fill`.
    pub fn load_run(&self, from: i64, fill: i64, out: &mut [i64]) { unimplemented!("A1: coc_load_run") }
}
impl<'a> Meta<'a> {
    /// coc.h:176 `coc_offsets` over the metadata alone: `off[b]` from the widths; answers the residuals' end.
    pub fn offsets(width: &[u8], nblk: usize, off: &mut [u64]) -> u64 { unimplemented!("A1: coc_offsets") }
}
/// coc.h:303 `width_exc`: from the histogram `h` of the block's residual bit lengths, the width that minimises
/// residual plus patch bytes, and the patch count at it.
pub fn width_exc(h: &[u32], nnul: usize, esz: usize, nb: usize) -> (u8, u32) { unimplemented!("A1: width_exc") }
/// coc.h:2102 `res_cmp2`: `nb` decoded pairs compared by `op` into the bit mask `out`.
pub fn res_cmp2(x: &[i64], y: &[i64], op: i32, out: &mut [u64]) { unimplemented!("A1: res_cmp2") }
/// coc.h:2129 `coc_cmp2_res`: blocks `lo .. hi` of `a op b` into `out`; `deep` lists the blocks whose frames do not
/// decide the answer.
pub fn cmp2_res(a: &Coc, b: &Coc, op: i32, out: &mut [u64], deep: &[u32], lo: usize, hi: usize) {
    unimplemented!("A1: coc_cmp2_res")
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
