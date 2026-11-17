//! structural.c's last fourteen Lean exports, from `qlean_structural_til_foR` to the end: `til`, `string`, `mmu`, the
//! transposes, the amends and the scatters. Each unboxes its arguments, sizes the answer and makes one call into
//! `structural.rs`, which owns the loops. Lean passes `Nat` counts as `size_t`, `Bool` as `uint8_t`.
#![deny(unsafe_code)]
use crate::exports::structural::{bytes_of, count_at, pair};
use crate::ffi::{amend, box_array, encode_fill, encode_scatter, syms_of};
use crate::ids::ids_bytes;
use crate::lean::{B, O, SArr, box_, boxed, ctor, export};
use crate::structural::{self, STR_BLK, rows_at};
use crate::{c, pod};
use alloc::vec::Vec;

fn die(args: core::fmt::Arguments) -> ! {
    crate::os::eprint(args).expect("qlean: stderr");
    crate::os::exit(1)
}
/// A `Nat` array of the `n` values `f(i)`, as tagged scalars (a count below 2^63).
fn boxed_array(n: usize, f: impl Fn(usize) -> usize) -> O {
    box_array(n, |o| for (i, x) in o.iter_mut().enumerate() { *x = box_(f(i)) as usize })
}
/// The `Int64`s of an index column, `size / 8` of them.
fn longs<'a, T: pod::Pod>(b: B<'a>) -> &'a [T] {
    let b = b.bytes();
    pod::cast(&b[..b.len() / 8 * 8]).expect("qlean structural: an index column is not 8-aligned")
}
/// An `Array ByteArray` of rows, each at `want` bytes (a short one zero-padded, `Column.bitsAt`'s convention), as the `f64`s
/// the specification reads.
fn f64_rows<'a>(rows: &'a structural::Rows<'_, '_>, k: usize) -> Vec<&'a [f64]> {
    (0..k).map(|i| pod::cast(rows.get(i)).expect("qlean mmu: a padded row is not 8-aligned")).collect()
}

export! {
    /// Spec: `tilFoR n` is `Coc.encode 8 (tilLongs n)`. The ramp is handed to the writer a block at a time, so the dense column is
    /// never built.
    fn qlean_structural_til_foR(n: usize) -> O { encode_fill(n, 8, &structural::til_fill) }

    /// Spec: `stringDigits w n x` is `(blob, offs)` where `offs` is the `n + 1` starts and the bytes between `offs[i]` and
    /// `offs[i+1]` are `atomText` of element `i` -- its decimal spelling, and the empty string where it is that width's null. `w` is
    /// 2, 4 or 8; anything else aborts rather than answering an empty pair and dropping a column's contents silently.
    fn qlean_structural_string_digits(width: u8, n: usize, x: B) -> O {
        let w = width as usize;
        if !matches!(w, 2 | 4 | 8) { die(format_args!("qlean_structural_string_digits: width {width} is not 2, 4 or 8\n")) }
        let n = n.min(x.bytes().len() / w);
        let src = &x.bytes()[..n * w];
        let mut at = alloc::vec![0usize; n.div_ceil(STR_BLK) + 1];
        let total = structural::str_count(c::pool(), w, src, n, &mut at);
        let mut blob = SArr::new(1, total);
        let offs = box_array(n + 1, |o| structural::str_write(c::pool(), w, src, n, &at, blob.bytes_mut(), o));
        pair(blob.into(), offs)
    }

    /// Spec: `mmuF64 a b` is the n * p products of n rows of m against m rows of p, row by row, each a strict left fold over k:
    /// float addition is not associative, so the order is part of the specification. A row is read at the width `b` fixes (`m`
    /// doubles for `a`, `p` for `b`), a short one as zeros.
    fn qlean_structural_mmu(av: B, bv: B) -> O {
        let (a, b) = (av.array(), bv.array());
        let (n, m) = (a.len(), b.len());
        let p = if m != 0 { b[0].bytes().len() / 8 } else { 0 };
        let (ab, bb) = (bytes_of(a), bytes_of(b));
        let (rb, ra) = (rows_at(&bb, p * 8), rows_at(&ab, m * 8));
        // the answer is allocated up to a whole number of blocks so that the last block is a whole block
        let mut res = SArr::with_capacity(1, n * p * 8, n.div_ceil(4) * 4 * p * 8);
        structural::mmu(&f64_rows(&ra, n), &f64_rows(&rb, m), p, pod::cast_mut(res.capacity_mut()).expect("qlean mmu: the answer is not 8-aligned"));
        res.into()
    }

    /// Spec: `transpose w n k cols` is `(blob, offs)` where `offs` is `0, k*w, 2*k*w, ...` -- the `n + 1` boundaries of `n` rows of
    /// `k` elements -- and the bytes of row `i` are element `i` of each of the `k` columns in order, `w` bytes each. Every column
    /// is read at the `n` the caller gives and not at its own length.
    fn qlean_structural_transpose(w: u8, n: usize, cols: B) -> O {
        let (wd, cs) = (w as usize, bytes_of(cols.array()));
        let stride = cs.len() * wd;
        let rows = rows_at(&cs, n * wd);
        let cv: Vec<&[u8]> = (0..cs.len()).map(|j| rows.get(j)).collect();
        let mut blob = SArr::new(1, n * stride);
        structural::transpose(wd, n, &cv, blob.bytes_mut());
        pair(blob.into(), boxed_array(n + 1, |i| i * stride))
    }

    /// Spec: `untranspose w offs b` is `some (blob, cuts)` where `b` holds `n` rows of `k` cells of `w` bytes -- which is what `offs`
    /// says exactly when it is `0, s, 2s, ...` for `s = k * w` -- and `blob` is the `k` columns laid end to end with `cuts` the
    /// `k + 1` boundaries between them. `none` at any other `offs`, which is a ragged slices value and not a matrix.
    fn qlean_structural_untranspose(w: u8, offsv: B, bv: B) -> O {
        let (ofs, wd) = (offsv.array(), w as usize);
        if wd == 0 || ofs.len() < 2 { return boxed(0) }
        let n = ofs.len() - 1;
        let Some(k) = structural::uniform_stride(wd, n, bv.bytes().len(), |i| count_at(ofs, i)) else { return boxed(0) };
        let mut blob = SArr::new(1, n * k * wd);
        structural::untranspose(wd, n, k, bv.bytes(), blob.bytes_mut());
        ctor(1, [pair(blob.into(), boxed_array(k + 1, |j| j * n * wd))], &[])
    }

    /// Spec: the answer `transpose` would give for the two columns `l[k / m]` and `r[k % m]`, without building either: every row is
    /// one element of `l` beside one of `r`.
    fn qlean_structural_cross(w: u8, n: usize, m: usize, l: B, r: B) -> O {
        let (wd, rows) = (w as usize, n * m);
        let stride = 2 * wd;
        let mut blob = SArr::new(1, rows * stride);
        structural::cross(wd, n, m, l.bytes(), r.bytes(), blob.bytes_mut());
        pair(blob.into(), boxed_array(rows + 1, |i| i * stride))
    }

    /// Spec: `amendRounds n wi ranked idx`. Word 0 is the round count, or all ones when an index misses `[0, n)` -- q's `'length`,
    /// `0N` and negatives included -- with that index in word 1. Ranked and repeated, the round ends and the positions grouped by
    /// round follow; an index narrower than a long follows widened.
    fn qlean_structural_amend_rounds(n: usize, wi: usize, ranked: u8, idxv: B) -> O {
        amend_of(n, wi, ranked, false, idxv).0
    }

    /// Spec: `amendIndex n wi ranked idx` -- `amendRounds` and, when no index misses, `amendCompact` of the indices widened, both
    /// empty when one does.
    fn qlean_structural_amend_index(n: usize, wi: usize, ranked: u8, idxv: B) -> O {
        let (res, dom, rank) = amend_of(n, wi, ranked, true, idxv);
        let empty = || SArr::new(1, 0).into();
        pair(res, pair(dom.unwrap_or_else(empty), rank.unwrap_or_else(empty)))
    }

    /// Spec: `scatterPacked wb dst idx src soff bcast` -- for each long `idx[k]` in order, the field at it in `dst` becomes field
    /// `soff + k` of `src`, or field `soff` for every `k` under `bcast`; fields are `wb` bits, packed low field first below a byte.
    /// In order, so the last write to a repeated index is the one that stays, which is q's `:`. An index past `dst` writes nothing;
    /// `amendRounds` raised it.
    fn qlean_structural_scatter(wb: usize, dst: O, idxv: B, srcv: B, soff: usize, bcast: u8) -> O {
        scatter(wb, dst, idxv, srcv, soff, bcast)
    }

    /// Spec: `scatterIds wa wb n ids idx yids bcast` is `scatterPacked wb` of the `n` ids widened from `wa` bits to `wb` -- an id
    /// past the payload reading `0`, `Column.idAt`'s convention -- and the ids themselves where the widths agree, which `scatter`
    /// writes in place when nothing else holds them.
    fn qlean_structural_scatter_ids(wa: usize, wb: usize, n: usize, ids: O, idxv: B, yv: B, bcast: u8) -> O {
        let ids = if wa == wb { ids } else {
            let mut o = SArr::new(1, ids_bytes(n, wb as u32));
            structural::widen_ids(n, wa as u32, wb as u32, ids.borrow().bytes(), o.bytes_mut());
            drop(ids); // as the C `lean_dec`: the wider copy is the only one the scatter holds
            o.into()
        };
        scatter(wb, ids, idxv, yv, 0, bcast)
    }

    /// Spec: `scatterSyms b o idx yb yo bcast` -- element `idx[k]` of the blob replaced, in order, by symbol `k` of `y` (`0` under
    /// `bcast`), the last write to a repeated index kept. Symbols have no fixed width, so the blob is rebuilt rather than written
    /// in place.
    fn qlean_structural_scatter_syms(bv: B, ov: B, idxv: B, ybv: B, yov: B, bcast: u8) -> O {
        let (b, y) = (syms_of(bv, ov), syms_of(ybv, yov));
        let src = structural::scatter_sources(b.count(), y.count(), longs::<u64>(idxv), bcast != 0);
        let mut blob = SArr::new(1, structural::scatter_syms_total(&src, &b, &y));
        let offs = box_array(src.len() + 1, |o| structural::scatter_syms_write(&src, &b, &y, blob.bytes_mut(), o));
        pair(blob.into(), offs)
    }

    /// Spec: `amendCompact n idx` -- `(u, rk)`: `u` the distinct longs of `idx` ascending, `rk[k]` the position of `idx[k]` in `u`.
    /// Every index is below `n`; `amendRounds` raised one that is not. An amend's rounds run over `x@u`, so the column takes one
    /// sorted scatter at the end rather than being decoded whole for a few writes.
    fn qlean_structural_amend_compact(n: usize, idxv: B) -> O {
        let ix = longs::<u64>(idxv);
        let cp = structural::Compact::new(n, ix)
            .unwrap_or_else(|k| die(format_args!("qlean amend: index {} of a column of {n} reached the compaction\n", ix[k])));
        let (mut u, mut rk) = (SArr::new(1, cp.count * 8), SArr::new(1, ix.len() * 8));
        cp.fill(ix, pod::cast_mut(u.bytes_mut()).expect("qlean amend: u is not 8-aligned"), pod::cast_mut(rk.bytes_mut()).expect("qlean amend: rk is not 8-aligned"));
        pair(u.into(), rk.into())
    }

    /// Spec: `scatterFoR w meta pack n ix vals` -- `Coc.encode w (scatterPacked (8 * w) (Coc.decode w meta pack n) ix vals 0 false)`,
    /// `ix` ascending, distinct and below `n` (`amendCompact`'s `u`), re-encoding only the blocks an index lands in.
    fn qlean_structural_scatter_for(w: usize, meta: B, pack: B, n: usize, idxv: B, valv: B) -> O {
        encode_scatter(w, meta.bytes(), pack.bytes(), None, n, idxv.bytes(), valv.bytes())
    }

    /// Spec: `scatterALP`, `scatterFoR` through ALP's encode and decode; the exponents `alpv` are the ALP part of the column.
    fn qlean_structural_scatter_alp(w: usize, meta: B, pack: B, alpv: B, n: usize, idxv: B, valv: B) -> O {
        encode_scatter(w, meta.bytes(), pack.bytes(), Some(alpv.bytes()), n, idxv.bytes(), valv.bytes())
    }
}

/// `amend`'s arrays for an index column, its width checked: 1, 2, 4 and 8 are read.
fn amend_of(n: usize, wi: usize, ranked: u8, compact: bool, idxv: B) -> (O, Option<O>, Option<O>) {
    if !matches!(wi, 1 | 2 | 4 | 8) { die(format_args!("qlean amend: index width {wi}; 1, 2, 4 and 8 are read\n")) }
    amend(n, wi, ranked != 0, compact, idxv.bytes())
}
/// `scatterPacked` in the answer `dst` itself where this reference holds it alone, a copy otherwise.
fn scatter(wb: usize, dst: O, idxv: B, srcv: B, soff: usize, bcast: u8) -> O {
    if wb == 0 { return dst }
    let mut dst = dst.into_exclusive();
    structural::scatter_packed(wb, dst.bytes_mut(), longs::<i64>(idxv), srcv.bytes(), soff, bcast != 0);
    dst.into()
}
