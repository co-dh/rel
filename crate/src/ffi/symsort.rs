//! sort.rs's symbol, id and guid exports from `qlean_sort_grade_syms` to the end: the grades, order tests, distinct, group
//! and intern over a symbol column (blob and `Array Nat` of starts), over an interned one (dictionary and packed ids), and
//! over guids, plus `symOffs` and `thinSweep`. Each unboxes its arguments, sizes the answer and makes one call into
//! `sort.rs`, which owns the loops. Lean passes `Nat` counts as `size_t` and `Bool` as `uint8_t`.
#![deny(unsafe_code)]
use crate::c::pool;
use crate::exports::sort::longs;
use crate::exports::structural::pair;
use crate::ffi::syms_of;
use crate::ids::{id_width, ids_avail, ids_bytes};
use crate::lean::{B, O, SArr, arr, boxed, export, nat};
use crate::{ids, pod, sort};

/// `Order.symsAt`: the symbols' bytes each followed by its NUL, and the starts as an `Array Nat` of tagged scalars (a blob
/// byte count below 2^63, so nothing allocates a bignum). No symbols give no bytes and the one terminating start.
fn syms_out(v: &[&[u8]]) -> (O, O) {
    let mut b = SArr::new(1, sort::syms_len(v.iter().copied()));
    let mut o = pod::uninit::<usize>(v.len() + 1);
    sort::syms_at(v.iter().copied(), b.bytes_mut(), &mut o);
    (b.into(), arr(o.iter().map(|&w| boxed(w >> 1))))
}
/// The `distinct` answer: the symbols `v` as a `Column.syms` payload.
fn syms_pair(v: &[&[u8]]) -> O { let (b, o) = syms_out(v); pair(b, o) }
/// The bucket payload and its `ng + 1` byte offsets (`QValue.slices`), from each element's group and how many name each.
fn buckets(gid: &[u32], ng: usize, cnt: &[u32]) -> (O, O) {
    let mut ord = SArr::new(1, gid.len() * 8);
    let mut bnd = pod::uninit::<usize>(ng + 1);
    crate::group::buckets(gid, &cnt[..ng], longs(&mut ord), &mut bnd);
    (ord.into(), arr(bnd.iter().map(|&w| boxed(w >> 1))))
}
/// `(syms, (offsets, (ord, bounds)))`, the `groupSyms` answer: the symbols `v` and the buckets of `gid`.
fn group_answer(v: &[&[u8]], gid: &[u32], ng: usize, cnt: &[u32]) -> O {
    let (nb, no) = syms_out(v);
    let (ord, bnd) = buckets(gid, ng, cnt);
    pair(nb, pair(no, pair(ord, bnd)))
}
/// The ids of `n` rows clamped to what `ids` holds at `w`, and the dictionary's symbol count and id width.
fn clamp(n: usize, dof: B, ids: B) -> (usize, usize, u32) {
    let nd = dof.array().len().saturating_sub(1);
    let w = id_width(nd);
    (n.min(ids_avail(ids.bytes().len(), w)), nd, w)
}

export! {
    /// `gradeSyms desc blob offs` is `0 .. n-1` ordered by `symCmp` on the symbols' bytes, ties in their original order,
    /// as little-endian `Int64`s.
    fn qlean_sort_grade_syms(desc: u8, blob: B, offs: B) -> O {
        let s = syms_of(blob, offs);
        let mut r = SArr::new(1, s.count() * 8);
        sort::grade_syms(desc != 0, &s, longs(&mut r));
        r.into()
    }

    /// `ascendingSyms desc blob offs`: the adjacent `symCmp` comparison over the column's own symbols.
    fn qlean_sort_ascending_syms(desc: u8, strict: u8, blobv: B, offsv: B) -> u8 {
        let s = syms_of(blobv, offsv);
        sort::ascending_syms(desc != 0, strict != 0, &s, s.count()) as u8
    }

    /// `ascendingIds desc dict dof ids`: the same comparison over the dictionary entry each id names; an id past the
    /// dictionary reads the empty symbol.
    fn qlean_sort_ascending_ids(desc: u8, strict: u8, n: usize, dictv: B, dofv: B, idsv: B) -> u8 {
        let (n, _, w) = clamp(n, dofv, idsv);
        sort::ascending_ids(desc != 0, strict != 0, &syms_of(dictv, dofv), &idsv.bytes()[..ids_bytes(n, w)], w, n) as u8
    }

    /// `partedSyms strict blob offs`: the distinct symbol count against the run count, or the element count when `strict`.
    fn qlean_sort_parted_syms(strict: u8, blobv: B, offsv: B) -> u8 { sort::parted_syms(strict != 0, &syms_of(blobv, offsv)) as u8 }

    /// `gradeIds desc n dict dof ids` is `grade i32 desc` over each element's dictionary rank.
    fn qlean_sort_grade_ids(desc: u8, n: usize, dictv: B, dofv: B, idsv: B) -> O {
        let (n, _, w) = clamp(n, dofv, idsv);
        let mut r = SArr::new(1, n * 8);
        if n != 0 { sort::grade_ids(desc != 0, n, &syms_of(dictv, dofv), &idsv.bytes()[..ids_bytes(n, w)], w, longs(&mut r)) }
        r.into()
    }

    /// `sortedIds desc n dict dof ids` is `gradeIds`' permutation gathered out of `ids`, as ids of the column's own width.
    fn qlean_sort_sorted_ids(desc: u8, n: usize, dictv: B, dofv: B, idsv: B) -> O {
        let (n, _, w) = clamp(n, dofv, idsv);
        let mut r = SArr::new(1, ids_bytes(n, w));
        r.bytes_mut().fill(0);
        if n != 0 { sort::sorted_ids(desc != 0, n, &syms_of(dictv, dofv), &idsv.bytes()[..ids_bytes(n, w)], w, r.bytes_mut()) }
        r.into()
    }

    /// `distinctSyms blob offs` is `symsAt blob offs (symFirsts blob offs)`: the first occurrence of each distinct symbol, in
    /// the order they occur.
    fn qlean_sort_distinct_syms(blob: B, offs: B) -> O {
        let s = syms_of(blob, offs);
        let n = s.count();
        if n == 0 { return syms_pair(&[]) }
        let mut first = pod::uninit::<usize>(n);
        let ng = sort::distinct_syms(&s, &mut first);
        syms_pair(&sort::sym_heads(&s, &first[..ng]))
    }

    /// `distinctIds n dict dof ids` is `symsAt` at the ids that occur first, in that order.
    fn qlean_sort_distinct_ids(n: usize, dictv: B, dofv: B, idsv: B) -> O {
        let (n, nd, w) = clamp(n, dofv, idsv);
        if n == 0 { return syms_pair(&[]) }
        let p = &idsv.bytes()[..ids_bytes(n, w)];
        let (mut slot, mut first) = (alloc::vec![usize::MAX; nd + 1], pod::uninit::<usize>(n.min(nd + 1)));
        let ng = ids::firsts(p, n, w, nd, &mut slot, &mut first);
        syms_pair(&sort::ids_heads(&syms_of(dictv, dofv), p, w, &first[..ng]))
    }

    /// `groupIdsSyms n dict dof ids` is `distinctIds`' two vectors, then the indices concatenated bucket by bucket, then the
    /// `ng + 1` byte offsets that cut them.
    fn qlean_sort_group_ids_syms(n: usize, dictv: B, dofv: B, idsv: B) -> O {
        let (n, nd, w) = clamp(n, dofv, idsv);
        if n == 0 { return group_answer(&[], &[], 0, &[]) }
        sort::group_bound(n); // before the allocations; the limit is named
        let p = &idsv.bytes()[..ids_bytes(n, w)];
        let (mut gid, mut cnt) = (pod::uninit::<u32>(n), pod::uninit::<u32>(nd + 1));
        let first = sort::ids_group(p, n, w, nd, Some(pod::bytes_mut(&mut gid)), &mut cnt);
        group_answer(&sort::ids_heads(&syms_of(dictv, dofv), p, w, &first), &gid, first.len(), &cnt)
    }

    /// `idGroups d n w ids` is `(the group each row falls in, Order.idFirsts d n w ids)`.
    fn qlean_sort_id_groups(d: usize, n: usize, w: usize, idsv: B) -> O {
        let w = w as u32;
        let n = n.min(ids_avail(idsv.bytes().len(), w));
        if n == 0 { return pair(SArr::new(1, 0).into(), SArr::new(1, 0).into()) }
        let p = &idsv.bytes()[..ids_bytes(n, w)];
        let (mut slot, mut first) = (alloc::vec![usize::MAX; d + 1], pod::uninit::<usize>(n.min(d + 1)));
        let ng = ids::firsts(p, n, w, d, &mut slot, &mut first);
        let wo = id_width(ng);
        let mut gid = SArr::new(1, ids_bytes(n, wo));
        gid.bytes_mut().fill(0);
        ids::map(pool(), p, n, w, d, &slot, wo, gid.bytes_mut());
        let mut f = SArr::new(1, ng * 8);
        f.bytes_mut().copy_from_slice(pod::bytes(&first[..ng]));
        pair(gid.into(), f.into())
    }

    /// `partedIds strict d n w ids` is the distinct count against the run count, or the element count when `strict`.
    fn qlean_sort_parted_ids(strict: u8, d: usize, n: usize, w: usize, idsv: B) -> u8 {
        let w = w as u32;
        let n = n.min(ids_avail(idsv.bytes().len(), w));
        sort::parted_ids(strict != 0, d, n, w, &idsv.bytes()[..ids_bytes(n, w)]) as u8
    }

    /// `internSyms blob offs` is `distinctSyms` and, per element, `findSymScalar` against it: the dictionary and the ids of
    /// `Column.enum`.
    fn qlean_sort_intern_syms(blob: B, offs: B) -> O {
        let s = syms_of(blob, offs);
        let n = s.count();
        if n == 0 { let (nb, no) = syms_out(&[]); return pair(nb, pair(no, SArr::new(1, 0).into())) }
        sort::group_bound(n); // before the allocations; the limit is named
        let mut first = pod::uninit::<usize>(n);
        // the width is the answer's, known once `ng` is: the ids go into scratch sized for `id_width(n)` and are copied
        let mut tmp = pod::uninit::<u8>(ids_bytes(n, id_width(n)) + 1);
        let ng = sort::intern_syms(&s, id_width(n), &mut tmp, &mut first);
        let (nb, no) = syms_out(&sort::sym_heads(&s, &first[..ng]));
        let mut idv = SArr::new(1, ids_bytes(n, id_width(ng)));
        idv.bytes_mut().copy_from_slice(&tmp[..ids_bytes(n, id_width(ng))]);
        pair(nb, pair(no, idv.into()))
    }

    /// `groupSyms blob offs` is `(distinctSyms's blob, its offsets, the indices concatenated bucket by bucket, the ng + 1
    /// byte offsets that cut them)`.
    fn qlean_sort_group_syms(blob: B, offs: B) -> O {
        let s = syms_of(blob, offs);
        let n = s.count();
        if n == 0 { return group_answer(&[], &[], 0, &[]) }
        sort::group_bound(n); // before the allocations; the limit is named
        let g = sort::sym_group(&s, n, 2);
        group_answer(&sort::sym_heads(&s, &g.first), &g.gid, g.ng, &g.cnt)
    }

    /// `gradeGuid desc b` is `0 .. n-1`, `n = b.size / 16`, ordered by each element's sixteen bytes compared unsigned in
    /// address order, ties in their original order, as little-endian `Int64`s.
    fn qlean_sort_grade_guid(desc: u8, b: B) -> O {
        let n = b.bytes().len() / 16;
        let mut r = SArr::new(1, n * 8);
        sort::grade_guid(desc != 0, &b.bytes()[..16 * n], longs(&mut r));
        r.into()
    }

    /// `ascendingGuid desc strict b` is the adjacent comparison of `gradeGuid`'s order over every pair.
    fn qlean_sort_ascending_guid(desc: u8, strict: u8, b: B) -> u8 {
        let n = b.bytes().len() / 16;
        sort::ascending_guid(desc != 0, strict != 0, &b.bytes()[..16 * n], n) as u8
    }

    /// `partedGuid strict b` is whether every two equal elements stand in one run of equals, and when `strict` whether no
    /// two are equal at all.
    fn qlean_sort_parted_guid(strict: u8, b: B) -> u8 {
        let n = b.bytes().len() / 16;
        sort::parted_guid(strict != 0, &b.bytes()[..16 * n], n) as u8
    }

    /// `Kernel.Order.symOffs`: the `offs` of the first `n` NUL-terminated strings from byte `start`, and whether every
    /// byte scanned is ASCII.
    fn qlean_sort_sym_offs(b: B, start: usize, n: usize) -> O {
        let (ends, ascii) = sort::sym_offs(b.bytes(), start, n);
        let offs = arr(core::iter::once(boxed(0)).chain(ends.into_iter().map(nat)).collect::<alloc::vec::Vec<O>>().into_iter());
        pair(offs, boxed(ascii as usize))
    }

    /// `Kernel.thinSweep cs big o`: the sweep is `sort::thin_sweep`.
    fn qlean_sort_thin_sweep(csv: B, bigv: B, o: B) -> O {
        let cols: alloc::vec::Vec<&[u8]> = csv.array().iter().map(|c| c.bytes()).collect();
        let big: alloc::vec::Vec<bool> = bigv.array().iter().map(|b| b.unbox() != 0).collect();
        let n = cols.first().map_or(0, |c| c.len() / 8);
        let mut r = SArr::new(1, n.div_ceil(8));
        sort::thin_sweep(&cols, &big, o.bytes(), n, r.bytes_mut());
        r.into()
    }
}
