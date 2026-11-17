//! sort.rs's symbol, id and guid exports from `qlean_sort_grade_syms` to the end: the grades, order tests, distinct, group
//! and intern over a symbol column (blob and `Array Nat` of starts), over an interned one (dictionary and packed ids), and
//! over guids, plus `symOffs` and `thinSweep`. Each unboxes its arguments, sizes the answer and makes one call into
//! `sort.rs`, which owns the loops. Lean passes `Nat` counts as `size_t` and `Bool` as `uint8_t`.
#![deny(unsafe_code)]
use crate::exports::structural::pair;
use crate::ids::{id_width, ids_avail};
use crate::lean::{B, O, SArr, arr, boxed, export};
use crate::{pod, sort};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::c::pool, crate::exports::sort::longs, crate::ffi::syms_of, crate::ids::ids_bytes, crate::ids};

/// `Order.symsAt`: the symbols' bytes each followed by its NUL, and the starts as an `Array Nat` of tagged scalars (a blob
/// byte count below 2^63, so nothing allocates a bignum). No symbols give no bytes and the one terminating start.
pub fn syms_out(v: &[&[u8]]) -> (O, O) {
    let mut b = SArr::new(1, sort::syms_len(v.iter().copied()));
    let mut o = pod::uninit::<usize>(v.len() + 1);
    sort::syms_at(v.iter().copied(), b.bytes_mut(), &mut o);
    (b.into(), arr(o.iter().map(|&w| boxed(w >> 1))))
}
/// The `distinct` answer: the symbols `v` as a `Column.syms` payload.
pub fn syms_pair(v: &[&[u8]]) -> O { let (b, o) = syms_out(v); pair(b, o) }
/// The ids of `n` rows clamped to what `ids` holds at `w`, and the dictionary's symbol count and id width.
pub fn clamp(n: usize, dof: B, ids: B) -> (usize, usize, u32) {
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




    /// `gradeIds desc n dict dof ids` is `grade i32 desc` over each element's dictionary rank.
    fn qlean_sort_grade_ids(desc: u8, n: usize, dictv: B, dofv: B, idsv: B) -> O {
        let (n, _, w) = clamp(n, dofv, idsv);
        let mut r = SArr::new(1, n * 8);
        if n != 0 { sort::grade_ids(desc != 0, n, &syms_of(dictv, dofv), &idsv.bytes()[..ids_bytes(n, w)], w, longs(&mut r)) }
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


    /// `internSyms blob offs` is `distinctSyms` and, per element, `findSymScalar` against it: the dictionary and the ids of
    /// `Column.enum`.
    fn qlean_sort_intern_syms(blob: B, offs: B) -> O {
        let s = syms_of(blob, offs);
        let n = s.count();
        if n == 0 { let (nb, no) = syms_out(&[]); return pair(nb, pair(no, SArr::new(1, 0).into())) }
        let mut first = pod::uninit::<usize>(n);
        // the width is the answer's, known once `ng` is: the ids go into scratch sized for `id_width(n)` and are copied
        let mut tmp = pod::uninit::<u8>(ids_bytes(n, id_width(n)) + 1);
        let ng = sort::intern_syms(&s, id_width(n), &mut tmp, &mut first);
        let (nb, no) = syms_out(&sort::sym_heads(&s, &first[..ng]));
        let mut idv = SArr::new(1, ids_bytes(n, id_width(ng)));
        idv.bytes_mut().copy_from_slice(&tmp[..ids_bytes(n, id_width(ng))]);
        pair(nb, pair(no, idv.into()))
    }






}
