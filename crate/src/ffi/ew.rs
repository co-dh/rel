//! elementwise.c's first eleven Lean exports: the value verbs (dense and over encoded columns), the comparisons and the
//! bitwise verbs on longs, the symbol ranking, and the three comparisons over interned ids. Each unboxes its arguments,
//! allocates the answer and makes one call into `ew.rs`, which owns the loops and the split over the pool (`c::pool()`).
//! Lean passes `Int64` as C's `uint64_t`.
#![deny(unsafe_code)]
use crate::exports::coc::view;
use crate::exports::reduce::elems;
use alloc::vec::Vec;
use crate::lean::{B, O, SArr, ctor, export};
use crate::sym::Syms;
use crate::{c, ew};

/// An answer of `n` bytes, undefined until the kernel writes it.
fn answer(n: usize) -> SArr { SArr::new(1, n) }
/// The bitmap of `n` elements, one bit each.
fn bits(n: usize) -> SArr { answer(n.div_ceil(8)) }
/// The starts of a symbol column as `Syms` holds them, boxed words; a bignum becomes an even word, which `Syms::off`
/// refuses when it is read, as `sym.h`'s `off_at` did.
fn boxed_offs(offs: B) -> Vec<usize> { offs.array().iter().map(|o| if o.is_scalar() { o.unbox() << 1 | 1 } else { 0 }).collect() }

export! {
    /// `val op cls shape nul a b n`: `a op b` at class `cls`, `shape` naming which side is an atom (read at 0).
    fn qlean_ew_val(op: u8, cls: u8, shape: u8, nul: u64, a: B, b: B, n: usize) -> O {
        let mut r = answer(n * ew::ew_width(cls as u32));
        ew::val(c::pool(), op, cls, shape, nul as i64, a.bytes(), b.bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `foRValAtom op cls shape nul m p n atom`: `val` over the decoded column and `atom` (`ew_width(cls)` bytes).
    fn qlean_coc_ew_val_atom(op: u8, cls: u8, shape: u8, nul: u64, mv: B, pv: B, n: usize, av: B) -> O {
        let w = ew::ew_width(cls as u32);
        let col = view("qlean_coc_ew_val_atom", mv, pv, n);
        let mut r = answer(n * w);
        ew::val_enc_atom(c::pool(), op, cls, shape, nul as i64, &col, &av.bytes()[..w], r.bytes_mut());
        r.into()
    }

    /// `foRVal op cls nul ma pa mb pb n`: `val` over the two decoded columns.
    fn qlean_coc_ew_val(op: u8, cls: u8, nul: u64, ma: B, pa: B, mb: B, pb: B, n: usize) -> O {
        let (ca, cb) = (view("qlean_coc_ew_val", ma, pa, n), view("qlean_coc_ew_val", mb, pb, n));
        let mut r = answer(n * ew::ew_width(cls as u32));
        ew::val_enc(c::pool(), op, cls, nul as i64, &ca, &cb, r.bytes_mut());
        r.into()
    }

    /// `cmp op cls shape a b n`: the `Column.bits` payload of the comparison, the bits above `n` zero.
    fn qlean_ew_cmp(op: u8, cls: u8, shape: u8, a: B, b: B, n: usize) -> O {
        let mut r = bits(n);
        ew::cmp(c::pool(), op, cls, shape, a.bytes(), b.bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `lowZero a b n`: bit `i` is `(a[i] & b[0]) = 0` over `n` longs.
    fn qlean_ew_low_zero(a: B, b: B, n: usize) -> O {
        let mut r = bits(n);
        ew::low_zero(c::pool(), a.bytes(), b.bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `foRLowZero m p n atom`: `lowZero` over the decoded column of `n` longs.
    fn qlean_coc_low_zero(mv: B, pv: B, n: usize, av: B) -> O {
        let col = view("qlean_coc_low_zero", mv, pv, n);
        let mut r = bits(n);
        ew::low_zero_enc(c::pool(), &col, av.bytes(), r.bytes_mut());
        r.into()
    }

    /// `bitw op a b n`: `&`, `|` or `& ~` of two long columns (any other `op` reads as `&`).
    fn qlean_ew_bitw(op: u8, a: B, b: B, n: usize) -> O {
        let mut r = answer(n * 8);
        ew::bitw(c::pool(), op, a.bytes(), b.bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `rankPair da doa db dob`: each dictionary's entries ranked among the distinct symbols of both, as `Int32`s.
    fn qlean_ew_rank_pair(dav: B, doav: B, dbv: B, dobv: B) -> O {
        let (oa, ob) = (boxed_offs(doav), boxed_offs(dobv));
        let (da, db) = (Syms { blob: dav.bytes(), offs: &oa }, Syms { blob: dbv.bytes(), offs: &ob });
        let (mut ra, mut rb) = (answer(da.count() * 4), answer(db.count() * 4));
        let (sa, sb) = (crate::pod::cast_mut(ra.bytes_mut()).expect("qlean_ew_rank_pair: the answer is not 4-aligned"),
                        crate::pod::cast_mut(rb.bytes_mut()).expect("qlean_ew_rank_pair: the answer is not 4-aligned"));
        ew::rank_pair(&da, &db, sa, sb);
        ctor(0, [ra.into(), rb.into()], &[])
    }

    /// `eqIds op shape ia ib w n`: bit `i` is whether the two ids the shape indexes, both read at `w`, are equal (`=`) or differ.
    fn qlean_ew_eq_ids(op: u8, shape: u8, iav: B, ibv: B, w: usize, n: usize) -> O {
        let (w, iab, ibb) = (w as u32, iav.bytes(), ibv.bytes());
        let n = ew::ids_n(shape, n, iab.len(), w, ibb.len(), w);
        let mut r = bits(n);
        ew::eq_ids(c::pool(), op, shape, iab, ibb, w, n, r.bytes_mut());
        r.into()
    }

    /// `cmpIds op shape ra ia rb ib n`: `op` between the ranks `r[id[j]]` of the two sides the shape indexes.
    fn qlean_ew_cmp_ids(op: u8, shape: u8, rav: B, iav: B, wav: usize, rbv: B, ibv: B, wbv: usize, n: usize) -> O {
        let (wa, wb, iab, ibb) = (wav as u32, wbv as u32, iav.bytes(), ibv.bytes());
        let n = ew::ids_n(shape, n, iab.len(), wa, ibb.len(), wb);
        let mut r = bits(n);
        ew::cmp_ids(c::pool(), op, shape, elems::<i32>(rav), iab, wa, elems::<i32>(rbv), ibb, wb, n, r.bytes_mut());
        r.into()
    }

    /// `cmpIdsKey op dict dof ids w key n`: bit `i` is `op` between the symbol element `i`'s id names and `key`, in q's order.
    fn qlean_ew_cmp_ids_key(op: u8, dictv: B, dofv: B, idsv: B, w: usize, keyv: B, n: usize) -> O {
        let offs = boxed_offs(dofv);
        let mut r = bits(n);
        ew::cmp_ids_key(c::pool(), op, &Syms { blob: dictv.bytes(), offs: &offs }, idsv.bytes(), w as u32, keyv.bytes(), n, r.bytes_mut());
        r.into()
    }
}
