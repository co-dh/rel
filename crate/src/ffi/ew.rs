//! elementwise.c's Lean exports: the value verbs (dense and over encoded columns), the comparisons, bitmap verbs and
//! bitwise verbs, the symbol ranking, comparison, `like`, `ss`/`ssr` and translate, the monadic verbs, `floor`, casts and
//! widening. Each unboxes its arguments, allocates the answer and makes one call into `ew.rs`, which owns the loops and the
//! split over the pool (`c::pool()`). Lean passes `Int64` as C's `uint64_t`.
#![deny(unsafe_code)]
use crate::exports::coc::view;
use crate::exports::reduce::elems;
use crate::ffi::{encode_fill, syms_of};
use crate::lean::{B, O, SArr, arr, boxed, ctor, export};
use crate::{c, ew, pod};

/// An answer of `n` bytes, undefined until the kernel writes it.
fn answer(n: usize) -> SArr { SArr::new(1, n) }
/// The bitmap of `n` elements, one bit each.
fn bits(n: usize) -> SArr { answer(n.div_ceil(8)) }

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
        let (da, db) = (syms_of(dav, doav), syms_of(dbv, dobv));
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
        let mut r = bits(n);
        ew::cmp_ids_key(c::pool(), op, &syms_of(dictv, dofv), idsv.bytes(), w as u32, keyv.bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `fixedHits pat b atom`: `some` of every non-overlapping match start (`Int64`s), `none` for the refusals `fixed_width` names.
    fn qlean_ew_fixed_hits(patv: B, bv: B, atom: u8) -> O {
        let (p, b, atom) = (patv.bytes(), bv.bytes(), atom != 0);
        let w = ew::fixed_width(atom, p);
        if w == 0 { return boxed(0) }
        let mut h = pod::uninit::<i64>(b.len() / w + 1);
        let hits = ew::fixed_scan(atom, p, b, &mut h);
        let mut r = answer(hits * 8);
        r.bytes_mut().copy_from_slice(pod::bytes_mut(&mut h[..hits]));
        ctor(1, [r.into()], &[])
    }

    /// `ssrBytes pat repl b atom`: `b` with every match of `fixedHits` replaced by `repl`, `none` on the same refusals.
    fn qlean_ew_ssr(patv: B, replv: B, bv: B, atom: u8) -> O {
        let (p, t, b, atom) = (patv.bytes(), replv.bytes(), bv.bytes(), atom != 0);
        let w = ew::fixed_width(atom, p);
        if w == 0 { return boxed(0) }
        let mut h = pod::uninit::<i64>(b.len() / w + 1);
        let hits = ew::fixed_scan(atom, p, b, &mut h);
        let total = b.len() - hits * w + hits * t.len();
        // 16 bytes of slack, so a short run is one fixed-width move rather than a call
        let mut r = SArr::with_capacity(1, total, total + 16);
        ew::ssr_fill(r.capacity_mut(), b, &h[..hits], w, t);
        ctor(1, [r.into()], &[])
    }

    /// `likeSyms pat blob offs`: bit `i` is `patMatch` at symbol `i`; `none` where `parsePat` refuses the pattern.
    fn qlean_ew_like_syms(patv: B, blobv: B, offsv: B) -> O {
        let s = syms_of(blobv, offsv);
        let mut r = bits(s.count());
        if ew::like_syms(patv.bytes(), &s, r.bytes_mut()) { ctor(1, [r.into()], &[]) } else { boxed(0) }
    }

    /// `translateSyms pre tab blob offs`: every symbol's bytes mapped through `tab`, `pre` in front unless already there; the (blob, starts) pair.
    fn qlean_ew_translate_syms(prev: B, tabv: B, blobv: B, offsv: B) -> O {
        let s = syms_of(blobv, offsv);
        let (pre, tab, n) = (prev.bytes(), tabv.bytes(), s.count());
        let mut nb = answer(ew::translate_size(pre, tab, &s));
        let mut ends = pod::uninit::<usize>(n);
        ew::translate_fill(pre, tab, &s, nb.bytes_mut(), &mut ends);
        // start 0, then the end of each symbol, boxed
        ctor(0, [nb.into(), arr((0..n + 1).map(|i| boxed(if i == 0 { 0 } else { ends[i - 1] })))], &[])
    }

    /// `cmpSyms op shape blobA offsA blobB offsB n`: bit `i` is `Order.symCmp` of the two symbols the shape indexes satisfying `op`.
    fn qlean_ew_cmp_syms(op: u8, shape: u8, ba: B, oa: B, bb: B, ob: B, n: usize) -> O {
        let mut r = bits(n);
        ew::cmp_syms(c::pool(), op, shape, &syms_of(ba, oa), &syms_of(bb, ob), n, r.bytes_mut());
        r.into()
    }

    /// `bit op shape a b n`: a verb of two bitmaps (`&`, `|`, fill, the six comparisons), the bits above `n` zero.
    fn qlean_ew_bit(op: u8, shape: u8, a: B, b: B, n: usize) -> O {
        let mut r = bits(n);
        ew::bit(c::pool(), op, shape, a.bytes(), b.bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `mon op cls nul x n`: `neg`, `abs` or one of the nine float maps over `n` elements of class `cls`.
    fn qlean_ew_mon(op: u8, cls: u8, nul: u64, x: B, n: usize) -> O {
        let mut r = answer(n * ew::ew_width(cls as u32));
        ew::mon(c::pool(), op, cls, nul as i64, x.bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `foRMonEnc op cls nul m p n`: the writer's encoding of `mon` over the decoded column, the map run a block at a time.
    fn qlean_coc_ew_mon_enc(op: u8, cls: u8, nul: u64, mv: B, pv: B, n: usize) -> O {
        let col = view("qlean_coc_ew_mon_enc", mv, pv, n);
        encode_fill(col.meta.n, ew::ew_width(cls as u32), &|buf: &mut [i64], i0: usize| ew::mon_fill(op, cls, nul as i64, &col, buf, i0))
    }

    /// `foRMon op cls nul m p n`: `mon` over the decoded column.
    fn qlean_coc_ew_mon(op: u8, cls: u8, nul: u64, mv: B, pv: B, n: usize) -> O {
        let col = view("qlean_coc_ew_mon", mv, pv, n);
        let mut r = answer(n * ew::ew_width(cls as u32));
        ew::mon_enc(c::pool(), op, cls, nul as i64, &col, r.bytes_mut());
        r.into()
    }

    /// `floor cls x n`: `_` at a float class, answering `long`s, `0N` out of range.
    fn qlean_ew_floor(cls: u8, x: B, n: usize) -> O {
        let mut r = answer(n * 8);
        ew::floor(c::pool(), cls, x.bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `cast src dst nulIn x n`: `$` from class `src` to `dst`.
    fn qlean_ew_cast(src: u8, dst: u8, nul_in: u64, x: B, n: usize) -> O {
        let mut r = answer(n * ew::ew_width(dst as u32));
        ew::cast(c::pool(), src, dst, nul_in as i64, x.bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `widen src dst nulIn nulOut x n`: an operand brought up to the class its verb's result is at, nulls remapped.
    fn qlean_ew_widen(src: u8, dst: u8, nul_in: u64, nul_out: u64, x: B, n: usize) -> O {
        let mut r = answer(n * ew::ew_width(dst as u32));
        ew::widen(c::pool(), src, dst, nul_in as i64, nul_out as i64, x.bytes(), n, r.bytes_mut());
        r.into()
    }
}
