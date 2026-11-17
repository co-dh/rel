//! ew.rs's Lean exports: the chains (`chain`, `chainEnc`, `statsChain`), guid `=`/`<>`/fill, the value verbs (dense and over encoded columns), the comparisons, bitmap verbs and
//! bitwise verbs, the symbol ranking, comparison, `like`, `ss`/`ssr` and translate, the monadic verbs, `floor`, casts and
//! widening. Each unboxes its arguments, allocates the answer and makes one call into `ew.rs`, which owns the loops and the
//! split over the pool (`c::pool()`). Lean passes `Int64` as C's `uint64_t`.
#![deny(unsafe_code)]
use crate::lean::{SArr, export};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::exports::coc::view, crate::ffi::chain_enc, crate::lean::{B, O}, crate::{c, ew}};

/// An answer of `n` bytes, undefined until the kernel writes it.
pub fn answer(n: usize) -> SArr { SArr::new(1, n) }
/// The bitmap of `n` elements, one bit each.
pub fn bits(n: usize) -> SArr { answer(n.div_ceil(8)) }

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





    /// `eqIds op shape ia ib w n`: bit `i` is whether the two ids the shape indexes, both read at `w`, are equal (`=`) or differ.
    fn qlean_ew_eq_ids(op: u8, shape: u8, iav: B, ibv: B, w: usize, n: usize) -> O {
        let (w, iab, ibb) = (w as u32, iav.bytes(), ibv.bytes());
        let n = ew::ids_n(shape, n, iab.len(), w, ibb.len(), w);
        let mut r = bits(n);
        ew::eq_ids(c::pool(), op, shape, iab, ibb, w, n, r.bytes_mut());
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

    /// `chain prog inputs n`: the fused chain `Ew.chain` specifies, a tile at a time; the last stage's payload.
    fn qlean_ew_chain(progv: B, inputsv: B, n: usize) -> O {
        let (prog, ins) = (progv.bytes(), inputsv.array());
        let mut r = answer(ew::chain_bytes(prog, n));
        ew::chain(prog, &|i| ins[i as usize].bytes(), n, r.bytes_mut());
        r.into()
    }

    /// `chainEnc prog inputs n w`: `Coc.encode w (Ew.chain prog inputs n)`, the chain being the encoder's source above the fusing threshold.
    fn qlean_ew_chain_enc(progv: B, inputsv: B, n: usize, width: usize) -> O {
        let ins = inputsv.array();
        chain_enc(progv.bytes(), &|i| ins[i as usize].bytes(), n, width)
    }



}
