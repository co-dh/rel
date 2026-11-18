//! ew.rs's Lean exports: the chains (`chain`, `chainEnc`, `statsChain`), the value verbs (dense and over encoded columns), the comparisons, bitmap verbs and
//! bitwise verbs, the symbol ranking, comparison, `like`, `ss`/`ssr` and translate, the monadic verbs, `floor`, casts and
//! widening. Each unboxes its arguments, allocates the answer and makes one call into `ew.rs`, which owns the loops and the
//! split over the pool (`c::pool()`). Lean passes `Int64` as C's `uint64_t`.
#![deny(unsafe_code)]
use crate::lean::{SArr, export};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::lean::{B, O}, crate::{c, ew}};

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

    /// `cmp op cls shape a b n`: the `Column.bits` payload of the comparison, the bits above `n` zero.
    fn qlean_ew_cmp(op: u8, cls: u8, shape: u8, a: B, b: B, n: usize) -> O {
        let mut r = bits(n);
        ew::cmp(c::pool(), op, cls, shape, a.bytes(), b.bytes(), n, r.bytes_mut());
        r.into()
    }





    /// `bit op shape a b n`: a verb of two bitmaps (`&`, `|`, fill, the six comparisons), the bits above `n` zero.
    fn qlean_ew_bit(op: u8, shape: u8, a: B, b: B, n: usize) -> O {
        let mut r = bits(n);
        ew::bit(c::pool(), op, shape, a.bytes(), b.bytes(), n, r.bytes_mut());
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

}
