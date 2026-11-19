//! reduce.rs's Lean exports: the reductions over a byte payload, whole, grouped (by id or by segment) and per bit row.
//! Each unboxes its arguments, allocates the answer and makes one call into `reduce.rs`, which owns the loops and the
//! split over the pool (`c::pool()`). Lean passes `Int64` as C's `uint64_t` and `Bool` as `uint8_t`.
#![deny(unsafe_code)]
use crate::lean::{B, SArr, export};
use crate::pod;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::lean::O, crate::{c, reduce}, alloc::{format, string::String, vec::Vec},
     crate::{exports::scatter::{blocks_view, except, for_view}, ffi::{Form, Sink}}};

/// The whole `T` elements of a payload (a ragged tail is not one, as `size >> 3` in C).
pub fn elems<'a, T: pod::Pod>(b: B<'a>) -> &'a [T] {
    let v = b.bytes();
    pod::cast(&v[..v.len() - v.len() % size_of::<T>()]).expect("reduce: a payload is not aligned for its element")
}
/// An answer of `n` bytes, undefined until the kernel writes it.
pub fn answer(n: usize) -> SArr { SArr::new(1, n) }

/// The `n` words of a block source, as `i64` (`foRWords`' reading of an index column).
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn words(b: &crate::blocks::Blocks) -> Vec<i64> {
    let mut v = alloc::vec![0i64; b.n];
    for (k, lo, nb) in b.walk() { b.load(k, nb, &mut v[lo..lo + nb]) }
    v
}

/// `Kernel.kbitrows` (Rel/Kernel/BitRows.lean): its checks in the model's order, then `bit_rows` over `m`'s bitmap
/// (`col_bits`), answered as `Sink::bools` writes a `u1` column (`Coc.encodeAt lgEnc 1 _ false`).
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
#[allow(clippy::too_many_arguments)]
fn bitrows(all: bool, w: usize, na: usize, ni: usize, g: usize, ends: B, idx: B, m: B) -> Result<O, String> {
    let (Some(nm), Some(no)) = (na.checked_mul(w).filter(|&x| x < 1 << 32), g.checked_mul(w).filter(|&x| x < 1 << 32)) else {
        return Err(format!("bitrows: {na} or {g} rows of {w} bits reach 2^32"))
    };
    let es = words(&blocks_view("bitrows: ends", g, ends)?);
    let is = words(&blocks_view("bitrows: idx", ni, idx)?);
    let c = for_view("bitrows: m", nm, m)?;
    for r in 0..g {
        let (lo, hi) = (if r == 0 { 0 } else { es[r - 1] as u64 }, es[r] as u64);
        if !(lo <= hi && hi <= ni as u64) { return Err(format!("bitrows: segment {r} ends at {hi}, not in [{lo}, {ni}]")) }
    }
    if let Some((k, &i)) = is.iter().enumerate().find(|&(_, &i)| i as u64 >= na as u64) {
        return Err(format!("bitrows: idx {} at row {k} is not below na = {na}", i as u64))
    }
    let offs: Vec<i64> = core::iter::once(0).chain(es.iter().copied()).collect();
    let mut out = alloc::vec![0u8; no.div_ceil(8)];
    reduce::bit_rows(c::pool(), all, w, &offs, &is, &reduce::col_bits(&c, nm), &mut out);
    Ok(Sink::new(no, 1, Form::For).enc().bools(crate::QLEAN_COST_COPY, &|lo, hi, o| {
        o[..(hi - lo).div_ceil(8)].copy_from_slice(&out[lo / 8..hi.div_ceil(8)])
    }))
}

export! {


    /// `overBytes`: the fold of the six verbs over the elements of class `cls`.
    fn qlean_over_bytes(op: u8, cls: u8, nul: u64, a: B) -> u64 { reduce::over_bytes(op, cls, nul as i64, a.bytes()) as u64 }

    /// `bitRowsOver`: row `g` of `w` bits is the `|` (`&` under `all`) of the rows `idx[k]` of `m`, `k` over segment `g`.
    fn qlean_bit_rows_over(all: u8, w: usize, offv: B, idxv: B, mv: B) -> O {
        let offs = elems::<i64>(offv);
        let ng = offs.len().saturating_sub(1);
        let bytes = if w != 0 && ng != 0 { (ng * w).div_ceil(8) } else { 0 };
        let mut r = answer(bytes);
        reduce::bit_rows(c::pool(), all != 0, w, offs, elems::<i64>(idxv), mv.bytes(), r.bytes_mut());
        r.into()
    }

    /// Spec: `kbitrows all w na ni g ends idx m` (Rel/Kernel/BitRows.lean): bit `r·w + j` of the `g·w`-bit `u1` answer
    /// is the `|` (`&` under `all`) of bit `idx[k]·w + j` of `m` over `k` in `[ends[r-1], ends[r])`, or the model's error.
    fn qlean_k_bitrows(all: u8, w: usize, na: usize, ni: usize, g: usize, ends: B, idx: B, m: B) -> O {
        except(bitrows(all != 0, w, na, ni, g, ends, idx, m))
    }



}
