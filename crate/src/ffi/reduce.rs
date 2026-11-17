//! reduce.rs's Lean exports: the reductions over a byte payload, whole, grouped (by id or by segment) and per bit row.
//! Each unboxes its arguments, allocates the answer and makes one call into `reduce.rs`, which owns the loops and the
//! split over the pool (`c::pool()`). Lean passes `Int64` as C's `uint64_t` and `Bool` as `uint8_t`.
#![deny(unsafe_code)]
use crate::lean::{B, SArr, export};
use crate::pod;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::lean::O, crate::{c, reduce}};

/// The whole `T` elements of a payload (a ragged tail is not one, as `size >> 3` in C).
pub fn elems<'a, T: pod::Pod>(b: B<'a>) -> &'a [T] {
    let v = b.bytes();
    pod::cast(&v[..v.len() - v.len() % size_of::<T>()]).expect("reduce: a payload is not aligned for its element")
}
/// An answer of `n` bytes, undefined until the kernel writes it.
pub fn answer(n: usize) -> SArr { SArr::new(1, n) }

export! {


    /// `overBytes`: the fold of the six verbs over the elements of class `cls`.
    fn qlean_over_bytes(op: u8, cls: u8, nul: u64, a: B) -> u64 { reduce::over_bytes(op, cls, nul as i64, a.bytes()) as u64 }

    /// `overGroups`: `2 * ng` slots, each group's fold and then its live count; `iw` is the id width, `rows` the count
    /// Lean handed over.
    fn qlean_over_groups(op: u8, cls: u8, nul: u64, ng: usize, iw: usize, rows: usize, gidv: B, a: B) -> O {
        let mut r = answer(ng * 16);
        if ng != 0 {
            let res = pod::cast_mut(r.bytes_mut()).expect("qlean_over_groups: the answer is not 8-aligned");
            reduce::over_groups(c::pool(), op, cls, nul as i64, ng, iw as u32, rows, gidv.bytes(), a.bytes(), res);
        }
        r.into()
    }


    /// `bitRowsOver`: row `g` of `w` bits is the `|` (`&` under `all`) of the rows `idx[k]` of `m`, `k` over segment `g`.
    fn qlean_bit_rows_over(all: u8, w: usize, offv: B, idxv: B, mv: B) -> O {
        let offs = elems::<i64>(offv);
        let ng = offs.len().saturating_sub(1);
        let bytes = if w != 0 && ng != 0 { (ng * w).div_ceil(8) } else { 0 };
        let mut r = answer(bytes);
        reduce::bit_rows(c::pool(), all != 0, w, offs, elems::<i64>(idxv), mv.bytes(), r.bytes_mut());
        r.into()
    }



    /// `groupCells`: cell `i` of `ord` as `w` bytes (eight under the two averages) from the `2 * ng` slots of `m`.
    fn qlean_group_cells(kind: u8, w: usize, ng: usize, mv: B, ordv: B) -> O {
        let ord = elems::<u64>(ordv);
        let ow = if kind == 2 || kind == 4 { 8 } else { w };
        // the spec reads past a short `m` as zero slots; a caller never passes one, so it is an abort
        if mv.bytes().len() < ng.wrapping_mul(16) || !matches!(ow, 1 | 2 | 4 | 8) {
            panic!("qlean_group_cells: {} slot bytes for {} groups at width {}", mv.bytes().len(), ng, ow);
        }
        let mut r = answer(ord.len() * ow);
        reduce::group_cells(kind, w, ng, elems::<i64>(mv), ord, r.bytes_mut());
        r.into()
    }


}
