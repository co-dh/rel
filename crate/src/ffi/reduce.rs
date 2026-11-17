//! reduce.rs's Lean exports: the reductions over a byte payload, whole, grouped (by id or by segment) and per bit row.
//! Each unboxes its arguments, allocates the answer and makes one call into `reduce.rs`, which owns the loops and the
//! split over the pool (`c::pool()`). Lean passes `Int64` as C's `uint64_t` and `Bool` as `uint8_t`.
#![deny(unsafe_code)]
use crate::lean::{B, O, SArr, export};
use crate::{c, pod, reduce};

/// The whole `T` elements of a payload (a ragged tail is not one, as `size >> 3` in C).
pub fn elems<'a, T: pod::Pod>(b: B<'a>) -> &'a [T] {
    let v = b.bytes();
    pod::cast(&v[..v.len() - v.len() % size_of::<T>()]).expect("reduce: a payload is not aligned for its element")
}
/// An answer of `n` bytes, undefined until the kernel writes it.
fn answer(n: usize) -> SArr { SArr::new(1, n) }

export! {
    /// RFC 1321's digest of `bv`.
    fn qlean_md5(bv: B) -> O {
        let mut r = answer(16);
        r.bytes_mut().copy_from_slice(&reduce::md5(bv.bytes()));
        r.into()
    }

    /// `svLongs`: `acc * base + digit` down the longs of `a`, wrapping (`reduce::over_sv`).
    fn qlean_over_sv(base: u64, a: B) -> u64 { reduce::over_sv(base as i64, a.bytes()) as u64 }

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

    /// `overSegments`: `overGroups`' fold over the rows of each segment of `offv` (ascending starts split by rows).
    fn qlean_over_segments(op: u8, cls: u8, nul: u64, offv: B, a: B) -> O {
        let offs = elems::<i64>(offv);
        let ng = offs.len().saturating_sub(1);
        let mut r = answer(ng * 16);
        if ng != 0 {
            let (src, w) = (a.bytes(), 1usize << cls.min(3));
            let res = pod::cast_mut(r.bytes_mut()).expect("qlean_over_segments: the answer is not 8-aligned");
            reduce::segments(c::pool(), op, cls, nul as i64, offs, src, src.len() / w, res);
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

    /// `overGroupsFloat`: `overGroups`' layout, each group's fold as double bits and then its live count.
    fn qlean_over_groups_float(op: u8, f32: u8, avg: u8, ng: usize, iw: usize, rows: usize, gidv: B, a: B) -> O {
        let mut r = answer(ng * 16);
        reduce::over_groups_float(op, f32 != 0, avg != 0, ng, iw, rows, gidv.bytes(), a.bytes(), r.bytes_mut());
        r.into()
    }

    /// `overSegmentsFloat`: `overGroupsFloat`'s fold over each segment of `offv`.
    fn qlean_over_segments_float(op: u8, f32: u8, avg: u8, offv: B, a: B) -> O {
        let offs = elems::<i64>(offv);
        let mut r = answer(offs.len().saturating_sub(1) * 16);
        reduce::over_segments_float(op, f32 != 0, avg != 0, offs, a.bytes(), r.bytes_mut());
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

    /// `overF64`: the bits of `op` over the doubles of `a`.
    fn qlean_over_f64(op: u8, a: B) -> u64 { reduce::over_f64(op, elems::<f64>(a), None).to_bits() }

    /// `overF32`: the bits of `op` over the floats of `a`.
    fn qlean_over_f32(op: u8, a: B) -> u32 { reduce::over_f32(op, elems::<f32>(a), None).to_bits() }
}
