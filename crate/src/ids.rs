#![forbid(unsafe_code)]
//! ids.h:19, 25, 40; own.c:231, 245.
use crate::bits::{lane_width, width_for};

/// `Column.idWidth`: zero at one entry and at none -- there is one id, so nothing is stored.
pub fn id_width(nd: usize) -> u32 { if nd < 2 { 0 } else { lane_width(width_for((nd - 1) as u64)) as u32 } }

/// Bytes `n` ids occupy at `w` bits: `⌈n·w/8⌉`, wrapping like the C `size_t` arithmetic.
pub fn ids_bytes(n: usize, w: u32) -> usize { n.wrapping_mul(w as usize).wrapping_add(7) / 8 }

/// `Column.idAt`. Narrow widths share a byte, low field first; eight and above are whole elements.
pub fn id_at(p: &[u8], w: u32, i: usize) -> usize {
    let le = |k: usize| p[i * k..i * k + k].iter().rev().fold(0usize, |a, &b| a << 8 | b as usize);
    match w {
        0 => 0,
        1 => (p[i >> 3] >> (i & 7) & 1) as usize,
        2 => (p[i >> 2] >> ((i & 3) * 2) & 3) as usize,
        4 => (p[i >> 1] >> ((i & 1) * 4) & 15) as usize,
        8 => p[i] as usize,
        16 => le(2),
        32 => le(4),
        _ => le(8),
    }
}

// The largest of whole bytes' fields at a constant narrow width: a const generic so the field loop unrolls.
fn narrow_max<const W: u32>(p: &[u8]) -> u8 {
    p.iter().fold(0, |a, &b| (0..8 / W).map(|k| b >> (k * W) & ((1 << W) - 1)).fold(a, u8::max))
}

fn wide_max<const K: usize>(p: &[u8], n: usize) -> usize {
    p.chunks_exact(K).take(n).map(|c| c.iter().rev().fold(0usize, |a, &b| a << 8 | b as usize)).max().unwrap_or(0)
}

/// The largest of `n` ids at `w` bits, in one pass.
pub fn ids_max(p: &[u8], w: u32, n: usize) -> usize {
    match w {
        0 => 0,
        8 => wide_max::<1>(p, n),
        16 => wide_max::<2>(p, n),
        32 => wide_max::<4>(p, n),
        64 => wide_max::<8>(p, n),
        _ => {
            let nb = n / (8 / w as usize);
            let m = match w { 1 => narrow_max::<1>(&p[..nb]), 2 => narrow_max::<2>(&p[..nb]), _ => narrow_max::<4>(&p[..nb]) } as usize;
            (nb * (8 / w as usize)..n).fold(m, |m, i| m.max(id_at(p, w, i)))
        }
    }
}

/// `ids_firsts` (ids.h:271): each group's first row into `first` (`min(n, nd + 1)` long) and into `slot` (`nd + 1`
/// entries, all `usize::MAX` on entry) the group of each value `min(id, nd)`; answers the group count.
#[allow(unused_variables)] // scaffold: B1 fills it
pub fn firsts(ids: &[u8], n: usize, w: u32, nd: usize, slot: &mut [usize], first: &mut [usize]) -> usize {
    unimplemented!()
}

/// `idGroups`' second pass (sort.c:3283-3315, 3400-3414): row `i`'s group `slot[min(id, nd)]` into `out` at `wo`
/// bits, `ids_bytes(n, wo)` bytes, the bits past `n` zero; threaded by `c::run_map`.
#[allow(unused_variables)] // scaffold: B2 fills it
pub fn map(ids: &[u8], n: usize, w: u32, nd: usize, slot: &[usize], wo: u32, out: &mut [u8]) { unimplemented!() }

/// `IDS_PACK` (ids.h:167) in place: `n` ids one byte each in `g` packed to `w < 8` bits from `g[0]`.
#[allow(unused_variables)] // scaffold: B6 fills it
pub fn pack_in_place(g: &mut [u8], w: u32, n: usize) { unimplemented!() }

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn widths() {
        assert_eq!((width_for(0), width_for(1), width_for(255), width_for(256), width_for(u64::MAX)), (0, 1, 8, 9, 64));
        assert_eq!([0, 1, 2, 3, 4, 5, 8, 9, 16, 17, 32, 33, 64].map(lane_width), [0, 1, 2, 4, 4, 8, 8, 16, 16, 32, 32, 64, 64]);
        assert_eq!([0, 1, 2, 3, 4, 5, 256, 257, 65537].map(id_width), [0, 0, 1, 2, 2, 4, 8, 16, 32]);
        assert_eq!((ids_bytes(0, 4), ids_bytes(3, 1), ids_bytes(5, 2), ids_bytes(3, 64)), (0, 1, 2, 24));
    }
    #[test] fn at_and_max() {
        let p = [0b1110_0100u8, 0b0000_0011, 5, 0, 0, 0, 0, 0, 0, 0];
        assert_eq!([0, 1, 2, 3].map(|i| id_at(&p, 2, i)), [0, 1, 2, 3]);
        assert_eq!(id_at(&p, 4, 1), 14);
        assert_eq!(id_at(&p, 16, 1), 5);
        assert_eq!(id_at(&p, 0, 99), 0);
        for w in [1u32, 2, 4, 8, 16, 32, 64] {
            for n in 0..(80 / w as usize).min(10) {
                assert_eq!(ids_max(&p, w, n), (0..n).map(|i| id_at(&p, w, i)).max().unwrap_or(0), "w={w} n={n}");
            }
        }
        assert_eq!(ids_max(&p, 0, 5), 0);
    }
}
