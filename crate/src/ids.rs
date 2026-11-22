#![forbid(unsafe_code)]
//! ids.rs, 25, 40; own.rs, 245.
#[cfg(test)] use crate::bits::{lane_width, width_for};

/// The one width dispatch, switched once per column and never per element. `by_width!(w, f::<A…>(args))` is
/// `f::<A…, W>(args)` at the id width `w` bits, so `id_at`'s match folds as the C's `IDS_WIDTHS` does; `int w` and
/// `uint w` are `f::<T, A…>(args)` for the element of `w` bytes: the coc storage class (`u8 i16 i32 i64`) or the
/// unsigned lane (`u8 u16 u32 u64`). `f` may be a method path (`self.load`).
#[macro_export]
macro_rules! by_width {
    (int $w:expr, $($f:ident).+ $(::<$($t:ty),*>)? ($($a:expr),* $(,)?)) => { match $w {
        1 => $($f).+::<u8 $($(, $t)*)?>($($a),*), 2 => $($f).+::<i16 $($(, $t)*)?>($($a),*),
        4 => $($f).+::<i32 $($(, $t)*)?>($($a),*), _ => $($f).+::<i64 $($(, $t)*)?>($($a),*),
    } };
    (uint $w:expr, $($f:ident).+ $(::<$($t:ty),*>)? ($($a:expr),* $(,)?)) => { match $w {
        1 => $($f).+::<u8 $($(, $t)*)?>($($a),*), 2 => $($f).+::<u16 $($(, $t)*)?>($($a),*),
        4 => $($f).+::<u32 $($(, $t)*)?>($($a),*), _ => $($f).+::<u64 $($(, $t)*)?>($($a),*),
    } };
    ($w:expr, $($f:ident).+ $(::<$($t:ty),*>)? ($($a:expr),* $(,)?)) => { match $w {
        0 => $($f).+::<$($($t,)*)? 0>($($a),*), 1 => $($f).+::<$($($t,)*)? 1>($($a),*),
        2 => $($f).+::<$($($t,)*)? 2>($($a),*), 4 => $($f).+::<$($($t,)*)? 4>($($a),*),
        8 => $($f).+::<$($($t,)*)? 8>($($a),*), 16 => $($f).+::<$($($t,)*)? 16>($($a),*),
        32 => $($f).+::<$($($t,)*)? 32>($($a),*), _ => $($f).+::<$($($t,)*)? 64>($($a),*),
    } };
}



/// Element `i` of `p` at the lane width `W` bits (0, 1, 2, 4, 8, 16, 32, 64): the one reader of a lane, so a width
/// dispatch is `by_width!` over a function that reads through it, the width a constant inside.
#[inline(always)]
pub fn lane<const W: u32>(p: &[u8], i: usize) -> u64 {
    match W {
        0 => 0,
        1 | 2 | 4 => (p[i * W as usize >> 3] >> (i * W as usize & 7) & ((1u16 << W) - 1) as u8) as u64,
        8 => p[i] as u64,
        16 => u16::from_le_bytes(le(p, i)) as u64,
        32 => u32::from_le_bytes(le(p, i)) as u64,
        _ => u64::from_le_bytes(le(p, i)),
    }
}
/// Element `i` of `p` at `W` bytes.
#[inline(always)]
pub fn le<const W: usize>(p: &[u8], i: usize) -> [u8; W] { p[i * W..(i + 1) * W].try_into().unwrap() }

/// `IDS_UNPACK` (ids.rs): `f(i, &mut out[i], id)` for each element of `out` and the id of the same index at the
/// constant width `W`. Below a byte one word holds `64 / W` ids at constant shifts, a whole-byte lane is a chunked
/// load, and `out` is walked in step: no per-id bounds test or index shift, which `id_at` at a running index has,
/// so the loop vectorises as the C's does.
#[inline(always)]
pub fn unpack<const W: u32, T>(p: &[u8], out: &mut [T], mut f: impl FnMut(usize, &mut T, usize)) {
    let mut i = 0;
    match W {
        0 => out.iter_mut().enumerate().for_each(|(i, e)| f(i, e, 0)),
        1 | 2 | 4 => {
            let (per, m) = (64 / W as usize, (1u64 << W) - 1);
            for (c, x) in out.chunks_exact_mut(per).zip(p.chunks_exact(8)) {
                let x = u64::from_le_bytes(x.try_into().unwrap());
                for (t, e) in c.iter_mut().enumerate() { f(i + t, e, (x >> (t as u32 * W) & m) as usize) }
                i += per;
            }
            for (j, e) in out[i..].iter_mut().enumerate() { f(i + j, e, lane::<W>(p, i + j) as usize) }
        }
        _ => {
            for (j, (e, c)) in out.iter_mut().zip(p.chunks_exact(whole_bytes(W))).enumerate() { f(j, e, word::<W>(c)) }
        }
    }
}
/// Bytes of one id at a whole-byte width `w` (1 below a byte, where no caller reads whole ids).
pub const fn whole_bytes(w: u32) -> usize { if w >= 8 { w as usize / 8 } else { 1 } }
/// The id `c` holds at the whole-byte width `W`, `c` exactly `whole_bytes(W)` long: a load of that width.
#[inline(always)]
pub fn word<const W: u32>(c: &[u8]) -> usize {
    match W { 8 => c[0] as usize, 16 => u16::from_le_bytes([c[0], c[1]]) as usize,
              32 => u32::from_le_bytes([c[0], c[1], c[2], c[3]]) as usize, _ => u64::from_le_bytes(c.try_into().unwrap()) as usize }
}




// `W` const so `id_at`'s match folds, as the C's `IDS_WIDTHS` does.




#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::id_put;
    #[test] fn widths() {
        assert_eq!((width_for(0), width_for(1), width_for(255), width_for(256), width_for(u64::MAX)), (0, 1, 8, 9, 64));
        assert_eq!([0, 1, 2, 3, 4, 5, 8, 9, 16, 17, 32, 33, 64].map(lane_width), [0, 1, 2, 4, 4, 8, 8, 16, 16, 32, 32, 64, 64]);
    }
    // `unpack` against the per-id `lane` on ids written by `id_put`, across the word boundary and its tail
    #[test] fn unpack_matches_id_at() {
        fn go<const W: u32>() {
            for n in [0usize, 1, 7, 63, 64, 65, 200, 517] {
                let mask = if W == 64 { !0 } else { (1u64 << W) - 1 };
                let val = |i: usize| (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(17) & mask;
                let mut a = alloc::vec![0u8; (n * W as usize + 7) / 8];
                (0..n).for_each(|i| id_put(&mut a, W, i, val(i)));
                assert!((0..n).all(|i| lane::<W>(&a, i) == val(i)), "id_at w={W} n={n}");
                let mut got = alloc::vec![usize::MAX; n];
                unpack::<W, usize>(&a, &mut got, |i, e, v| { assert!(*e == usize::MAX); *e = v; assert_eq!(v, lane::<W>(&a, i) as usize) });
                assert!(got.iter().enumerate().all(|(i, &v)| v == lane::<W>(&a, i) as usize), "unpack w={W} n={n}");
            }
        }
        go::<0>(); go::<1>(); go::<2>(); go::<4>(); go::<8>(); go::<16>(); go::<32>(); go::<64>();
    }
}
