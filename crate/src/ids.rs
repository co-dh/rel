#![forbid(unsafe_code)]
//! ids.rs, 25, 40; own.rs, 245.
use crate::bits::{lane_width, width_for};

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


/// `Column.idWidth`: zero at one entry and at none -- there is one id, so nothing is stored.
pub fn id_width(nd: usize) -> u32 { if nd < 2 { 0 } else { lane_width(width_for((nd - 1) as u64)) as u32 } }


/// Bytes `n` ids occupy at `w` bits: `⌈n·w/8⌉`, wrapping like the C `size_t` arithmetic.
pub fn ids_bytes(n: usize, w: u32) -> usize { n.wrapping_mul(w as usize).wrapping_add(7) / 8 }
/// `ids_avail`: how many ids a payload of `len` bytes holds at `w` bits, which every kernel clamps the count Lean handed it
/// to (`ids_bytes` is not invertible, so this rounds down). `usize::MAX` at width 0: a one-entry dictionary stores nothing
/// and `id_at` answers 0 at every index.
pub fn ids_avail(len: usize, w: u32) -> usize { if w == 0 { usize::MAX } else { len.wrapping_mul(8) / w as usize } }

/// `Column.idAt`. Narrow widths share a byte, low field first; eight and above are whole elements. Inlined with a
/// fixed-width load per arm, as ids.rs's `static inline` is: an out-of-line call per element was most of `find` ids.
#[inline(always)]
pub fn id_at(p: &[u8], w: u32, i: usize) -> usize { by_width!(w, lane(p, i)) as usize }
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
            for (j, e) in out[i..].iter_mut().enumerate() { f(i + j, e, id_at(p, W, i + j)) }
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


// The largest of whole bytes' fields at a constant narrow width: a const generic so the field loop unrolls.
pub fn narrow_max<const W: u32>(p: &[u8]) -> u8 {
    p.iter().fold(0, |a, &b| (0..8 / W).map(|k| b >> (k * W) & ((1 << W) - 1)).fold(a, u8::max))
}

/// The largest of `n` ids at `w` bits, in one pass.
pub fn ids_max(p: &[u8], w: u32, n: usize) -> usize {
    fn at<const W: u32>(p: &[u8], n: usize) -> usize {
        match W {
            0 => 0,
            1 | 2 | 4 => {
                let nb = n / (8 / W as usize);
                (nb * (8 / W as usize)..n).fold(narrow_max::<W>(&p[..nb]) as usize, |m, i| m.max(lane::<W>(p, i) as usize))
            }
            _ => p.chunks_exact(W as usize / 8).take(n).map(word::<W>).max().unwrap_or(0),
        }
    }
    by_width!(w, at(p, n))
}


// `W` const so `id_at`'s match folds, as the C's `IDS_WIDTHS` does.





#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn widths() {
        assert_eq!((width_for(0), width_for(1), width_for(255), width_for(256), width_for(u64::MAX)), (0, 1, 8, 9, 64));
        assert_eq!([0, 1, 2, 3, 4, 5, 8, 9, 16, 17, 32, 33, 64].map(lane_width), [0, 1, 2, 4, 4, 8, 8, 16, 16, 32, 32, 64, 64]);
        assert_eq!([0, 1, 2, 3, 4, 5, 256, 257, 65537].map(id_width), [0, 0, 1, 2, 2, 4, 8, 16, 32]);
        assert_eq!((ids_bytes(0, 4), ids_bytes(3, 1), ids_bytes(5, 2), ids_bytes(3, 64)), (0, 1, 2, 24));
    }
    // `pack` and `unpack` against the per-id `id_put` and `id_at` they replace, across the word boundary and its tail
    #[test] fn pack_unpack_match_id_put_id_at() {
        fn go<const W: u32>() {
            for n in [0usize, 1, 7, 63, 64, 65, 200, 517] {
                let mask = if W == 64 { !0 } else { (1u64 << W) - 1 };
                let val = |i: usize| (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(17) & mask;
                let (mut a, mut b) = (vec![0u8; ids_bytes(n, W)], vec![0u8; ids_bytes(n, W)]);
                pack(&mut a, W, n, val);
                (0..n).for_each(|i| id_put(&mut b, W, i, val(i)));
                assert_eq!(a, b, "pack w={W} n={n}");
                let mut got = vec![usize::MAX; n];
                unpack::<W, usize>(&a, &mut got, |i, e, v| { assert!(*e == usize::MAX); *e = v; assert_eq!(v, id_at(&a, W, i)) });
                assert!(got.iter().enumerate().all(|(i, &v)| v == id_at(&a, W, i)), "unpack w={W} n={n}");
                let mut runs_out = vec![0i64; n + 1];
                let g = runs(&a, n, W, usize::MAX, n, &mut runs_out);
                let want: Vec<i64> = (0..n).filter(|&i| i == 0 || id_at(&a, W, i) != id_at(&a, W, i - 1)).map(|i| i as i64).collect();
                assert_eq!(&runs_out[..g], &want[..], "runs w={W} n={n}");
            }
        }
        go::<0>(); go::<1>(); go::<2>(); go::<4>(); go::<8>(); go::<16>(); go::<32>(); go::<64>();
    }
    #[test] fn pack_roundtrip() {
        for w in [1u32, 2, 4] {
            for n in 0..70usize {
                let src: Vec<u8> = (0..n).map(|i| (i * 7 + 3) as u8 & ((1 << w) - 1)).collect();
                let mut g = src.clone();
                pack_in_place(&mut g, w, n);
                assert!(src.iter().enumerate().all(|(i, &v)| id_at(&g, w, i) == v as usize), "w={w} n={n}");
            }
        }
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

#[cfg(test)]
mod firsts_tests {
    use super::*;
    // The C driver (/data/tmp/qrs/B1/drv.c) answered (ng, first[1]) = (2, pos), or (1, 0) with no id >= nd, for
    // every (w, nd, pos) of this table; the ids are all 0 but `v` at `pos`.
    #[test] fn firsts_cases() {
        let n = 130;
        for w in [1u32, 2, 4, 8, 16, 32, 64] {
            let nds: &[usize] = if w <= 16 { &[1 << w, (1 << w) - 1] } else { &[3] };
            for &nd in nds {
                let v: u64 = if w >= 32 { 5 } else { (nd as u64).min((1 << w) - 1) };
                for pos in [Some(0), Some(63), Some(64), Some(n - 1), None] {
                    let mut p = vec![0u8; n * 8 + 16];
                    if let Some(i) = pos {
                        if w < 8 { p[i * w as usize / 8] |= (v << (i * w as usize % 8)) as u8 }
                        else { let k = w as usize / 8; p[i * k..(i + 1) * k].copy_from_slice(&v.to_le_bytes()[..k]) }
                    }
                    let (mut slot, mut first) = (vec![usize::MAX; nd + 1], vec![0; n.min(nd + 1)]);
                    let ng = firsts(&p[..ids_bytes(n, w)], n, w, nd, &mut slot, &mut first);
                    let (wng, wf1) = match pos { Some(i) if i != 0 => (2, i), Some(_) => (2, 1), None => (1, 0) };
                    assert_eq!((ng, if ng > 1 { first[1] } else { 0 }), (wng, wf1), "w={w} nd={nd} pos={pos:?}");
                }
            }
        }
    }
}

#[cfg(test)]
mod map_tests {
    use super::*;
    // The C `ids_map_run` + table agreed (/data/tmp/qrs/B2/h.c, 26268 random cases); here the per-row definition.
    #[test] fn map_is_slot_of_id() {
        let mut s = 7u64;
        let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        for w in [1u32, 2, 4, 8, 16, 32, 64] {
            for n in [0usize, 1, 3, 7, 8, 9, 63, 130] {
                let ids: Vec<u8> = (0..ids_bytes(n, w) + 8).map(|_| rnd() as u8).collect();
                let nd = if w <= 8 { 1 << w } else { 5 };
                let slot: Vec<usize> = (0..=nd).map(|v| v % 3).collect();
                for wo in [2u32, 8, 16, 32, 64].into_iter().filter(|&wo| wo >= 8 || w >= 2) {
                    let mut out = vec![0u8; ids_bytes(n, wo)];
                    map(crate::c::qlean_run_c, &ids, n, w, nd, &slot, wo, &mut out);
                    for i in 0..n { assert_eq!(id_at(&out, wo, i), slot[id_at(&ids, w, i).min(nd)], "w={w} n={n} wo={wo} i={i}"); }
                    if (n * wo as usize) & 7 != 0 { assert_eq!(out[out.len() - 1] >> ((n * wo as usize) & 7), 0); }
                }
            }
        }
    }
}

// ---- A10: ids.rs (per element: C keeps these bodies while a C caller remains) ----


// One destination byte of `bitcopy`: up to the byte's end of the `bits - i` left, from bit `sb + i` of the source.





// The head test of `runs`: field `i` raw value `raw` is a head where `min(raw, nd)` differs from the field before.
// Taken by value into `runs_at`, so its fields live in registers; `get_mut` is the C's `if (out)` and the store's
// bounds test in one compare (a non-empty `out` holds every head).



#[cfg(test)]
mod a10_tests {
    use super::*;

    struct Rng(u64);
    impl Rng {
        fn rnd(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 >> 33 }
        fn rnd64(&mut self) -> u64 { let a = self.rnd(); a << 31 ^ self.rnd() }
    }
    fn hb(h: &mut u64, b: &[u8]) { for &x in b { *h = (*h ^ x as u64).wrapping_mul(1099511628211); } }
    fn h16(h: &mut u64, d: &[u16]) { for x in d { hb(h, &x.to_le_bytes()); } }

    // The same random walk as the C harness over ids.rs at 98305ab: the expected hashes are the C's output.
    #[test]
    fn matches_c() {
        let mut r = Rng(0x9E3779B97F4A7C15);
        let [mut hp, mut hf, mut hu, mut hr, mut hc] = [14695981039346656037u64; 5];
        for _ in 0..3000 {
            for w in [0u32, 1, 2, 4, 8, 16, 32, 64] {
                let cap = if w != 0 { 64 * 8 / w as usize } else { 100 };
                let buf: Vec<u8> = (0..64).map(|_| r.rnd() as u8).collect();
                let mut b2 = buf.clone();
                let i = r.rnd() as usize % cap; let v = r.rnd64();
                id_put(&mut b2, w, i, v); hb(&mut hp, &b2);
                let mut b2 = buf.clone();
                let at = r.rnd() as usize % (cap + 1); let cnt = r.rnd() as usize % (cap - at + 1); let v = r.rnd64();
                ids_fill(&mut b2, w, at, cnt, v); hb(&mut hf, &b2);
                let p: Vec<u8> = (0..64).map(|_| r.rnd() as u8).collect();
                let from = r.rnd() as usize % (cap + 1); let m = r.rnd() as usize % (cap - from + 1);
                let mut d = [0u16; 800];
                unpack16(&p, w, from, m, &mut d); h16(&mut hu, &d[..m]);
                let n = r.rnd() as usize % (cap + 1); let nd = 1 + r.rnd() as usize % 300;
                let mut most = if r.rnd() % 4 != 0 { r.rnd() as usize % (n + 2) } else { usize::MAX };
                let mut prev = 0u8;
                let p: Vec<u8> = (0..40).map(|_| { if r.rnd() % 4 == 0 { prev = r.rnd() as u8; } prev }).collect();
                let n = n.min(40 * 8 / w.max(1) as usize);
                let mut o = [-1i64; 400];
                let g = if r.rnd() % 3 != 0 { most = n; runs(&p, n, w, nd, most, &mut o[..most]) } else { runs(&p, n, w, nd, most, &mut []) };
                hb(&mut hr, &(g as u64).to_le_bytes());
                for x in &o[..g.min(400)] { hb(&mut hr, &x.to_le_bytes()); }
            }
            let src: Vec<u8> = (0..40).map(|_| r.rnd() as u8).collect();
            let ss = 24 + r.rnd() as usize % 17; let sb = r.rnd() as usize % (ss * 8); let db = r.rnd() as usize % 64;
            let lim = (ss * 8 - sb).min(320 - db); let bits = r.rnd() as usize % (lim + 1);
            let mut dst = [0u8; 40];
            bitcopy(&mut dst, db, &src[..ss], sb, bits); hb(&mut hc, &dst);
        }
        assert_eq!([hp, hf, hu, hr, hc], [0x6a45bdefcd81525e, 0xad88878f87de21f7, 0xf8cd5342bebc2451, 0x60ea9b1386f531b5, 0x2ad203a0f427c6ff]);
    }

    #[test]
    fn edges() {
        assert_eq!(slice_elems(0), 1); assert_eq!(slice_elems(2), 4); assert_eq!(slice_elems(8), 1);
        assert_eq!(runs(&[], 0, 8, 3, 5, &mut []), 0);
        let mut o = [0i64; 3];
        assert_eq!(runs(&[1, 1, 2], 3, 8, 9, 9, &mut o), 2); assert_eq!(o[..2], [0, 2]);
        // ids past nd read as nd: 5 and 9 are one run at nd = 3
        assert_eq!(runs(&[5, 9], 2, 8, 3, 9, &mut []), 1);
    }
}
