#![forbid(unsafe_code)]
//! Column (a), coc.rs: one block's residuals as bits — single fields (A2), the scalar pack (A2; the AVX-512 one is
//! `simd::res_pack`), the residual sums (A3, `simd::res_sum8` for 8 bits), the smallest nonzero residual (A4).
//! `p` is always the block's `(1 << lg) * w / 8` bytes.

use alloc::{vec, vec::Vec};

// ---- A2: coc.rs, 678-760 ----
/// coc.rs `res_get`: field `j` of width `w`. Per element: C keeps its body while a C caller remains.
#[inline]
pub fn res_get(p: &[u8], w: u8, j: usize) -> u64 {
    if w == 0 { return 0 }
    let (bit, w) = (j * w as usize, w as usize);
    let (o, sh) = (bit >> 3, bit & 7);
    // a whole word where the payload holds one past the field: one load, where copying the `nby` bytes the field
    // spans is a `memcpy` call of a run-time length per element (perf: the calls were most of `reverse foR`)
    if sh + w <= 64 && let Some(c) = p.get(o..o + 8) {
        let v = u64::from_le_bytes(c.try_into().unwrap()) >> sh;
        return if w == 64 { v } else { v & ((1u64 << w) - 1) }
    }
    let nby = (sh + w + 7) >> 3;
    let mut b = [0u8; 8];
    let m = nby.min(8);
    b[..m].copy_from_slice(&p[o..o + m]);
    let mut v = u64::from_le_bytes(b) >> sh;
    if nby > 8 { v |= (p[o + 8] as u64) << (64 - sh) }
    if w == 64 { v } else { v & ((1u64 << w) - 1) }
}
/// coc.rs `res_get_in`: as `res_get`, never reading at or past byte `end`.
pub fn res_get_in(p: &[u8], w: u8, j: usize, end: usize) -> u64 {
    let (bit, w) = (j * w as usize, w as usize);
    let (o, sh) = (bit >> 3, bit & 7);
    if o + 8 > end || sh + w > 64 { return res_get(p, w as u8, j) }
    let v = u64::from_le_bytes(p[o..o + 8].try_into().unwrap()) >> sh;
    if w >= 64 { v } else { v & ((1u64 << w) - 1) }
}
/// coc.rs `res_put`
pub fn res_put(p: &mut [u8], w: u8, j: usize, v: u64) {
    for k in 0..w as usize {
        let bit = j * w as usize + k;
        p[bit >> 3] = (p[bit >> 3] & !(1u8 << (bit & 7))) | ((((v >> k) & 1) as u8) << (bit & 7));
    }
}
/// coc.rs `res_pack_scalar`: the low `w` bits of each of `nb` values of `v` into the first ⌈nb*w/8⌉ bytes of `dst`,
/// each group of 8 built in words before it is stored; no byte past those is written. Panics at a power-of-two or
/// over-64 width, as `res_unpack_scalar` does.
pub fn res_pack_scalar(v: &[u64], w: u8, nb: usize, dst: &mut [u8]) {
    assert!(w >= 3 && w < 64 && !w.is_power_of_two(), "qlean: res_pack asked for width {w}, which is a power of two or over 64");
    let (wu, m) = (w as usize, (1u64 << w) - 1);
    let group = |s: &[u64; 8], out: &mut [u8]| {
        let mut t = [0u64; 8];
        for (k, &x) in s.iter().enumerate() {
            let bit = k * wu;
            let sh = bit & 63;
            t[bit >> 6] |= x << sh;
            if sh + wu > 64 { t[(bit >> 6) + 1] |= x >> (64 - sh) }
        }
        let mut b = [0u8; 64];
        for (i, x) in t.iter().enumerate() { b[i * 8..i * 8 + 8].copy_from_slice(&x.to_le_bytes()) }
        out.copy_from_slice(&b[..out.len()]);
    };
    let mut g = 0;
    while g * 8 + 8 <= nb {
        let mut s = [0u64; 8];
        for k in 0..8 { s[k] = v[g * 8 + k] & m }
        group(&s, &mut dst[g * wu..g * wu + wu]);
        g += 1;
    }
    if g * 8 < nb {
        let mut s = [0u64; 8];
        for k in 0..nb - g * 8 { s[k] = v[g * 8 + k] & m }
        group(&s, &mut dst[g * wu..g * wu + ((nb - g * 8) * wu + 7) / 8]);
    }
}

// ---- A3: coc.rs ----
/// coc.rs `res_count_lt8`: of `nb` 8-bit residuals, how many are below `t`.
pub fn res_count_lt8(p: &[u8], nb: usize, t: u64) -> usize { p[..nb].iter().filter(|&&x| (x as u64) < t).count() }
/// coc.rs `res_count_lt`: of a block's `nb` residuals at width `w`, how many are below `t`. `p` is the lanes
/// `coc::lanes` answers, so `w` is a power of two; 1, 2 and 4 are read a byte at a time.
pub fn res_count_lt(p: &[u8], nb: usize, w: u8, t: u64) -> usize {
    fn sub<const W: usize>(p: &[u8], nb: usize, t: u64) -> usize {
        let (per, m) = (8 / W, (1u8 << W) - 1);
        let at = |v: u8, s: usize| ((((v >> (s * W)) & m) as u64) < t) as usize;
        let k = p[..nb / per].iter().map(|&v| (0..per).map(|s| at(v, s)).sum::<usize>()).sum::<usize>();
        k + (0..nb % per).map(|s| at(p[nb / per], s)).sum::<usize>()
    }
    match w {
        0 => if t > 0 { nb } else { 0 },
        1 => sub::<1>(p, nb, t),
        2 => sub::<2>(p, nb, t),
        4 => sub::<4>(p, nb, t),
        8 => res_count_lt8(p, nb, t),
        16 => p.chunks_exact(2).take(nb).map(|c| ((u16::from_ne_bytes([c[0], c[1]]) as u64) < t) as usize).sum(),
        32 => p.chunks_exact(4).take(nb).map(|c| ((u32::from_ne_bytes([c[0], c[1], c[2], c[3]]) as u64) < t) as usize).sum(),
        64 => p.chunks_exact(8).take(nb).map(|c| (u64::from_ne_bytes(c.try_into().unwrap()) < t) as usize).sum(),
        _ => panic!("qlean: res_count_lt asked for width {w}, which is not a lane"),
    }
}
/// coc.rs `res_unpack_agrees`: over one block of pseudo-random stream bytes at width `w` and `nb` residuals, whether
/// `simd::res_unpack` answers what `unpack::res_unpack_scalar` does on every lane below `nb`, the in-register compare
/// and the one-pass decode agree with them, and `res_pack` of those lanes writes back exactly the stream's first
/// ⌈nb*w/8⌉ bytes -- its bits past the last field cleared -- and not one byte more.
pub fn res_unpack_agrees(w: u8, nb: usize) -> bool {
    use crate::{simd, unpack};
    const BLK: usize = 1 << crate::DEFAULT_LG;
    if w & w.wrapping_sub(1) == 0 || w > 64 || nb > BLK { return false }
    let (mut s, mut x) = (vec![0u8; BLK * 8], 0x9e3779b97f4a7c15u64.wrapping_mul(w as u64 + 1).wrapping_add(nb as u64));
    for b in &mut s[..BLK * w as usize / 8] { x ^= x << 13; x ^= x >> 7; x ^= x << 17; *b = x as u8 }
    let (mut a, mut b, mut c) = (vec![0xa5u8; BLK * 8], vec![0x5au8; BLK * 8], vec![0xc3u8; BLK * 8 + 1]);
    unpack::res_unpack_scalar(&s, w, nb, &mut a);
    simd::res_unpack(&s, w, nb, &mut b);
    let (lw, len) = (if w < 8 { 1 } else { crate::bits::lane_width(w) as usize / 8 }, (nb * w as usize).div_ceil(8));
    if a[..nb * lw] != b[..nb * lw] { return false }
    let mut v: Vec<u64> = (0..nb).map(|i| a[i * lw..(i + 1) * lw].iter().rev().fold(0, |r, &x| r << 8 | x as u64)).collect();
    // the in-register compare against the residuals just checked, both senses; refused (false) in a build without it
    for inv in [false, true] {
        let (mut got, mut want) = ([0u64; BLK / 64], [0u64; BLK / 64]);
        let (lo, span) = ((1u64 << (w - 1)) / 3, (1u64 << (w - 1)) - 1);
        if simd::RES_SIMD {
            if !simd::res_vcmp(&s, w, nb, lo, span, inv, &mut got) { return false }
            for i in 0..nb { want[i / 64] |= (((v[i].wrapping_sub(lo) <= span) ^ inv) as u64) << (i % 64) }
            if got != want { return false }
        }
    }
    // the one-pass decode at every element width the lanes fit, and nothing written past `nb`
    if simd::RES_SIMD {
        for tw in [1usize, 2, 4, 8] {
            let (base, mut d) = (0x8000000000000123u64, vec![0xeeu8; BLK * 8 + 64]);
            if !simd::res_unpack_add(&s, w, nb, base, &mut d, tw as u32) {
                if tw * 8 >= (if w < 8 { 8 } else { crate::bits::lane_width(w) as usize }) { return false }
                continue
            }
            for i in 0..nb {
                let e = d[i * tw..(i + 1) * tw].iter().rev().fold(0u64, |r, &x| r << 8 | x as u64);
                let y = base.wrapping_add(v[i]);
                if e != if tw == 8 { y } else { y & ((1u64 << (8 * tw)) - 1) } { return false }
            }
            if d[nb * tw] != 0xee { return false }
        }
    }
    for x in &mut v { *x |= !0u64 << (w - 1) << 1 }
    simd::res_pack(&v, w, nb, &mut c);   // the bits above each field are set, so a pack that keeps them shows
    if nb * w as usize % 8 != 0 { s[len - 1] &= ((1u32 << (nb * w as usize % 8)) - 1) as u8 }
    c[..len] == s[..len] && c[len] == 0xc3
}
/// coc.rs `res_sum`: `nb` residuals of width `w` summed, wrapping. `w` is a lane width (`coc::lanes` has run) or
/// 1, 2, 4; like C, any other width reads one byte per residual, so a field crossing a byte is cut.
pub fn res_sum(p: &[u8], nb: usize, w: u8) -> u64 {
    fn lanes<const N: usize>(p: &[u8], nb: usize, f: fn([u8; N]) -> u64) -> u64 {
        p[..nb * N].chunks_exact(N).fold(0u64, |a, c| a.wrapping_add(f(c.try_into().unwrap())))
    }
    match w {
        0 => 0,
        8 => crate::simd::res_sum8(p, nb, w),
        16 => lanes(p, nb, |c| u16::from_ne_bytes(c) as u64),
        32 => lanes(p, nb, |c| u32::from_ne_bytes(c) as u64),
        64 => lanes(p, nb, u64::from_ne_bytes),
        _ => (0..nb).fold(0u64, |a, i| { let bit = i * w as usize; a.wrapping_add(((p[bit >> 3] >> (bit & 7)) as u64) & ((1u64 << w) - 1)) }),
    }
}

// ---- A4: coc.rs ----
/// coc.rs `res_min_nonzero`: the smallest nonzero residual of the block, 0 when every element is null.
pub fn res_min_nonzero(p: &[u8], nb: usize, w: u8) -> u64 { (0..nb).map(|j| res_get(p, w, j)).filter(|&r| r != 0).min().unwrap_or(0) }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BLK;
    fn rng(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }
    // the reference: residual j is bits [j*w, j*w+w) of the stream, the spec of coc.rs
    fn bit(p: &[u8], i: usize) -> u64 { (p[i >> 3] >> (i & 7)) as u64 & 1 }
    fn spec(p: &[u8], w: usize, j: usize) -> u64 { (0..w).map(|k| bit(p, j * w + k) << k).sum() }
    // res_count_lt against the spec at every lane width coc::lanes leaves, thresholds below, inside and past the lane; the
    // C differential is /data/tmp/qrs/K25/diff.c
    #[test] fn count_lt_agrees_with_the_bit_stream() {
        let mut s = 0x9E3779B97F4A7C15u64;
        for w in [0u8, 1, 2, 4, 8, 16, 32, 64] {
            let p: Vec<u8> = (0..BLK * w as usize / 8).map(|_| rng(&mut s) as u8).collect();
            for nb in [0, 1, 7, 8, 9, 63, 1000, 1024] {
                for t in [0u64, 1, 2, 3, 15, 16, 255, 256, 65535, 1 << 31, u64::MAX, rng(&mut s)] {
                    let want = (0..nb).filter(|&j| spec(&p, w as usize, j) < t).count();
                    assert_eq!(res_count_lt(&p, nb, w, t), want, "w {w} nb {nb} t {t}");
                }
            }
        }
    }
    // coc.rs's self-check holds at every width it is asked at, and refuses a power of two, a width over 64 and a long block
    #[test] fn unpack_agrees_at_every_odd_width() {
        for w in 3..=63u8 { for nb in [0, 1, 7, 63, 64, 65, 1000, BLK] { assert_eq!(res_unpack_agrees(w, nb), !w.is_power_of_two(), "w {w} nb {nb}") } }
        assert!(!res_unpack_agrees(64, 10) && !res_unpack_agrees(65, 10) && !res_unpack_agrees(5, BLK + 1));
    }
    #[test] fn get_put_agree_with_the_bit_stream() {
        let mut s = 0x9E3779B97F4A7C15u64;
        for w in 0..=64u8 {
            let p: Vec<u8> = (0..BLK * w as usize / 8).map(|_| rng(&mut s) as u8).collect();
            let end = p.len();
            for j in (0..BLK).step_by(13).chain([BLK - 1]) {
                let e = spec(&p, w as usize, j);
                assert_eq!(res_get(&p, w, j), e, "get w {w} j {j}");
                assert_eq!(res_get_in(&p, w, j, end), e, "get_in w {w} j {j}");
            }
            let mut q = p.clone();
            for j in (0..BLK).step_by(7) { let v = rng(&mut s); res_put(&mut q, w, j, v); 
                assert_eq!(res_get(&q, w, j), if w == 64 { v } else { v & ((1u64 << w) - 1) }, "put w {w} j {j}"); }
        }
    }
    #[test] fn pack_scalar_roundtrips_and_stops_at_the_last_byte() {
        let mut s = 0x2545F4914F6CDD1Du64;
        for w in 3..64u8 {
            if w.is_power_of_two() { continue }
            let v: Vec<u64> = (0..BLK).map(|_| rng(&mut s)).collect();
            for nb in [1, 7, 8, 9, 63, 64, 1023, 1024] {
                let mut d = vec![0xC3u8; BLK * 8];
                res_pack_scalar(&v, w, nb, &mut d);
                let len = (nb * w as usize + 7) / 8;
                for j in 0..nb { assert_eq!(spec(&d, w as usize, j), v[j] & ((1u64 << w) - 1), "w {w} nb {nb} j {j}"); }
                // the bits past the last field are cleared and no byte after is touched
                for i in nb * w as usize..len * 8 { assert_eq!(bit(&d, i), 0, "w {w} nb {nb} bit {i}") }
                assert!(d[len..].iter().all(|&x| x == 0xC3), "w {w} nb {nb} wrote past {len}");
            }
        }
    }
    #[test] fn sum_and_count_agree_with_the_bit_stream() {
        let mut s = 0x1234567899AB1u64;
        for w in [0u8, 1, 2, 4, 8, 16, 32, 64] {
            let p: Vec<u8> = (0..BLK * w as usize / 8).map(|_| rng(&mut s) as u8).collect();
            for nb in [0, 1, 31, 32, 33, 1000, BLK] {
                let e = (0..nb).fold(0u64, |a, j| a.wrapping_add(spec(&p, w as usize, j)));
                assert_eq!(res_sum(&p, nb, w), e, "w {w} nb {nb}");
            }
        }
        let p: Vec<u8> = (0..BLK).map(|i| (i * 7) as u8).collect();
        for t in [0u64, 1, 100, 255, 256, 9999] { assert_eq!(res_count_lt8(&p, 1000, t), p[..1000].iter().filter(|&&x| (x as u64) < t).count()) }
        assert_eq!(res_count_lt8(&p, 1000, 256), 1000);
    }
    #[test] #[should_panic(expected = "res_pack asked for width 8, which is a power of two or over 64")]
    fn pack_refuses_a_power_of_two() { res_pack_scalar(&[0; BLK], 8, 1, &mut [0; 8]) }
}
