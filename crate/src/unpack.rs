#![forbid(unsafe_code)]
//! coc.rs, the scalar spec of every decode.

/// `W`-bit residuals of the block `p` into `L`-byte lanes of `out`, eight to a group of `W` bytes.
pub fn lanes_of<const L: usize>(p: &[u8], w: usize, nb: usize, out: &mut [u8]) {
    for g in 0..nb.div_ceil(8) {
        // the last group can reach past the block's bytes: read a zero-padded copy (the window is 16 bytes over)
        let mut t = [0u8; 64 + 16];
        let q: &[u8] = match p.get(g * w..g * w + w + 16) {
            Some(q) if g * w + w + 9 <= p.len() => q,
            _ => { let e = p.len().min(g * w + w); t[..e - g * w].copy_from_slice(&p[g * w..e]); &t }
        };
        for k in 0..8 {
            let (bit, i) = (k * w, g * 8 + k);
            let sh = bit & 7;
            let mut v = u64::from_le_bytes(q[bit >> 3..(bit >> 3) + 8].try_into().unwrap()) >> sh;
            if sh + w > 64 { v |= (q[(bit >> 3) + 8] as u64) << (64 - sh) }
            v &= (1u64 << w) - 1;
            out[i * L..(i + 1) * L].copy_from_slice(&v.to_le_bytes()[..L]);
        }
    }
}

/// out.len() == 8 * (block size); a power-of-two width or one over 64 is a bug, as in C, and aborts.
pub fn res_unpack_scalar(p: &[u8], w: u8, nb: usize, out: &mut [u8]) {
    let w = w as usize;
    match w {
        3 | 5 | 6 | 7 => lanes_of::<1>(p, w, nb, out),
        9..=15 => lanes_of::<2>(p, w, nb, out),
        17..=31 => lanes_of::<4>(p, w, nb, out),
        33..=63 => lanes_of::<8>(p, w, nb, out),
        _ => panic!("qlean: res_unpack asked for width {w}, which is a power of two or over 64"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BLK;
    // `unpack.in`: FNV-1a of the first nb * lane bytes C's res_unpack_scalar wrote, by [width - 1][nb index]
    // (testdata/drv.c (deleted; in git history) dumped it); 0 at a width C refuses.
    const WANT: [[u64; 4]; 64] = include!("../../testdata/unpack.in");
    fn fnv(p: &[u8]) -> u64 { p.iter().fold(0xcbf29ce484222325, |h, &b| (h ^ b as u64).wrapping_mul(0x100000001b3)) }
    #[test] fn every_width_against_c() {
        for w in 3..64u8 {
            if w.is_power_of_two() { continue }
            let mut s = (w as u64).wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
            let p: Vec<u8> = (0..BLK * w as usize / 8).map(|_| {
                s ^= s << 13; s ^= s >> 7; s ^= s << 17; (s >> 32) as u8
            }).collect();
            let l = if w <= 8 { 1 } else if w <= 16 { 2 } else if w <= 32 { 4 } else { 8 };
            for (k, nb) in [1, 7, 1023, 1024].into_iter().enumerate() {
                let mut out = vec![0xAAu8; BLK * 8];
                res_unpack_scalar(&p, w, nb, &mut out);
                assert_eq!(fnv(&out[..nb * l]), WANT[w as usize - 1][k], "w {w} nb {nb}");
                crate::simd::res_unpack(&p, w, nb, &mut out);
                assert_eq!(fnv(&out[..nb * l]), WANT[w as usize - 1][k], "simd w {w} nb {nb}");
            }
        }
    }
    #[test] fn powers_of_two_and_over_64_are_refused() {
        for w in [1u8, 2, 4, 8, 16, 32, 64, 65, 0] {
            let r = std::panic::catch_unwind(|| res_unpack_scalar(&[0; BLK * 8], w, 8, &mut [0; BLK * 8]));
            assert!(r.is_err(), "w {w}");
        }
    }
    #[test] fn short_block_is_read_zero_padded_not_past_its_end() {
        // 7 bytes hold one 7-bit group of 8 residuals only up to the buffer's end; nothing past it is read
        let mut out = vec![0u8; BLK * 8];
        res_unpack_scalar(&[0xFF; 7], 7, 8, &mut out);
        assert_eq!(&out[..8], &[0x7F; 8]);
    }
}
