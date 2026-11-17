#![forbid(unsafe_code)]
//! coc.rs, 429.

/// `Column.widthFor`: the bits a range needs, exactly -- any width 0..64.
pub fn width_for(range: u64) -> u8 { (64 - range.leading_zeros()) as u8 }

/// `Column.laneWidth`: the narrowest of 0/1/2/4/8/16/32/64 holding `w` bits.
pub fn lane_width(w: u8) -> u8 {
    match w { 0..=2 => w, 3..=4 => 4, 5..=8 => 8, 9..=16 => 16, 17..=32 => 32, _ => 64 }
}

/// coc.rs `coc_popcount`: the set bits among the first `nbits` of `p` (`nbits.div_ceil(8)` bytes), LSB first inside a byte.
/// Bits above `nbits` in the last byte are ignored; no byte past it is read (a `Column.bits` payload is exactly that long).
pub fn popcount(p: &[u8], nbits: usize) -> usize {
    let (whole, rest) = (nbits >> 3, nbits & 7);
    let (words, tail) = p[..whole].as_chunks::<8>();
    let k = words.iter().map(|w| u64::from_ne_bytes(*w).count_ones() as usize).sum::<usize>()
        + tail.iter().map(|b| b.count_ones() as usize).sum::<usize>();
    if rest == 0 { k } else { k + (p[whole] & ((1u8 << rest) - 1)).count_ones() as usize }
}

/// coc.rs `qlean_coc_some_bit`: whether some bit among the first `n` (cut to the `8 * p.len()` there are) is `set`, else
/// whether some is clear. Both stop at the 64-byte block that decides, and only the last byte is masked to the bits that exist.
pub fn some_bit(set: bool, p: &[u8], n: usize) -> bool {
    let n = n.min(p.len() * 8);
    let (whole, rest) = (n / 8, n % 8);
    // 64 bytes folded at a time with no exit inside, which vectorises where a per-byte early exit does not; the width test
    // is outside the loops
    let (blocks, tail) = p[..whole].as_chunks::<64>();
    let hit = if set { blocks.iter().any(|c| c.iter().fold(0u8, |a, &b| a | b) != 0) || tail.iter().any(|&b| b != 0) }
              else { blocks.iter().any(|c| c.iter().fold(0xffu8, |a, &b| a & b) != 0xff) || tail.iter().any(|&b| b != 0xff) };
    if hit { return true }
    let mask = ((1u16 << rest) - 1) as u8;
    rest != 0 && if set { p[whole] & mask != 0 } else { p[whole] & mask != mask }
}

#[cfg(test)]
mod tests {
    use super::{popcount, some_bit};
    #[test] fn popcount_ignores_bits_past_nbits() {
        let p = [0xffu8; 17];
        for n in 0..=136usize { assert_eq!(popcount(&p[..n.div_ceil(8)], n), n, "n {n}") }
        assert_eq!(popcount(&[], 0), 0);
        assert_eq!(popcount(&[0b1010_1010, 0xff], 12), 4 + 4);
    }
    // against the bit-by-bit definition, every length and a few patterns, `n` past the array included
    #[test] fn some_bit_matches_the_bitwise_definition() {
        for pat in [0x00u8, 0xff, 0x01, 0x80, 0xf0, 0x7f, 0xfe] {
            for len in [0usize, 1, 2, 3, 63, 64, 65, 130] {
                let p = alloc::vec![pat; len];
                for n in 0..=len * 8 + 9 {
                    let bit = |i: usize| p[i / 8] >> (i % 8) & 1 == 1;
                    let m = n.min(len * 8);
                    for set in [false, true] { assert_eq!(some_bit(set, &p, n), (0..m).any(|i| bit(i) == set), "pat {pat:#x} len {len} n {n} set {set}") }
                }
            }
        }
    }
}
