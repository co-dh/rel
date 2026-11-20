#![forbid(unsafe_code)]
//! coc.rs, 429.

/// `Column.widthFor`: the bits a range needs, exactly -- any width 0..64.
pub fn width_for(range: u64) -> u8 { (64 - range.leading_zeros()) as u8 }

/// `Column.laneWidth`: the narrowest of 0/1/2/4/8/16/32/64 holding `w` bits.
pub fn lane_width(w: u8) -> u8 {
    match w { 0..=2 => w, 3..=4 => 4, 5..=8 => 8, 9..=16 => 16, 17..=32 => 32, _ => 64 }
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
