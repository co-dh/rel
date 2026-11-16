#![forbid(unsafe_code)]
//! coc.h:425, 429.

/// `Column.widthFor`: the bits a range needs, exactly -- any width 0..64.
pub fn width_for(range: u64) -> u8 { (64 - range.leading_zeros()) as u8 }

/// `Column.laneWidth`: the narrowest of 0/1/2/4/8/16/32/64 holding `w` bits.
pub fn lane_width(w: u8) -> u8 {
    match w { 0..=2 => w, 3..=4 => 4, 5..=8 => 8, 9..=16 => 16, 17..=32 => 32, _ => 64 }
}

/// coc.h `coc_popcount`: the set bits among the first `nbits` of `p` (`nbits.div_ceil(8)` bytes), LSB first inside a byte.
/// Bits above `nbits` in the last byte are ignored; no byte past it is read (a `Column.bits` payload is exactly that long).
pub fn popcount(p: &[u8], nbits: usize) -> usize {
    let (whole, rest) = (nbits >> 3, nbits & 7);
    let (words, tail) = p[..whole].as_chunks::<8>();
    let k = words.iter().map(|w| u64::from_ne_bytes(*w).count_ones() as usize).sum::<usize>()
        + tail.iter().map(|b| b.count_ones() as usize).sum::<usize>();
    if rest == 0 { k } else { k + (p[whole] & ((1u8 << rest) - 1)).count_ones() as usize }
}

#[cfg(test)]
mod tests {
    use super::popcount;
    #[test] fn popcount_ignores_bits_past_nbits() {
        let p = [0xffu8; 17];
        for n in 0..=136 { assert_eq!(popcount(&p[..n.div_ceil(8)], n), n, "n {n}") }
        assert_eq!(popcount(&[], 0), 0);
        assert_eq!(popcount(&[0b1010_1010, 0xff], 12), 4 + 4);
    }
}
