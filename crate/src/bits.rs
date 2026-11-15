#![forbid(unsafe_code)]
//! coc.h:425, 429.

/// `Column.widthFor`: the bits a range needs, exactly -- any width 0..64.
pub fn width_for(range: u64) -> u8 { (64 - range.leading_zeros()) as u8 }

/// `Column.laneWidth`: the narrowest of 0/1/2/4/8/16/32/64 holding `w` bits.
pub fn lane_width(w: u8) -> u8 {
    match w { 0..=2 => w, 3..=4 => 4, 5..=8 => 8, 9..=16 => 16, 17..=32 => 32, _ => 64 }
}
