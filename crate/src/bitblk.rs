#![forbid(unsafe_code)]
//! A coc block of width 1, base 0 and no patch is a bit vector: its `blk / 8` payload bytes are the `Column.bits`
//! encoding of its rows, LSB first. The coc kernels ask `Coc::bit_blk` once per block, outside the element loops, and run
//! the `bits.rs` / `search.rs` word algorithms on the payload instead of unpacking it (G3: bits folded into coc).
use crate::coc::Coc;
use crate::cocops::{EQ, GT, LE, LT, NE};

/// word `i` of a payload (8-byte aligned in length for every block: `blk * 1 / 8` is a multiple of 8)
pub fn word(p: &[u8], i: usize) -> u64 { u64::from_le_bytes(p[i * 8..i * 8 + 8].try_into().expect("8 bytes")) }
/// the bits of word `i` that are rows of an `nb`-row block
pub fn live(nb: usize, i: usize) -> u64 { let r = nb - (i << 6).min(nb); if r >= 64 { !0 } else { !0 >> (64 - r) } }

impl<'a> Coc<'a> {
    /// Block `b`'s payload when the block is a bit vector: width 1, frame 0 (base and frame delta), no patch.
    pub fn bit_blk(&self, b: usize) -> Option<&'a [u8]> {
        let m = &self.meta;
        if m.width[b] != 1 || self.frame(b) != 0 || self.blk_nexc(b) != 0 { return None }
        let at = m.off[b] as usize;
        Some(&self.pack[at..at + m.blk() / 8])
    }
}

/// `x op v` of a bit block into the zeroed words `out`: each of the two values 0, 1 passes or not, so the answer is
/// none, all, the bits or their complement.
pub fn mask_cmp(p: &[u8], nb: usize, op: i32, v: i64, out: &mut [u64]) {
    let t = |x: i64| match op { EQ => x == v, NE => x != v, LT => x < v, LE => x <= v, GT => x > v, _ => x >= v };
    let inv = match (t(0), t(1)) { (false, false) => return, (true, true) => !0u64, (false, true) => 0, (true, false) => !0u64 };
    let fill = t(0) && t(1);
    for (i, o) in out[..nb.div_ceil(64)].iter_mut().enumerate() {
        *o = if fill { live(nb, i) } else { (word(p, i) ^ inv) & live(nb, i) }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
}

/// Coc-level checks and the G3a measurement: a width-1, base-0 column built by hand against the `_bits` kernels.
#[cfg(test)]
mod coc_tests {
    use crate::coc::{view, Coc};
    use crate::cocops::{EQ, GE, GT, LE, LT, NE};
    use crate::{bits, codec, pod};


}
