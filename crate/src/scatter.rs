#![forbid(unsafe_code)]
//! `scatter`, the primitive that writes data to computed positions (design §4, `Kernel.kscatter` in
//! Rel/Kernel/Scatter.lean): `out[ix[k]] = e[k]` over `n` cells that start as `fill`. An index `>= n` is an error naming
//! it, never dropped; a composition that discards a row sends it to a spare cell and cuts that cell off (WHERE,
//! doc/rel-kernels.md).
use alloc::{format, string::String, vec, vec::Vec};
use crate::DEFAULT_LG;
use crate::c::Runner;
use crate::pack::{self, Pack, Packed};

/// `Kernel.packedWords` past its constructor test: the `m` raw 64-bit words of `p`, or `what` and its layout error.
pub fn unpack(run: Runner, what: &str, p: &Packed, m: usize) -> Result<Vec<u64>, String> {
    let mut b = vec![0u8; 8 * m];
    pack::decode_w(run, p, m, 8, &mut b).map_err(|e| format!("{what}: {e}"))?;
    Ok(b.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().expect("scatter: chunks_exact(8) yields 8 bytes"))).collect())
}

/// `Kernel.scatterWords is es n fill`: rows in order, so the last row naming a cell is the one it keeps; the first row
/// whose index is not below `n` is the error.
pub fn words(is: &[u64], es: &[u64], n: usize, fill: u64) -> Result<Vec<u64>, String> {
    let mut o = vec![fill; n];
    for (k, (&i, &x)) in is.iter().zip(es).enumerate() {
        if i >= n as u64 { return Err(format!("scatter: index {i} at row {k} is not below n = {n}")) }
        o[i as usize] = x;
    }
    Ok(o)
}

/// `kscatter` on decoded words: `words`, encoded as `Coc.packedOf lgEnc 8` (`pack::encode` at 8 bytes).
pub fn scatter(run: Runner, is: &[u64], es: &[u64], n: usize, fill: u64) -> Result<Pack, String> {
    let o = words(is, es, n, fill)?;
    pack::encode_w(run, DEFAULT_LG as u8, &|v: &mut [i64], lo: usize| v.iter_mut().enumerate().for_each(|(k, x)| *x = o[lo + k] as i64), n, 8)
        .map_err(|e| format!("scatter: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c::qlean_run_c as run;

    #[test] fn last_write_wins_and_fill_stays() {
        assert_eq!(words(&[2, 0, 2], &[10, 11, 12], 4, 7), Ok(vec![11, 7, 12, 7]));
    }
    #[test] fn index_past_n_is_an_error() {
        assert_eq!(words(&[1, 5, 9], &[1, 2, 3], 3, 0), Err("scatter: index 5 at row 1 is not below n = 3".into()));
    }
    #[test] fn round_trip_through_pack() {
        let p = scatter(run, &[3, 1], &[u64::MAX, 40], 5, 9).unwrap();
        assert_eq!(unpack(run, "out", &p.view(), 5), Ok(vec![9, 40, 9, u64::MAX, 9]));
        // read at a length its one block of 2^10 does not cover: the layout error, prefixed with what was read
        assert_eq!(unpack(run, "ix", &p.view(), 2000), Err("ix: packed: 1 widths for 2 blocks of 2^10 at n = 2000".into()));
    }
}
