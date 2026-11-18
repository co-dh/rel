#![forbid(unsafe_code)]
//! `scatter`, the primitive that writes data to computed positions (design §4, `Kernel.kscatter` in
//! Rel/Kernel/Scatter.lean): `out[ix[k]] = e[k]` over `n` cells that start as `fill`. An index `>= n` is an error naming
//! it, never dropped; a composition that discards a row sends it to a spare cell and cuts that cell off (WHERE,
//! doc/rel-kernels.md). Its `foR` arguments and answer are read and written in ffi/scatter.rs through coc's codec.
use alloc::{format, string::String, vec, vec::Vec};

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test] fn last_write_wins_and_fill_stays() {
        assert_eq!(words(&[2, 0, 2], &[10, 11, 12], 4, 7), Ok(vec![11, 7, 12, 7]));
    }
    #[test] fn index_past_n_is_an_error() {
        assert_eq!(words(&[1, 5, 9], &[1, 2, 3], 3, 0), Err("scatter: index 5 at row 1 is not below n = 3".into()));
    }
}
