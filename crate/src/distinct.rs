#![forbid(unsafe_code)]
//! `distinct` (design §4, `Kernel.kdistinct` in Rel/Kernel/Distinct.lean): on rows whose equal ones are contiguous,
//! the position of the first row of each run. The Lean body is `scan` (adjacent compare) then `scatter` (compact);
//! this is the fused form, one pass that compares each row with the one before and appends the starts.
use alloc::vec::Vec;

/// `Kernel.distinctWords n cs`: the rows that start a run, row 0 and each row some column of `cs` changes at.
pub fn words(cs: &[Vec<u64>], n: usize) -> Vec<u64> {
    (0..n).filter(|&i| i == 0 || cs.iter().any(|c| c[i] != c[i - 1])).map(|i| i as u64).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test] fn a_run_starts_where_any_column_changes() {
        // rows (1,0) (1,0) (2,0) (2,1) (2,1): runs start at 0, 2, 3
        assert_eq!(words(&[vec![1, 1, 2, 2, 2], vec![0, 0, 0, 1, 1]], 5), vec![0, 2, 3]);
        // no column: every row is the empty row, one run; no row: no run
        assert_eq!(words(&[], 3), vec![0]);
        assert_eq!(words(&[vec![]], 0), Vec::<u64>::new());
    }
}
