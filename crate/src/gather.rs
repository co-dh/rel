#![forbid(unsafe_code)]
//! `gather`, the kernel that reads data at computed positions (design §4, `Kernel.kgather` in Rel/Kernel/Gather.lean):
//! `out[i] = e[ix[i]]`. The Lean body is the composition concat → asc → scan fill → scatter; this is its fused form, one
//! read per row (`Rel.Verify.gatherWords_eq`). An index `>= n` is an error naming it, never a fill.
use alloc::{format, string::String, vec::Vec};

/// `Kernel.gatherWords is es`: `es[is[i]]` for each row `i`; the first row whose index is not below `es.len()` is the
/// error.
pub fn words(is: &[u64], es: &[u64]) -> Result<Vec<u64>, String> {
    is.iter().enumerate().map(|(k, &i)| if i < es.len() as u64 { Ok(es[i as usize]) }
        else { Err(format!("gather: index {i} at row {k} is not below n = {}", es.len())) }).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test] fn reads_each_row() {
        assert_eq!(words(&[2, 0, 2, 3], &[10, 11, 12, 13]), Ok(vec![12, 10, 12, 13]));
    }
    #[test] fn index_past_n_is_an_error() {
        assert_eq!(words(&[1, 3, 9], &[1, 2, 3]), Err("gather: index 3 at row 1 is not below n = 3".into()));
        // above `usize::MAX` on a 32-bit target too: the `u64` comparison, not the cast, decides
        assert_eq!(words(&[u64::MAX], &[1]), Err(format!("gather: index {} at row 0 is not below n = 1", u64::MAX)));
    }
}
