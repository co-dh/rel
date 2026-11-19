//! seen.rs's Lean export, `Kernel.kseen` (Rel/Kernel/Seen.lean): `(type, foR)` key columns in, read as `kasc` reads them
//! (`ascCol`: `asc::order`, `for_view`), and the two `foR` answers `seen::blocks` writes.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, string::String, vec::Vec}, crate::{asc, seen, exports::{asc::key, scatter::except},
    lean::{B, O, ctor, nat}}};

/// `kseen`'s body in its order of failure: each of `es` left to right, `ascCol`'s checks (the type, then the layout),
/// its place in `es` naming it; then the rows' order. A `pos` key ascends with no ties, so only the keys before the
/// first one order the rows, and every row is its own group.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kseen(n: usize, es: B) -> Result<O, String> {
    // `pre`: the keys before the first `pos` column
    let (mut ks, mut pre, mut i, mut l) = (Vec::new(), None, 0usize, es);
    while !l.is_scalar() {
        let k = key(n, l.field(0)).map_err(|s| format!("seen: es[{i}]: {s}"))?.0;
        if matches!(k, asc::Col::Pos) { pre.get_or_insert(ks.len()); }
        ks.push(k);
        (i, l) = (i + 1, l.field(1));
    }
    let (k, g, f) = seen::blocks(&ks[..pre.unwrap_or(ks.len())], n, pre.is_some())?;
    Ok(ctor(0, [nat(k), ctor(0, [g, f], &[])], &[]))
}

export! {
    /// Spec: `kseen n es` reads the `n` words of each `(type, foR)` of `es` as `kasc` does and answers `(k, g, first)`:
    /// the number of distinct rows under the order codes' equality, each row's group numbered by first occurrence, and
    /// each group's first row, both as `Coc.encode 8` writes them; the first column that does not read is the error.
    /// The rows must be in `kasc` order (callers run `kasc` first): the first row out of order is the error too.
    fn qlean_k_seen(n: usize, es: B) -> O { except(kseen(n, es)) }
}
