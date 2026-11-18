//! distinct.rs's Lean export, `Kernel.kdistinct` (Rel/Kernel/Distinct.lean): `foR` columns in, a `foR` answer out; the
//! columns are checked by `ffi::scatter::for_blocks` and read a block at a time by `distinct::blocks`, which writes the answer.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, string::String, vec::Vec}, crate::{distinct, exports::scatter::{except, for_blocks},
    lean::{B, O, ctor, nat}}};

/// `kdistinct`'s body in its order of failure: each of `es` left to right, its place in `es` naming it.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kdistinct(n: usize, es: B) -> Result<O, String> {
    let (mut cs, mut l) = (Vec::new(), es);
    while !l.is_scalar() { cs.push(for_blocks(&format!("distinct: es[{}]", cs.len()), n, l.field(0))?); l = l.field(1) }
    let (k, o) = distinct::blocks(&cs, n);
    Ok(ctor(0, [nat(k), o], &[]))
}

export! {
    /// Spec: `kdistinct n es` reads the `n` words of each column of `es` (each a standard `foR` at `n`) and answers
    /// `(k, o)`: `o` the `k` rows that start a run of equal rows, row 0 and each row some column changes at, as the
    /// `foR` `Coc.encode` writes at 8 bytes; the first column that does not read is the error.
    fn qlean_k_distinct(n: usize, es: B) -> O { except(kdistinct(n, es)) }
}
