//! distinct.rs's Lean export, `Kernel.kdistinct` (Rel/Kernel/Distinct.lean): `foR` columns in, a `foR` answer out; the
//! columns are read by `ffi::scatter::for_words_of`, the answer written by `ffi::scan::for_words`.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, string::String, vec::Vec}, crate::{distinct, exports::{scan::for_words, scatter::{except, for_words_of}},
    lean::{B, O, ctor, nat}}};

/// `kdistinct`'s body in its order of failure: each of `es` left to right, its place in `es` naming it.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kdistinct(n: usize, es: B) -> Result<O, String> {
    let (mut cs, mut l) = (Vec::new(), es);
    while !l.is_scalar() { cs.push(for_words_of(&format!("distinct: es[{}]", cs.len()), n, l.field(0))?); l = l.field(1) }
    let o = distinct::words(&cs, n);
    Ok(ctor(0, [nat(o.len()), for_words(&o)], &[]))
}

export! {
    /// Spec: `kdistinct n es` reads the `n` words of each column of `es` (each a standard `foR` at `n`) and answers
    /// `(k, o)`: `o` the `k` rows that start a run of equal rows, row 0 and each row some column changes at, as the
    /// `foR` `Coc.encode` writes at 8 bytes; the first column that does not read is the error.
    fn qlean_k_distinct(n: usize, es: B) -> O { except(kdistinct(n, es)) }
}
