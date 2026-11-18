//! asc.rs's Lean export, `Kernel.kasc` (Rel/Kernel/Asc.lean): each key column read through
//! `ffi::scatter::for_words_of`, the grade, and every answer column written by `ffi::scan::for_words`.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::{asc, exports::{scan::for_words, scatter::{except, for_words_of}}, lean::{B, O, boxed, ctor}},
    alloc::{format, string::String, vec::Vec}};

/// `Kernel.ascCol`: the `m` words of the `foR` column `e` and their codes at the type `t`, or the model's error.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn col(t: u8, e: B, m: usize) -> Result<(Vec<u64>, Vec<u64>), String> {
    let (w, f, s) = asc::order(t).ok_or_else(|| format!("asc: type {t} has no fixed-width order"))?;
    let x = for_words_of("asc", m, e)?;
    let k = x.iter().map(|&v| asc::ord_key(w, f, s, v)).collect();
    Ok((x, k))
}

/// `kasc`'s body in its order of failure: the columns left to right, then the grade and the answers.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kasc(m: usize, es: B) -> Result<O, String> {
    let (mut xs, mut ks, mut l) = (Vec::new(), Vec::new(), es);
    while !l.is_scalar() {
        let e = l.field(0);
        let (x, k) = col(e.field(0).unbox() as u8, e.field(1), m)?;
        xs.push(x);
        ks.push(k);
        l = l.field(1);
    }
    let p = asc::grade(&ks, m);
    // the `List Enc` of sorted columns, built from its end
    let vs = xs.iter().rev().fold(boxed(0), |vs, x| ctor(1, [for_words(&p.iter().map(|&i| x[i]).collect::<Vec<_>>()), vs], &[]));
    Ok(ctor(0, [vs, for_words(&p.iter().map(|&i| i as u64).collect::<Vec<_>>())], &[]))
}

export! {
    /// Spec: `kasc m es` reads the `m` words of each `(type, foR)` of `es` (each `foR`, its layout whole), sorts the rows
    /// stably and lexicographically by their order codes at their types, and answers `Except String (List Enc × Enc)`:
    /// every column's words sorted and the permutation, each as `Coc.encodeAt lgEnc 8` writes it; the first error in
    /// the order of `es` is the answer.
    fn qlean_k_asc(m: usize, es: B) -> O { except(kasc(m, es)) }
}
