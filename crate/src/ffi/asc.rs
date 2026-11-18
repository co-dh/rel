//! asc.rs's Lean export, `Kernel.kasc` (Rel/Kernel/Asc.lean): each key column taken as its encoded blocks
//! (`ffi::scatter::coc_of`), the grade (`asc::grade`), and every answer column written a block at a time through a
//! `Sink`, the encoder's own block step, so the bytes are `Coc.encode`'s.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::{asc, blocks::Blocks, c::pool, exports::scatter::{coc_of, except}, ffi::{Form, Sink}, lean::{B, O, boxed, ctor}, pod},
    alloc::{format, string::String, vec::Vec}};

/// `kasc`'s body in its order of failure: the columns left to right (`ascCol`: the type, then the layout), then the
/// grade and the answers. Where the rows are already in order (`None`) each column is its own blocks re-encoded and
/// the permutation `til m`; else answer row `i` is input row `p[i]`, read at its address (`Coc::get_w`).
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kasc(m: usize, es: B) -> Result<O, String> {
    let (mut ks, mut l) = (Vec::new(), es);
    while !l.is_scalar() {
        let (e, t) = (l.field(0), l.field(0).field(0).unbox() as u8);
        let o = asc::order(t).ok_or_else(|| format!("asc: type {t} has no fixed-width order"))?;
        ks.push(asc::Key::new(coc_of("asc", m, e.field(1))?, o));
        l = l.field(1);
    }
    let p = asc::grade(pool(), &ks, m);
    let sink = || Sink::new(m, 8, Form::For).enc();
    let col = |k: &asc::Key| match &p {
        None => sink().answer(&Blocks::from(k.c)),
        Some(p) => {
            let uw = k.c.one_width();
            sink().answer(&|buf: &mut [i64], i0: usize| for (o, &i) in buf.iter_mut().zip(&p[i0..]) { *o = k.c.get_w(uw, i as usize) })
        }
    };
    // the `List Enc` of sorted columns, built from its end
    let vs = ks.iter().rev().fold(boxed(0), |vs, k| ctor(1, [col(k), vs], &[]));
    let pe = match &p {
        None => sink().answer(&|buf: &mut [i64], i0: usize| for (j, o) in buf.iter_mut().enumerate() { *o = (i0 + j) as i64 }),
        Some(p) => sink().answer(&Blocks::dense(pod::bytes(p), 8)),
    };
    Ok(ctor(0, [vs, pe], &[]))
}

export! {
    /// Spec: `kasc m es` reads the `m` words of each `(type, foR)` of `es` (each `foR`, its layout whole), sorts the rows
    /// stably and lexicographically by their order codes at their types, and answers `Except String (List Enc × Enc)`:
    /// every column's words sorted and the permutation, each as `Coc.encodeAt lgEnc 8` writes it; the first error in
    /// the order of `es` is the answer.
    fn qlean_k_asc(m: usize, es: B) -> O { except(kasc(m, es)) }
}
