//! asc.rs's Lean export, `Kernel.kasc` (Rel/Kernel/Asc.lean): each key column read as `Enc.raw` reads a `foR`, the
//! grade, and every answer column written as `Kernel.foRWords` (`qlean_coc_encode` at 8 bytes).
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::{asc, blocks::Blocks, c::pool, coc, codec, ffi::{Form, Sink}, lean::{B, O, boxed, ctor, string}},
    alloc::{format, string::String, vec, vec::Vec}};

/// `Ext.Enc.foR`'s constructor tag: the fourth of `Ext.Enc` (Rel/Kernel/Value.lean), after `bytes bits syms`.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
const FOR: u32 = 3;

/// `Kernel.ascCol`: the `m` raw words of the `foR` column `e` at the type `t` (cut to `t`'s width, as `Enc.raw` cuts
/// them) and their codes, or the model's error. A `foR` whose blocks hold fewer than `m` elements is refused here where
/// `raw` would read past them.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn col(t: u8, e: B, m: usize) -> Result<(Vec<u64>, Vec<u64>), String> {
    let (w, f, s) = asc::order(t).ok_or_else(|| format!("asc: type {t} has no fixed-width order"))?;
    if e.tag() != FOR { return Err(format!("asc: constructor {} is not foR", e.tag())) }
    // `raw` reads no word of a `foR` at `boolean` (1)
    if t == 1 { return if m == 0 { Ok((vec![], vec![])) } else { Err(format!("asc: a foR column reads 0 words at type {t}, not {m}")) } }
    let c = coc::view(e.field(0).bytes(), e.field(1).bytes(), m).map_err(|err| format!("asc: {err}"))?;
    if c.meta.n < m { return Err(format!("asc: a foR column's blocks hold {} elements, not {m}", c.meta.n)) }
    let mut x = vec![0i64; m];
    codec::decode(pool(), &c, &mut x);
    let mask = if w == 8 { u64::MAX } else { (1u64 << (8 * w)) - 1 };
    let x: Vec<u64> = x.into_iter().map(|v| v as u64 & mask).collect();
    let k = x.iter().map(|&v| asc::ord_key(w, f, s, v)).collect();
    Ok((x, k))
}

/// `Kernel.foRWords`: the words as an `Enc.foR` of 8-byte elements.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn for_words(ws: &[u64]) -> O {
    let b: Vec<u8> = ws.iter().flat_map(|v| v.to_le_bytes()).collect();
    let pr = Sink::new(ws.len(), 8, Form::For).answer(&Blocks::dense(&b, 8));
    let p = pr.borrow();
    ctor(FOR as u8, [p.field(0).to_owned(), p.field(1).to_owned()], &[])
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
    /// Spec: `kasc m es` reads each `(type, foR)` of `es` at `m` rows, sorts the rows stably and lexicographically by their
    /// order codes, and answers `Except String (List Enc × Enc)`: every column's words sorted and the permutation, each a
    /// `foR` of 8-byte elements; the first error in the order of `es` is the answer.
    fn qlean_k_asc(m: usize, es: B) -> O {
        match kasc(m, es) { Ok(o) => ctor(1, [o], &[]), Err(s) => ctor(0, [string(&s)], &[]) }
    }
}
