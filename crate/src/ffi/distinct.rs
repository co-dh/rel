//! distinct.rs's Lean export, `Kernel.kdistinct` (Rel/Kernel/Distinct.lean): `foR` columns in, a `foR` answer out.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, string::String, vec, vec::Vec}, crate::{c::pool, codec, coc, distinct, ffi::Form,
    lean::{B, O, SArr, ctor, nat, string}}, super::coc::encode};

/// `Ext.Enc.foR`'s constructor tag: the fourth of `Ext.Enc` (Rel/Kernel/Value.lean), after `bytes bits syms`.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
const FOR: u8 = 3;

/// `Kernel.foRWords`: the `n` words of a `foR` column whose layout `Coc::std` (Lean's `Coc.foRStd`) accepts at `n`.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn words(what: &str, n: usize, e: B) -> Result<Vec<u64>, String> {
    if e.tag() != FOR as u32 { return Err(format!("{what}: constructor {} is not foR", e.tag())) }
    let c = coc::view(e.field(0).bytes(), e.field(1).bytes(), n).ok().filter(|c| c.std(n))
        .ok_or_else(|| format!("{what}: not a standard foR layout of {n} elements"))?;
    let mut o = vec![0u64; n];
    codec::decode(pool(), &c, &mut o);
    Ok(o)
}

/// `kdistinct`'s body in its order of failure: each of `es` left to right, its place in `es` naming it.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kdistinct(n: usize, es: B) -> Result<O, String> {
    let (mut cs, mut l) = (Vec::new(), es);
    while !l.is_scalar() { cs.push(words(&format!("distinct: es[{}]", cs.len()), n, l.field(0))?); l = l.field(1) }
    let o = distinct::words(&cs, n);
    let mut a = SArr::new(1, 8 * o.len());
    a.bytes_mut().chunks_exact_mut(8).zip(&o).for_each(|(c, w)| c.copy_from_slice(&w.to_le_bytes()));
    // `qlean_coc_encode`'s `(metadata, pack)`, its fields moved into `Enc.foR`
    let a: O = a.into();
    let p = encode(a.borrow(), 8, Form::For, false);
    let (md, pk) = (p.borrow().field(0).to_owned(), p.borrow().field(1).to_owned());
    Ok(ctor(0, [nat(o.len()), ctor(FOR, [md, pk], &[])], &[]))
}

export! {
    /// Spec: `kdistinct n es` reads the `n` words of each column of `es` (each a standard `foR` at `n`) and answers
    /// `(k, o)`: `o` the `k` rows that start a run of equal rows, row 0 and each row some column changes at, as the
    /// `foR` `Coc.encode` writes at 8 bytes; the first column that does not read is the error.
    fn qlean_k_distinct(n: usize, es: B) -> O {
        match kdistinct(n, es) { Ok(o) => ctor(1, [o], &[]), Err(e) => ctor(0, [string(&e)], &[]) }
    }
}
