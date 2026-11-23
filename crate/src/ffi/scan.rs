//! scan.rs's twelve Lean exports: the running scans, `avg`, `ema` and the moving-window family over a payload or an encoded
//! column, each an answer sized by `crate::scan` and filled by it.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::lean::{B, O}, crate::scan};

#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::lean::{box_u64, boxed, ctor, string}, alloc::{string::String, vec::Vec}};


/// The elements of a Lean `List`.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn list(mut l: B) -> Vec<B> {
    let mut v = Vec::new();
    while !l.is_scalar() { v.push(l.field(0)); l = l.field(1) }
    v
}

/// `kscan` (`crate::scan::kscan`) of the Lean `Option Enc` `seg` (`none` the scalar 0, `some` tag 1), the list `es`,
/// the list `es` of `(USize × Enc)`, and the chains `pre`, `post`: lists of pairs (tag 0) of an `Op` and a boxed `UInt64`.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kscan(op: u8, rev: bool, s: u8, t: u8, n: usize, seg: B, es: B, pre: B, post: B) -> Result<(O, Option<u64>), String> {
    let steps = |l: B| list(l).into_iter().map(|p| (scan::op_code(p.field(0)), p.field(1).unbox_u64())).collect::<Vec<_>>();
    let seg = if seg.is_scalar() { None } else { Some(seg.field(0)) };
    // each source a pair (tag 0) of its row count, a boxed `USize` (the 64-bit layout of a boxed `UInt64`), and its column
    let es = list(es).into_iter().map(|p| (p.field(0).unbox_u64() as usize, p.field(1))).collect::<Vec<_>>();
    scan::kscan(op, rev, s, t, n, seg, &es, &steps(pre), &steps(post))
}


export! {


    /// `Kernel.kscan op rev s t n seg es pre post` (Rel/Kernel/Scan.lean): `seg` an `Option Enc` (`none` the scalar 0,
    /// every row its own segment), `pre`/`post` lists of `(Op × UInt64)` pairs, each `UInt64` boxed.
    /// `Except String (Enc × Option UInt64)`, the error (tag 0)
    /// carrying the model's text, the answer (tag 1) a pair (tag 0) of an `Enc.foR` (tag 3) at every `t`, a boolean one
    /// a `foR` of `u1`, and the fold result: `none` (the scalar 0) at `n = 0`, else `some` (tag 1) of a boxed `UInt64`.
    fn qlean_k_scan(op: B, rev: u8, s: u8, t: u8, n: usize, seg: B, es: B, pre: B, post: B) -> O {
        match kscan(scan::op_code(op), rev != 0, s, t, n, seg, es, pre, post) {
            Ok((e, v)) => ctor(1, [ctor(0, [e, v.map_or_else(|| boxed(0), |v| ctor(1, [box_u64(v)], &[]))], &[])], &[]),
            Err(m) => ctor(0, [string(&m)], &[]),
        }
    }










}
