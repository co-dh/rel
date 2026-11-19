//! scan.rs's twelve Lean exports: the running scans, `avg`, `ema` and the moving-window family over a payload or an encoded
//! column, each an answer sized by `crate::scan` and filled by it.
#![deny(unsafe_code)]
use crate::lean::{O, SArr, export};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::lean::B, crate::scan};

#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::{blocks::Blocks, ffi::{Form, Sink}, lean::{box_u64, boxed, ctor, string}}, alloc::{string::String, vec::Vec}};

/// `Coc.encode 8` of the words `ws` as an `Enc.foR`, every cache filled: the answer of a design-§4 kernel at a
/// fixed-width type other than `boolean`, which `Enc.raw` reads back cut to that type's width.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub fn for_words(ws: &[u64]) -> O {
    let b: Vec<u8> = ws.iter().flat_map(|v| v.to_le_bytes()).collect();
    Sink::new(ws.len(), 8, Form::For).enc().answer(&Blocks::dense(&b, 8))
}

/// `kscan` (`crate::scan::kscan`) of the Lean list `es`.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kscan(op: u8, rev: bool, s: u8, t: u8, n: usize, seg: B, es: B) -> Result<(O, Option<u64>), String> {
    let (mut v, mut l) = (Vec::new(), es);
    while !l.is_scalar() { v.push(l.field(0)); l = l.field(1) }
    scan::kscan(op, rev, s, t, n, seg, &v)
}

/// A fresh answer of `n` bytes, filled by `fill`.
pub fn answer(n: usize, fill: impl FnOnce(&mut [u8])) -> O {
    let mut o = SArr::new(1, n);
    fill(o.bytes_mut());
    o.into()
}

export! {

    /// The ByteArray of `n` elements at `sc_out_width` whose ith element is the accumulator after element i of the fold of
    /// `Verb` (QLean/Kernel/Scan.lean). Where that fold is the identity the answer is the argument object, refcounted.
    fn qlean_scan(op: u8, kind: u8, n: usize, a: B) -> O {
        let p = a.bytes();
        if scan::col_same(op, kind, n, p) { return a.to_owned() }
        answer(scan::col_len(op, kind, n, p.len()), |o| scan::col(op, kind, n, p, o))
    }

    /// `Kernel.kscan op rev s t n seg es` (Rel/Kernel/Scan.lean): `Except String (Enc × Option UInt64)`, the error (tag 0)
    /// carrying the model's text, the answer (tag 1) a pair (tag 0) of an `Enc.foR` (tag 3) at every `t`, a boolean one
    /// a `foR` of `u1`, and the fold result: `none` (the scalar 0) at `n = 0`, else `some` (tag 1) of a boxed `UInt64`.
    fn qlean_k_scan(op: u8, rev: u8, s: u8, t: u8, n: usize, seg: B, es: B) -> O {
        match kscan(op, rev != 0, s, t, n, seg, es) {
            Ok((e, v)) => ctor(1, [ctor(0, [e, v.map_or_else(|| boxed(0), |v| ctor(1, [box_u64(v)], &[]))], &[])], &[]),
            Err(m) => ctor(0, [string(&m)], &[]),
        }
    }










}
