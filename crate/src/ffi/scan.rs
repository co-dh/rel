//! scan.rs's twelve Lean exports: the running scans, `avg`, `ema` and the moving-window family over a payload or an encoded
//! column, each an answer sized by `crate::scan` and filled by it.
#![deny(unsafe_code)]
use crate::lean::{B, O, SArr, export};
use crate::scan;

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










}
