//! scan.rs's twelve Lean exports: the running scans, `avg`, `ema` and the moving-window family over a payload or an encoded
//! column, each an answer sized by `crate::scan` and filled by it.
#![deny(unsafe_code)]
use crate::lean::{O, SArr, export};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::lean::B, crate::scan};

#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::{blocks::Blocks, ffi::{Form, Sink}, ids, lean::{ctor, string}}, alloc::{string::String, vec, vec::Vec}};

/// `Enc.raw t n e` (Rel/Kernel/Value.lean), arm for arm: `None` where `raw` is `#[]`, a form `t` does not read. A dense,
/// bit or id payload short of `n` reads 0 past its end, as `bitsAt`, `bitAt` and `idAt` do.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub fn raw(t: u8, n: usize, e: B) -> Option<Vec<u64>> {
    let rd = |p: &[u8], o: usize, w: usize| (0..w).fold(0u64, |v, k| v | (p.get(o + k).copied().unwrap_or(0) as u64) << (8 * k));
    let (w, boolean) = (scan::qtype_width(t), t == scan::QT_BOOLEAN);
    match (e.tag(), w) {
        (0, Some(w)) if !boolean => { let p = e.field(0).bytes(); Some((0..n).map(|i| rd(p, i * w, w)).collect()) }
        (1, _) if boolean => { let p = e.field(0).bytes(); Some((0..n).map(|i| p.get(i >> 3).map_or(0, |b| (b >> (i & 7)) as u64 & 1)).collect()) }
        (3 | 4, Some(w)) if !boolean => {
            let (bl, mut v) = (Blocks::of(e, w, n, "qlean_k_scan"), Vec::with_capacity(n));
            let mut buf = vec![0u8; bl.blk() * w];
            for (b, _, nb) in bl.walk() { v.extend(bl.load_w(b, nb, w, &mut buf).chunks_exact(w).map(|c| rd(c, 0, w))) }
            Some(v)
        }
        (5, _) if t == scan::QT_SYMBOL => {
            let (p, lw) = (e.field(2).bytes(), ids::id_width(e.field(1).words().len().saturating_sub(1)));
            let cap = ids::ids_avail(p.len(), lw);
            Some((0..n).map(|i| if lw == 0 || i >= cap { 0 } else { ids::id_at(p, lw, i) as u64 }).collect())
        }
        _ => None,
    }
}

/// `Coc.encode 8` of the words `ws` as an `Enc.foR`, every cache filled: the answer of a design-§4 kernel at a
/// fixed-width type other than `boolean`, which `Enc.raw` reads back cut to that type's width.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub fn for_words(ws: &[u64]) -> O {
    let b: Vec<u8> = ws.iter().flat_map(|v| v.to_le_bytes()).collect();
    Sink::new(ws.len(), 8, Form::For).enc().answer(&Blocks::dense(&b, 8))
}

/// `kscan` (`crate::scan::kscan`) of the Lean list `es`.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kscan(op: u8, s: u8, t: u8, n: usize, seg: B, es: B) -> Result<O, String> {
    let (mut v, mut l) = (Vec::new(), es);
    while !l.is_scalar() { v.push(l.field(0)); l = l.field(1) }
    scan::kscan(op, s, t, n, seg, &v)
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

    /// `Kernel.kscan op s t n seg es` (Rel/Kernel/Scan.lean): `Except String Enc`, the error (tag 0) carrying the
    /// model's text, the answer (tag 1) an `Enc.bits` (tag 1) at a boolean `t` and an `Enc.foR` (tag 3) otherwise.
    fn qlean_k_scan(op: u8, s: u8, t: u8, n: usize, seg: B, es: B) -> O {
        match kscan(op, s, t, n, seg, es) { Ok(e) => ctor(1, [e], &[]), Err(m) => ctor(0, [string(&m)], &[]) }
    }










}
