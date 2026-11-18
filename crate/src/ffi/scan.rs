//! scan.rs's twelve Lean exports: the running scans, `avg`, `ema` and the moving-window family over a payload or an encoded
//! column, each an answer sized by `crate::scan` and filled by it.
#![deny(unsafe_code)]
use crate::lean::{O, SArr, export};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::lean::B, crate::scan};

#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::{blocks::Blocks, c, ids, lean::{ctor, string}, pack}, alloc::{format, string::String, vec, vec::Vec}};

/// `Enc.raw t n e` (Rel/Kernel/Value.lean), arm for arm: `None` where `raw` is `#[]`, a form `t` does not read or a
/// `packed` layout `Enc.packedErr` refuses. A dense, bit or id payload short of `n` reads 0 past its end, as `bitsAt`,
/// `bitAt` and `idAt` do.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn raw(t: u8, n: usize, e: B) -> Option<Vec<u64>> {
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
        (7, _) => {
            // `lg` is the one scalar, after the three ByteArray fields; a boolean word is its low bit
            let p = pack::Packed { lg: e.scalar_u8(0), bases: e.field(0).bytes(), widths: e.field(1).bytes(), payload: e.field(2).bytes() };
            let ww = if boolean { 1 } else { w.unwrap_or(8) };
            let mut o = vec![0u8; n * ww];
            pack::decode_w(c::pool(), &p, n, ww, &mut o).ok()?;
            Some(o.chunks_exact(ww).map(|c| if boolean { rd(c, 0, 1) & 1 } else { rd(c, 0, ww) }).collect())
        }
        _ => None,
    }
}

/// `kscan`'s body (Rel/Kernel/Scan.lean) in its order of failure: `seg`, each of `es` left to right, the rows, the width.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kscan(op: u8, s: u8, t: u8, n: usize, seg: B, es: B) -> Result<O, String> {
    // `None` is `raw`'s `#[]`, its size 0: `rawAll`'s test, not a read that failed
    let all = |t: u8, e: B| -> Result<Vec<u64>, String> {
        let v = raw(t, n, e).unwrap_or_default();
        if v.len() == n { Ok(v) } else { Err(format!("kscan: a column holds {} raw elements, not {n}", v.len())) }
    };
    let g = all(scan::QT_BOOLEAN, seg)?;
    let (mut cols, mut l) = (Vec::new(), es);
    while !l.is_scalar() { cols.push(all(s, l.field(0))?); l = l.field(1) }
    let Some((seed, xs)) = cols.split_first() else { return Err("kscan: es is empty; its first column is the seed".into()) };
    let out = scan::kscan_rows(op, &g, seed, xs)?;
    let w = scan::qtype_width(t).ok_or("kscan: the answer type has no fixed width")?;
    let p = scan::kscan_pack(if t == scan::QT_BOOLEAN { 1 } else { 8 * w }, &out);
    let mut a = SArr::new(1, p.len());
    a.bytes_mut().copy_from_slice(&p);
    Ok(ctor(if t == scan::QT_BOOLEAN { 1 } else { 0 }, [a.into()], &[]))
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
    /// model's text, the answer (tag 1) an `Enc.bits` (tag 1) at a boolean `t` and an `Enc.bytes` (tag 0) otherwise.
    fn qlean_k_scan(op: u8, s: u8, t: u8, n: usize, seg: B, es: B) -> O {
        match kscan(op, s, t, n, seg, es) { Ok(e) => ctor(1, [e], &[]), Err(m) => ctor(0, [string(&m)], &[]) }
    }










}
