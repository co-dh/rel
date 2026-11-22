//! csv.rs's Lean exports: the CSV reader and writer. `IO` externs (no world argument in Lean 4.28); a failure is an errno
//! the Lean side reports as the runtime's `IO.Error` for the path, or the model's refusal text after `{path}: `.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, string::String, vec::Vec}, core::sync::atomic::AtomicUsize,
     crate::{DEFAULT_LG, csv::{self, Col}, ffi::Sink, lean::{B, O, box_usize_o, boxed, ctor}, own::{self, Fail}, scan}};

/// The schema `CsvCols` (`List (String × CsvShape × QAtomicType × List String)`) as columns: each pair a ctor of two
/// fields, the enums `CsvShape` and `QAtomicType` boxed constructor indices.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn cols<'a>(mut l: B<'a>) -> Result<Vec<Col<'a>>, String> {
    let s = |o: B<'a>| core::str::from_utf8(o.str_bytes()).map_err(|e| format!("CsvCols: a column name that is not UTF-8: {e}"));
    let mut v = Vec::new();
    while !l.is_scalar() {
        let (c, sh) = (l.field(0), l.field(0).field(1));
        let rest = sh.field(1);
        let (mut ns, mut k) = (Vec::new(), rest.field(1));
        while !k.is_scalar() { ns.push(s(k.field(0))?); k = k.field(1) }
        v.push(Col { name: s(c.field(0))?, shape: sh.field(0).unbox() as u8, t: rest.field(0).unbox() as u8, names: ns });
        l = l.field(1);
    }
    Ok(v)
}

/// `Db.csvRead path cols`: the file mapped, then `csvWords`' checks in its order; each part of each column (`layout`'s)
/// goes to its own `Sink` a block at a time (`csv::fill` is the producer's step), so no column is ever held decoded.
/// `IO (USize × List (USize × Enc))`, each `Enc` a `foR` of 8-byte words, as `wordsFoR` builds, beside its count.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn read(path: B, cs: B) -> Result<O, Fail> {
    let m = csv::map(path.cstr())?;
    let b = m.as_ref().map_or(&[][..], |m| m.as_slice());
    let at = |e: String| Fail::User(format!("{}: {e}", String::from_utf8_lossy(path.str_bytes())));
    let cs = cols(cs).map_err(at)?;
    csv::schema(&cs).map_err(at)?;
    let lx = csv::lex(b, &cs, DEFAULT_LG).map_err(at)?;
    csv::header(&cs, &lx).map_err(at)?;
    let bad: Vec<AtomicUsize> = cs.iter().map(|_| AtomicUsize::new(usize::MAX)).collect();
    let mut es: Vec<O> = Vec::new();
    for (c, (col, bad)) in cs.iter().zip(&bad).enumerate() {
        for (part, k) in csv::counts(&lx, c, col).into_iter().enumerate() {
            let e = Sink::new(k, 8).enc().answer(&|buf: &mut [i64], lo: usize| csv::fill(b, &lx, c, col, part, lo, buf, bad));
            es.push(ctor(0, [box_usize_o(k), e], &[]));
        }
    }
    csv::refusal(b, &lx, &cs, &bad).map_err(at)?;
    if let Some(m) = m { m.unmap()? }
    Ok(ctor(0, [box_usize_o(lx.n), es.into_iter().rev().fold(boxed(0), |t, h| ctor(1, [h, t], &[]))], &[]))
}

/// `Db.csvWrite path cols n es`, in its body's order: the parent directories (`createDirAll`), the part count, each part
/// read as `rawAll` reads it at its count (`scan::raw_all`: any `Enc` form, a block at a time through `Col::load`, never
/// decoded whole; the null's values only counted, `CsvShape.atoms`), `csvText`'s schema refusals, then the rows
/// (`csv::write`). `IO Unit`.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn write(path: B, cs: B, n: usize, es: B) -> Result<O, Fail> {
    own::mkdirs(path.cstr())?;
    let at = |e: String| Fail::User(format!("{}: {e}", String::from_utf8_lossy(path.str_bytes())));
    let cs = cols(cs).map_err(at)?;
    let (mut v, mut l) = (Vec::new(), es);
    while !l.is_scalar() { v.push((l.field(0).field(0).usize_field(0), l.field(0).field(1))); l = l.field(1) }
    csv::arity(&cs, v.len()).map_err(at)?;
    // each part's atom, `CsvShape.atoms`: `None` for the null's values
    let ts = cs.iter().flat_map(|c| match c.shape {
        csv::SH_NULL => alloc::vec![Some(csv::QT_U1), Some(csv::QT_I64), Some(c.t), None],
        csv::SH_TEXT => alloc::vec![Some(csv::QT_I64), Some(csv::QT_I64), Some(c.t)],
        _ => alloc::vec![Some(c.t)],
    });
    let src = ts.zip(&v).map(|(t, &(k, e))| t.map(|t| scan::raw_all(t, k, e)).transpose()).collect::<Result<Vec<_>, _>>().map_err(at)?;
    csv::schema(&cs).map_err(at)?;
    let cnt: Vec<usize> = v.iter().map(|p| p.0).collect();
    let mut tmp = alloc::vec![0u8; 8 << DEFAULT_LG];
    csv::write(path.cstr(), &cs, n, &cnt, DEFAULT_LG, |p, lo, out| match &src[p] { Some(s) => s.load(lo, out, &mut tmp), None => out.fill(0) })
        .map_err(|e| match e { Fail::User(t) => at(t), e => e })?;
    Ok(boxed(0))
}

export! {

    /// `Db.csvRead` (Rel/Kernel/Db/Csv.lean).
    fn qlean_csv_read(path: B, cols: B) -> O { super::own::answer(read(path, cols), path) }

    /// `Db.csvWrite` (Rel/Kernel/Db/Csv.lean).
    fn qlean_csv_write(path: B, cols: B, n: usize, es: B) -> O { super::own::answer(write(path, cols, n, es), path) }

}
