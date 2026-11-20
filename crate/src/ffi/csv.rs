//! csv.rs's Lean exports: the CSV reader and writer. `IO` externs (no world argument in Lean 4.28); a failure is an errno
//! the Lean side reports as the runtime's `IO.Error` for the path, or the model's refusal text after `{path}: `.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, string::String, vec::Vec}, core::sync::atomic::AtomicUsize,
     crate::{DEFAULT_LG, csv::{self, Col}, ffi::{Form, Sink}, lean::{B, O, box_usize_o, boxed, ctor}, own::{self, Fail}, scan}};

/// The schema `CsvCols` (`List (String × QAtomicType × List String)`) as columns: each pair a ctor of two fields, the
/// enum `QAtomicType` a boxed constructor index.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn cols<'a>(mut l: B<'a>) -> Result<Vec<Col<'a>>, String> {
    let s = |o: B<'a>| core::str::from_utf8(o.str_bytes()).map_err(|e| format!("CsvCols: a column name that is not UTF-8: {e}"));
    let mut v = Vec::new();
    while !l.is_scalar() {
        let (c, rest) = (l.field(0), l.field(0).field(1));
        let (mut ns, mut k) = (Vec::new(), rest.field(1));
        while !k.is_scalar() { ns.push(s(k.field(0))?); k = k.field(1) }
        v.push(Col { name: s(c.field(0))?, t: rest.field(0).unbox() as u8, names: ns });
        l = l.field(1);
    }
    Ok(v)
}

/// `Db.csvRead path cols`: the file mapped, then `csvWords`' checks in its order; each column's words go to its `Sink`
/// a block at a time (`csv::fill` is the producer's step), so no column is ever held decoded. `IO (USize × List Enc)`,
/// each `Enc` a `foR` of 8-byte words, as `wordsFoR` builds.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn read(path: B, cs: B) -> Result<O, Fail> {
    let m = csv::map(path.cstr())?;
    let b = m.as_ref().map_or(&[][..], |m| m.as_slice());
    let at = |e: String| Fail::User(format!("{}: {e}", String::from_utf8_lossy(path.str_bytes())));
    let cs = cols(cs).map_err(at)?;
    csv::schema(&cs).map_err(at)?;
    let lx = csv::lex(b, cs.len(), DEFAULT_LG).map_err(at)?;
    csv::header(&cs, &lx).map_err(at)?;
    let bad: Vec<AtomicUsize> = cs.iter().map(|_| AtomicUsize::new(usize::MAX)).collect();
    let es: Vec<O> = cs.iter().zip(&bad).enumerate()
        .map(|(c, (col, bad))| Sink::new(lx.n, 8, Form::For).enc().answer(&|buf: &mut [i64], lo: usize| csv::fill(b, &lx, c, col, lo, buf, bad)))
        .collect();
    csv::refusal(b, &lx, &cs, &bad).map_err(at)?;
    if let Some(m) = m { m.unmap()? }
    Ok(ctor(0, [box_usize_o(lx.n), es.into_iter().rev().fold(boxed(0), |t, h| ctor(1, [h, t], &[]))], &[]))
}

/// `Db.csvWrite path cols n es`, in its body's order: the parent directories (`createDirAll`), the column count, each
/// column read as `rawAll` reads it (`scan::raw_all`: any `Enc` form, a block of rows at a time through `Col::load`, never
/// decoded whole), `csvText`'s schema refusals, then the rows (`csv::write`). `IO Unit`.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn write(path: B, cs: B, n: usize, es: B) -> Result<O, Fail> {
    own::mkdirs(path.cstr())?;
    let at = |e: String| Fail::User(format!("{}: {e}", String::from_utf8_lossy(path.str_bytes())));
    let cs = cols(cs).map_err(at)?;
    let (mut v, mut l) = (Vec::new(), es);
    while !l.is_scalar() { v.push(l.field(0)); l = l.field(1) }
    csv::arity(&cs, v.len()).map_err(at)?;
    let src = cs.iter().zip(&v).map(|(c, &e)| scan::raw_all(c.t, n, e)).collect::<Result<Vec<_>, _>>().map_err(at)?;
    csv::schema(&cs).map_err(at)?;
    let mut tmp = alloc::vec![0u8; 8 << DEFAULT_LG];
    csv::write(path.cstr(), &cs, n, DEFAULT_LG, |c, lo, out| src[c].load(lo, out, &mut tmp))
        .map_err(|e| match e { Fail::User(t) => at(t), e => e })?;
    Ok(boxed(0))
}

export! {

    /// `Db.csvRead` (Rel/Kernel/Db/Csv.lean).
    fn qlean_csv_read(path: B, cols: B) -> O { super::own::answer(read(path, cols), path) }

    /// `Db.csvWrite` (Rel/Kernel/Db/Csv.lean).
    fn qlean_csv_write(path: B, cols: B, n: usize, es: B) -> O { super::own::answer(write(path, cols, n, es), path) }

}
