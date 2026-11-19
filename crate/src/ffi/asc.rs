//! asc.rs's Lean export, `Kernel.kasc` (Rel/Kernel/Asc.lean): each key column taken as its encoded blocks
//! (`ffi::scatter::for_view`), the grade (`asc::grade_cols`), and every answer column written a block at a time through
//! a `Sink`, the encoder's own block step, so the bytes are `Coc.encode`'s.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::{asc, blocks::Blocks, c::pool, exports::scatter::{POS, for_view, except}, ffi::{Form, Sink}, lean::{B, O, boxed, ctor}, pod},
    alloc::{format, string::String, vec::Vec}};

/// `foRWords`: `m` words of a `pos` (word `i` is `i`, at any row count) or `foR` column.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn ix<'a>(what: &str, m: usize, e: B<'a>) -> Result<asc::Ix<'a>, String> {
    if e.tag() == POS { Ok(asc::Ix::Pos) } else { for_view(what, m, e).map(|c| asc::Ix::of(Some(c))) }
}

/// `ascCol`, one `(AscKey, Enc)` at `m` rows, in its order of failure: the key column and the column it carries.
/// `atom t` (ctor 0, `t` its one byte): the type's order, then `ascWords` (`pos` only at `i64`, code 4, and at most
/// `2^63` rows). `cells n c lo hi els` (ctor 1, objects `lo hi els`, then `n c`): the column's words, each below `n`,
/// `lo`, `hi`, then each of `els` at `c` rows.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub(crate) fn key<'a>(m: usize, el: B<'a>) -> Result<(asc::Col<'a>, asc::Ix<'a>), String> {
    let (k, e) = (el.field(0), el.field(1));
    if k.tag() == 0 {
        let t = k.u8_field(0);
        let o = asc::order(t).ok_or_else(|| format!("asc: type {t} has no fixed-width order"))?;
        if e.tag() != POS { let c = for_view("asc", m, e)?; return Ok((asc::Col::Atom(asc::Key::new(c, o)), asc::Ix::of(Some(c)))) }
        if t != 4 { return Err(format!("asc: a pos column is type 4, not {t}")) }
        return asc::pos_rows(m).map(|_| (asc::Col::Pos, asc::Ix::Pos))
    }
    let (n, c) = (k.usize_field(3), k.usize_field(4));
    let x = ix("asc: cells", m, e)?;
    if let Some(r) = (0..m).map(|i| x.get(i) as u64).find(|&r| r >= n as u64) { return Err(format!("asc: cells: row word {r} names no cell of {n}")) }
    let (lo, hi) = (ix("asc: cells lo", n, k.field(0))?, ix("asc: cells hi", n, k.field(1))?);
    let (mut els, mut l) = (Vec::new(), k.field(2));
    while !l.is_scalar() { els.push(key(c, l.field(0))?.0); l = l.field(1) }
    Ok((asc::Col::Cells(asc::Cells { ix: x, c, lo, hi, els }), x))
}

/// `kasc`'s body in its order of failure: the columns left to right (`ascCol`), then the grade and the answers. Where
/// the rows are already in order (`None`) each carried column is its own blocks re-encoded and the permutation `til m`;
/// else answer row `i` is input row `p[i]`, read at its address (`Coc::get_w`).
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kasc(m: usize, es: B) -> Result<O, String> {
    let (mut ks, mut cs, mut l) = (Vec::new(), Vec::new(), es);
    while !l.is_scalar() { let (k, c) = key(m, l.field(0))?; ks.push(k); cs.push(c); l = l.field(1) }
    // law A1: a `pos` key (at most 2^63 rows, `pos_rows`) has no ties and is in row order, so it and every later key
    // decide nothing a stable sort by the keys before it does not
    let nk = ks.iter().position(|k| matches!(k, asc::Col::Pos)).unwrap_or(ks.len());
    let p = if nk == 0 { None } else { asc::grade_cols(pool(), &ks[..nk], m) };
    let sink = || Sink::new(m, 8, Form::For).enc();
    // the permutation, which is also a `pos` column sorted
    let pe = || match &p {
        None => sink().answer(&Blocks::pos(m)),
        Some(p) => sink().answer(&Blocks::dense(pod::bytes(p), 8)),
    };
    let col = |c: &asc::Ix| match (c, &p) {
        (asc::Ix::Pos, _) => pe(),
        (asc::Ix::For(c, _), None) => sink().answer(&Blocks::from(*c)),
        (asc::Ix::For(c, uw), Some(p)) => sink().answer(&|buf: &mut [i64], i0: usize| for (o, &i) in buf.iter_mut().zip(&p[i0..]) { *o = c.get_w(*uw, i as usize) }),
    };
    // the `List Enc` of sorted columns, built from its end
    let vs = cs.iter().rev().fold(boxed(0), |vs, c| ctor(1, [col(c), vs], &[]));
    Ok(ctor(0, [vs, pe()], &[]))
}

export! {
    /// Spec: `kasc m es` reads each `(AscKey, Enc)` of `es` at `m` rows (`ascCol`: an atom column's words, or a `cells`
    /// column naming cells of an `arr` side), sorts the rows stably and lexicographically by their order codes, and
    /// answers `Except String (List Enc × Enc)`: every column's words sorted and the permutation, each as
    /// `Coc.encodeAt lgEnc 8` writes it; the first error in the order of `es` is the answer.
    fn qlean_k_asc(m: usize, es: B) -> O { except(kasc(m, es)) }
}
