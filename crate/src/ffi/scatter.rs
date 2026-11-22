//! scatter.rs's Lean export, `Kernel.kscatter` (Rel/Kernel/Scatter.lean): its `foR` arguments checked by `for_view`
//! and read a block at a time by `scatter::blocks`, which writes the answer.
#![deny(unsafe_code)]
use alloc::string::String;
use crate::lean::{O, ctor, export, string};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::format, crate::{blocks::Blocks, coc, lean::B, scatter}};

#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub use crate::blocks::tag::{FOR, POS};

/// `Kernel.foRWords what m e` as a block source: `pos` is the positions `0 .. m` (`Blocks::pos`), a `foR` is `for_view`'s
/// column, and any other form is `for_view`'s error.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub fn blocks_view<'a>(what: &str, m: usize, e: B<'a>) -> Result<Blocks<'a>, String> {
    if e.tag() == POS { return Ok(Blocks::pos(m)) }
    for_view(what, m, e).map(Blocks::from)
}

/// `Kernel.foRWords what m e`'s layout test: the `foR` argument `e` as the block source of its `m` words where
/// `Column.lgOk` and `Coc.foRStd` admit it at `m` (`coc::view` and `Coc::std`), else the model's error text.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub fn for_view<'a>(what: &str, m: usize, e: B<'a>) -> Result<coc::Coc<'a>, String> {
    if e.tag() != FOR { return Err(format!("{what}: constructor {} is not foR", e.tag())) }
    let (md, pk) = (e.field(0).bytes(), e.field(1).bytes());
    if let Ok(c) = coc::view(md, pk, m) && c.std(m) { return Ok(c) }
    // `Column.nblk` and `Column.lgAt`: a byte past the metadata reads 0, as `bitsAt` does
    let nb = md.len() / 33;
    let lg = (0..8).fold(0u64, |v, k| v | (md.get(32 * nb + 16 + k).copied().unwrap_or(0) as u64) << (8 * k));
    Err(format!("{what}: foR: {nb} blocks of 2^{lg} and a {}-byte pack are not the layout of {m} elements", pk.len()))
}

/// `Except.ok e` (tag 1) or `Except.error` (tag 0) of the message.
pub fn except(r: Result<O, String>) -> O {
    match r { Ok(e) => ctor(1, [e], &[]), Err(m) => ctor(0, [string(&m)], &[]) }
}

export! {
    /// Spec: `kscatter op m ix e n fill` reads the `m` words of `ix`, then of `e` (each `foR`, its layout whole), and answers
    /// `n` cells, each `fill` folded with `Op.eval op` over the rows `k` naming it (`e[k]`), in row order, encoded as
    /// `Coc.encode 8`; the first error met in that order is the answer, an index `>= n` or a failing step among them.
    fn qlean_k_scatter(op: B, m: usize, ix: B, e: B, n: usize, fill: u64) -> O {
        let op = crate::scan::op_code(op);
        if crate::scan::reads_divisor(op) { return except(Err("scatter: rdiv and rmod divide by the cell, which no row test sees".into())) }
        except(blocks_view("scatter: ix", m, ix).and_then(|is| blocks_view("scatter: e", m, e).and_then(|es| scatter::blocks(op, &is, &es, n, fill))))
    }
}
