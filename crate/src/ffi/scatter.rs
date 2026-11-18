//! scatter.rs's Lean export, `Kernel.kscatter` (Rel/Kernel/Scatter.lean): its `foR` arguments checked by `for_blocks`
//! and read a block at a time by `scatter::blocks`, which writes the answer.
#![deny(unsafe_code)]
use alloc::string::String;
use crate::lean::{O, ctor, export, string};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, vec::Vec}, crate::{blocks::Blocks, coc, exports::scan::raw, lean::B, scatter}};

/// `Ext.Enc.foR`'s constructor tag (Rel/Kernel/Value.lean: `bytes bits syms foR ..`).
pub const FOR: u32 = 3;
/// `QAtomicType.long`'s constructor index, the 64-bit column `Kernel.foRWords` reads its argument as.
pub const QT_LONG: u8 = 5;

/// `Kernel.foRWords what m e`'s layout test: the `foR` argument `e` as the block source of its `m` words where
/// `Column.lgOk` and `Coc.foRStd` admit it at `m` (`coc::view` and `Coc::std`), else the model's error text.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub fn for_blocks<'a>(what: &str, m: usize, e: B<'a>) -> Result<Blocks<'a>, String> {
    if e.tag() != FOR { return Err(format!("{what}: constructor {} is not foR", e.tag())) }
    let (md, pk) = (e.field(0).bytes(), e.field(1).bytes());
    match coc::view(md, pk, m) { Ok(c) if c.std(m) => return Ok(Blocks::from(c)), _ => {} }
    // `Column.nblk` and `Column.lgAt`: a byte past the metadata reads 0, as `bitsAt` does
    let nb = md.len() / 33;
    let lg = (0..8).fold(0u64, |v, k| v | (md.get(32 * nb + 16 + k).copied().unwrap_or(0) as u64) << (8 * k));
    Err(format!("{what}: foR: {nb} blocks of 2^{lg} and a {}-byte pack are not the layout of {m} elements", pk.len()))
}

/// `Kernel.foRWords what m e`: the `m` raw words of a `foR` argument `for_blocks` admits.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub fn for_words_of(what: &str, m: usize, e: B) -> Result<Vec<u64>, String> {
    for_blocks(what, m, e)?;
    raw(QT_LONG, m, e).ok_or_else(|| format!("{what}: a foR column of {m} elements has no raw words at long"))
}

/// `Except.ok e` (tag 1) or `Except.error` (tag 0) of the message.
pub fn except(r: Result<O, String>) -> O {
    match r { Ok(e) => ctor(1, [e], &[]), Err(m) => ctor(0, [string(&m)], &[]) }
}

export! {
    /// Spec: `kscatter m ix e n fill` reads the `m` words of `ix`, then of `e` (each `foR`, its layout whole), and answers
    /// `n` cells, `fill` but where a row `k` writes `e[k]` at `ix[k]`, the last such row winning, encoded as
    /// `Coc.encode 8`; the first error met in that order is the answer, an index `>= n` among them.
    fn qlean_k_scatter(m: usize, ix: B, e: B, n: usize, fill: u64) -> O {
        except(for_blocks("scatter: ix", m, ix).and_then(|is| for_blocks("scatter: e", m, e).and_then(|es| scatter::blocks(&is, &es, n, fill))))
    }
}
