//! scatter.rs's Lean export, `Kernel.kscatter` (Rel/Kernel/Scatter.lean): its `foR` arguments read through
//! `ffi::scan::raw`, its answer written by `ffi::scan::for_words`.
#![deny(unsafe_code)]
use alloc::string::String;
use crate::lean::{O, ctor, export, string};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, vec::Vec}, crate::{coc, exports::scan::{for_words, raw}, lean::B, scatter}};

/// `Ext.Enc.foR`'s constructor tag (Rel/Kernel/Value.lean: `bytes bits syms foR ..`).
pub const FOR: u32 = 3;
/// `QAtomicType.i64`'s constructor index, the 64-bit column `Kernel.foRWords` reads its argument as.
pub const QT_LONG: u8 = 4;

/// `Kernel.foRWords what m e`: the `m` raw words of a `foR` argument whose layout `Column.lgOk` and `Coc.foRStd` admit
/// at `m` (`coc::view` and `Coc::std`), else the model's error text.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub fn for_words_of(what: &str, m: usize, e: B) -> Result<Vec<u64>, String> {
    if e.tag() != FOR { return Err(format!("{what}: constructor {} is not foR", e.tag())) }
    let (md, pk) = (e.field(0).bytes(), e.field(1).bytes());
    if coc::view(md, pk, m).is_ok_and(|c| c.std(m)) {
        return raw(QT_LONG, m, e).ok_or_else(|| format!("{what}: a foR column of {m} elements has no raw words at long"))
    }
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
    /// Spec: `kscatter m ix e n fill` reads the `m` words of `ix`, then of `e` (each `foR`, its layout whole), and answers
    /// `n` cells, `fill` but where a row `k` writes `e[k]` at `ix[k]`, the last such row winning, encoded as
    /// `Coc.encode 8`; the first error met in that order is the answer, an index `>= n` among them.
    fn qlean_k_scatter(m: usize, ix: B, e: B, n: usize, fill: u64) -> O {
        except(for_words_of("scatter: ix", m, ix).and_then(|is| for_words_of("scatter: e", m, e)
            .and_then(|es| scatter::words(&is, &es, n, fill))).map(|o| for_words(&o)))
    }
}
