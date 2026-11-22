//! gather.rs's Lean export, `Kernel.kgather` (Rel/Kernel/Gather.lean): its `foR` arguments viewed in place through
//! `ffi::scatter::for_view`, the gather and its answer `gather::enc`'s, block by block.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use crate::{exports::scatter::{POS, blocks_view, except, for_view, no_nul}, gather, lean::{B, O}};

export! {
    /// Spec: `kgather m ix n e` reads the `m` words of `ix`, then the `n` words of `e` (each `foR`, its layout whole),
    /// refuses a null index, and answers `e[ix[i]]` for each row `i`, a null of `e` gathered as a null, encoded as
    /// `Coc.encodeAt lgEnc 8` writes it; the first error met in that order is the answer, an index `>= n` among them.
    fn qlean_k_gather(m: usize, ix: B, n: usize, e: B) -> O {
        except(blocks_view("gather: ix", m, ix).and_then(|ib| {
            let ec = if e.tag() == POS { None } else { Some(for_view("gather: e", n, e)?) };
            no_nul("gather: ix", m, ix)?;
            // `e = pos` is law G2: `e[ix[i]] = ix[i]`, so the answer is `ix` once every index is below `n`
            match ec { None => gather::of_pos(&ib, n), Some(ec) => gather::enc(&ib, &ec) }
        }))
    }
}
