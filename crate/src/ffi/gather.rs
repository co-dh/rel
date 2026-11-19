//! gather.rs's Lean export, `Kernel.kgather` (Rel/Kernel/Gather.lean): its `foR` arguments viewed in place through
//! `ffi::scatter::for_view`, the gather and its answer `gather::enc`'s, block by block.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use crate::{exports::scatter::{POS, blocks_view, except, for_view}, gather, lean::{B, O}};

export! {
    /// Spec: `kgather m ix n e` reads the `m` words of `ix`, then the `n` words of `e` (each `foR`, its layout whole), and
    /// answers `e[ix[i]]` for each row `i`, encoded as `Coc.encodeAt lgEnc 8` writes it; the first error met in that order
    /// is the answer, an index `>= n` among them.
    fn qlean_k_gather(m: usize, ix: B, n: usize, e: B) -> O {
        // `e = pos` is law G2: `e[ix[i]] = ix[i]`, so the answer is `ix` once every index is below `n`
        except(blocks_view("gather: ix", m, ix).and_then(|ib| if e.tag() == POS { gather::of_pos(&ib, n) }
            else { for_view("gather: e", n, e).and_then(|ec| gather::enc(&ib, &ec)) }))
    }
}
