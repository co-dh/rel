//! gather.rs's Lean export, `Kernel.kgather` (Rel/Kernel/Gather.lean): its `foR` arguments read through
//! `ffi::scatter::for_words_of`, its answer written by `ffi::scan::for_words`.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use crate::{exports::{scan::for_words, scatter::{except, for_words_of}}, gather, lean::{B, O}};

export! {
    /// Spec: `kgather m ix n e` reads the `m` words of `ix`, then the `n` words of `e` (each `foR`, its layout whole), and
    /// answers `e[ix[i]]` for each row `i`, encoded as `Coc.encodeAt lgEnc 8` writes it; the first error met in that order
    /// is the answer, an index `>= n` among them.
    fn qlean_k_gather(m: usize, ix: B, n: usize, e: B) -> O {
        except(for_words_of("gather: ix", m, ix).and_then(|is| for_words_of("gather: e", n, e).and_then(|es| gather::words(&is, &es))).map(|o| for_words(&o)))
    }
}
