//! env.c's Lean exports that moved.
#![deny(unsafe_code)]
use crate::lean::{Io, O, box_u64, export};
use crate::os;

export! {
    /// `\ts`'s space column: the process's peak resident set, in bytes (`os::peak_rss`). q answers the bytes its own
    /// heap allocated for the expression; the Lean runtime keeps no such count, so the peak's growth across the run is
    /// what is measured, and it is 0 for an expression that fits under an earlier peak. No world argument: Lean 4.28
    /// calls an `IO` extern with none.
    fn qlean_peak_rss() -> O {
        match os::peak_rss() { Ok(b) => Io::ok(box_u64(b)), Err(eno) => Io::errno(eno, None) }
    }
}
