//! env.c's Lean exports.
#![deny(unsafe_code)]
use crate::lean::{B, Io, O, apply, boxed, box_u64, export};
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

export! {
    /// `setenv(name, value, 1)`: 0, or the negated errno. Lean's `IO` reads the environment and does not write it, so
    /// this is the one write; there is no oracle (q's own `setenv` raises), so it does what `setenv(3)` does.
    fn qlean_setenv(name: B, value: B) -> u64 {
        match os::setenv(name.cstr(), value.cstr()) { Ok(()) => 0, Err(eno) => (-(eno as i64)) as u64 }
    }

    /// `QLean.Kernel.stop`, the failing branch of `need`: prints `qlean: ` and `msg ()` and exits 1, so it never returns
    /// and cannot disagree with the Lean body `model ()`.
    fn qlean_stop(msg: O, model: O) -> O {
        drop(model);
        let s = apply(msg, [boxed(0)]);
        // the exit is the report; a failed write to stderr changes nothing about it
        // as C's `fprintf(stderr, "qlean: %s\n", …)`: up to the first NUL, no 1 KiB cut, no UTF-8 check
        let _ = os::write_all(2, &[b"qlean: ", s.borrow().cstr().to_bytes(), b"\n"].concat());
        os::exit(1)
    }
}
