//! ffi/env.rs's Lean exports.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::lean::{O, apply, boxed}, crate::os};

export! {
}

export! {

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
