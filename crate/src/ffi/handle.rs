//! handle.c's Lean exports that are not the descriptor calls themselves.
#![deny(unsafe_code)]
use crate::lean::{O, export, string, string_c};
use crate::os;

export! {
    /// The OS's own text for the `-errno` (or errno) a handle call answered; XSI `strerror_r`, whose one buffer is the
    /// caller's, so two handles failing at once do not answer each other's text. `errno N` when libc has none.
    /// Lean passes `Int64` as C's `uint64_t`.
    fn qlean_handle_error(code: u64) -> O {
        let c = code as i64;
        let e = (if c < 0 { c.wrapping_neg() } else { c }) as i32;
        let mut buf = [0u8; 256];
        match os::strerror(e, &mut buf) { Some(s) => string_c(s), None => string(&alloc::format!("errno {e}")) }
    }
}
