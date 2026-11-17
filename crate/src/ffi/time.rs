//! ffi/time.rs's Lean export: the one call `ltime` and `gtime` make into libc's zone table.
#![deny(unsafe_code)]
use crate::lean::export;
use crate::os;

export! {
    /// The offset from UTC in force at `secs`, in seconds (`os::utc_offset`). Lean passes and takes `Int64` as C's
    /// `uint64_t`, which is what the `proto` gate holds this signature to.
    fn qlean_utc_offset(secs: u64) -> u64 { os::utc_offset(secs as i64) as u64 }
}
