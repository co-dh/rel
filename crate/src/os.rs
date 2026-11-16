//! libc beyond the allocator, as safe calls: bytes and numbers in, bytes and numbers out (phase-2 §2.4; O0 extends it).
//! Every mirrored struct is asserted against its C header in c/abi.c.

/// glibc's `struct tm` on x86-64; `gmtoff` is the GNU/BSD field that makes `utc_offset` the offset at that instant
#[repr(C)]
pub struct Tm { pub sec: i32, pub min: i32, pub hour: i32, pub mday: i32, pub mon: i32, pub year: i32, pub wday: i32,
                pub yday: i32, pub isdst: i32, pub gmtoff: i64, pub zone: *const u8 }
/// glibc's `struct rusage` on x86-64: two `timeval`s, then fourteen `long`s from `ru_maxrss` (in KiB) on
#[repr(C)]
pub struct Rusage { pub utime: [i64; 2], pub stime: [i64; 2], pub maxrss: i64, pub rest: [i64; 13] }

// libc declares these itself, with its own types
/// cbindgen:ignore
mod sys {
    use super::{Rusage, Tm};
    unsafe extern "C" {
        pub fn getrusage(who: i32, u: *mut Rusage) -> i32;
        pub fn __errno_location() -> *mut i32;
        /// the XSI `strerror_r` C reaches without `_GNU_SOURCE`: fills `buf`, answers 0 or an errno
        pub fn __xpg_strerror_r(e: i32, buf: *mut u8, n: usize) -> i32;
        pub fn tzset();
        pub fn localtime_r(t: *const i64, tm: *mut Tm) -> *mut Tm;
    }
}
use sys::*;

/// The offset from UTC in force at the instant `secs`, in seconds, from libc's zone table -- the table q reads too,
/// so the two agree on every transition (time.c's note). 0 when `localtime_r` fails, as in C.
pub fn utc_offset(secs: i64) -> i64 {
    let mut tm = core::mem::MaybeUninit::<Tm>::uninit();
    unsafe {
        tzset();
        if localtime_r(&secs, tm.as_mut_ptr()).is_null() { return 0 }
        tm.assume_init().gmtoff
    }
}

fn errno() -> i32 { unsafe { *__errno_location() } }

/// The process's peak resident set in bytes (`getrusage(RUSAGE_SELF)`'s `ru_maxrss` · 1024), or the errno it failed with
pub fn peak_rss() -> Result<u64, i32> {
    let mut u = core::mem::MaybeUninit::<Rusage>::uninit();
    if unsafe { getrusage(0, u.as_mut_ptr()) } < 0 { return Err(errno()) }
    Ok((unsafe { u.assume_init() }.maxrss as u64).wrapping_mul(1024))
}

/// libc's text for errno `e` in `buf` (XSI `strerror_r`), or `None` when it has none (`EINVAL`, `ERANGE`)
pub fn strerror(e: i32, buf: &mut [u8; 256]) -> Option<&core::ffi::CStr> {
    if unsafe { __xpg_strerror_r(e, buf.as_mut_ptr(), buf.len()) } != 0 { return None }
    Some(core::ffi::CStr::from_bytes_until_nul(buf).expect("os::strerror: strerror_r left no NUL in its buffer"))
}
