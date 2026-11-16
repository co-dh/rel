//! handle.c's Lean exports: `hopen`, `hclose`, the write an applied handle does, and the text of the errno they answer.
//! Every one answers a non-negative result or `-errno`, as an `Int64` (Lean passes and takes it as C's `uint64_t`).
#![deny(unsafe_code)]
use crate::lean::{B, O, export, string, string_c};
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

/// `q` names the host when it does not resolve and `hop` everywhere else: measured, `` hopen `:nohost.invalid:5 `` is
/// `'nohost.invalid. OS reports: No route to host` and `hopen 5` is `'hop. OS reports: Connection refused`; this bit, above
/// every errno, tells the caller which.
const UNRESOLVED: i64 = 1 << 32;
fn answer(r: Result<i32, i32>) -> u64 { (match r { Ok(v) => v as i64, Err(e) => -(e as i64) }) as u64 }

export! {
    /// `hopen` of a path: the descriptor of the file opened for append (created `0666`), or `-errno`
    fn qlean_handle_open(path: B) -> u64 {
        answer(os::File::open(path.cstr(), os::O_WRONLY | os::O_CREAT | os::O_APPEND, 0o666).map(os::File::into_raw))
    }
    /// `hopen` of a port: a TCP connection to `host` (this machine where it is empty), the descriptor, or `-errno`; a name
    /// that does not resolve is `-EHOSTUNREACH - UNRESOLVED`
    fn qlean_handle_connect(host: B, port: u64) -> u64 {
        (match os::Sock::connect(host.cstr(), port as i64) {
            Ok(s) => s.into_raw() as i64,
            Err(os::Conn::Unresolved) => -(os::EHOSTUNREACH as i64) - UNRESOLVED,
            Err(os::Conn::Errno(e)) => -(e as i64),
        }) as u64
    }
    /// The write a handle does when applied: the whole of `bytes` (a short write continued, `EINTR` retried), else `-errno`
    /// with no count of what got out; a descriptor that moves nothing is `-EIO`
    fn qlean_handle_write(fd: u64, bytes: B) -> u64 {
        let p = bytes.bytes();
        (match os::write_all(fd as i32, p) { Ok(()) => p.len() as i64, Err(e) => -(e as i64) }) as u64
    }
    /// `hclose`: 0, or `-errno`; not retried on `EINTR`
    fn qlean_handle_close(fd: u64) -> u64 { answer(os::close_fd(fd as i32).map(|()| 0)) }
}
