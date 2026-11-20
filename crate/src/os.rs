//! libc beyond the allocator, as safe calls: bytes and numbers in, bytes and numbers out (phase-2 §2.4; O0 extends it).
//! Every mirrored struct is asserted against its C header in c/abi.c.


// libc declares these itself, with its own types
/// cbindgen:ignore
pub mod sys {
    unsafe extern "C" {
        pub fn __errno_location() -> *mut i32;
        /// the XSI `strerror_r` C reaches without `_GNU_SOURCE`: fills `buf`, answers 0 or an errno
        pub fn __xpg_strerror_r(e: i32, buf: *mut u8, n: usize) -> i32;
        pub fn tzset();
    }
}
use sys::*;


pub fn errno() -> i32 { unsafe { *__errno_location() } }



pub const O_RDONLY: i32 = 0;
pub const O_WRONLY: i32 = 1;
pub const PROT_READ: i32 = 1;
pub const PROT_WRITE: i32 = 2;
pub const MAP_PRIVATE: i32 = 2;
pub const MAP_NORESERVE: i32 = 0x4000;
pub const S_IFDIR: u32 = 0o040000;
pub const EISDIR: i32 = 21;
pub const O_CREAT: i32 = 0o100;
pub const O_EXCL: i32 = 0o200;
pub const O_CLOEXEC: i32 = 0o2000000;
pub const S_IFMT: u32 = 0o170000;
pub const S_IFREG: u32 = 0o100000;
pub const ENOENT: i32 = 2;
pub const EEXIST: i32 = 17;
pub const EINTR: i32 = 4;
pub const EIO: i32 = 5;
pub const PATH_MAX: usize = 4096;
pub const EMSGSIZE: i32 = 90;

/// glibc's `struct stat` on x86-64 (144 bytes): the fields a caller reads are named, the rest is padding
#[repr(C)]
pub struct Stat { pub dev: u64, pub ino: u64, pub nlink: u64, pub mode: u32, pub uid: u32, pub gid: u32, pub pad0: i32,
                  pub rdev: u64, pub size: i64, pub blksize: i64, pub blocks: i64, pub times: [i64; 6], pub rest: [i64; 3] }

// ---------------------------------------------------------------------------------------------------------------------
// Phase-2 §2.4: files, mappings, shared libraries, sockets, the environment. Each wrapper answers `Result<_, i32>` with
// the errno, so a caller builds its own message (`strerror`) and nothing is lost between the call and the report.
// Consumers: File/Map -> B3 (own.rs) and B4 (zip.rs); Lib -> B4; Sock -> B2 (ffi/handle.rs); setenv -> B1 (ffi/env.rs);
// eprint/exit -> B1 (`qlean_stop`); getenv/sysconf -> P1 (pool.rs); rename/unlink/realpath/getpid/fchmod -> B3.

use alloc::vec::Vec;
use core::ffi::CStr;

// libc declares these itself, with its own types
/// cbindgen:ignore
pub mod sys2 {
    use super::Stat;
    use core::ffi::{c_char, c_void};
    unsafe extern "C" {
        pub fn open(path: *const c_char, flags: i32, ...) -> i32;
        pub fn close(fd: i32) -> i32;
        pub fn pread(fd: i32, buf: *mut u8, n: usize, off: i64) -> isize;
        pub fn write(fd: i32, buf: *const u8, n: usize) -> isize;
        pub fn fstat(fd: i32, st: *mut Stat) -> i32;
        pub fn stat(path: *const c_char, st: *mut Stat) -> i32;
        pub fn fchmod(fd: i32, mode: u32) -> i32;
        pub fn mmap(addr: *mut c_void, n: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut c_void;
        pub fn munmap(addr: *mut c_void, n: usize) -> i32;
        pub fn rename(from: *const c_char, to: *const c_char) -> i32;
        pub fn unlink(path: *const c_char) -> i32;
        pub fn mkdir(path: *const c_char, mode: u32) -> i32;
        pub fn realpath(path: *const c_char, out: *mut c_char) -> *mut c_char;
        pub fn getpid() -> i32;
        pub fn dlopen(path: *const c_char, flags: i32) -> *mut c_void;
        pub fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
        pub fn dlerror() -> *const c_char;
        pub fn socket(domain: i32, ty: i32, proto: i32) -> i32;
        pub fn connect(fd: i32, addr: *const u8, len: u32) -> i32;
        pub fn setenv(name: *const c_char, value: *const c_char, overwrite: i32) -> i32;
        pub fn getenv(name: *const c_char) -> *const c_char;
        pub fn sysconf(name: i32) -> i64;
        pub fn exit(code: i32) -> !;
    }
}


pub fn ok(r: i32) -> Result<(), i32> { if r < 0 { Err(errno()) } else { Ok(()) } }

/// `write(2)` until every byte is out. A short write (a pipe or socket whose buffer fills) is continued, `EINTR` retried,
/// and a write that moves nothing is `EIO`, so a descriptor that will not move cannot spin: ffi/handle.rs's loop.
pub fn write_all(fd: i32, mut p: &[u8]) -> Result<(), i32> {
    while !p.is_empty() {
        let k = unsafe { sys2::write(fd, p.as_ptr(), p.len()) };
        if k < 0 { match errno() { EINTR => continue, e => return Err(e) } }
        if k == 0 { return Err(EIO) }
        p = &p[k as usize..];
    }
    Ok(())
}

/// An open file descriptor. `Drop` closes it and has nowhere to report a failure, so a path that must see `close`'s
/// errno calls `close()`; `into_raw` hands the descriptor to a caller who owns it from then on (Lean's `hopen` integer).
pub struct File(pub i32);


impl File {
    /// `open(2)`, retried on `EINTR` as ffi/handle.rs does
    pub fn open(path: &CStr, flags: i32, mode: u32) -> Result<File, i32> {
        loop {
            let fd = unsafe { sys2::open(path.as_ptr(), flags, mode) };
            if fd >= 0 { return Ok(File(fd)) }
            if errno() != EINTR { return Err(errno()) }
        }
    }
    pub fn into_raw(self) -> i32 { let fd = self.0; core::mem::forget(self); fd }
    /// `close(2)` and its errno; not retried on `EINTR`, because Linux has released the descriptor by then and a second
    /// `close` would shut whatever was opened next
    pub fn close(self) -> Result<(), i32> { ok(unsafe { sys2::close(self.into_raw()) }) }
    pub fn stat(&self) -> Result<Stat, i32> {
        let mut st = core::mem::MaybeUninit::<Stat>::uninit();
        ok(unsafe { sys2::fstat(self.0, st.as_mut_ptr()) })?;
        Ok(unsafe { st.assume_init() })
    }
    pub fn fchmod(&self, mode: u32) -> Result<(), i32> { ok(unsafe { sys2::fchmod(self.0, mode) }) }
    pub fn write_all(&self, p: &[u8]) -> Result<(), i32> { write_all(self.0, p) }
}
impl Drop for File { fn drop(&mut self) { unsafe { sys2::close(self.0); } } }

/// `stat(2)` of a path
pub fn stat(path: &CStr) -> Result<Stat, i32> {
    let mut st = core::mem::MaybeUninit::<Stat>::uninit();
    ok(unsafe { sys2::stat(path.as_ptr(), st.as_mut_ptr()) })?;
    Ok(unsafe { st.assume_init() })
}
pub fn rename(from: &CStr, to: &CStr) -> Result<(), i32> { ok(unsafe { sys2::rename(from.as_ptr(), to.as_ptr()) }) }
pub fn unlink(path: &CStr) -> Result<(), i32> { ok(unsafe { sys2::unlink(path.as_ptr()) }) }
pub fn mkdir(path: &CStr, mode: u32) -> Result<(), i32> { ok(unsafe { sys2::mkdir(path.as_ptr(), mode) }) }
/// the canonical path, in `out` (`PATH_MAX` bytes is what `realpath(3)` requires)
pub fn realpath<'a>(path: &CStr, out: &'a mut [u8; PATH_MAX]) -> Result<&'a CStr, i32> {
    if unsafe { sys2::realpath(path.as_ptr(), out.as_mut_ptr().cast()) }.is_null() { return Err(errno()) }
    Ok(CStr::from_bytes_until_nul(out).expect("os::realpath: realpath left no NUL in its buffer"))
}
pub fn getpid() -> i32 { unsafe { sys2::getpid() } }






/// The decompressors zip.rs reaches by `dlopen`, as q itself does. Each is loaded once a process and never closed; a failed
/// load is tried again by the next caller, as zip.rs's `zlib_load` did.
/// cbindgen:ignore
mod codecs {
    
    
    



}

/// A `core::fmt` sink on a stack buffer: `n` bytes, then `Err` (so a too-long value is an error, never a truncation)
pub struct Buf<const N: usize> { b: [u8; N], n: usize }
impl<const N: usize> Buf<N> {
    pub fn new() -> Self { Buf { b: [0; N], n: 0 } }
    pub fn bytes(&self) -> &[u8] { &self.b[..self.n] }
}
impl<const N: usize> Default for Buf<N> { fn default() -> Self { Self::new() } }
impl<const N: usize> core::fmt::Write for Buf<N> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let e = self.n.checked_add(s.len()).filter(|&e| e <= N).ok_or(core::fmt::Error)?;
        self.b[self.n..e].copy_from_slice(s.as_bytes());
        self.n = e;
        Ok(())
    }
}

/// `args` formatted and written to fd 2 with `write(2)`, whole or not at all up to 1 KiB (what C's `fprintf(stderr, …)`
/// sites of qlean print); a longer one goes out cut at 1 KiB and answers `EMSGSIZE`
pub fn eprint(args: core::fmt::Arguments) -> Result<(), i32> {
    let mut b = Buf::<1024>::new();
    let full = core::fmt::write(&mut b, args).is_ok();
    write_all(2, b.bytes())?;
    if full { Ok(()) } else { Err(EMSGSIZE) }
}
/// `exit(code)`: runs `atexit` handlers and flushes stdio, as the C `exit(1)` sites do
pub fn exit(code: i32) -> ! { unsafe { sys2::exit(code) } }



/// the value of `name`, copied out (the libc pointer dies with the next `setenv`)
pub fn getenv(name: &CStr) -> Option<Vec<u8>> {
    let p = unsafe { sys2::getenv(name.as_ptr()) };
    if p.is_null() { None } else { Some(unsafe { CStr::from_ptr(p) }.to_bytes().to_vec()) }
}
/// `sysconf(name)`; `None` when the answer is -1 (unsupported or indeterminate)
pub fn sysconf(name: i32) -> Option<i64> { let v = unsafe { sys2::sysconf(name) }; if v < 0 { None } else { Some(v) } }

// a dlopen handle is a process-wide token, safe to use from every thread
/// A file mapped into memory. `Drop` unmaps and has nowhere to report a failure, so a path that must see `munmap`'s errno
/// calls `unmap()`; `leak` gives the bytes to the process for good, as own.rs's `.own` parts are.
pub struct Map { p: *mut u8, len: usize }
impl Map {
    /// `mmap(NULL, len, prot, flags, fd, 0)`; the descriptor may be closed afterwards, the mapping holds the file
    pub fn file(f: &File, len: usize, prot: i32, flags: i32) -> Result<Map, i32> {
        let p = unsafe { sys2::mmap(core::ptr::null_mut(), len, prot, flags, f.0, 0) };
        if p as usize == usize::MAX { return Err(errno()) }
        Ok(Map { p: p.cast(), len })
    }
    pub fn as_slice(&self) -> &[u8] { unsafe { core::slice::from_raw_parts(self.p, self.len) } }
    /// never unmapped: the mapping lives as long as the process (`lean::sarrays_in` takes it)
    pub fn leak(self) -> &'static mut [u8] {
        let s = unsafe { core::slice::from_raw_parts_mut(self.p, self.len) };
        core::mem::forget(self);
        s
    }
    pub fn unmap(self) -> Result<(), i32> {
        let r = ok(unsafe { sys2::munmap(self.p.cast(), self.len) });
        core::mem::forget(self);
        r
    }
}
impl Drop for Map { fn drop(&mut self) { unsafe { sys2::munmap(self.p.cast(), self.len); } } }
