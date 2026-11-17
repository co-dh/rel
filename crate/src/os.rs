//! libc beyond the allocator, as safe calls: bytes and numbers in, bytes and numbers out (phase-2 §2.4; O0 extends it).
//! Every mirrored struct is asserted against its C header in c/abi.c.


// libc declares these itself, with its own types
/// cbindgen:ignore
pub mod sys {
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


pub fn errno() -> i32 { unsafe { *__errno_location() } }



pub const O_WRONLY: i32 = 1;
pub const O_CREAT: i32 = 0o100;
pub const O_EXCL: i32 = 0o200;
pub const O_CLOEXEC: i32 = 0o2000000;
pub const S_IFMT: u32 = 0o170000;
pub const S_IFREG: u32 = 0o100000;
pub const ENOENT: i32 = 2;
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

use alloc::{string::String, vec::Vec};
use core::ffi::{c_void, CStr};

// libc declares these itself, with its own types
/// cbindgen:ignore
pub mod sys2 {
    use super::{AddrInfo, Stat};
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
        pub fn realpath(path: *const c_char, out: *mut c_char) -> *mut c_char;
        pub fn getpid() -> i32;
        pub fn dlopen(path: *const c_char, flags: i32) -> *mut c_void;
        pub fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
        pub fn dlerror() -> *const c_char;
        pub fn socket(domain: i32, ty: i32, proto: i32) -> i32;
        pub fn connect(fd: i32, addr: *const u8, len: u32) -> i32;
        pub fn getaddrinfo(node: *const c_char, service: *const c_char, hints: *const AddrInfo, res: *mut *mut AddrInfo) -> i32;
        pub fn freeaddrinfo(res: *mut AddrInfo);
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
    /// `buf.len()` bytes from offset `off`, looping over short reads and `EINTR` as zip.rs's `zpread` does; the end of the
    /// file before `buf` is full is `Short::Eof(bytes read so far)`
    pub fn pread_exact(&self, buf: &mut [u8], off: u64) -> Result<(), Short> {
        let mut got = 0;
        while got < buf.len() {
            let r = unsafe { sys2::pread(self.0, buf.as_mut_ptr().add(got), buf.len() - got, (off + got as u64) as i64) };
            if r < 0 { match errno() { EINTR => continue, e => return Err(Short::Errno(e)) } }
            if r == 0 { return Err(Short::Eof(got)) }
            got += r as usize;
        }
        Ok(())
    }
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
    use super::*;
    use core::ffi::{c_char, c_int, c_ulong};
    use core::sync::atomic::{AtomicPtr, Ordering};

    /// `name` of `lib` as the function type `F`
    fn fnptr<F: Copy>(lib: &Lib, so: &'static str, name: &'static CStr) -> Result<F, Missing> {
        const { assert!(core::mem::size_of::<F>() == core::mem::size_of::<*mut c_void>()) };
        let p = lib.sym(name).map_err(|why| Missing { so, sym: name.to_str().expect("os: a symbol name is ASCII"), why })?;
        // a function pointer is a data pointer's size on every target this builds for (asserted above); `p` is a
        // `dlsym` answer for the symbol whose C type `F` spells
        Ok(unsafe { core::mem::transmute_copy::<*mut c_void, F>(&p) })
    }
    fn open(so: &'static str, sym: &'static CStr) -> Result<Lib, Missing> {
        let c = alloc::ffi::CString::new(so).expect("os: a library name has no NUL");
        Lib::open(&c, RTLD_NOW).map_err(|why| Missing { so, sym: sym.to_str().expect("os: a symbol name is ASCII"), why })
    }
    /// `cell`'s value, or the `load()` of it published there; a racing loser's copy is dropped, the libraries not closed
    fn once<T>(cell: &AtomicPtr<T>, load: impl FnOnce() -> Result<T, Missing>) -> Result<&'static T, Missing> {
        let p = cell.load(Ordering::Acquire);
        if !p.is_null() { return Ok(unsafe { &*p }) }
        let b = alloc::boxed::Box::into_raw(alloc::boxed::Box::new(load()?));
        match cell.compare_exchange(core::ptr::null_mut(), b, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => Ok(unsafe { &*b }),
            Err(won) => { drop(unsafe { alloc::boxed::Box::from_raw(b) }); Ok(unsafe { &*won }) }
        }
    }
    fn text(p: *const c_char) -> String { String::from_utf8_lossy(unsafe { CStr::from_ptr(p) }.to_bytes()).into_owned() }

    pub struct Zlib { uncompress: unsafe extern "C" fn(*mut u8, *mut c_ulong, *const u8, c_ulong) -> c_int,
                      error: unsafe extern "C" fn(c_int) -> *const c_char }
    impl Zlib {
        /// zlib's `uncompress(dst, &n, src, src.len())`: the bytes it wrote, or `zError`'s text for its code
        pub fn uncompress(&self, dst: &mut [u8], src: &[u8]) -> Result<usize, String> {
            let mut n = dst.len() as c_ulong;
            let r = unsafe { (self.uncompress)(dst.as_mut_ptr(), &mut n, src.as_ptr(), src.len() as c_ulong) };
            if r != 0 { return Err(text(unsafe { (self.error)(r) })) }
            Ok(n as usize)
        }
    }
    pub struct Snappy { uncompress: unsafe extern "C" fn(*const u8, usize, *mut u8, *mut usize) -> c_int }
    impl Snappy {
        /// `snappy_uncompress(src, src.len(), dst, &n)` with `n` the room of `dst`: the bytes it wrote
        pub fn uncompress(&self, dst: &mut [u8], src: &[u8]) -> Result<usize, String> {
            let mut n = dst.len();
            match unsafe { (self.uncompress)(src.as_ptr(), src.len(), dst.as_mut_ptr(), &mut n) } {
                0 => Ok(n),
                1 => Err("invalid input".into()),
                _ => Err("buffer too small".into()),
            }
        }
    }
    pub struct Lz4 { decompress_safe: unsafe extern "C" fn(*const u8, *mut u8, c_int, c_int) -> c_int }
    impl Lz4 {
        /// `LZ4_decompress_safe(src, dst, src.len(), dst.len())`, lengths as C `int`s as zip.rs passed them
        pub fn uncompress(&self, dst: &mut [u8], src: &[u8]) -> Result<usize, String> {
            let r = unsafe { (self.decompress_safe)(src.as_ptr(), dst.as_mut_ptr(), src.len() as c_int, dst.len() as c_int) };
            if r < 0 { Err("malformed input".into()) } else { Ok(r as usize) }
        }
    }
    pub struct Zstd { decompress: unsafe extern "C" fn(*mut u8, usize, *const u8, usize) -> usize,
                      is_error: unsafe extern "C" fn(usize) -> u32, error_name: unsafe extern "C" fn(usize) -> *const c_char }
    impl Zstd {
        /// `ZSTD_decompress(dst, dst.len(), src, src.len())`: the bytes it wrote, or `ZSTD_getErrorName`'s text
        pub fn uncompress(&self, dst: &mut [u8], src: &[u8]) -> Result<usize, String> {
            let r = unsafe { (self.decompress)(dst.as_mut_ptr(), dst.len(), src.as_ptr(), src.len()) };
            if unsafe { (self.is_error)(r) } != 0 { return Err(text(unsafe { (self.error_name)(r) })) }
            Ok(r)
        }
    }

    static ZLIB: AtomicPtr<Zlib> = AtomicPtr::new(core::ptr::null_mut());
    static SNAPPY: AtomicPtr<Snappy> = AtomicPtr::new(core::ptr::null_mut());
    static LZ4: AtomicPtr<Lz4> = AtomicPtr::new(core::ptr::null_mut());
    static ZSTD: AtomicPtr<Zstd> = AtomicPtr::new(core::ptr::null_mut());
    pub fn zlib() -> Result<&'static Zlib, Missing> {
        once(&ZLIB, || {
            let l = open("libz.so.1", c"zError")?;
            let error = fnptr(&l, "libz.so.1", c"zError")?;
            Ok(Zlib { error, uncompress: fnptr(&l, "libz.so.1", c"uncompress")? })
        })
    }
    pub fn snappy() -> Result<&'static Snappy, Missing> {
        once(&SNAPPY, || { let l = open("libsnappy.so.1", c"snappy_uncompress")?;
                           Ok(Snappy { uncompress: fnptr(&l, "libsnappy.so.1", c"snappy_uncompress")? }) })
    }
    pub fn lz4() -> Result<&'static Lz4, Missing> {
        once(&LZ4, || { let l = open("liblz4.so.1", c"LZ4_decompress_safe")?;
                        Ok(Lz4 { decompress_safe: fnptr(&l, "liblz4.so.1", c"LZ4_decompress_safe")? }) })
    }
    pub fn zstd() -> Result<&'static Zstd, Missing> {
        once(&ZSTD, || {
            let l = open("libzstd.so.1", c"ZSTD_isError")?;
            let is_error = fnptr(&l, "libzstd.so.1", c"ZSTD_isError")?;
            let error_name = fnptr(&l, "libzstd.so.1", c"ZSTD_getErrorName")?;
            Ok(Zstd { is_error, error_name, decompress: fnptr(&l, "libzstd.so.1", c"ZSTD_decompress")? })
        })
    }
}
pub use codecs::{lz4, snappy, zlib, zstd, Lz4, Snappy, Zlib, Zstd};

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

/// glibc's `struct addrinfo` on x86-64: `addrlen` is a `socklen_t`, so 4 bytes of padding follow it; `next` is typed `void *` because cbindgen cannot print a self-referential typedef
#[repr(C)]
pub struct AddrInfo { pub flags: i32, pub family: i32, pub socktype: i32, pub protocol: i32, pub addrlen: u32,
                      pub pad0: u32, pub addr: *mut u8, pub canonname: *mut u8, pub next: *mut c_void }
#[cfg(test)]
mod tests {
    use super::*;
    const ENOENT: i32 = 2;
    const EBADF: i32 = 9;
    const ECONNREFUSED: i32 = 111;
    fn dir() -> std::path::PathBuf {
        let d = std::path::PathBuf::from(std::env::var("TMPDIR").unwrap_or("/data/tmp/qrs/O0".into())).join("os-unit");
        std::fs::create_dir_all(&d).expect("os tests: cannot create the scratch directory");
        d
    }
    fn c(p: &std::path::Path) -> alloc::ffi::CString { alloc::ffi::CString::new(p.to_str().unwrap()).unwrap() }

    #[test] fn file_roundtrip() {
        let p = c(&dir().join("rt.bin"));
        let f = File::open(&p, O_WRONLY | O_CREAT | O_CLOEXEC, 0o644).unwrap();
        f.write_all(b"hello, mapping").unwrap();
        f.close().unwrap();
        let f = File::open(&p, O_RDONLY | O_CLOEXEC, 0).unwrap();
        let st = f.stat().unwrap();
        assert_eq!(st.size, 14);
        assert_eq!(st.mode & S_IFMT, 0o100000);
        let mut b = [0u8; 5];
        f.pread_exact(&mut b, 7).unwrap();
        assert_eq!(&b, b"mappi");
        assert_eq!(f.pread_exact(&mut [0u8; 8], 10), Err(Short::Eof(4)));
        let m = Map::file(&f, 14, PROT_READ, MAP_PRIVATE).unwrap();
        assert_eq!(m.as_slice(), b"hello, mapping");
        m.unmap().unwrap();
        assert_eq!(stat(&p).unwrap().size, 14);
        unlink(&p).unwrap();
        assert_eq!(unlink(&p), Err(ENOENT));
    }
    #[test] fn errors_are_the_errno() {
        assert_eq!(File::open(&c(&dir().join("absent")), O_RDONLY, 0).err(), Some(ENOENT));
        assert_eq!(stat(c"/data/tmp/qrs/O0/absent/x").err(), Some(ENOENT));
        assert_eq!(write_all(-1, b"x"), Err(EBADF));
        assert_eq!(File(-1).stat().err(), Some(EBADF));
        assert_eq!(File(-1).into_raw(), -1);
        assert_eq!(File(-1).close(), Err(EBADF));
        // a zero-length mapping is `EINVAL`
        let f = File::open(c"/dev/null", O_RDONLY, 0).unwrap();
        assert_eq!(Map::file(&f, 0, PROT_READ, MAP_PRIVATE).err(), Some(22));
        let mut b = [0u8; 256];
        assert_eq!(strerror(ENOENT, &mut b).unwrap().to_str().unwrap(), "No such file or directory");
        assert_eq!(f.stat().unwrap().mode & S_IFMT, 0o020000);
        let d = File::open(c"/", O_RDONLY, 0).unwrap();
        assert_eq!(d.stat().unwrap().mode & S_IFMT, S_IFDIR);
    }
    #[test] fn rename_realpath_getpid() {
        let a = c(&dir().join("a.tmp"));
        let b = c(&dir().join("b.tmp"));
        File::open(&a, O_WRONLY | O_CREAT | O_EXCL, 0o600).unwrap().fchmod(0o640).unwrap();
        assert_eq!(File::open(&a, O_WRONLY | O_CREAT | O_EXCL, 0o600).err(), Some(17));
        assert_eq!(stat(&a).unwrap().mode & 0o7777, 0o640);
        rename(&a, &b).unwrap();
        assert_eq!(stat(&a).err(), Some(ENOENT));
        let mut out = [0u8; PATH_MAX];
        let rp = realpath(&b, &mut out).unwrap();
        assert!(rp.to_str().unwrap().ends_with("os-unit/b.tmp"));
        assert_eq!(realpath(&a, &mut [0u8; PATH_MAX]).err(), Some(ENOENT));
        unlink(&b).unwrap();
        assert_eq!(getpid() as u32, std::process::id());
    }
    #[test] fn env_and_sysconf() {
        assert_eq!(getenv(c"QRS_O0_UNSET"), None);
        setenv(c"QRS_O0_SET", c"v1").unwrap();
        assert_eq!(getenv(c"QRS_O0_SET"), Some(b"v1".to_vec()));
        setenv(c"QRS_O0_SET", c"v2").unwrap();
        assert_eq!(getenv(c"QRS_O0_SET"), Some(b"v2".to_vec()));
        assert_eq!(setenv(c"a=b", c"x"), Err(22));
        assert!(sysconf(SC_NPROCESSORS_ONLN).unwrap() >= 1);
        assert_eq!(sysconf(-1), None);
    }
    #[test] fn lib_open_and_sym() {
        let l = Lib::open(c"libm.so.6", RTLD_NOW).unwrap();
        let f: extern "C" fn(f64) -> f64 = unsafe { core::mem::transmute(l.sym(c"cos").unwrap()) };
        assert_eq!(f(0.0), 1.0);
        assert!(l.sym(c"qrs_no_such_symbol").unwrap_err().contains("qrs_no_such_symbol"));
        assert!(Lib::open(c"libqrs_absent.so", RTLD_NOW).unwrap_err().contains("libqrs_absent.so"));
    }
    #[test] fn sock_connect() {
        let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let port = l.local_addr().unwrap().port() as i64;
        let s = Sock::connect(c"127.0.0.1", port).unwrap();
        let (mut peer, _) = l.accept().unwrap();
        s.0.write_all(b"ping").unwrap();
        let mut b = [0u8; 4];
        std::io::Read::read_exact(&mut peer, &mut b).unwrap();
        assert_eq!(&b, b"ping");
        assert!(s.into_raw() >= 0);
        drop(l);
        assert_eq!(Sock::connect(c"127.0.0.1", port).err(), Some(Conn::Errno(ECONNREFUSED)));
        assert_eq!(Sock::connect(c"nohost.invalid", 5).err(), Some(Conn::Unresolved));
        assert_eq!(Sock::connect(c"", port).err(), Some(Conn::Errno(ECONNREFUSED)));
    }
    #[test] fn eprint_formats() {
        let mut b = Buf::<8>::new();
        assert!(core::fmt::write(&mut b, format_args!("{}-{}", 12, "ab")).is_ok());
        assert_eq!(b.bytes(), b"12-ab");
        assert!(core::fmt::write(&mut b, format_args!("toolong")).is_err());
        assert_eq!(eprint(format_args!("os::eprint test {}\n", 1)), Ok(()));
        assert_eq!(eprint(format_args!("{}", "x".repeat(2000))), Err(EMSGSIZE));
    }
}
/// A shared library from `dlopen`. Never closed: zip.rs keeps its four for the life of the process, so there is no `Drop`.
#[derive(Debug)]
pub struct Lib(*mut c_void);
// a dlopen handle is a process-wide token, safe to use from every thread
unsafe impl Send for Lib {}
unsafe impl Sync for Lib {}
impl Lib {
    /// `dlopen(path, flags)`; the error is `dlerror`'s text
    pub fn open(path: &CStr, flags: i32) -> Result<Lib, String> {
        let h = unsafe { sys2::dlopen(path.as_ptr(), flags) };
        if h.is_null() { Err(dl_error("dlopen")) } else { Ok(Lib(h)) }
    }
    /// the address of `name`; a null address is a failure, as in zip.rs's `zsym`
    pub fn sym(&self, name: &CStr) -> Result<*mut c_void, String> {
        let f = unsafe { sys2::dlsym(self.0, name.as_ptr()) };
        if f.is_null() { Err(dl_error("dlsym")) } else { Ok(f) }
    }
}
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
/// A library or symbol zip.rs needs that `dlopen`/`dlsym` could not give: the library's file name, the symbol the load was
/// after, and `dlerror`'s text.
#[derive(Debug)]
pub struct Missing { pub so: &'static str, pub sym: &'static str, pub why: String }
pub const RTLD_NOW: i32 = 2;
/// glibc's `struct rusage` on x86-64: two `timeval`s, then fourteen `long`s from `ru_maxrss` (in KiB) on
#[repr(C)]
pub struct Rusage { pub utime: [i64; 2], pub stime: [i64; 2], pub maxrss: i64, pub rest: [i64; 13] }
/// How `pread_exact` stopped short: an errno, or the end of the file after `Eof(n)` bytes had been read
#[derive(Debug, PartialEq)]
pub enum Short { Errno(i32), Eof(usize) }
/// glibc's `struct tm` on x86-64; `gmtoff` is the GNU/BSD field that makes `utc_offset` the offset at that instant
#[repr(C)]
pub struct Tm { pub sec: i32, pub min: i32, pub hour: i32, pub mday: i32, pub mon: i32, pub year: i32, pub wday: i32,
                pub yday: i32, pub isdst: i32, pub gmtoff: i64, pub zone: *const u8 }
pub fn dl_error(what: &str) -> String {
    let e = unsafe { sys2::dlerror() };
    if e.is_null() { return alloc::format!("{what}: dlerror has no text") }
    String::from_utf8_lossy(unsafe { CStr::from_ptr(e) }.to_bytes()).into_owned()
}
