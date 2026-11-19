#![forbid(unsafe_code)]
//! qlean's own column file (own.rs's `qlean_file_replace`, `qlean_own_write`, `qlean_own_map`), without the Lean objects:
//! the header and its checks, the write-all and the temp-file-and-rename replace, and the mapping of the parts.
//!
//! The file: bytes 0..8 `qleancol`; byte 8 the format version (`OWN_VERSION`, `OWN_OLDEST` is read too); byte 9 the q type
//! code of the elements; byte 10 the attribute (0 none, 1 `s#, 2 `u#, 3 `p#, 4 `g#); byte 11 the constructor kind (0 bytes,
//! 1 the removed bitmap, refused: a boolean is a u1 foR, 2 foR, 3 alp, 4 enum); bytes 12..14 the u16 part count (`OWN_NPARTS`); bytes 14..16 the u16 byte length of the
//! enumeration domain name; bytes 16..24 the u64 element count; then 16 bytes a part (u64 offset, u64 length), the domain name,
//! and each part after zeros up to an offset that is a multiple of 8 and leaves `OWN_ROOM` zero bytes before it; then
//! `OWN_ROOM` zero bytes. The parts are the dense bytes; `metadata`, `pack`; `metadata`, `pack`, `alp`; `dict`,
//! `ids`. Nothing is transformed in either direction.
//!
//! A mapped part is a `ByteArray` of rc 0 (persistent: `lean_inc_ref`/`lean_dec_ref` do nothing, never exclusive, so every
//! in-place update copies first, as for an `.olean` compact region), its header written into the `OWN_ROOM` bytes before it;
//! the mapping is `MAP_PRIVATE`, so that write copies one page and never reaches the file. The mapping is never unmapped:
//! a persistent object has no finaliser, so nothing can say when the last `ByteArray` into it is gone. That is why a file is
//! replaced by a temporary and a rename: truncating a mapped path would turn every later read of its pages into SIGBUS.
use crate::why::Why;
use crate::os::{self, File};
use alloc::{format, string::String, vec, vec::Vec};
use core::ffi::CStr;
use core::sync::atomic::{AtomicUsize, Ordering};


pub const OWN_MAXPARTS: usize = 3;

pub const OWN_ROOM: u64 = 32;
pub const OWN_HEAD: usize = 24;
pub const OWN_VERSION: u8 = 4;
pub const OWN_NPARTS: [usize; 5] = [1, 1, 2, 3, 2];



/// The refusal `write_head` gives a bad kind, part count or name length; None, so a caller returns it.
pub fn refuse_head(kind: u8, np: usize, nl: usize, why: &mut Why) -> Option<usize> {
    why.say(format_args!("a column of kind 0, 2, 3 or 4 (kind 1, the bitmap, is gone: a boolean column is a u1 foR, kind 2) with its parts and a domain name under 65536 \
bytes, given kind {} with {} parts and a {}-byte name", kind, np, nl));
    None
}

/// `qlean_own_write` (own.rs) without the file: the header (`OWN_HEAD + 16 * len.len()` bytes into `head`)
/// and each part's 8-aligned offset after `OWN_ROOM` into `off`; answers the header length. None and `why` filled
/// when the kind, the part count or the `nl`-byte domain name is refused.
pub fn write_head(code: u8, attr: u8, kind: u8, count: u64, nl: usize, len: &[usize],
                  head: &mut [u8], off: &mut [usize], why: &mut Why) -> Option<usize> {
    let np = len.len();
    if kind > 4 || kind == 1 || np != OWN_NPARTS[kind as usize] || nl > 0xffff { return refuse_head(kind, np, nl, why) }
    head[..8].copy_from_slice(b"qleancol");
    head[8..12].copy_from_slice(&[OWN_VERSION, code, attr, kind]);
    head[12..14].copy_from_slice(&(np as u16).to_le_bytes());
    head[14..16].copy_from_slice(&(nl as u16).to_le_bytes());
    head[16..24].copy_from_slice(&count.to_le_bytes());
    let mut at = OWN_HEAD + 16 * np + nl;
    for (k, &l) in len.iter().enumerate() {
        let o = (at + OWN_ROOM as usize + 7) & !7;
        let t = OWN_HEAD + 16 * k;
        head[t..t + 8].copy_from_slice(&(o as u64).to_le_bytes());
        head[t + 8..t + 16].copy_from_slice(&(l as u64).to_le_bytes());
        off[k] = o;
        at = o + l;
    }
    Some(OWN_HEAD + 16 * np)
}




/// Why a column write or read failed: an errno, which the Lean side reports as `path. OS reports: <strerror>`, or the text
/// of a refusal -- a column or a file no kernel may read.
#[derive(Debug)]
pub enum Fail { Errno(i32), User(String) }
impl From<i32> for Fail { fn from(e: i32) -> Fail { Fail::Errno(e) } }

/// A `Why` buffer's text up to its NUL; every refusal is ASCII (numbers and fixed words).
pub fn text(buf: &[u8]) -> String {
    let z = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
    String::from_utf8(buf[..z].to_vec()).expect("own: a refusal text is ASCII")
}

/// `own_write_all` over a file: every segment whole (`os::write_all` continues a short write and retries `EINTR`).
pub fn write_segs(f: &File, segs: &[&[u8]]) -> Result<(), i32> { segs.iter().try_for_each(|s| f.write_all(s)) }

/// `r`, else the `close` error: the write's errno is the one reported when both fail.
pub fn close_after(f: File, r: Result<(), i32>) -> Result<(), i32> { let c = f.close(); r.and(c) }

/// own.rs `own_replace`: the segments as the whole content of `target`: a temporary in the same directory, then `rename`
/// (truncating a mapped path would turn the next read of its pages into SIGBUS; the old mapping keeps the old inode).
/// A link is written through as `open` would, and a device, fifo or socket is written in place: the name is the thing
/// itself and cannot be renamed over.
pub fn replace(target: &CStr, segs: &[&[u8]]) -> Result<(), i32> {
    static SERIAL: AtomicUsize = AtomicUsize::new(0);
    let st = match os::stat(target) { Ok(s) => Some(s), Err(os::ENOENT) => None, Err(e) => return Err(e) };
    let mut real = [0u8; os::PATH_MAX];
    let target = if st.is_some() { os::realpath(target, &mut real)? } else { target };
    if st.as_ref().is_some_and(|s| s.mode & os::S_IFMT != os::S_IFREG) {
        let f = File::open(target, os::O_WRONLY | os::O_CLOEXEC, 0)?;
        let w = write_segs(&f, segs);
        return close_after(f, w);
    }
    let mut tmp = target.to_bytes().to_vec();
    tmp.extend_from_slice(format!(".{}.{}.tmp\0", os::getpid(), SERIAL.fetch_add(1, Ordering::Relaxed)).as_bytes());
    let tmp = CStr::from_bytes_with_nul(&tmp).expect("own::replace: a NUL inside the path");
    let f = File::open(tmp, os::O_WRONLY | os::O_CREAT | os::O_EXCL | os::O_CLOEXEC, 0o666)?;
    let w = write_segs(&f, segs).and_then(|()| match &st { Some(s) => f.fchmod(s.mode & 0o7777), None => Ok(()) });
    let r = close_after(f, w).and_then(|()| os::rename(tmp, target));
    // the write's errno is the one reported; a temporary that also cannot be removed stays behind
    if r.is_err() { let _ = os::unlink(tmp); }
    r
}

/// own.rs `qlean_own_write`: the column file of `parts` (the constructor's `ByteArray`s) under `domain`, in the layout the
/// header note above describes (the format is `write_head`'s and `head`'s).
pub fn write(target: &CStr, code: u8, attr: u8, kind: u8, count: u64, domain: &[u8], parts: &[&[u8]]) -> Result<(), Fail> {
    static ZEROS: [u8; OWN_ROOM as usize + 8] = [0; OWN_ROOM as usize + 8];
    let len: Vec<usize> = parts.iter().map(|p| p.len()).collect();
    let (mut head, mut off, mut buf) = ([0u8; OWN_HEAD + 16 * OWN_MAXPARTS], [0usize; OWN_MAXPARTS], [0u8; 160]);
    let mut why = Why::new(&mut buf);
    let Some(hl) = write_head(code, attr, kind, count, domain.len(), &len, &mut head, &mut off, &mut why) else {
        return Err(Fail::User(text(&buf)));
    };
    let mut segs: Vec<&[u8]> = vec![&head[..hl], domain];
    let mut at = hl + domain.len();
    for (k, p) in parts.iter().enumerate() {
        segs.push(&ZEROS[..off[k] - at]);
        segs.push(p);
        at = off[k] + p.len();
    }
    segs.push(&ZEROS[..OWN_ROOM as usize]);
    Ok(replace(target, &segs)?)
}



