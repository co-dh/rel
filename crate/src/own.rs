#![forbid(unsafe_code)]
//! qlean's own column file (own.rs's `qlean_file_replace`, `qlean_own_write`, `qlean_own_map`), without the Lean objects:
//! the header and its checks, the write-all and the temp-file-and-rename replace, and the mapping of the parts.
//!
//! The file: bytes 0..8 `qleancol`; byte 8 the format version (`OWN_VERSION`, `OWN_OLDEST` is read too); byte 9 the q type
//! code of the elements; byte 10 the attribute (0 none, 1 `s#, 2 `u#, 3 `p#, 4 `g#); byte 11 the constructor kind (0 bytes,
//! 1 bits, 2 foR, 3 alp, 4 enum); bytes 12..14 the u16 part count (`OWN_NPARTS`); bytes 14..16 the u16 byte length of the
//! enumeration domain name; bytes 16..24 the u64 element count; then 16 bytes a part (u64 offset, u64 length), the domain name,
//! and each part after zeros up to an offset that is a multiple of 8 and leaves `OWN_ROOM` zero bytes before it; then
//! `OWN_ROOM` zero bytes. The parts are the dense bytes; the bitmap; `metadata`, `pack`; `metadata`, `pack`, `alp`; `dict`,
//! `ids`. Nothing is transformed in either direction.
//!
//! A mapped part is a `ByteArray` of rc 0 (persistent: `lean_inc_ref`/`lean_dec_ref` do nothing, never exclusive, so every
//! in-place update copies first, as for an `.olean` compact region), its header written into the `OWN_ROOM` bytes before it;
//! the mapping is `MAP_PRIVATE`, so that write copies one page and never reaches the file. The mapping is never unmapped:
//! a persistent object has no finaliser, so nothing can say when the last `ByteArray` into it is gone. That is why a file is
//! replaced by a temporary and a rename: truncating a mapped path would turn every later read of its pages into SIGBUS.
use crate::why::Why;
use crate::coc::{COC_EXC_FRM, Meta};
use crate::ids::{id_at, id_width, ids_bytes, ids_max};
use crate::layout::{Tail, exc_ok};
use crate::os::{self, File, Map};
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
    why.say(format_args!("a column of kind 0..4 with its parts and a domain name under 65536 \
bytes, given kind {} with {} parts and a {}-byte name", kind, np, nl));
    None
}

/// `qlean_own_write` (own.rs) without the file: the header (`OWN_HEAD + 16 * len.len()` bytes into `head`)
/// and each part's 8-aligned offset after `OWN_ROOM` into `off`; answers the header length. None and `why` filled
/// when the kind, the part count or the `nl`-byte domain name is refused.
pub fn write_head(code: u8, attr: u8, kind: u8, count: u64, nl: usize, len: &[usize],
                  head: &mut [u8], off: &mut [usize], why: &mut Why) -> Option<usize> {
    let np = len.len();
    if kind > 4 || np != OWN_NPARTS[kind as usize] || nl > 0xffff { return refuse_head(kind, np, nl, why) }
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



pub struct OwnHead { pub n: u64, pub hdr: usize, pub np: usize,
                     pub off: [usize; OWN_MAXPARTS], pub len: [usize; OWN_MAXPARTS], pub kind: u8 }
pub const OWN_OLDEST: u8 = 3;
pub fn le(m: &[u8], at: usize, w: usize) -> u64 {
    let mut b = [0u8; 8];
    b[..w].copy_from_slice(&m[at..at + w]);
    u64::from_le_bytes(b)
}
/// `m` = the whole mapping, at least OWN_HEAD bytes (the caller checks).
pub fn head(m: &[u8], why: &mut Why) -> Option<OwnHead> {
    let size = m.len() as u64;
    let kind = m[11];
    let np = le(m, 12, 2) as usize;
    let nl = le(m, 14, 2) as usize;
    let hdr = OWN_HEAD + 16 * np + nl;
    let n = le(m, 16, 8);
    if &m[..8] != b"qleancol" { why.say(format_args!("byte 0: the magic `qleancol`")); return None; }
    if m[8] < OWN_OLDEST || m[8] > OWN_VERSION {
        why.say(format_args!("byte 8: format version {} or {}, found {}; a version-1 file predates the \
Frame of Reference patch list and a version-2 one its per-block frames, and either is \
rewritten by `set` from the data it was made from", OWN_OLDEST, OWN_VERSION, m[8]));
        return None;
    }
    if kind > 4 || np != OWN_NPARTS[kind as usize] {
        why.say(format_args!("byte 11: a constructor kind in 0..4 with its 1, 1, 2, 3 or 2 parts, \
found kind {} with {} parts", kind, np));
        return None;
    }
    if hdr as u64 > size {
        why.say(format_args!("byte {}: a part table and domain name ending at byte {}, the file is \
{} bytes", OWN_HEAD, hdr, size));
        return None;
    }
    let mut h = OwnHead { n, hdr, np, off: [0; OWN_MAXPARTS], len: [0; OWN_MAXPARTS], kind };
    let mut end = hdr as u64;
    for k in 0..np {
        let at = OWN_HEAD + 16 * k;
        let (off, l) = (le(m, at, 8), le(m, at + 8, 8));
        if off % 8 != 0 {
            why.say(format_args!("part {} at byte {}: a data offset that is a multiple of 8, \
found {}", k, at, off));
            return None;
        }
        if off < end + OWN_ROOM {
            why.say(format_args!("part {} at byte {}: {} reserved bytes after byte {} before its \
data, found offset {}", k, at, OWN_ROOM, end, off));
            return None;
        }
        if off > size || l > size - off {
            why.say(format_args!("part {} at byte {}: {} bytes from byte {}, the file is {} \
bytes", k, at, l, off, size));
            return None;
        }
        h.off[k] = off as usize;
        h.len[k] = l as usize;
        end = off + l;
    }
    Some(h)
}
/// own.rs `own_check`: what a kernel trusts about the parts and the file could have wrong -- the Frame of Reference block
/// widths and offsets (`coc_view`: "the stored offsets are trusted"), the ALP sections, and an id past its dictionary.
/// Residuals and the cached `maxv` and `bsum` cannot make a read leave its part, so they are not checked. False with
/// `why` filled. `p` are the parts, `kind`'s first `OWN_NPARTS[kind]` of them.
pub fn check(kind: u8, n: u64, p: [&[u8]; OWN_MAXPARTS], why: &mut Why) -> bool {
    if kind == 2 || kind == 3 {
        if !check_coc(kind, n, p, why) { return false }
    }
    // `Enc.WF`'s bits clause: b.size = (n+7)/8 exactly. The dense kind's `n * width` is checked by `Own.lean`, which alone
    // knows the type's width.
    if kind == 1 && (n > u64::MAX - 7 || p[0].len() as u64 != n.wrapping_add(7) / 8) {
        why.say(format_args!("part 0 (bitmap): {} booleans need exactly {} bytes, found {}", n, n.wrapping_add(7) / 8, p[0].len()));
        return false;
    }
    kind != 4 || check_syms(n, p, why)
}
/// `check`'s Frame of Reference and ALP kinds (2 and 3): the metadata part, the pack, the patch list or ALP blob.
pub fn check_coc(kind: u8, n: u64, p: [&[u8]; OWN_MAXPARTS], why: &mut Why) -> bool {
    let (m, pk) = (p[0], p[1]);
    let nblk = m.len() / 33;
    if m.len() != 33 * nblk + 24 {
        why.say(format_args!("part 0: Frame of Reference metadata of 33 bytes a block and a 24-byte trailer, found {} bytes", m.len()));
        return false;
    }
    let lg = le(m, 32 * nblk + 16, 8);
    if !(crate::MIN_LG as u64..=crate::MAX_LG as u64).contains(&lg) {
        why.say(format_args!("part 0: a block size lg in {}..={}, found {}", crate::MIN_LG, crate::MAX_LG, lg));
        return false;
    }
    let blk = 1u64 << lg;
    if n > nblk as u64 * blk {
        why.say(format_args!("part 0: blocks for {} elements, found {} blocks of {}", n, nblk, blk));
        return false;
    }
    let Some(meta) = Meta::new(m, n as usize) else {
        why.say(format_args!("part 0: Frame of Reference metadata at an address that is not a multiple of 8"));
        return false;
    };
    // one branch-free pass that vectorises; only a file it rejects is walked again for the block
    let plen = pk.len() as u64;
    let bad = (0..nblk).fold(false, |bad, b| {
        let (wd, o) = (meta.width[b] as u64, meta.off[b]);
        bad | (wd > 64) | (o % 8 != 0) | (o > plen) | (blk * wd / 8 > plen.wrapping_sub(o))
    });
    if bad {
        for b in 0..nblk {
            let (wd, o) = (meta.width[b] as u64, meta.off[b]);
            let need = blk * wd / 8;
            if wd > 64 {
                why.say(format_args!("part 0 block {}: a residual width of 0..64 bits, found {}", b, wd));
                return false;
            }
            if o % 8 != 0 || o > plen || need > plen - o {
                why.say(format_args!("part 1 block {}: {} residual bytes at a pack offset that is a multiple of 8, found offset {} \
in a pack of {} bytes", b, need, o, plen));
                return false;
            }
        }
    }
    let e = meta.res_end();
    if kind == 2 {
        if pk.len() > e {
            let t = &pk[e..];
            if t.len() < 16 {
                why.say(format_args!("part 1: a 16-byte patch list header at byte {}, found {} bytes", e, t.len()));
                return false;
            }
            let (nexc, h1) = (u64::from_ne_bytes(t[..8].try_into().unwrap()), u64::from_ne_bytes(t[8..16].try_into().unwrap()));
            let (frm, esz) = (h1 & COC_EXC_FRM as u64 != 0, h1 & !(COC_EXC_FRM as u64));
            if !matches!(esz, 1 | 2 | 4 | 8) {
                why.say(format_args!("part 1: a patch list element width of 1, 2, 4 or 8 bytes, found {}", esz));
                return false;
            }
            return exc_ok(t, blk as usize, nblk, nexc, esz as usize, 1, if frm { Tail::Frames } else { Tail::None }, why);
        }
    } else {
        if pk.len() != e {
            why.say(format_args!("part 1: an ALP pack of exactly its {} residual bytes, found {}", e, pk.len()));
            return false;
        }
        let a = p[2];
        if a.len() < 16 {
            why.say(format_args!("part 2: a 16-byte ALP header, found {} bytes", a.len()));
            return false;
        }
        let flags = u64::from_ne_bytes(a[8..16].try_into().unwrap());
        return exc_ok(a, blk as usize, nblk, u64::from_ne_bytes(a[..8].try_into().unwrap()), if flags & 1 != 0 { 4 } else { 8 }, 2, Tail::Exps, why);
    }
    true
}
/// `check`'s symbol column (kind 4): a dictionary of NUL-ended symbols and the ids into it.
pub fn check_syms(n: u64, p: [&[u8]; OWN_MAXPARTS], why: &mut Why) -> bool {
    let (d, ids) = (p[0], p[1]);
    if d.last().is_some_and(|&z| z != 0) {
        why.say(format_args!("part 0: a NUL ending the last dictionary symbol at byte {}", d.len() - 1));
        return false;
    }
    let nd = d.iter().filter(|&&z| z == 0).count();
    let wd = id_width(nd);
    // `Enc.WF`'s enum clause: ids.size = ⌈n·idWidth/8⌉ exactly, not at least -- a longer pack is a file no writer made
    if n > usize::MAX as u64 / 64 || ids.len() != ids_bytes(n as usize, wd) {
        why.say(format_args!("part 1 (ids of the symbol column): {} ids of {} bits need exactly {} bytes, found {}", n, wd,
                             if n > usize::MAX as u64 / 64 { 0 } else { ids_bytes(n as usize, wd) }, ids.len()));
        return false;
    }
    // Checked here and not at each use: no fixed-width code for d != 2^w ids is free of patterns past d, and the ~40 kernels
    // that read ids are pure and clamp (`tab[u < nm ? u : nm]`, `idKey`), so they cannot raise.
    let n = n as usize;
    let loose = if wd == 0 { nd == 0 } else { wd == 64 || nd != 1usize << wd };
    if n != 0 && loose && ids_max(ids, wd, n) >= nd {
        if let Some(i) = (0..n).find(|&i| id_at(ids, wd, i) >= nd) {
            why.say(format_args!("part 1 id {}: an index into the {} dictionary symbols, found {}", i, nd, id_at(ids, wd, i)));
            return false;
        }
    }
    true
}
/// What `map` hands the Lean side: the header, part table and domain name copied out, and the mapping with each part's
/// `(offset, length)` in it; `lean::sarrays_in` turns the parts into `ByteArray`s.
pub struct Mapped { pub head: Vec<u8>, pub map: &'static mut [u8], pub spans: Vec<(usize, usize)> }
/// own.rs `qlean_own_map`: maps `path` (`MAP_PRIVATE`, so the header write of a part copies the page and never reaches the
/// file) and checks it. The mapping is never unmapped, the lifetime rule of a compact region: a persistent object has no
/// count to say when the last `ByteArray` into it is gone; a refused file is unmapped.
pub fn map(path: &CStr) -> Result<Mapped, Fail> {
    let f = File::open(path, os::O_RDONLY | os::O_CLOEXEC, 0)?;
    let st = f.stat()?;
    if st.mode & os::S_IFMT == os::S_IFDIR { return Err(Fail::Errno(os::EISDIR)) }
    let size = st.size as u64;
    if size < OWN_HEAD as u64 {
        return Err(Fail::User(format!("a {}-byte own-format header, the file is {} bytes", OWN_HEAD, size)));
    }
    // NORESERVE: only the header pages are ever written, so the file's size is not memory to commit
    let m = Map::file(&f, size as usize, os::PROT_READ | os::PROT_WRITE, os::MAP_PRIVATE | os::MAP_NORESERVE)?;
    // the mapping holds the file; the descriptor has nothing left to report that a read could lose
    drop(f);
    let mut buf = [0u8; 320];
    let mut why = Why::new(&mut buf);
    let h = head(m.as_slice(), &mut why);
    let none: &[u8] = &[];
    let ok = h.as_ref().is_some_and(|h| {
        let s = m.as_slice();
        check(h.kind, h.n, core::array::from_fn(|k| if k < h.np { &s[h.off[k]..h.off[k] + h.len[k]] } else { none }), &mut why)
    });
    let Some(h) = h.filter(|_| ok) else { m.unmap()?; return Err(Fail::User(text(&buf))) };
    let head = m.as_slice()[..h.hdr].to_vec();
    Ok(Mapped { head, spans: (0..h.np).map(|k| (h.off[k], h.len[k])).collect(), map: m.leak() })
}
#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    // kind 0, one part at 64 of length 16, domain name 0 bytes: hdr = 24 + 16 = 40, end + 32 = 72 > 64 is
    // refused, so the part sits at 72.
    #[test] fn head_ok() {
        let mut m = vec![0u8; 96];
        m[..8].copy_from_slice(b"qleancol");
        m[8] = 4; m[11] = 0; m[12] = 1; m[16] = 7;
        m[24..32].copy_from_slice(&72u64.to_le_bytes());
        m[32..40].copy_from_slice(&16u64.to_le_bytes());
        let mut buf = [0u8; 64];
        let h = head(&m, &mut Why::new(&mut buf)).unwrap();
        assert_eq!((h.n, h.hdr, h.np, h.off[0], h.len[0], h.kind), (7, 40, 1, 72, 16, 0));
    }

    fn err(m: &[u8]) -> alloc::string::String {
        let mut buf = [0u8; 320];
        assert!(head(m, &mut Why::new(&mut buf)).is_none());
        let z = buf.iter().position(|&b| b == 0).unwrap();
        alloc::string::String::from_utf8(buf[..z].to_vec()).unwrap()
    }
    fn good() -> alloc::vec::Vec<u8> {
        let mut m = vec![0u8; 96];
        m[..8].copy_from_slice(b"qleancol");
        m[8] = 4; m[12] = 1;
        m[24..32].copy_from_slice(&72u64.to_le_bytes());
        m[32..40].copy_from_slice(&16u64.to_le_bytes());
        m
    }
    #[test] fn head_errors() {
        let mut m = good(); m[0] = b'x';
        assert_eq!(err(&m), "byte 0: the magic `qleancol`");
        let mut m = good(); m[8] = 2;
        assert!(err(&m).starts_with("byte 8: format version 3 or 4, found 2; a version-1 file predates the Frame"));
        let mut m = good(); m[11] = 5;
        assert_eq!(err(&m), "byte 11: a constructor kind in 0..4 with its 1, 1, 2, 3 or 2 parts, found kind 5 with 1 parts");
        let mut m = good(); m[11] = 2;
        assert_eq!(err(&m), "byte 11: a constructor kind in 0..4 with its 1, 1, 2, 3 or 2 parts, found kind 2 with 1 parts");
        let mut m = good(); m[14] = 100;
        assert_eq!(err(&m), "byte 24: a part table and domain name ending at byte 140, the file is 96 bytes");
        let mut m = good(); m[24] = 73;
        assert_eq!(err(&m), "part 0 at byte 24: a data offset that is a multiple of 8, found 73");
        let mut m = good(); m[24] = 64;
        assert_eq!(err(&m), "part 0 at byte 24: 32 reserved bytes after byte 40 before its data, found offset 64");
        let mut m = good(); m[32] = 40;
        assert_eq!(err(&m), "part 0 at byte 24: 40 bytes from byte 72, the file is 96 bytes");
    }

    // expected values: the C of e16b3fd (/data/tmp/qrs/K26/diff.c: 40000 parts of every kind, mutated headers, 0 mismatches)
    fn say(kind: u8, n: u64, p: [&[u8]; OWN_MAXPARTS]) -> (bool, alloc::string::String) {
        let mut buf = [0u8; 320];
        let ok = check(kind, n, p, &mut Why::new(&mut buf));
        let z = buf.iter().position(|&b| b == 0).unwrap();
        (ok, alloc::string::String::from_utf8(buf[..z].to_vec()).unwrap())
    }
    #[test] fn check_bitmap_and_symbols() {
        let e: &[u8] = &[];
        assert_eq!(say(1, 9, [&[0; 2], e, e]), (true, "".into()));
        assert_eq!(say(1, 9, [&[0; 3], e, e]), (false, "part 0 (bitmap): 9 booleans need exactly 2 bytes, found 3".into()));
        assert_eq!(say(1, u64::MAX, [e, e, e]).1, "part 0 (bitmap): 18446744073709551615 booleans need exactly 0 bytes, found 0");
        // 3 symbols need 2-bit ids, so 5 ids are 2 bytes; the last symbol must end in its NUL
        assert_eq!(say(4, 5, [b"a\0b\0c\0", &[0; 2], e]), (true, "".into()));
        assert_eq!(say(4, 5, [b"a\0b\0c", &[0; 2], e]), (false, "part 0: a NUL ending the last dictionary symbol at byte 4".into()));
        assert_eq!(say(4, 5, [b"a\0b\0c\0", &[0; 3], e]).1, "part 1 (ids of the symbol column): 5 ids of 2 bits need exactly 2 bytes, found 3");
        // id 3 is past the 3 symbols (2-bit ids are not all valid)
        assert_eq!(say(4, 2, [b"a\0b\0c\0", &[0b1100], e]).1, "part 1 id 1: an index into the 3 dictionary symbols, found 3");
    }
    #[test] fn check_frame_of_reference_metadata() {
        let e: &[u8] = &[];
        assert_eq!(say(2, 0, [&[0; 20], e, e]).1, "part 0: Frame of Reference metadata of 33 bytes a block and a 24-byte trailer, found 20 bytes");
        let mut m = [0u8; 57];
        assert_eq!(say(2, 2000, [&m, e, e]).1, "part 0: a block size lg in 6..=16, found 0");
        for lg in [5u8, 17] { m[48] = lg; assert_eq!(say(2, 10, [&m, e, e]).1, format!("part 0: a block size lg in 6..=16, found {lg}")) }
        m[48] = 10;
        assert_eq!(say(2, 2000, [&m, e, e]).1, "part 0: blocks for 2000 elements, found 1 blocks of 1024");
        m[48] = 6;
        assert_eq!(say(2, 65, [&m, e, e]).1, "part 0: blocks for 65 elements, found 1 blocks of 64");
        m[48] = 10;
        m[56] = 65; // block 0's width, past 64 bits
        assert_eq!(say(2, 10, [&m, &[0; 8], e]).1, "part 0 block 0: a residual width of 0..64 bits, found 65");
        m[56] = 8; // 1024 residual bytes in an 8-byte pack
        assert_eq!(say(2, 10, [&m, &[0; 8], e]).1, "part 1 block 0: 1024 residual bytes at a pack offset that is a multiple of 8, found offset 0 in a pack of 8 bytes");
    }

    fn tmp(name: &str) -> alloc::ffi::CString {
        let d = std::path::PathBuf::from(std::env::var("TMPDIR").unwrap_or("/data/tmp/relk".into())).join("own-unit");
        let f = d.join(name);
        std::fs::create_dir_all(f.parent().unwrap()).expect("own tests: cannot create the scratch directory");
        alloc::ffi::CString::new(f.to_str().unwrap()).unwrap()
    }
    // a kind 0 column written then mapped: the parts come back at their offsets, the file is the layout of the header note
    #[test] fn write_then_map() {
        let p = tmp("w.col");
        write(&p, 7, 0, 0, 3, b"", &[b"abc"]).unwrap();
        let m = map(&p).unwrap();
        assert_eq!((m.head.len(), m.spans.len()), (40, 1));
        assert_eq!(&m.map[m.spans[0].0..m.spans[0].0 + 3], b"abc");
        assert_eq!(m.spans[0].0 % 8, 0);
        let f = std::fs::read(p.to_str().unwrap()).unwrap();
        assert_eq!(&f[..12], b"qleancol\x04\x07\x00\x00");
        assert_eq!(f.len(), m.spans[0].0 + 3 + OWN_ROOM as usize);
    }
    #[test] fn write_refuses_and_fails() {
        let p = tmp("r.col");
        assert!(matches!(write(&p, 7, 0, 5, 3, b"", &[b"abc"]), Err(Fail::User(w)) if w.starts_with("a column of kind 0..4")));
        assert!(matches!(write(&p, 7, 0, 2, 3, b"", &[b"abc"]), Err(Fail::User(_))));
        assert!(matches!(write(c"/data/tmp/relk-absent-dir/x", 7, 0, 0, 3, b"", &[b"abc"]), Err(Fail::Errno(os::ENOENT))));
        assert!(matches!(map(c"/data/tmp/relk-absent-dir/x"), Err(Fail::Errno(os::ENOENT))));
        assert!(matches!(map(c"/data/tmp"), Err(Fail::Errno(os::EISDIR))));
        let short = tmp("short.col");
        std::fs::write(short.to_str().unwrap(), b"qleancol").unwrap();
        assert!(matches!(map(&short), Err(Fail::User(w)) if w == "a 24-byte own-format header, the file is 8 bytes"));
    }
    // a replace keeps the mode of the file it replaces and leaves no temporary
    #[test] fn replace_keeps_mode() {
        use std::os::unix::fs::PermissionsExt;
        let p = tmp("alone/m.bin");
        std::fs::write(p.to_str().unwrap(), b"old").unwrap();
        std::fs::set_permissions(p.to_str().unwrap(), std::fs::Permissions::from_mode(0o640)).unwrap();
        replace(&p, &[b"ne", b"w!"]).unwrap();
        assert_eq!(std::fs::read(p.to_str().unwrap()).unwrap(), b"new!");
        assert_eq!(std::fs::metadata(p.to_str().unwrap()).unwrap().permissions().mode() & 0o7777, 0o640);
        let n = std::fs::read_dir(std::path::Path::new(p.to_str().unwrap()).parent().unwrap()).unwrap()
            .filter(|e| e.as_ref().unwrap().file_name().to_str().unwrap().ends_with(".tmp")).count();
        assert_eq!(n, 0);
    }
}
