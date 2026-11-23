#![forbid(unsafe_code)]
//! qlean's own column file (own.rs's `qlean_file_replace`, `qlean_own_write`, `qlean_own_map`), without the Lean objects:
//! the header and its checks, the write-all and the temp-file-and-rename replace, and the mapping of the parts.
//!
//! The file: bytes 0..8 `qleancol`; byte 8 the format version (`OWN_VERSION`, `OWN_OLDEST` is read too); byte 9 the q type
//! code of the elements; byte 10 the constructor kind (2 foR, 5 a side of `1`, its count and no part; 0 bytes and 3 alp
//! were removed in version 5, 4 enum after it: the kinds `OWN_NPARTS` gives a part count); byte 11 the part count
//! (`OWN_NPARTS[kind]`); bytes 12..16 zero, so the count is 8-aligned (version 7 removed the attribute byte and the
//! enumeration domain name, which nothing read); bytes 16..24 the u64 element
//! count; then 16 bytes a part (u64 offset, u64 length), and each part after zeros up to an offset
//! that is a multiple of 8 and leaves `OWN_ROOM` zero bytes before it; then `OWN_ROOM` zero bytes. The parts are the
//! foR's `metadata` and `pack`. Nothing is transformed in either
//! direction.
//!
//! A mapped part is a `ByteArray` of rc 0 (persistent: `lean_inc_ref`/`lean_dec_ref` do nothing, never exclusive, so every
//! in-place update copies first, as for an `.olean` compact region), its header written into the `OWN_ROOM` bytes before it;
//! the mapping is `MAP_PRIVATE`, so that write copies one page and never reaches the file. The mapping is never unmapped:
//! a persistent object has no finaliser, so nothing can say when the last `ByteArray` into it is gone. That is why a file is
//! replaced by a temporary and a rename: truncating a mapped path would turn every later read of its pages into SIGBUS.
use crate::why::Why;
use crate::coc::{COC_EXC_FRM, Meta};
use crate::layout::{Tail, exc_ok};
use crate::os::{self, File, Map};
use alloc::{format, string::String, vec, vec::Vec};
use core::ffi::CStr;
use core::sync::atomic::{AtomicUsize, Ordering};


pub const OWN_MAXPARTS: usize = 3;

pub const OWN_ROOM: u64 = 32;
pub const OWN_HEAD: usize = 24;
pub const OWN_VERSION: u8 = 8;
/// The part count of each constructor kind, `None` for a number that is no kind: 1 was the bitmap, gone since a boolean
/// is a u1 foR (kind 2), 4 the symbol dictionary and ids, gone since a symbol column is its foR ids (PLAN 8.3); 2 and 5
/// keep their numbers, so a file on disk keeps its meaning. `Own.lean`'s `ownNParts`.
pub const OWN_NPARTS: [Option<usize>; 6] = [None, None, Some(2), None, None, Some(0)];
/// The part count of `kind`, None when `kind` is no kind: the one test the writer and the reader make of it.
pub fn nparts(kind: u8) -> Option<usize> { OWN_NPARTS.get(kind as usize).copied().flatten() }

/// The kinds with their part counts as both refusals name them, `2:2 or 5:0` (`Own.lean`'s `ownKinds`).
pub struct Kinds;
impl core::fmt::Display for Kinds {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let ks = || OWN_NPARTS.iter().enumerate().filter_map(|(k, n)| n.map(|n| (k, n)));
        let last = ks().count() - 1;
        ks().enumerate().try_for_each(|(i, (k, n))| write!(f, "{}{}:{}", if i == 0 { "" } else if i == last { " or " } else { ", " }, k, n))
    }
}

/// The bytes `write`'s refusal needs: `refuse_head`'s text at kind 255, `usize::MAX` parts and a `usize::MAX`-byte name
/// (`write_refuses_and_fails` checks it is not cut).
pub const OWN_WHY: usize = 256;

/// The refusal `write_head` gives a bad kind or part count; None, so a caller returns it.
pub fn refuse_head(kind: u8, np: usize, why: &mut Why) -> Option<usize> {
    why.say(format_args!("a column of kind and part count {}, given kind {} with {} parts", Kinds, kind, np));
    None
}

/// `qlean_own_write` (own.rs) without the file: the header (`OWN_HEAD + 16 * len.len()` bytes into `head`)
/// and each part's 8-aligned offset after `OWN_ROOM` into `off`; answers the header length. None and `why` filled
/// when the kind or the part count is refused.
pub fn write_head(code: u8, kind: u8, count: u64, len: &[usize],
                  head: &mut [u8], off: &mut [usize], why: &mut Why) -> Option<usize> {
    let np = len.len();
    if nparts(kind) != Some(np) { return refuse_head(kind, np, why) }
    head[..8].copy_from_slice(b"qleancol");
    head[8..16].copy_from_slice(&[OWN_VERSION, code, kind, np as u8, 0, 0, 0, 0]);
    head[16..24].copy_from_slice(&count.to_le_bytes());
    let mut at = OWN_HEAD + 16 * np;
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


/// every missing ancestor directory of `target`, outermost first, mode 0o777 under the umask; `EEXIST` is success (another
/// writer made it), any other errno is returned. A POSIX path: the separator is the byte `/`, empty components are skipped.
pub fn mkdirs(target: &CStr) -> Result<(), i32> {
    let mut buf = target.to_bytes_with_nul().to_vec();
    for i in 1..buf.len() - 1 {
        if buf[i] != b'/' || buf[i - 1] == b'/' { continue; }
        buf[i] = 0;
        let r = os::mkdir(CStr::from_bytes_until_nul(&buf).expect("own::mkdirs: NUL written above"), 0o777);
        buf[i] = b'/';
        match r { Err(e) if e != os::EEXIST => return Err(e), _ => {} }
    }
    Ok(())
}

/// own.rs `own_replace`: the segments as the whole content of `target`: a temporary in the same directory, then `rename`
/// (truncating a mapped path would turn the next read of its pages into SIGBUS; the old mapping keeps the old inode).
/// A link is written through as `open` would, and a device, fifo or socket is written in place: the name is the thing
/// itself and cannot be renamed over.
pub fn replace(target: &CStr, segs: &[&[u8]]) -> Result<(), i32> { replace_by(target, |f| write_segs(f, segs)) }

/// `replace` with the content written by `write` into the open file, for a writer that produces it in pieces; an error
/// of `write` (an errno or a refusal of its own) leaves `target` as it was.
pub fn replace_by<E: From<i32>>(target: &CStr, write: impl FnOnce(&File) -> Result<(), E>) -> Result<(), E> {
    static SERIAL: AtomicUsize = AtomicUsize::new(0);
    let st = match os::stat(target) { Ok(s) => Some(s), Err(os::ENOENT) => None, Err(e) => return Err(E::from(e)) };
    let mut real = [0u8; os::PATH_MAX];
    let target = if st.is_some() { os::realpath(target, &mut real)? } else { target };
    if st.as_ref().is_some_and(|s| s.mode & os::S_IFMT != os::S_IFREG) {
        let f = File::open(target, os::O_WRONLY | os::O_CLOEXEC, 0)?;
        let w = write(&f);
        let c = f.close();
        return w.and(c.map_err(E::from));
    }
    let mut tmp = target.to_bytes().to_vec();
    tmp.extend_from_slice(format!(".{}.{}.tmp\0", os::getpid(), SERIAL.fetch_add(1, Ordering::Relaxed)).as_bytes());
    let tmp = CStr::from_bytes_with_nul(&tmp).expect("own::replace: a NUL inside the path");
    let flags = os::O_WRONLY | os::O_CREAT | os::O_EXCL | os::O_CLOEXEC;
    // a missing target may have missing ancestors: made only after the open said ENOENT, so the common case pays nothing
    let f = match File::open(tmp, flags, 0o666) {
        Err(os::ENOENT) if st.is_none() => { mkdirs(target)?; File::open(tmp, flags, 0o666)? }
        r => r?,
    };
    let w = write(&f).and_then(|()| match &st { Some(s) => f.fchmod(s.mode & 0o7777).map_err(E::from), None => Ok(()) });
    // closed whatever `w` is; the write's error is the one reported when both fail
    let c = f.close();
    let r = w.and(c.map_err(E::from)).and_then(|()| os::rename(tmp, target).map_err(E::from));
    // the write's errno is the one reported; a temporary that also cannot be removed stays behind
    if r.is_err() { let _ = os::unlink(tmp); }
    r
}

/// own.rs `qlean_own_write`: the column file of `parts` (the constructor's `ByteArray`s), in the layout the
/// header note above describes (the format is `write_head`'s and `head`'s).
pub fn write(target: &CStr, code: u8, kind: u8, count: u64, parts: &[&[u8]]) -> Result<(), Fail> {
    static ZEROS: [u8; OWN_ROOM as usize + 8] = [0; OWN_ROOM as usize + 8];
    let len: Vec<usize> = parts.iter().map(|p| p.len()).collect();
    let (mut head, mut off, mut buf) = ([0u8; OWN_HEAD + 16 * OWN_MAXPARTS], [0usize; OWN_MAXPARTS], [0u8; OWN_WHY]);
    let mut why = Why::new(&mut buf);
    let Some(hl) = write_head(code, kind, count, &len, &mut head, &mut off, &mut why) else {
        return Err(Fail::User(text(&buf)));
    };
    let mut segs: Vec<&[u8]> = vec![&head[..hl]];
    let mut at = hl;
    for (k, p) in parts.iter().enumerate() {
        segs.push(&ZEROS[..off[k] - at]);
        segs.push(p);
        at = off[k] + p.len();
    }
    segs.push(&ZEROS[..OWN_ROOM as usize]);
    Ok(replace(target, &segs)?)
}



pub struct OwnHead { pub n: u64, pub np: usize,
                     pub off: [usize; OWN_MAXPARTS], pub len: [usize; OWN_MAXPARTS], pub code: u8, pub kind: u8 }
pub const OWN_OLDEST: u8 = 8;
pub fn le(m: &[u8], at: usize, w: usize) -> u64 {
    let mut b = [0u8; 8];
    b[..w].copy_from_slice(&m[at..at + w]);
    u64::from_le_bytes(b)
}
/// `m` = the whole mapping, at least OWN_HEAD bytes (the caller checks).
pub fn head(m: &[u8], why: &mut Why) -> Option<OwnHead> {
    let size = m.len() as u64;
    let kind = m[10];
    let np = m[11] as usize;
    let hdr = OWN_HEAD + 16 * np;
    let n = le(m, 16, 8);
    if &m[..8] != b"qleancol" { why.say(format_args!("byte 0: the magic `qleancol`")); return None; }
    if m[8] < OWN_OLDEST || m[8] > OWN_VERSION {
        why.say(format_args!("byte 8: format version {}, found {}; a file before version {} is rewritten by `set` from the data \
it was made from: version 8 made null residual 0, 7 removed the attribute byte and the domain name, 6 widened the patch list's block \
offsets to u64, and 5 removed the dense `bytes` (kind 0) and `alp` (kind 3) forms", OWN_VERSION, m[8], OWN_VERSION));
        return None;
    }
    if nparts(kind) != Some(np) {
        why.say(format_args!("byte 10: a constructor kind and part count {}, found kind {} with {} parts", Kinds, kind, np));
        return None;
    }
    if hdr as u64 > size {
        why.say(format_args!("byte {}: a part table ending at byte {}, the file is {} bytes", OWN_HEAD, hdr, size));
        return None;
    }
    let mut h = OwnHead { n, np, off: [0; OWN_MAXPARTS], len: [0; OWN_MAXPARTS], code: m[9], kind };
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
/// `why` filled. `p` are the parts, `kind`'s first `nparts(kind)` of them.
pub fn check(kind: u8, n: u64, p: [&[u8]; OWN_MAXPARTS], why: &mut Why) -> bool {
    if kind == 2 {
        if !check_coc(kind, n, p, why) { return false }
    }
    // the dense kind's `n * width` is checked by `Own.lean`, which alone knows the type's width
    true
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
        let (wd, o) = (meta.w(b) as u64, meta.off[b]);
        bad | (wd > 64) | (o % 8 != 0) | (o > plen) | (blk * wd / 8 > plen.wrapping_sub(o))
    });
    if bad {
        for b in 0..nblk {
            let (wd, o) = (meta.w(b) as u64, meta.off[b]);
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
    }
    true
}
/// What `map` hands the Lean side, `Db.OwnFile`'s fields: the header's and the mapping with each part's
/// `(offset, length)` in it, which `lean::sarrays_in` turns into `ByteArray`s in place.
pub struct Mapped { pub code: u8, pub kind: u8, pub n: u64, pub map: &'static mut [u8], pub spans: Vec<(usize, usize)> }
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
    Ok(Mapped { code: h.code, kind: h.kind, n: h.n,
                spans: (0..h.np).map(|k| (h.off[k], h.len[k])).collect(), map: m.leak() })
}
#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    // kind 2, two parts of 16 bytes: hdr = 24 + 2 * 16 = 56, so part 0 sits at 56 + 32 = 88 and
    // part 1 at 88 + 16 + 32 = 136; the file is 160 bytes.
    #[test] fn head_ok() {
        let mut m = good(); m[16] = 7;
        let mut buf = [0u8; 64];
        let h = head(&m, &mut Why::new(&mut buf)).unwrap();
        assert_eq!((h.n, h.np, h.off[0], h.len[0], h.off[1], h.kind), (7, 2, 88, 16, 136, 2));
        m[16] = 0;
    }

    fn err(m: &[u8]) -> alloc::string::String {
        let mut buf = [0u8; 320];
        assert!(head(m, &mut Why::new(&mut buf)).is_none());
        let z = buf.iter().position(|&b| b == 0).unwrap();
        alloc::string::String::from_utf8(buf[..z].to_vec()).unwrap()
    }
    fn good() -> alloc::vec::Vec<u8> {
        let mut m = vec![0u8; 160];
        m[..8].copy_from_slice(b"qleancol");
        m[8] = OWN_VERSION; m[10] = 2; m[11] = 2;
        m[24..32].copy_from_slice(&88u64.to_le_bytes());
        m[32..40].copy_from_slice(&16u64.to_le_bytes());
        m[40..48].copy_from_slice(&136u64.to_le_bytes());
        m[48..56].copy_from_slice(&16u64.to_le_bytes());
        m
    }
    #[test] fn head_errors() {
        let mut m = good(); m[0] = b'x';
        assert_eq!(err(&m), "byte 0: the magic `qleancol`");
        let mut m = good(); m[8] = 4;
        assert!(err(&m).starts_with("byte 8: format version 8, found 4; a file before version 8 is rewritten by `set`"));
        let mut m = good(); m[10] = 5;
        assert_eq!(err(&m), "byte 10: a constructor kind and part count 2:2 or 5:0, found kind 5 with 2 parts");
        let mut m = good(); m[11] = 1;
        assert_eq!(err(&m), "byte 10: a constructor kind and part count 2:2 or 5:0, found kind 2 with 1 parts");
        // kinds 0 (`bytes`), 1 (the bitmap) and 3 (`alp`) are no kind, whatever their part count
        for k in [0u8, 1, 3] {
            let mut m = good(); m[10] = k; m[11] = 1;
            assert_eq!(err(&m), format!("byte 10: a constructor kind and part count 2:2 or 5:0, found kind {k} with 1 parts"));
        }
        let mut m = good(); m[10] = 255; m[11] = 255;
        assert_eq!(err(&m), "byte 10: a constructor kind and part count 2:2 or 5:0, found kind 255 with 255 parts");
        let mut m = good(); m.truncate(40);
        assert_eq!(err(&m), "byte 24: a part table ending at byte 56, the file is 40 bytes");
        let mut m = good(); m[24] = 89;
        assert_eq!(err(&m), "part 0 at byte 24: a data offset that is a multiple of 8, found 89");
        let mut m = good(); m[24] = 80;
        assert_eq!(err(&m), "part 0 at byte 24: 32 reserved bytes after byte 56 before its data, found offset 80");
        let mut m = good(); m[40] = 128;
        assert_eq!(err(&m), "part 1 at byte 40: 32 reserved bytes after byte 104 before its data, found offset 128");
        let mut m = good(); m[32] = 80;
        assert_eq!(err(&m), "part 0 at byte 24: 80 bytes from byte 88, the file is 160 bytes");
    }

    // expected values: the C of e16b3fd (/data/tmp/qrs/K26/diff.c: 40000 parts of every kind, mutated headers, 0 mismatches)
    fn say(kind: u8, n: u64, p: [&[u8]; OWN_MAXPARTS]) -> (bool, alloc::string::String) {
        let mut buf = [0u8; 320];
        let ok = check(kind, n, p, &mut Why::new(&mut buf));
        let z = buf.iter().position(|&b| b == 0).unwrap();
        (ok, alloc::string::String::from_utf8(buf[..z].to_vec()).unwrap())
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
    // an empty kind 2 column (no block, `lg` 10 in the trailer, an empty pack) written then mapped: the parts come
    // back at their offsets, the file is the layout of the header note
    #[test] fn write_then_map() {
        let p = tmp("w.col");
        let mut md = [0u8; 24]; md[16] = 10;
        write(&p, 7, 2, 0, &[&md, &[]]).unwrap();
        let m = map(&p).unwrap();
        assert_eq!((m.code, m.kind, m.n, m.spans.len()), (7, 2, 0, 2));
        assert_eq!(&m.map[m.spans[0].0..m.spans[0].0 + 24], &md);
        assert_eq!((m.spans[0].0 % 8, m.spans[1].0 % 8), (0, 0));
        let f = std::fs::read(p.to_str().unwrap()).unwrap();
        assert_eq!(&f[..12], b"qleancol\x08\x07\x02\x02");
        assert_eq!(f.len(), m.spans[1].0 + OWN_ROOM as usize);
    }
    #[test] fn write_refuses_and_fails() {
        let p = tmp("r.col");
        assert!(matches!(write(&p, 7, 6, 3, &[b"abc"]), Err(Fail::User(w)) if w == "a column of kind and part count \
2:2 or 5:0, given kind 6 with 1 parts"));
        assert!(matches!(write(&p, 7, 2, 3, &[b"abc"]), Err(Fail::User(_))));
        // kind 1, the bitmap, is no kind: refused at its old part count
        assert!(matches!(write(&p, 7, 1, 3, &[b"abc"]), Err(Fail::User(w)) if w.ends_with("given kind 1 with 1 parts")));
        // the worst case fits `write`'s buffer whole
        let mut buf = [0u8; OWN_WHY];
        refuse_head(255, usize::MAX, &mut Why::new(&mut buf));
        assert_eq!(text(&buf), "a column of kind and part count 2:2 or 5:0, given kind 255 with 18446744073709551615 parts");
        assert!(matches!(write(c"/dev/null/x", 7, 2, 3, &[b"abc", b"d"]), Err(Fail::Errno(20))));
        assert!(matches!(map(c"/data/tmp/relk-absent-dir/x"), Err(Fail::Errno(os::ENOENT))));
        assert!(matches!(map(c"/data/tmp"), Err(Fail::Errno(os::EISDIR))));
        let short = tmp("short.col");
        std::fs::write(short.to_str().unwrap(), b"qleancol").unwrap();
        assert!(matches!(map(&short), Err(Fail::User(w)) if w == "a 24-byte own-format header, the file is 8 bytes"));
    }
    // a target whose ancestors do not exist gets them; an ancestor that is a regular file is ENOTDIR, not success
    #[test] fn replace_makes_ancestors() {
        let p = tmp("mk/seed.bin");
        let d = std::path::Path::new(p.to_str().unwrap()).parent().unwrap().to_owned();
        std::fs::remove_dir_all(d.join("deep")).ok();
        let q = alloc::ffi::CString::new(d.join("deep/a/b/c.bin").to_str().unwrap()).unwrap();
        replace(&q, &[b"xy"]).unwrap();
        assert_eq!(std::fs::read(q.to_str().unwrap()).unwrap(), b"xy");
        std::fs::write(d.join("file"), b"f").unwrap();
        let bad = alloc::ffi::CString::new(d.join("file/x/c.bin").to_str().unwrap()).unwrap();
        assert_eq!(replace(&bad, &[b"z"]), Err(20));
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
