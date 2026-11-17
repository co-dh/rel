#![forbid(unsafe_code)]
//! A kdb+ column file as a block source (zip.rs, moved): the file and its block table, a cursor per worker, and q's IPC
//! compression. The file layout is the one zip.rs's header comment described:
//!
//!   bytes 0..8 "kxzipped", the compressed logical blocks, a 32-byte trailer (u8 version 3, 3 pad, u8 algorithm, u8 level, 2 pad,
//!   u64 uncompressed length, u64 file offset the blocks end at, u64 logical block size), 8 bytes a block (u32 compressed
//!   length, u32 the block's own algorithm), and a last u64 block count. A file without the magic is the stream itself.
//!
//! Every failed read, inflate or malformed trailer is recorded once, the first one wins, and raised as an `IO.Error`.

use crate::os::{self, First, Short};
use alloc::{format, string::String, vec::Vec};
use core::ffi::CStr;

/// Why a read failed: the errno of a failed `open`/`fstat` (Lean words it, naming the file), or the text of any other
/// failure (an `IO.userError`; the Lean side adds the path).
#[derive(Debug, PartialEq)]
pub enum Fail { Errno(i32), Why(String) }

/// What zip.rs's `vsnprintf` into `why[480]` left of a message
const WHY_MAX: usize = 479;
const ZNAME: [&str; 6] = ["stored", "kdb+ ipc", "gzip", "snappy", "lz4hc", "zstd"];

/// `n` copies of `v`, or `None` when the allocator refuses: zip.rs reports a refused allocation as an error, not an abort
fn filled<T: Clone>(v: T, n: usize) -> Option<Vec<T>> {
    let mut x = Vec::new();
    x.try_reserve_exact(n).ok()?;
    x.resize(n, v);
    Some(x)
}

/// The decompressors the open file's blocks name, loaded when the block table was read
#[derive(Default)]
struct Libs { zlib: Option<&'static os::Zlib>, snappy: Option<&'static os::Snappy>, lz4: Option<&'static os::Lz4>,
              zstd: Option<&'static os::Zstd> }

/// A kdb+ column file: either `kxzipped` (a block table and compressed logical blocks) or a plain stream, which is read as
/// blocks of 128 KiB. Shared by the workers of one pass, each with a `Cursor`; the first failure any of them records is the
/// one `error` reports.
pub struct File {
    file: os::File,
    /// file bytes; uncompressed bytes, logical block size, blocks
    size: u64, ulen: u64, l: u64, nblk: u64,
    /// the `nblk + 1` file offsets of the blocks, `None` for a plain file
    at: Option<Vec<u64>>,
    algo: Vec<u32>,
    /// the longest compressed block
    maxc: usize,
    /// where the element region begins in the uncompressed stream
    start: u64,
    libs: Libs,
    bad: First<String>,
}

impl File {
    /// `zopen`: `Fail::Errno` for a missing file or a directory, `Fail::Why` for a `kxzipped` file whose trailer, block table
    /// or algorithms do not hold up
    pub fn open(path: &CStr) -> Result<File, Fail> {
        let file = os::File::open(path, os::O_RDONLY | os::O_CLOEXEC, 0).map_err(Fail::Errno)?;
        let st = file.stat().map_err(Fail::Errno)?;
        if st.mode & os::S_IFMT == os::S_IFDIR { return Err(Fail::Errno(os::EISDIR)) }
        let mut z = File { file, size: st.size as u64, ulen: st.size as u64, l: 0, nblk: 0, at: None, algo: Vec::new(), maxc: 0,
                           start: 0, libs: Libs::default(), bad: First::new() };
        if z.parse() { Ok(z) } else { Err(z.error()) }
    }
    /// the uncompressed stream's length
    pub fn ulen(&self) -> usize { self.ulen as usize }
    /// a failure was recorded: the pass stops
    pub fn bad(&self) -> bool { self.bad.is_set() }
    /// the first failure recorded
    pub fn error(&self) -> Fail { Fail::Why(self.bad.get().cloned().unwrap_or_default()) }
    /// records `why` unless an earlier failure holds the cell; always false, so a check reads `return self.fail(..)`
    fn fail(&self, mut why: String) -> bool {
        while why.len() > WHY_MAX { why.pop(); }
        self.bad.set(why);
        false
    }
    /// `zpread`: exactly `buf.len()` bytes at `off`, or a recorded failure naming `what`
    fn pread(&self, buf: &mut [u8], off: u64, what: &str) -> bool {
        let n = buf.len();
        match self.file.pread_exact(buf, off) {
            Ok(()) => true,
            Err(Short::Errno(e)) => {
                let mut b = [0u8; 256];
                let why = os::strerror(e, &mut b).map_or_else(|| format!("Unknown error {e}"), |s| s.to_string_lossy().into_owned());
                self.fail(format!("{what}: pread of {n} bytes at byte {off}: {why}"))
            }
            Err(Short::Eof(got)) => self.fail(format!("{what}: {n} bytes at byte {off}, the file ends after {}", off + got as u64)),
        }
    }
    /// `zlib_load`: resolves what block algorithm `a` calls, once a process
    fn load(&mut self, a: u32) -> bool {
        let r = match a {
            0 | 1 => Ok(()),
            2 => os::zlib().map(|l| self.libs.zlib = Some(l)),
            3 => os::snappy().map(|l| self.libs.snappy = Some(l)),
            4 => os::lz4().map(|l| self.libs.lz4 = Some(l)),
            5 => os::zstd().map(|l| self.libs.zstd = Some(l)),
            _ => return self.fail(format!("a block algorithm in 0..5, found {a}")),
        };
        match r {
            Ok(()) => true,
            Err(m) => self.fail(format!("algorithm {a} ({}) needs `{}` of {}: {}", ZNAME[a as usize], m.sym, m.so, m.why)),
        }
    }
    /// the rest of `zopen`: the magic, the trailer and the block table of a `kxzipped` file
    fn parse(&mut self) -> bool {
        self.l = 1 << 17;
        self.nblk = self.ulen / self.l + (self.ulen % self.l != 0) as u64;
        if self.size < 8 { return true }
        let mut magic = [0u8; 8];
        if !self.pread(&mut magic, 0, "the file's first 8 bytes") { return false }
        if &magic != b"kxzipped" { return true }
        if self.size < 48 {
            return self.fail(format!("a kxzipped file of at least 48 bytes (magic, 32-byte trailer, block count), found {}", self.size));
        }
        let mut cnt = [0u8; 8];
        if !self.pread(&mut cnt, self.size - 8, "kxzipped block count") { return false }
        let nblk = u64::from_ne_bytes(cnt);
        if nblk > (self.size - 48) / 8 {
            return self.fail(format!("kxzipped block count at byte {}: a count the file's {} bytes can hold, found {nblk}", self.size - 8, self.size));
        }
        let hat = self.size - 8 - 8 * nblk - 32;
        let mut hdr = [0u8; 32];
        if !self.pread(&mut hdr, hat, "kxzipped trailer") { return false }
        let word = |i: usize| u64::from_ne_bytes(hdr[i..i + 8].try_into().expect("zip: 8 bytes of a 32-byte trailer"));
        (self.ulen, self.l) = (word(8), word(24));
        let cend = word(16);
        if hdr[0] != 3 { return self.fail(format!("kxzipped trailer at byte {hat}: format version 3, found {}", hdr[0])) }
        if cend != hat {
            return self.fail(format!("kxzipped trailer at byte {hat}: the blocks ending where it starts, it records byte {cend}"));
        }
        if self.l == 0 || self.l & (self.l - 1) != 0 || self.l > 1 << 30 {
            return self.fail(format!("kxzipped trailer at byte {hat}: a logical block size that is a power of two up to 2^30, found {}", self.l));
        }
        let want = self.ulen / self.l + (self.ulen % self.l != 0) as u64;
        if nblk != want {
            return self.fail(format!("kxzipped trailer at byte {hat}: {} uncompressed bytes in blocks of {} is {want} blocks, it lists {nblk}", self.ulen, self.l));
        }
        self.nblk = nblk;
        let (Some(mut ent), Some(mut at), Some(mut algo)) = (filled(0u8, 8 * nblk as usize), filled(0u64, nblk as usize + 1), filled(0u32, nblk as usize)) else {
            return self.fail(format!("memory for {nblk} block entries"));
        };
        if !self.pread(&mut ent, hat + 32, "kxzipped block table") { return false }
        at[0] = 8;
        let mut seen = 0u32;
        for k in 0..nblk as usize {
            let len = u32::from_ne_bytes(ent[8 * k..8 * k + 4].try_into().expect("zip: 4 bytes"));
            let a = u32::from_ne_bytes(ent[8 * k + 4..8 * k + 8].try_into().expect("zip: 4 bytes"));
            at[k + 1] = at[k] + len as u64;
            algo[k] = a;
            self.maxc = self.maxc.max(len as usize);
            if a > 5 || seen >> a & 1 == 0 {
                if !self.load(a) { return false }
                seen |= 1 << a;
            }
        }
        let end = at[nblk as usize];
        self.at = Some(at);
        self.algo = algo;
        if end != cend {
            return self.fail(format!("kxzipped block table at byte {}: block lengths that end at byte {cend} where the trailer starts, they end at byte {end}", hat + 32));
        }
        true
    }
    /// How many bytes `head_into` reads: the stream's first 4096, or all of a shorter one
    pub fn head_len(&self) -> usize { self.ulen.min(4096) as usize }
    /// `qlean_zip_head`'s read: the first `dst.len()` (= `head_len`) bytes of the stream. A plain file is read as it lies,
    /// not through the 128 KiB logical block a cursor would allocate and fill around them.
    pub fn head_into(&self, dst: &mut [u8]) -> Result<(), Fail> {
        if self.at.is_none() {
            return if self.pread(dst, 0, "the file's first bytes") { Ok(()) } else { Err(self.error()) };
        }
        let n = dst.len();
        let Some(mut c) = Cursor::new(self) else { return Err(self.error()) };
        match c.at(self, 0, n) {
            Some(p) => { dst.copy_from_slice(p); Ok(()) }
            None => Err(self.error()),
        }
    }
    /// `qlean_zip_bytes`'s read: the whole stream into `dst` (`ulen` bytes). A plain file is one `pread`; each block of a
    /// `kxzipped` one is inflated in a cursor and copied once into place.
    pub fn bytes_into(&self, dst: &mut [u8]) -> Result<(), Fail> {
        if self.at.is_none() {
            return if self.pread(dst, 0, "the whole file") { Ok(()) } else { Err(self.error()) };
        }
        let Some(mut c) = Cursor::new(self) else { return Err(self.error()) };
        for (k, part) in (0..self.nblk).zip(dst.chunks_mut(self.l as usize)) {
            match c.block(self, k) {
                Some(b) => part.copy_from_slice(b),
                None => return Err(self.error()),
            }
        }
        Ok(())
    }
    /// `qlean_zip_parts`'s argument check: `n` elements of `width` bytes from byte `start` must lie inside the stream;
    /// it is then the element region the cursors' offsets count from
    pub fn region(&mut self, start: usize, n: usize, width: usize) -> Result<(), Fail> {
        if width == 0 || n > (usize::MAX - start) / width || (start + n * width) as u64 > self.ulen {
            self.fail(format!("{n} elements of {width} bytes from byte {start}, the uncompressed stream is {} bytes", self.ulen));
            return Err(self.error());
        }
        self.start = start as u64;
        Ok(())
    }
}

/// One worker's view of a `File`: the logical block it holds, a compressed block, and a carry for an encoder block that
/// straddles two logical blocks.
pub struct Cursor {
    /// 64 bytes of zeros, then one logical block: algorithm 1 reads 8 zero bytes before its output
    raw: Vec<u8>,
    cbuf: Vec<u8>,
    carry: Vec<u8>,
    /// the logical block in `raw`
    k: Option<u64>,
}

impl Cursor {
    /// `zcur_open`; `None`, with the failure recorded, when the buffers cannot be had
    pub fn new(z: &File) -> Option<Cursor> {
        let (raw, cbuf) = (filled(0u8, 64 + ((z.l + 63) & !63) as usize), filled(0u8, z.maxc + 1));
        let (Some(raw), Some(cbuf)) = (raw, cbuf) else {
            z.fail(format!("memory for one {}-byte logical block", z.l));
            return None;
        };
        Some(Cursor { raw, cbuf, carry: Vec::new(), k: None })
    }
    /// `zload`: logical block `k`, inflated; the one place a block's algorithm is switched on
    pub fn block(&mut self, z: &File, k: u64) -> Option<&[u8]> {
        let want = (z.ulen - k * z.l).min(z.l) as usize;
        if self.k != Some(k) && !self.load(z, k, want) { return None }
        Some(&self.raw[64..64 + want])
    }
    fn load(&mut self, z: &File, k: u64, want: usize) -> bool {
        self.k = None;
        let what = format!("block {k} of {}", z.nblk);
        let Some(at) = &z.at else {
            if !z.pread(&mut self.raw[64..64 + want], k * z.l, &what) { return false }
            self.k = Some(k);
            return true;
        };
        let (off, algo) = (at[k as usize], z.algo[k as usize]);
        let n = (at[k as usize + 1] - off) as usize;
        let src = if algo != 0 { &mut self.cbuf[..n] } else { &mut self.raw[64..64 + n.min(want)] };
        if !z.pread(src, off, &what) { return false }
        let (src, raw) = (&self.cbuf[..n], &mut self.raw);
        let got = match algo {
            0 => Ok(n),
            1 => crate::zip::zq(src, &mut raw[56..64 + want]).map(|()| want).map_err(|e| e.to_string_lossy().into_owned()),
            2 => z.libs.zlib.expect("zip: zlib loaded with the block table").uncompress(&mut raw[64..64 + want], src),
            3 => z.libs.snappy.expect("zip: snappy loaded with the block table").uncompress(&mut raw[64..64 + want], src),
            4 => z.libs.lz4.expect("zip: lz4 loaded with the block table").uncompress(&mut raw[64..64 + want], src),
            _ => z.libs.zstd.expect("zip: zstd loaded with the block table").uncompress(&mut raw[64..64 + want], src),
        };
        let name = ZNAME[algo as usize];
        match got {
            Err(why) => z.fail(format!("{what} at byte {off}: {name} says {why}")),
            Ok(g) if g != want => z.fail(format!("{what} at byte {off}: {want} uncompressed bytes as the trailer implies, {name} gave {g}")),
            Ok(_) => { self.k = Some(k); true }
        }
    }
    /// `zat`: the `len` bytes at byte `off` of the element region, good until the cursor is asked again; `None`, with the
    /// failure recorded, stops the pass
    pub fn at(&mut self, z: &File, off: usize, len: usize) -> Option<&[u8]> {
        let (pos, len64) = (z.start + off as u64, len as u64);
        if pos.wrapping_add(len64) > z.ulen {
            z.fail(format!("bytes {pos} to {} of the uncompressed stream, which ends after {}", pos.wrapping_add(len64), z.ulen));
            return None;
        }
        if len == 0 { return Some(&self.raw[64..64]) }
        let (mut k, mut inn) = (pos / z.l, pos % z.l);
        if inn + len64 <= z.l {
            if self.block(z, k).is_none() { return None }
            return Some(&self.raw[64 + inn as usize..64 + inn as usize + len]);
        }
        if len > self.carry.len() {
            self.carry = Vec::new();
            match filled(0u8, (len + 63) & !63) {
                Some(c) => self.carry = c,
                None => { z.fail(format!("memory for a {len}-byte carry")); return None }
            }
        }
        let mut done = 0;
        while done < len {
            let take = ((z.l - inn) as usize).min(len - done);
            self.block(z, k)?;
            self.carry[done..done + take].copy_from_slice(&self.raw[64 + inn as usize..64 + inn as usize + take]);
            (done, k, inn) = (done + take, k + 1, 0);
        }
        Some(&self.carry[..len])
    }
}

/// q's IPC compression (algorithm 1): `b` is a whole compressed message, `dst` is 8 zero bytes + `want`; back
/// references are offsets into the message, header included. Every index is checked: the input is a file.
pub fn zq(b: &[u8], dst: &mut [u8]) -> Result<(), &'static core::ffi::CStr> {
    const END: &core::ffi::CStr = c"a stream that ends inside the block";
    const PAST: &core::ffi::CStr = c"a back reference that runs past the block";
    let n = b.len();
    if n < 12 { return Err(c"a message shorter than its 12-byte header") }
    if b[..4] != [1, 0, 1, 0] { return Err(c"a header that is not 01 00 01 00") }
    if u32::from_ne_bytes([b[4], b[5], b[6], b[7]]) as usize != n {
        return Err(c"a header whose message length is not the block's compressed length");
    }
    let total = u32::from_ne_bytes([b[8], b[9], b[10], b[11]]) as usize;
    if dst.len() != total { return Err(c"a message whose header states another length") }
    let mut aa = [0usize; 256];
    let (mut s, mut p, mut d, mut m, mut f, mut i) = (8usize, 8usize, 12usize, 0usize, 0u32, 0u32);
    while s < total {
        if i == 0 { f = *b.get(d).ok_or(END)? as u32; d += 1; i = 1 }
        let back = f & i != 0;
        if back {
            let (&x, &y) = b.get(d).zip(b.get(d + 1)).ok_or(END)?;
            d += 2;
            let r = aa[x as usize];
            m = y as usize;
            if s + 2 + m > total { return Err(PAST) }
            dst.copy_within(r..r + 2, s);
            s += 2;
            // byte by byte: the source overlaps the destination when the match repeats
            for j in 0..m { dst[s + j] = dst[r + 2 + j] }
        } else {
            dst[s] = *b.get(d).ok_or(END)?;
            s += 1;
            d += 1;
        }
        while p + 1 < s { aa[(dst[p] ^ dst[p + 1]) as usize] = p; p += 1 }
        if back { s += m; p = s }
        i = (i << 1) & 0xff;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    // expected values: the C zq of 369841b run on the same inputs (/data/tmp/qrs/6/drv.c)
    const LIT: [u8; 16] = [1, 0, 1, 0, 16, 0, 0, 0, 11, 0, 0, 0, 0, b'a', b'b', b'c'];
    const REF: [u8; 17] = [1, 0, 1, 0, 17, 0, 0, 0, 14, 0, 0, 0, 4, b'a', b'b', 3, 2];
    fn run(b: &[u8], want: usize) -> Result<Vec<u8>, &'static str> {
        let mut d = vec![0u8; want + 8];
        zq(b, &mut d).map(|()| d).map_err(|e| e.to_str().unwrap())
    }
    #[test] fn literals() { assert_eq!(run(&LIT, 3).unwrap(), [0, 0, 0, 0, 0, 0, 0, 0, 97, 98, 99]) }
    #[test] fn back_reference() { assert_eq!(run(&REF, 6).unwrap(), [0, 0, 0, 0, 0, 0, 0, 0, 97, 98, 97, 98, 97, 98]) }
    #[test] fn back_reference_into_the_zero_prefix() {
        let mut q = REF; q[15] = 200;
        assert_eq!(run(&q, 6).unwrap(), [0, 0, 0, 0, 0, 0, 0, 0, 97, 98, 0, 0, 0, 0]);
    }
    #[test] fn messages() {
        let mut h = LIT; h[0] = 2;
        let mut l = LIT; l[4] += 1;
        let mut q = REF; q[16] = 3;
        let mut e = REF; e[4] = 16;
        for (b, want, e) in [
            (&LIT[..11], 3, "a message shorter than its 12-byte header"),
            (&h[..], 3, "a header that is not 01 00 01 00"),
            (&l[..], 3, "a header whose message length is not the block's compressed length"),
            (&LIT[..], 4, "a message whose header states another length"),
            (&e[..16], 6, "a stream that ends inside the block"),
            (&q[..], 6, "a back reference that runs past the block"),
        ] { assert_eq!(run(b, want), Err(e)) }
    }
    #[test] fn truncated_stream_is_err_not_panic() {
        let mut t = LIT[..15].to_vec(); t[4] = 15;
        assert_eq!(run(&t, 3), Err("a stream that ends inside the block"));
        assert!(zq(&LIT, &mut []).is_err());
    }
    // ---- the file: a plain stream and a hand-built `kxzipped` one (version 3 trailer, 12 bytes of block table per 8) ----
    use alloc::ffi::CString;
    const ZLIB_HELLO: [u8; 17] = [120, 156, 203, 72, 205, 201, 201, 87, 200, 192, 78, 2, 0, 163, 16, 10, 229];
    fn dir() -> std::path::PathBuf {
        let d = std::path::PathBuf::from(std::env::var("TMPDIR").unwrap_or("/data/tmp/qrs/B4".into())).join("zip-unit");
        std::fs::create_dir_all(&d).expect("zip tests: cannot create the scratch directory");
        d
    }
    fn put(name: &str, bytes: &[u8]) -> CString {
        let p = dir().join(name);
        std::fs::write(&p, bytes).expect("zip tests: cannot write the file");
        CString::new(p.to_str().unwrap()).unwrap()
    }
    /// a `kxzipped` file of `blocks` (algorithm, compressed bytes), `ulen` uncompressed bytes in blocks of `l`
    fn kx(l: u64, ulen: u64, blocks: &[(u32, &[u8])]) -> Vec<u8> {
        let mut f = b"kxzipped".to_vec();
        for (_, b) in blocks { f.extend_from_slice(b) }
        let cend = f.len() as u64;
        f.extend_from_slice(&[3, 0, 0, 0, 0, 0, 0, 0]);
        for v in [ulen, cend, l] { f.extend_from_slice(&v.to_ne_bytes()) }
        for (a, b) in blocks { f.extend_from_slice(&(b.len() as u32).to_ne_bytes()); f.extend_from_slice(&a.to_ne_bytes()) }
        f.extend_from_slice(&(blocks.len() as u64).to_ne_bytes());
        f
    }
    fn stream(z: &File) -> Result<Vec<u8>, Fail> {
        let mut v = vec![0u8; z.ulen()];
        z.bytes_into(&mut v).map(|()| v)
    }
    fn why(r: Result<impl core::fmt::Debug, Fail>) -> String {
        match r { Err(Fail::Why(w)) => w, other => panic!("expected a failure with text, got {other:?}") }
    }

    #[test] fn plain_file() {
        let data: Vec<u8> = (0..300_000u32).map(|i| (i * 7 % 251) as u8).collect();
        let p = put("plain.bin", &data);
        let z = File::open(&p).unwrap();
        assert_eq!(z.ulen(), data.len());
        let mut h = vec![0u8; z.head_len()];
        z.head_into(&mut h).unwrap();
        assert_eq!(h, data[..4096]);
        assert_eq!(stream(&z).unwrap(), data);
    }
    #[test] fn plain_file_through_a_cursor_across_a_logical_block() {
        let data: Vec<u8> = (0..300_000u32).map(|i| (i * 7 % 251) as u8).collect();
        let mut z = File::open(&put("plain2.bin", &data)).unwrap();
        z.region(131_000, 4000, 1).unwrap();
        let mut c = Cursor::new(&z).unwrap();
        assert_eq!(c.at(&z, 0, 4000).unwrap(), &data[131_000..135_000]);
        assert_eq!(c.at(&z, 10, 5).unwrap(), &data[131_010..131_015]);
        assert_eq!(c.at(&z, 0, 0).unwrap(), &[] as &[u8]);
        assert!(c.at(&z, 168_999, 2).is_none() && z.bad());
        assert_eq!(z.error(), Fail::Why("bytes 299999 to 300001 of the uncompressed stream, which ends after 300000".into()));
    }
    #[test] fn short_and_empty_files() {
        let z = File::open(&put("empty.bin", &[])).unwrap();
        assert_eq!((z.ulen(), z.head_len()), (0, 0));
        assert_eq!(stream(&z).unwrap(), []);
        let z = File::open(&put("seven.bin", b"kxzippe")).unwrap();
        assert_eq!(stream(&z).unwrap(), b"kxzippe");
    }
    #[test] fn stored_and_inflated_blocks() {
        let f = kx(32, 60, &[(0, b"abcdefghijklmnopqrstuvwxyz012345"), (2, &ZLIB_HELLO)]);
        let z = File::open(&put("kx.bin", &f)).unwrap();
        assert_eq!(z.ulen(), 60);
        // the second block is 28 bytes by the trailer and 29 by zlib: zlib is given 28 and says so
        assert_eq!(why(stream(&z)), "block 1 of 2 at byte 40: gzip says buffer error");
        let f = kx(32, 61, &[(0, b"abcdefghijklmnopqrstuvwxyz012345"), (2, &ZLIB_HELLO)]);
        let z = File::open(&put("kx2.bin", &f)).unwrap();
        let mut want = b"abcdefghijklmnopqrstuvwxyz012345".to_vec();
        want.extend_from_slice(b"hello hello hello hello hello");
        assert_eq!(stream(&z).unwrap(), want);
        let mut h = vec![0u8; z.head_len()];
        z.head_into(&mut h).unwrap();
        assert_eq!(h, want);
        let mut z = z;
        z.region(30, 8, 1).unwrap();
        let mut c = Cursor::new(&z).unwrap();
        assert_eq!(c.at(&z, 0, 8).unwrap(), &want[30..38]);
    }
    #[test] fn corrupt_block_names_the_library_text() {
        let mut bad = ZLIB_HELLO;
        bad[8] ^= 0xff;
        let z = File::open(&put("kxbad.bin", &kx(32, 29, &[(2, &bad)]))).unwrap();
        assert_eq!(why(stream(&z)), "block 0 of 1 at byte 8: gzip says data error");
    }
    #[test] fn open_failures() {
        assert_eq!(File::open(c"/data/tmp/qrs/B4/zip-unit/no-such-file").err(), Some(Fail::Errno(2)));
        assert_eq!(File::open(c"/data/tmp/qrs/B4").err(), Some(Fail::Errno(os::EISDIR)));
        let good = kx(32, 60, &[(0, b"abcdefghijklmnopqrstuvwxyz012345"), (0, b"abcdefghijklmnopqrstuvwxyz01")]);
        let n = good.len();
        let cut = |k: usize| why(File::open(&put("cut.bin", &good[..k])).map(|_| ()));
        assert_eq!(cut(20), "a kxzipped file of at least 48 bytes (magic, 32-byte trailer, block count), found 20");
        assert!(cut(n - 1).starts_with("kxzipped block count at byte "));
        let mut v = good.clone();
        v[n - 8 - 16 - 32] = 4;
        assert_eq!(why(File::open(&put("ver.bin", &v)).map(|_| ())), format!("kxzipped trailer at byte {}: format version 3, found 4", n - 8 - 16 - 32));
        let mut v = good.clone();
        v[n - 8 - 16 + 4] = 7;
        assert_eq!(why(File::open(&put("alg.bin", &v)).map(|_| ())), "a block algorithm in 0..5, found 7");
        let mut v = good.clone();
        v[n - 8 - 16 - 32 + 24] = 24;
        assert!(why(File::open(&put("l.bin", &v)).map(|_| ())).contains("a logical block size that is a power of two"));
    }
    #[test] fn region_checks() {
        let mut z = File::open(&put("r.bin", b"0123456789")).unwrap();
        assert!(z.region(2, 8, 1).is_ok() && z.region(0, 5, 2).is_ok());
        assert_eq!(why(z.region(2, 9, 1)), "9 elements of 1 bytes from byte 2, the uncompressed stream is 10 bytes");
        assert!(z.region(0, 1, 0).is_err());
    }
}
