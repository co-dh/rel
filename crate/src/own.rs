#![forbid(unsafe_code)]
//! own.c:263 and the header checks of own.c:366-394, and `own_check`.
use crate::coc::{COC_EXC_FRM, Meta};
use crate::ids::{id_at, id_width, ids_bytes, ids_max};
use crate::layout::{Tail, exc_ok};
use crate::why::Why;
use crate::BLK;


pub const OWN_MAXPARTS: usize = 3;
#[repr(C)]
pub struct OwnHead { pub n: u64, pub hdr: usize, pub np: usize,
                     pub off: [usize; OWN_MAXPARTS], pub len: [usize; OWN_MAXPARTS], pub kind: u8 }

pub const OWN_ROOM: u64 = 32;
pub const OWN_HEAD: usize = 24;
pub const OWN_VERSION: u8 = 4;
pub const OWN_OLDEST: u8 = 3;
pub const OWN_NPARTS: [usize; 5] = [1, 1, 2, 3, 2];

fn le(m: &[u8], at: usize, w: usize) -> u64 {
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

/// The refusal `write_head` gives a bad kind, part count or name length; None, so a caller returns it.
pub fn refuse_head(kind: u8, np: usize, nl: usize, why: &mut Why) -> Option<usize> {
    why.say(format_args!("a column of kind 0..4 with its parts and a domain name under 65536 \
bytes, given kind {} with {} parts and a {}-byte name", kind, np, nl));
    None
}

/// `qlean_own_write` (own.c:147-179) without the file: the header (`OWN_HEAD + 16 * len.len()` bytes into `head`)
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

/// own.c `own_check`: what a kernel trusts about the parts and the file could have wrong -- the Frame of Reference block
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
fn check_coc(kind: u8, n: u64, p: [&[u8]; OWN_MAXPARTS], why: &mut Why) -> bool {
    let (m, pk) = (p[0], p[1]);
    let nblk = m.len() / 33;
    if m.len() != 33 * nblk + 16 {
        why.say(format_args!("part 0: Frame of Reference metadata of 33 bytes a block and a 16-byte trailer, found {} bytes", m.len()));
        return false;
    }
    if n > nblk as u64 * BLK as u64 {
        why.say(format_args!("part 0: blocks for {} elements, found {} blocks of {}", n, nblk, BLK));
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
        bad | (wd > 64) | (o % 8 != 0) | (o > plen) | (BLK as u64 * wd / 8 > plen.wrapping_sub(o))
    });
    if bad {
        for b in 0..nblk {
            let (wd, o) = (meta.width[b] as u64, meta.off[b]);
            let need = BLK as u64 * wd / 8;
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
            return exc_ok(t, nblk, nexc, esz as usize, 1, if frm { Tail::Frames } else { Tail::None }, why);
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
        return exc_ok(a, nblk, u64::from_ne_bytes(a[..8].try_into().unwrap()), if flags & 1 != 0 { 4 } else { 8 }, 2, Tail::Exps, why);
    }
    true
}

/// `check`'s symbol column (kind 4): a dictionary of NUL-ended symbols and the ids into it.
fn check_syms(n: u64, p: [&[u8]; OWN_MAXPARTS], why: &mut Why) -> bool {
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
}
