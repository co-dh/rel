#![forbid(unsafe_code)]
//! own.c:263 and the header checks of own.c:366-394.
use crate::why::Why;

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
