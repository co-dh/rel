#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: trailer and table are filled by task 7
//! zip.c:141 and the pure parts of zopen (zip.c:185-250).
use crate::why::Why;

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
#[repr(C)]
pub struct ZTrailer { pub ulen: u64, pub cend: u64, pub l: u64 }
pub fn trailer(hdr: &[u8; 32], size: u64, nblk: u64, hat: u64, why: &mut Why) -> Option<ZTrailer> { unimplemented!() }
/// Returns maxc; at[0] = 8.
pub fn table(ent: &[u8], at: &mut [u64], algo: &mut [u32]) -> usize { unimplemented!() }

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
}
