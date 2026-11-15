#![forbid(unsafe_code)]
//! sort.c:212-334: an encoded column's keys through a window of two blocks, each decoded on first touch, and the
//! column's key range from its metadata. The ALP arm (`kwin.f`, sort.c:2618) is column (a)'s, task A5: `alp` is
//! the `Option` it will fill, and is `None` until then.
use alloc::boxed::Box;

use crate::BLK;
use crate::coc::Coc;
use crate::key::{Keys, SK_C8, SK_F32, SK_F64, SK_I16, SK_I32, SK_I64, SK_U8};

/// `kwin` (sort.c:270): keys `lo .. lo + len` are in `key`; block `b` is in slot `b & 1`.
pub struct Kwin<'a> {
    kind: u8, c: Coc<'a>,
    #[allow(dead_code)] // A5 reads it: `kwin_blk` and `range_foR` branch on `w->f`
    alp: Option<()>,
     lo: usize, len: usize, key: Box<[u64; 2 * BLK]> }

/// `sk_dense_width` (coc.h:359) in bits; C exits at the kinds with no dense width, which an encoded column never has.
fn dense_bits(kind: u8) -> u32 {
    match kind {
        SK_U8 | SK_C8 => 8,
        SK_I16 => 16,
        SK_I32 | SK_F32 => 32,
        SK_I64 | SK_F64 => 64,
        _ => panic!("qlean: element kind {kind} has no dense width (impossible: an encoded column is never a bit or key payload)"),
    }
}

impl<'a> Kwin<'a> {
    /// `kwin_init`: an empty window.
    pub fn new(kind: u8, c: Coc<'a>) -> Self {
        dense_bits(kind);
        Kwin { kind, c, alp: None, lo: 0, len: 0, key: Box::new([0; 2 * BLK]) }
    }

    /// `kwin_blk`: block `b` into its slot; answers its key count.
    fn blk(&mut self, b: usize) -> usize {
        let at = b * BLK;
        let cnt = (self.c.meta.n - at).min(BLK);
        let s = (b & 1) * BLK;
        keys_blk(self.kind, &self.c, b, &mut self.key[s..s + cnt]);
        cnt
    }

    /// `kwin_miss`: slide on an ascending walk, else decode afresh.
    #[cold]
    #[inline(never)]
    fn miss(&mut self, i: usize) {
        let b = i / BLK;
        if self.len == 2 * BLK && b == self.lo / BLK + 2 { self.lo += BLK; self.len = BLK + self.blk(b); return }
        self.lo = b * BLK;
        self.len = self.blk(b);
        if self.lo + self.len < self.c.meta.n { self.len += self.blk(b + 1) }
    }
}

impl Keys for Kwin<'_> {
    #[inline(always)]
    fn at(&mut self, i: usize) -> u64 {
        if i.wrapping_sub(self.lo) >= self.len { self.miss(i) }
        self.key[i & (2 * BLK - 1)]
    }
    fn fork(&self) -> Self { Kwin::new(self.kind, self.c) }
}

/// sort.c:212: the bit `keys_of` flips at `kind`'s width.
pub fn key_flip(kind: u8) -> u64 {
    match kind { SK_I16 => 0x8000, SK_I32 => 0x8000_0000, SK_I64 => 0x8000_0000_0000_0000, _ => 0 }
}

fn mask(kind: u8) -> u64 { let w = dense_bits(kind); if w == 64 { !0 } else { (1 << w) - 1 } }

/// Residual `j` of the pack `p` at width `w`: bits `j*w ..` little-endian; the generic arm reads at most 9 bytes
/// and zero-pads past the block's end, as `unpack::res_unpack_scalar` does.
#[inline(always)]
fn res_at(p: &[u8], w: u32, j: usize) -> u64 {
    let w = w as usize;
    let bit = j * w;
    let (by, sh) = (bit >> 3, bit & 7);
    let mut t = [0u8; 16];
    let e = p.len().min(by + 9);
    t[..e - by].copy_from_slice(&p[by..e]);
    let v = u128::from_le_bytes(t) >> sh;
    (v as u64) & if w == 64 { !0 } else { (1u64 << w) - 1 }
}

/// `keys_blk_foR` (sort.c:243): block `b`'s `k.len()` keys.
pub fn keys_blk(kind: u8, c: &Coc, b: usize, k: &mut [u64]) {
    let (mask, flip) = (mask(kind), key_flip(kind));
    let p = &c.pack[c.meta.off[b] as usize..];
    let cnt = k.len();
    // a patched block is decoded (patches applied over the frame) and read as residuals of 64 bits over base 0
    if c.blk_nexc(b) != 0 {
        let (fr, w) = (c.frame(b), c.meta.width[b] as u32);
        let mut dec = [0u64; BLK];
        for j in 0..cnt { dec[j] = fr.wrapping_add(res_at(p, w, j)) }
        let e = c.exc.expect("blk_nexc != 0 has a patch list");
        for j in e.off[b] as usize..e.off[b + 1] as usize {
            if (e.pos[j] as usize) < cnt { dec[e.pos[j] as usize] = c.exc(j) as u64 }
        }
        for j in 0..cnt { k[j] = dec[j] & mask ^ flip }
        return;
    }
    let (base, w) = (c.meta.base[b] as u64, c.meta.width[b] as u32);
    macro_rules! go { ($r:expr) => { for j in 0..cnt { k[j] = (base.wrapping_add($r(j)) & mask) ^ flip } }; }
    match w {
        0 => go!(|_| 0u64),
        8 => go!(|j: usize| p[j] as u64),
        16 => go!(|j: usize| u16::from_le_bytes([p[2 * j], p[2 * j + 1]]) as u64),
        32 => go!(|j: usize| u32::from_le_bytes(p[4 * j..4 * j + 4].try_into().unwrap()) as u64),
        64 => go!(|j: usize| u64::from_le_bytes(p[8 * j..8 * j + 8].try_into().unwrap())),
        _ => go!(|j: usize| res_at(p, w, j)),
    }
}

/// `range_foR` (sort.c:320): the least and greatest key, from the frames, the maxima and the patches.
pub fn range(kind: u8, c: &Coc) -> (u64, u64) {
    let (mask, flip) = (mask(kind), key_flip(kind));
    let (mut mn, mut mx) = (!0u64, 0u64);
    for b in 0..c.meta.n.div_ceil(BLK) {
        mn = mn.min((c.meta.base[b] as u64 & mask) ^ flip);
        mx = mx.max((c.meta.maxv[b] as u64 & mask) ^ flip);
    }
    for j in 0..c.exc.map_or(0, |e| e.pos.len()) {
        let k = (c.exc(j) as u64 & mask) ^ flip;
        mn = mn.min(k);
        mx = mx.max(k);
    }
    (mn, mx)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn flip() {
        assert_eq!([SK_U8, SK_I16, SK_I32, SK_I64, SK_F32].map(key_flip), [0, 0x8000, 0x8000_0000, 1 << 63, 0]);
    }
    #[test] fn residuals_odd_widths() {
        // 3-bit residuals 5, 2, 7, 1 are the bits 101 010 111 001 low first
        let p = [0b11_010_101u8, 0b11];
        assert_eq!([0, 1, 2, 3].map(|j| res_at(&p, 3, j)), [5, 2, 7, 1]);
        assert_eq!(res_at(&[0xff; 8], 64, 0), !0);
        assert_eq!(res_at(&[0xff; 16], 63, 1), (1 << 63) - 1);
    }
}
