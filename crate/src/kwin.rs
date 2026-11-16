#![forbid(unsafe_code)]
//! sort.c:212-334: an encoded column's keys through a window of two blocks, each decoded on first touch, and the
//! column's key range from its metadata. The ALP arm (`kwin.f`, sort.c:2618) is `alp`, `None` for an integral column.
use alloc::boxed::Box;

use crate::BLK;
use crate::alp::Cocf;
use crate::coc::Coc;
use crate::key::{Keys, SK_C8, SK_F32, SK_F64, SK_I16, SK_I32, SK_I64, SK_U8};

/// `kwin` (sort.c:270): keys `lo .. lo + len` are in `key`; block `b` is in slot `b & 1`.
pub struct Kwin<'a> {
    kind: u8, c: Coc<'a>,
    /// the ALP arm, `kwin.f`: `kwin_blk` and `range_foR` branch on it
    alp: Option<Cocf<'a>>,
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
        match &self.alp {
            Some(f) => keys_blk_alp(f, b, &mut self.key[s..s + cnt]),
            None => keys_blk(self.kind, &self.c, b, &mut self.key[s..s + cnt]),
        }
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
    fn fork(&self) -> Self { self.alp.map_or_else(|| Kwin::new(self.kind, self.c), |f| Kwin::with_alp(self.kind, f)) }
}

/// sort.c:212: the bit `keys_of` flips at `kind`'s width.
pub fn key_flip(kind: u8) -> u64 {
    match kind { SK_I16 => 0x8000, SK_I32 => 0x8000_0000, SK_I64 => 0x8000_0000_0000_0000, _ => 0 }
}

fn mask(kind: u8) -> u64 { let w = dense_bits(kind); if w == 64 { !0 } else { (1 << w) - 1 } }

/// `keys_blk_foR` (sort.c:243): block `b`'s `k.len()` keys.
pub fn keys_blk(kind: u8, c: &Coc, b: usize, k: &mut [u64]) {
    let (mask, flip) = (mask(kind), key_flip(kind));
    let p = &c.pack[c.meta.off[b] as usize..];
    let cnt = k.len();
    let w = c.meta.width[b];
    // a patched block, and an odd width, are decoded (frame + residual, patches over it); frame is base without patches
    if c.blk_nexc(b) != 0 || !matches!(w, 0 | 8 | 16 | 32 | 64) {
        let mut dec = [0i64; BLK];
        c.decode_blk(b, cnt, &mut dec);
        for j in 0..cnt { k[j] = dec[j] as u64 & mask ^ flip }
        return;
    }
    let base = c.meta.base[b] as u64;
    macro_rules! go { ($r:expr) => { for j in 0..cnt { k[j] = (base.wrapping_add($r(j)) & mask) ^ flip } }; }
    match w {
        0 => go!(|_| 0u64),
        8 => go!(|j: usize| p[j] as u64),
        16 => go!(|j: usize| u16::from_le_bytes([p[2 * j], p[2 * j + 1]]) as u64),
        32 => go!(|j: usize| u32::from_le_bytes(p[4 * j..4 * j + 4].try_into().unwrap()) as u64),
        64 => go!(|j: usize| u64::from_le_bytes(p[8 * j..8 * j + 8].try_into().unwrap())),
        _ => unreachable!(),
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
}

// ---- sort.c:281 `keys_blk_alp`, the ALP arm of `kwin` ----
/// sort.c:281 `keys_blk_alp`: block `b` of `f`, `k.len()` elements restored and each ranked, as sort keys into `k`;
/// `rank32`/`rank64` are the key at the two float kinds whatever holds the payload.
pub fn keys_blk_alp(f: &Cocf, b: usize, k: &mut [u64]) {
    let mut v = [0u64; BLK];
    let v = crate::pod::bytes_mut(&mut v);
    f.load_blk(b, k.len(), v);
    if f.f32 { for (x, e) in k.iter_mut().zip(v.chunks_exact(4)) { *x = crate::key::rank32(u32::from_ne_bytes(e.try_into().unwrap())) } }
    else { for (x, e) in k.iter_mut().zip(v.chunks_exact(8)) { *x = crate::key::rank64(u64::from_ne_bytes(e.try_into().unwrap())) } }
}
impl<'a> Kwin<'a> {
    /// sort.c:2618 `kwin_init` over an ALP column: `kwin->f = &f`.
    pub fn with_alp(kind: u8, f: Cocf<'a>) -> Self { Kwin { alp: Some(f), ..Kwin::new(kind, f.c) } }
    /// sort.c:320 `range_foR`'s ALP line: a frame is over decimals, and a float's keys span the binades between its
    /// extremes, so the range is all of it and `dedup` takes its hashed loop; else `range`.
    pub fn range(&self) -> (u64, u64) { win_range(self.kind, &self.c, self.alp.is_some()) }
}

/// `range_foR` over a window of either arm: the ALP rule once, for `Kwin::range` and C's `qrs_kwin_range`.
pub fn win_range(kind: u8, c: &Coc, alp: bool) -> (u64, u64) { if alp { (0, !0) } else { range(kind, c) } }
