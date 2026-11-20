#![forbid(unsafe_code)]
//! sort.rs: an encoded column's keys through a window of two blocks, each decoded on first touch, and the
//! column's key range from its metadata. The ALP arm (`kwin.f`, sort.rs) is `alp`, `None` for an integral column.

use crate::coc::Coc;
use crate::key::{Keys, SK_C8, SK_I8, SK_F32, SK_F64, SK_I16, SK_I32, SK_I64, SK_U8};


/// `sk_dense_width` (coc.rs) in bits; C exits at the kinds with no dense width, which an encoded column never has.
pub fn dense_bits(kind: u8) -> u32 {
    match kind {
        SK_U8 | SK_C8 | SK_I8 => 8,
        SK_I16 => 16,
        SK_I32 | SK_F32 => 32,
        SK_I64 | SK_F64 => 64,
        _ => panic!("qlean: element kind {kind} has no dense width (impossible: an encoded column is never a bit or key payload)"),
    }
}



/// sort.rs: the bit `keys_of` flips at `kind`'s width.
pub fn key_flip(kind: u8) -> u64 {
    match kind { SK_I8 => 0x80, SK_I16 => 0x8000, SK_I32 => 0x8000_0000, SK_I64 => 0x8000_0000_0000_0000, _ => 0 }
}

pub fn mask(kind: u8) -> u64 { let w = dense_bits(kind); if w == 64 { !0 } else { (1 << w) - 1 } }

/// `keys_blk_foR` (sort.rs): block `b`'s `k.len()` keys.
pub fn keys_blk(kind: u8, c: &Coc, b: usize, k: &mut [u64]) {
    let (mask, flip) = (mask(kind), key_flip(kind));
    let p = &c.pack[c.meta.off[b] as usize..];
    let cnt = k.len();
    let w = c.meta.width[b];
    // a patched block, and an odd width, are decoded (frame + residual, patches over it); frame is base without patches
    if c.blk_nexc(b) != 0 || !matches!(w, 0 | 8 | 16 | 32 | 64) {
        let mut dec = crate::pod::Scr::<i64>::new(c.meta.blk());
        c.decode_blk(b, cnt, &mut dec);
        for j in 0..cnt { k[j] = dec[j] as u64 & mask ^ flip }
        return;
    }
    let base = c.meta.base[b] as u64;
    fn go<const W: u32>(p: &[u8], base: u64, mask: u64, flip: u64, k: &mut [u64]) {
        for (j, k) in k.iter_mut().enumerate() { *k = (base.wrapping_add(crate::ids::lane::<W>(p, j)) & mask) ^ flip }
    }
    crate::by_width!(w, go(p, base, mask, flip, k))
}

/// `range_foR` (sort.rs): the least and greatest key, from the frames, the maxima and the patches.
pub fn range(kind: u8, c: &Coc) -> (u64, u64) {
    let (mask, flip) = (mask(kind), key_flip(kind));
    let (mut mn, mut mx) = (!0u64, 0u64);
    for (b, ..) in crate::blocks::Blocks::from(*c).walk() {
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
        assert_eq!([SK_U8, SK_I8, SK_I16, SK_I32, SK_I64, SK_F32].map(key_flip), [0, 0x80, 0x8000, 0x8000_0000, 1 << 63, 0]);
    }
}

// ---- sort.rs `keys_blk_alp`, the ALP arm of `kwin` ----

