#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! The read views of coc.h's `coc`: metadata, patch list, and the whole column.
use crate::pod::Lane;

/// `coc_meta_view`: the 33*mblk + 16 byte buffer.
#[derive(Clone, Copy)]
pub struct Meta<'a> {
    pub base: &'a [i64], pub maxv: &'a [i64], pub off: &'a [u64], pub bsum: &'a [i64], pub width: &'a [u8],
    /// one slot each, read by value
    pub sumnul: i64, pub sumn: u64,
    /// slices are mblk long; nblk <= mblk is what n reaches
    pub n: usize, pub nblk: usize, pub mblk: usize,
}
/// nexc = pos.len()
#[derive(Clone, Copy)]
pub struct Exc<'a> { pub off: &'a [u32], pub pos: &'a [u16], pub raw: &'a [u8], pub esz: usize }
#[derive(Clone, Copy)]
pub struct Coc<'a> { pub meta: Meta<'a>, pub pack: &'a [u8], pub exc: Option<Exc<'a>>, pub fdelta: Option<&'a [u64]> }

impl<'a> Meta<'a> {
    /// coc.h:133; None = misaligned buffer
    pub fn new(m: &'a [u8], n: usize) -> Option<Self> { unimplemented!() }
    /// coc.h:222
    pub fn res_end(&self) -> usize { unimplemented!() }
    /// coc.h:233
    pub fn grid(&self, n: usize) -> bool { unimplemented!() }
}
impl<'a> Coc<'a> {
    /// coc.h:245; None where C aborts
    pub fn attach(meta: Meta<'a>, pack: &'a [u8]) -> Option<Self> { unimplemented!() }
    /// coc.h:234
    pub fn std(&self, n: usize) -> bool { unimplemented!() }
    /// coc.h:155; off stays absolute into pack
    pub fn blocks(&self, b0: usize, b1: usize) -> Coc<'a> { unimplemented!() }
    /// coc.h:217
    pub fn frame(&self, b: usize) -> u64 {
        (self.meta.base[b] as u64).wrapping_add(self.fdelta.map_or(0, |f| f[b]))
    }
    /// coc.h:277: exception `j`'s element, sign-extended; one byte zero-extends.
    pub fn exc(&self, j: usize) -> i64 {
        let e = self.exc.expect("coc exc: no patch list");
        let r = &e.raw[j * e.esz..(j + 1) * e.esz];
        match e.esz {
            1 => r[0] as i64,
            2 => i16::from_ne_bytes([r[0], r[1]]) as i64,
            4 => i32::from_ne_bytes([r[0], r[1], r[2], r[3]]) as i64,
            _ => i64::from_ne_bytes([r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7]]),
        }
    }
    /// coc.h:293
    pub fn blk_nexc(&self, b: usize) -> usize {
        self.exc.filter(|e| !e.pos.is_empty()).map_or(0, |e| (e.off[b + 1] - e.off[b]) as usize)
    }
    /// coc.h:2633: block `b`'s first `nb` elements into `out`, the patches applied.
    pub fn decode_blk<T: Lane>(&self, b: usize, nb: usize, out: &mut [T]) {
        let (mut w, base, out) = (self.meta.width[b], self.frame(b), &mut out[..nb]);
        let at = self.meta.off[b] as usize;
        let p = &self.pack[at..at + crate::BLK * w as usize / 8];
        // an odd width decoded in one pass, the lanes never stored
        if !crate::simd::res_unpack_add(p, w, nb, base, crate::pod::bytes_mut(out), size_of::<T>() as u32) {
            let mut lb = [0u64; crate::BLK];
            let p = lanes(p, &mut w, nb, crate::pod::bytes_mut(&mut lb));
            let add = |r: u64| T::wrap(base.wrapping_add(r));
            match w {
                0 => out.fill(T::wrap(base)),
                8 => out.iter_mut().zip(p).for_each(|(o, &r)| *o = add(r as u64)),
                16 => out.iter_mut().zip(p.chunks_exact(2)).for_each(|(o, r)| *o = add(u16::from_ne_bytes([r[0], r[1]]) as u64)),
                32 => out.iter_mut().zip(p.chunks_exact(4)).for_each(|(o, r)| *o = add(u32::from_ne_bytes(r.try_into().unwrap()) as u64)),
                64 => out.iter_mut().zip(p.chunks_exact(8)).for_each(|(o, r)| *o = add(u64::from_ne_bytes(r.try_into().unwrap()))),
                1 => load_sub::<T, 1>(p, base, out),
                2 => load_sub::<T, 2>(p, base, out),
                _ => load_sub::<T, 4>(p, base, out),
            }
        }
        if let Some(e) = self.exc.filter(|e| !e.pos.is_empty()) {
            for j in e.off[b] as usize..e.off[b + 1] as usize {
                if (e.pos[j] as usize) < nb { out[e.pos[j] as usize] = T::wrap(self.exc(j) as u64) }
            }
        }
    }
}

/// coc.h's `COC_LOAD_SUB`: residuals of `W` < 8 bits, `8 / W` to a byte, the shift a literal per byte so the loop
/// vectorises.
fn load_sub<T: Lane, const W: usize>(p: &[u8], base: u64, out: &mut [T]) {
    let (per, m) = (8 / W, (1u8 << W) - 1);
    let g = out.len() / per;
    let mut whole = out.chunks_exact_mut(per);
    for (o, &v) in (&mut whole).zip(p) {
        for (s, x) in o.iter_mut().enumerate() { *x = T::wrap(base.wrapping_add(((v >> (s * W)) & m) as u64)) }
    }
    let rest = whole.into_remainder();
    for (s, x) in rest.iter_mut().enumerate() { *x = T::wrap(base.wrapping_add(((p[g] >> (s * W)) & m) as u64)) }
}

/// coc.h:819: the residuals of a block at a power-of-two width in place, else unpacked into `buf` (`BLK * 8` bytes)
/// with `*w` raised to the lane it now has.
pub fn lanes<'b>(p: &'b [u8], w: &mut u8, nb: usize, buf: &'b mut [u8]) -> &'b [u8] {
    if *w & w.wrapping_sub(1) == 0 { return p }
    crate::simd::res_unpack(p, *w, nb, buf);
    *w = if *w < 8 { 8 } else { crate::bits::lane_width(*w) };
    buf
}

#[cfg(test)]
mod tests {
    use crate::BLK;
    // decode_blk at every width 0..=64 and element type against B8's scalar unpack plus the frame, on a block of
    // random residuals; the patches are checked against the C decoder in ffi.rs
    fn check<T: crate::pod::Lane + PartialEq + core::fmt::Debug>(mut s: u64) {
        for w in 0..=64u8 {
            let pack: Vec<u8> = (0..BLK * w as usize / 8).map(|_| { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s as u8 }).collect();
            let base = [s as i64]; let (z, off, width) = ([0i64], [0u64], [w]);
            let meta = super::Meta { base: &base, maxv: &z, off: &off, bsum: &z, width: &width, sumnul: 0, sumn: 0,
                                     n: BLK, nblk: 1, mblk: 1 };
            let c = super::Coc { meta, pack: &pack, exc: None, fdelta: None };
            for nb in [1, 7, 63, 64, 1023, 1024] {
                let mut got = vec![T::wrap(0x5A); nb];
                c.decode_blk(0, nb, &mut got);
                let want: Vec<T> = (0..nb).map(|i| T::wrap((s as u64).wrapping_add(res_get(&pack, w, i)))).collect();
                assert_eq!(got, want, "w {w} nb {nb}");
            }
        }
    }
    /// residual i of a block at width w, bit by bit
    fn res_get(p: &[u8], w: u8, i: usize) -> u64 {
        (0..w as usize).map(|k| { let bit = i * w as usize + k; ((p[bit / 8] >> (bit % 8)) & 1) as u64 }).enumerate()
            .fold(0, |a, (k, b)| a | b << k)
    }
    #[test] fn decode_blk_every_width() { check::<u8>(1); check::<i16>(2); check::<i32>(3); check::<i64>(4) }
}
