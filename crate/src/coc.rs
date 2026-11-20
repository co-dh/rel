#![forbid(unsafe_code)]
//! The read views of coc.rs's `coc`: metadata, patch list, and the whole column.
use crate::layout::{Tail, exc_layout};
use crate::pod::{self, Elt};

/// coc.rs: bit 8 of the patch list's element size, set when the frames follow
pub const COC_EXC_FRM: usize = 0x100;

/// `coc_meta_view`: the 33*mblk + 24 byte buffer (the trailer: sumnul, sumn, lg, then the widths).
#[derive(Clone, Copy)]
pub struct Meta<'a> {
    pub base: &'a [i64], pub maxv: &'a [i64], pub off: &'a [u64], pub bsum: &'a [i64], pub width: &'a [u8],
    /// the block size is `1 << lg`, `MIN_LG <= lg <= MAX_LG`
    pub lg: u32,
    /// slices are mblk long; nblk <= mblk is what n reaches
    pub n: usize, pub nblk: usize, pub mblk: usize,
}
/// nexc = pos.len(); `asc`: every block's positions strictly ascending (`ascending`), so `Coc::get` binary-searches them
#[derive(Clone, Copy)]
pub struct Exc<'a> { pub off: &'a [u32], pub pos: &'a [u16], pub raw: &'a [u8], pub esz: usize, pub asc: bool }
#[derive(Clone, Copy)]
pub struct Coc<'a> { pub meta: Meta<'a>, pub pack: &'a [u8], pub exc: Option<Exc<'a>>, pub fdelta: Option<&'a [u64]> }

impl<'a> Meta<'a> {
    /// coc.rs; None = misaligned buffer, or one shorter than `33 * (len / 33) + 24` where C reads past it, or whose `lg` is outside `MIN_LG ..= MAX_LG`
    pub fn new(m: &'a [u8], n: usize) -> Option<Self> {
        let nb = m.len() / 33;
        if m.len() < 33 * nb + 24 { return None }
        let (w, tail) = m.split_at(32 * nb + 24);
        let (head, sums) = w.split_at(32 * nb);
        let (base, rest) = head.split_at(8 * nb);
        let (maxv, rest) = rest.split_at(8 * nb);
        let (off, bsum) = rest.split_at(8 * nb);
        let lg = pod::cast::<u64>(&sums[16..24])?[0];
        if !(crate::MIN_LG as u64..=crate::MAX_LG as u64).contains(&lg) { return None }
        let (lg, n) = (lg as u32, n.min(nb << lg));
        Some(Meta {
            base: pod::cast(base)?, maxv: pod::cast(maxv)?, off: pod::cast(off)?, bsum: pod::cast(bsum)?,
            width: &tail[..nb],
            lg,
            n, nblk: n.div_ceil(1 << lg), mblk: nb,
        })
    }
    /// coc.rs
    pub fn res_end(&self) -> usize {
        if self.mblk == 0 { 0 } else { self.off[self.mblk - 1] as usize + self.blk() * self.width[self.mblk - 1] as usize / 8 }
    }
    /// the block size
    pub fn blk(&self) -> usize { 1 << self.lg }
    /// coc.rs
    pub fn grid(&self, n: usize) -> bool { self.mblk == n.div_ceil(self.blk()) }
}
impl<'a> Coc<'a> {
    /// coc.rs; None where C aborts, or where the pack's tail is misaligned for its sections
    pub fn attach(meta: Meta<'a>, pack: &'a [u8]) -> Option<Self> {
        let e = meta.res_end();
        let c = Coc { meta, pack, exc: None, fdelta: None };
        if pack.len() <= e { return Some(c) }
        let t = &pack[e..];
        let (nexc, h1) = (u64::from_ne_bytes(t.get(..8)?.try_into().ok()?), u64::from_ne_bytes(t.get(8..16)?.try_into().ok()?));
        let (esz, frm) = (h1 & !(COC_EXC_FRM as u64), h1 & COC_EXC_FRM as u64);
        if !matches!(esz, 1 | 2 | 4 | 8) || nexc > t.len() as u64 / 2 { return None }
        let (nexc, esz, mb) = (nexc as usize, esz as usize, meta.mblk);
        let l = exc_layout(mb, nexc, esz, if frm != 0 { Tail::Frames } else { Tail::None })?;
        if l.size != t.len() { return None }
        let (off, pos) = (pod::cast(&t[l.off..l.off + 4 * (mb + 1)])?, pod::cast(&t[l.pos..l.pos + 2 * nexc])?);
        let exc = Exc { off, pos, asc: ascending(off, pos),
                        raw: &t[l.raw..l.raw + nexc * esz], esz };
        let fdelta = if frm != 0 { Some(pod::cast(&t[l.tail..l.tail + 8 * mb])?) } else { None };
        Some(Coc { exc: Some(exc), fdelta, ..c })
    }
    /// coc.rs
    pub fn std(&self, n: usize) -> bool {
        let (m, e) = (&self.meta, self.meta.res_end());
        let pb = self.pack.len();
        if !m.grid(n) || pb < e || m.width.iter().any(|&w| w > 64) { return false }
        if pb == e { return true }
        let (nexc, esz) = self.exc.map_or((0, 0), |x| (x.pos.len(), x.esz));
        exc_layout(m.mblk, nexc, esz, if self.fdelta.is_some() { Tail::Frames } else { Tail::None }).is_some_and(|l| pb == e + l.size)
    }
    /// coc.rs; off stays absolute into pack
    pub fn blocks(&self, b0: usize, b1: usize) -> Coc<'a> {
        let (m, k) = (&self.meta, b1 - b0);
        let n = m.n.saturating_sub(b0 << m.lg).min(k << m.lg);
        let meta = Meta { base: &m.base[b0..b1], maxv: &m.maxv[b0..b1], off: &m.off[b0..b1], bsum: &m.bsum[b0..b1],
                          width: &m.width[b0..b1], n, nblk: k, mblk: k, ..*m };
        Coc { meta, pack: self.pack, exc: self.exc.map(|e| Exc { off: &e.off[b0..=b1], ..e }),
              fdelta: self.fdelta.map(|f| &f[b0..b1]) }
    }
    /// coc.rs
    pub fn frame(&self, b: usize) -> u64 {
        (self.meta.base[b] as u64).wrapping_add(self.fdelta.map_or(0, |f| f[b]))
    }
    /// coc.rs: exception `j`'s element, sign-extended; one byte zero-extends.
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
    /// coc.rs
    pub fn blk_nexc(&self, b: usize) -> usize {
        self.exc.filter(|e| !e.pos.is_empty()).map_or(0, |e| (e.off[b + 1] - e.off[b]) as usize)
    }
    /// coc.rs: block `b`'s first `nb` elements into `out`, the patches applied.
    pub fn decode_blk<T: Elt>(&self, b: usize, nb: usize, out: &mut [T]) {
        let (mut w, base, out) = (self.meta.width[b], self.frame(b), &mut out[..nb]);
        let at = self.meta.off[b] as usize;
        let p = &self.pack[at..at + self.meta.blk() * w as usize / 8];
        // an odd width decoded in one pass, the lanes never stored
        if !crate::simd::res_unpack_add(p, w, nb, base, crate::pod::bytes_mut(out), size_of::<T>() as u32) {
            let mut lb = crate::pod::Scr::<u64>::new(self.meta.blk());
            let p = lanes(p, &mut w, nb, crate::pod::bytes_mut(&mut lb));
            crate::by_width!(w, load_lanes::<T>(p, base, out))
        }
        if let Some(e) = self.exc.filter(|e| !e.pos.is_empty()) {
            for j in e.off[b] as usize..e.off[b + 1] as usize {
                if (e.pos[j] as usize) < nb { out[e.pos[j] as usize] = T::wrap(self.exc(j) as u64) }
            }
        }
    }
}

impl Coc<'_> {
}

/// coc.rs's `COC_LOAD_SUB`: residuals of `W` < 8 bits, `8 / W` to a byte, the shift a literal per byte so the loop
/// vectorises.
pub fn load_sub<T: Elt, const W: u32>(p: &[u8], base: u64, out: &mut [T]) {
    let (per, m, w) = (8 / W as usize, ((1u16 << W) - 1) as u8, W as usize);
    let g = out.len() / per;
    let mut whole = out.chunks_exact_mut(per);
    for (o, &v) in (&mut whole).zip(p) {
        for (s, x) in o.iter_mut().enumerate() { *x = T::wrap(base.wrapping_add(((v >> (s * w)) & m) as u64)) }
    }
    let rest = whole.into_remainder();
    for (s, x) in rest.iter_mut().enumerate() { *x = T::wrap(base.wrapping_add(((p[g] >> (s * w)) & m) as u64)) }
}

/// `base` plus each residual of a block at the lane width `W` into `out`: a sub-byte lane by `load_sub`, a whole one
/// through `ids::unpack`'s chunked load.
#[inline(always)]
pub fn load_lanes<T: Elt, const W: u32>(p: &[u8], base: u64, out: &mut [T]) {
    match W {
        1 | 2 | 4 => load_sub::<T, W>(p, base, out),
        _ => crate::ids::unpack::<W, T>(p, out, |_, o, r| *o = T::wrap(base.wrapping_add(r as u64))),
    }
}
/// coc.rs: the residuals of a block at a power-of-two width in place, else unpacked into `buf` (`blk * 8` bytes)
/// with `*w` raised to the lane it now has.
pub fn lanes<'b>(p: &'b [u8], w: &mut u8, nb: usize, buf: &'b mut [u8]) -> &'b [u8] {
    if *w & w.wrapping_sub(1) == 0 { return p }
    crate::simd::res_unpack(p, *w, nb, buf);
    *w = if *w < 8 { 8 } else { crate::bits::lane_width(*w) };
    buf
}

/// Whether each block's patch positions `pos[off[b] .. off[b + 1]]` lie in `pos` and strictly ascend, as the writer
/// lays them. Lean's `foRExc` reads the first match in any order and `Enc.WF` does not state the order, so an order
/// that fails this is still a column: `Coc::get` scans it.
pub fn ascending(off: &[u32], pos: &[u16]) -> bool {
    off.windows(2).all(|r| r[0] <= r[1] && r[1] as usize <= pos.len() && pos[r[0] as usize..r[1] as usize].windows(2).all(|p| p[0] < p[1]))
}

/// Why a metadata array and a pack are no column.
pub enum ViewErr { Meta, Pack { pack: usize, end: usize, mblk: usize } }
impl core::fmt::Display for ViewErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ViewErr::Meta => f.write_str("the metadata array is not a column's 33 * nblk + 24 bytes with 6 <= lg <= 16"),
            // coc.rs `coc_attach`'s text
            ViewErr::Pack { pack, end, mblk } => write!(f, "a Frame of Reference pack of {pack} bytes whose residuals end at {end} holds no patch list of {mblk} blocks after them"),
        }
    }
}
/// coc.rs `coc_view` over slices: `mv`, `pv` as a column of at most `n` elements (cut to what the blocks hold).
pub fn view<'a>(mv: &'a [u8], pv: &'a [u8], n: usize) -> Result<Coc<'a>, ViewErr> {
    let m = Meta::new(mv, n).ok_or(ViewErr::Meta)?;
    Coc::attach(m, pv).ok_or(ViewErr::Pack { pack: pv.len(), end: m.res_end(), mblk: m.mblk })
}

#[cfg(test)]
mod tests {
    use crate::BLK;
    // decode_blk at every width 0..=64 and element type against B8's scalar unpack plus the frame, on a block of
    // random residuals; the patches are checked against the C decoder in ffi.rs
    fn check<T: crate::pod::Elt + PartialEq + core::fmt::Debug>(mut s: u64) {
        for w in 0..=64u8 {
            let pack: Vec<u8> = (0..BLK * w as usize / 8).map(|_| { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s as u8 }).collect();
            let base = [s as i64]; let (z, off, width) = ([0i64], [0u64], [w]);
            let meta = super::Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &z, off: &off, bsum: &z, width: &width,
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
    // expected values: coc.rs's coc_attach (aborts) and coc_meta_view at 152d98f
    #[test] fn attach_refuses_what_c_aborts_on() {
        let (z, off, width) = ([0i64], [0u64], [8u8]);
        let meta = super::Meta { lg: crate::DEFAULT_LG, base: &z, maxv: &z, off: &off, bsum: &z, width: &width, n: 1, nblk: 1, mblk: 1 };
        let res = BLK; // one block of width 8
        assert!(super::Coc::attach(meta, &vec![0u8; res]).is_some());
        assert!(super::Coc::attach(meta, &vec![0u8; res + 8]).is_none());
        let mut p = vec![0u64; (res + 16 + 8) / 8];
        p[res / 8] = 1; p[res / 8 + 1] = 3; // nexc 1, esz 3
        assert!(super::Coc::attach(meta, &crate::pod::bytes_mut(&mut p)[..res + 24]).is_none());
    }
    // `get` binary-searches ascending positions and scans any other order, the first match winning either way
    #[test] fn get_finds_the_first_patch_in_any_order() {
        let (base, off, width, raw) = ([100i64], [0u64], [0u8], [7i64, 8, 9].map(i64::to_ne_bytes).concat());
        let meta = super::Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &base, off: &off, bsum: &base, width: &width, n: 20, nblk: 1, mblk: 1 };
        for (pos, want) in [([2u16, 5, 9], [100, 7, 100, 8, 9]), ([5, 2, 5], [100, 8, 100, 7, 100]), ([9, 5, 2], [100, 9, 100, 8, 7])] {
            let exc = super::Exc { off: &[0, 3], pos: &pos, raw: &raw, esz: 8, asc: super::ascending(&[0, 3], &pos) };
            assert_eq!(exc.asc, pos == [2, 5, 9]);
            let c = super::Coc { meta, pack: &[], exc: Some(exc), fdelta: None };
            assert_eq!([0, 2, 3, 5, 9].map(|i| c.get(i)), want, "pos {pos:?}");
        }
        assert!(!super::ascending(&[0, 4], &[1, 2, 3])); // a block offset past the list
    }
    #[test] fn meta_new_refuses_a_misaligned_or_short_buffer() {
        let mut v = vec![0u64; 8];
        v[6] = 10; // lg
        let b = &*crate::pod::bytes_mut(&mut v);
        assert!(super::Meta::new(&b[..57], 1).is_some()); // 33 + 24
        assert!(super::Meta::new(&b[1..58], 1).is_none());
        assert!(super::Meta::new(&b[..40], 1).is_none());
    }
}
