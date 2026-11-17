#![forbid(unsafe_code)]
//! The block source (coc plan §3): a column read a block at a time, whatever its kind. Every kernel walks a column
//! through `Blocks::walk`/`span` and decodes a block through `load`/`load_w`/`view`, so the grid arithmetic and the
//! width dispatch are written once here and each kind is one decoder.
use crate::alp::Cocf;
use crate::coc::Coc;
use crate::ids;
use crate::pod::{self, Lane};
use core::ops::Range;

/// The kinds a column's blocks come from: a dense payload, FoR (`Coc`), ALP (`Cocf`), or ids at `lw` bits. A bit column
/// is ids at `lw = 1` at the column's own `lg` (`Blocks::bits`); a symbol column is ids whose keys the caller reads
/// through its dictionary.
#[derive(Clone, Copy)]
pub enum Src<'a> { Dense(&'a [u8]), For(Coc<'a>), Alp(Cocf<'a>), Ids(&'a [u8], u32) }
/// The block grid of a column of `n` elements, `1 << lg` a block: what a source reads by and a `Sink` writes by.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Grid { pub n: usize, pub lg: u32 }
impl Grid {
    pub fn lg(&self) -> u32 { self.lg }
    pub fn blk(&self) -> usize { 1 << self.lg }
    pub fn nblk(&self) -> usize { self.n.div_ceil(self.blk()) }
    /// Block `b`'s first element and element count.
    pub fn span(&self, b: usize) -> (usize, usize) { let lo = b << self.lg; (lo, (self.n - lo).min(self.blk())) }
    /// Every block in order as `(b, lo, nb)`: the one walk over a column's grid.
    pub fn walk(&self) -> impl Iterator<Item = (usize, usize, usize)> + use<> {
        let g = *self;
        (0..g.nblk()).map(move |b| { let (lo, nb) = g.span(b); (b, lo, nb) })
    }
    /// The blocks elements `lo .. hi` cross, as `(b, blo, at, end)`: block `b` starts at element `blo`, and `at .. end` is
    /// its part of the range; the walk of a slice that may start or stop inside a block.
    pub fn tiles(&self, lo: usize, hi: usize) -> impl Iterator<Item = (usize, usize, usize, usize)> + use<> {
        let lg = self.lg;
        (lo >> lg..hi.div_ceil(1 << lg)).map(move |b| (b, b << lg, lo.max(b << lg), hi.min((b + 1) << lg)))
    }
}
/// A block source: `src` read on its grid `g` (its `n`, `lg`, `span`, `walk`, `tiles` are the grid's).
#[derive(Clone, Copy)]
pub struct Blocks<'a> { pub src: Src<'a>, pub g: Grid }
impl core::ops::Deref for Blocks<'_> { type Target = Grid; fn deref(&self) -> &Grid { &self.g } }
/// Block metadata: the frame base, the largest element (`None`: not stored, a dense block's is its scan), the sum
/// (stored for FoR and ALP only), the residual width in bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BlkMeta { pub base: i64, pub max: Option<i64>, pub sum: Option<i64>, pub width: u32 }
/// Block residuals as stored: `nb` elements, `pack` at `width` bits added to `base`, and the patches as a range of the patch list
/// (empty where the kind has none).
#[derive(Clone)]
pub struct Res<'a> { pub pack: &'a [u8], pub width: u32, pub base: u64, pub exc: Range<usize>, pub nb: usize }

impl<'a> From<Coc<'a>> for Blocks<'a> { fn from(c: Coc<'a>) -> Self { Blocks::new(Src::For(c), c.meta.n) } }
impl<'a> From<Cocf<'a>> for Blocks<'a> { fn from(f: Cocf<'a>) -> Self { Blocks::new(Src::Alp(f), f.c.meta.n) } }
impl<'a> Blocks<'a> {
    /// `n` elements of `src` on its grid: an encoded column's own block size, the writer's for a payload with none.
    pub fn new(src: Src<'a>, n: usize) -> Self {
        let lg = match src { Src::For(c) | Src::Alp(Cocf { c, .. }) => c.meta.lg, _ => crate::DEFAULT_LG };
        Blocks { src, g: Grid { n, lg } }
    }
    /// A dense payload `p` of `w`-byte elements (`opnd_dense`).
    pub fn dense(p: &'a [u8], w: usize) -> Self { Blocks::new(Src::Dense(p), p.len() / w) }
    /// `Column.idsCap`'s count of `n` ids at `lw` bits, which is all `id_at` may read (`opnd_ids`).
    pub fn ids(p: &'a [u8], n: usize, lw: u32) -> Self {
        let n = n.min(ids::ids_avail(p.len(), lw));
        Blocks::new(Src::Ids(&p[..ids::ids_bytes(n, lw)], lw), n)
    }
    /// A bit column of `n` bits: ids at width 1 (decision B).
    pub fn bits(p: &'a [u8], n: usize) -> Self { Self::ids(p, n, 1) }
    /// Block `b`'s metadata.
    pub fn meta(&self, b: usize) -> BlkMeta {
        match self.src {
            Src::For(c) | Src::Alp(Cocf { c, .. }) =>
                BlkMeta { base: c.meta.base[b], max: Some(c.meta.maxv[b]), sum: Some(c.meta.bsum[b]), width: c.meta.width[b] as u32 },
            Src::Ids(_, lw) => BlkMeta { base: 0, max: Some(crate::search::ids_top(lw) as i64), sum: None, width: lw },
            Src::Dense(d) => BlkMeta { base: 0, max: None, sum: None, width: 8 * (d.len() / self.n.max(1)) as u32 },
        }
    }
    /// Block `b`'s residuals as stored, read in place.
    pub fn res(&self, b: usize) -> Res<'a> {
        match self.src {
            Src::For(c) | Src::Alp(Cocf { c, .. }) => {
                let (w, at) = (c.meta.width[b] as u32, c.meta.off[b] as usize);
                let exc = c.exc.filter(|e| !e.pos.is_empty()).map_or(0..0, |e| e.off[b] as usize..e.off[b + 1] as usize);
                Res { pack: &c.pack[at..at + c.meta.blk() * w as usize / 8], width: w, base: c.frame(b), exc, nb: self.span(b).1 }
            }
            // a block holds `blk` elements, a multiple of 8, so an ids block starts on a byte
            Src::Ids(p, lw) => { let (lo, nb) = self.span(b); Res { pack: &p[lo * lw as usize / 8..ids::ids_bytes(lo + nb, lw)], width: lw, base: 0, exc: 0..0, nb } }
            Src::Dense(d) => { let (w, (lo, nb)) = (d.len() / self.n.max(1), self.span(b)); Res { pack: &d[lo * w..(lo + nb) * w], width: 8 * w as u32, base: 0, exc: 0..0, nb } }
        }
    }
    /// Block `b`'s first `cnt` elements as `T` into `out`, patches applied. ALP answers its floats' bits, so `T` is
    /// `i32` for `real` and `i64` for `float`; a dense payload's elements are `T`'s width.
    pub fn load<T: Lane>(&self, b: usize, cnt: usize, out: &mut [T]) {
        let lo = b << self.lg();
        match self.src {
            Src::For(c) => c.decode_blk(b, cnt, out),
            Src::Alp(f) => {
                assert_eq!(size_of::<T>(), if f.f32 { 4 } else { 8 }, "Blocks::load: an ALP block read at the wrong width");
                f.load_blk(b, cnt, pod::bytes_mut(&mut out[..cnt]))
            }
            Src::Ids(p, lw) => for (k, o) in out[..cnt].iter_mut().enumerate() { *o = T::wrap(ids::id_at(p, lw, lo + k) as u64) },
            Src::Dense(d) => pod::bytes_mut(&mut out[..cnt]).copy_from_slice(&d[lo * size_of::<T>()..(lo + cnt) * size_of::<T>()]),
        }
    }
    /// `load` at element width `w` (1, 2, 4, 8; an ids or dense source also 16, zero-extended past 8 bytes) into the
    /// bytes `out`: the one width dispatch.
    pub fn load_w<'b>(&self, b: usize, cnt: usize, w: usize, out: &'b mut [u8]) -> &'b [u8] {
        let out = &mut out[..cnt * w];
        let n = out.len();
        let bad = || -> ! { panic!("qlean Blocks: a block buffer of {n} bytes is misaligned for {w}-byte elements") };
        match (self.src, w) {
            (Src::Dense(d), _) => { let lo = (b << self.lg()) * w; out.copy_from_slice(&d[lo..lo + cnt * w]) }
            (Src::Ids(p, lw), 16) => {
                let lo = b << self.lg();
                for k in 0..cnt { out[k * 16..k * 16 + 16].fill(0); out[k * 16..k * 16 + 8].copy_from_slice(&(ids::id_at(p, lw, lo + k) as u64).to_le_bytes()) }
            }
            (_, 1) => self.load::<u8>(b, cnt, pod::cast_mut(out).unwrap_or_else(|| bad())),
            (_, 2) => self.load::<i16>(b, cnt, pod::cast_mut(out).unwrap_or_else(|| bad())),
            (_, 4) => self.load::<i32>(b, cnt, pod::cast_mut(out).unwrap_or_else(|| bad())),
            _ => self.load::<i64>(b, cnt, pod::cast_mut(out).unwrap_or_else(|| bad())),
        }
        out
    }
    /// Block `b` at width `w`: a slice of a dense payload in place, else restored into `buf` (block size * w bytes);
    /// the element count is the answer's length / `w` (`opnd_blk`).
    pub fn view<'b>(&self, b: usize, w: usize, buf: &'b mut [u8]) -> &'b [u8] where 'a: 'b {
        let (lo, nb) = self.span(b);
        if let Src::Dense(d) = self.src { return &d[lo * w..(lo + nb) * w] }
        self.load_w(b, nb, w, buf)
    }
    /// Elements `at .. at + cnt` at width `w`, as the slice of `buf` they are restored into: one or more of this source's own
    /// blocks, whichever its block size cuts them from.
    pub fn range<'b>(&self, at: usize, cnt: usize, w: usize, buf: &'b mut [u8]) -> &'b [u8] where 'a: 'b {
        let mut tmp = pod::Scr::<u64, 1024>::new(2 * self.blk());
        for (b, blo, s, e) in self.tiles(at, at + cnt) {
            let x = self.view(b, w, pod::bytes_mut(&mut tmp));
            buf[(s - at) * w..(e - at) * w].copy_from_slice(&x[(s - blo) * w..(e - blo) * w]);
        }
        &buf[..cnt * w]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // every kind's `view` against its elements, and the walk's spans covering `0..n` once
    #[test]
    fn kinds_agree() {
        let n = 2100usize;
        let v: alloc::vec::Vec<u32> = (0..n as u32).map(|i| i % 13).collect();
        let d = Blocks::dense(pod::bytes(&v), 4);
        let mut p = alloc::vec![0u8; ids::ids_bytes(n, 4)];
        for (k, &x) in v.iter().enumerate() { ids::id_put(&mut p, 4, k, x as u64) }
        let i = Blocks::ids(&p, n, 4);
        let mut got = 0;
        for (b, lo, nb) in d.walk() {
            assert_eq!(lo, got);
            got += nb;
            let (mut x, mut y) = (pod::Scr::<u64>::new(1024), pod::Scr::<u64>::new(1024));
            assert_eq!(d.view(b, 4, pod::bytes_mut(&mut x)), i.view(b, 4, pod::bytes_mut(&mut y)));
            assert_eq!(i.meta(b), BlkMeta { base: 0, max: Some(15), sum: None, width: 4 });
            assert_eq!(i.res(b).pack.len(), nb / 2);
        }
        assert_eq!(got, n);
        let mut r = alloc::vec![0u8; 4 * 100];
        assert_eq!(i.range(1000, 100, 4, &mut r), &pod::bytes(&v)[4000..4400]);
    }
}
