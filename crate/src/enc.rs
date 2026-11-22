#![forbid(unsafe_code)]
//! Column (a): the Frame of Reference encoder's per-block steps — coc.rs's FoR encode (A7), its patch list and the
//! whole-column decode (A8), coc.rs's block steps of `coc_enc` (A16) and of the fill/move sources (A17).
//!
//! `coc_enc` (coc.rs) owns three `lean_object*` and calls the source's C callbacks, so its orchestration —
//! `coc_enc_open/plan/layout/pair/free`, `src_pass`, `qlean_coc_encode_src`, `fill_*` — stays C in phase 1 (§1, Lean
//! boundary), as the pool does. Rust gets one block at a time: `EncMeta` is what the meta pass may write for block
//! `b`, `EncPack` what the pack pass may write; `ffi::CEnc` cuts them, so parallel blocks hold disjoint borrows.

use crate::coc::Coc;
use crate::pod::Elt;


/// Block `b`'s metadata slots in a column being written: the meta pass's whole output for that block.
pub struct EncMeta<'a> {
    pub b: usize,
    pub base: &'a mut i64, pub maxv: &'a mut i64, pub width: &'a mut u8, pub bsum: &'a mut i64,
    /// the frame above `base` (coc.rs `fdelta`), when the column keeps frames
    pub frm: Option<&'a mut u64>,
    /// the block's patch count, `exc_off[b + 1]` before the prefix sum
    pub nexc: &'a mut u32,
    /// whether the block may patch, Lean `Coc.encodeAt`'s `patch && n < 2 ^ 32`: a column of `2 ^ 32` elements or more
    /// has no patch list, its block offsets being `u32`
    pub patch: bool,
}
/// Block `b`'s output region in a column being written: residuals and patch slots, from the layout's offsets.
pub struct EncPack<'a> {
    pub nb: usize,
    pub frame: u64, pub width: u8,
    /// `blk * width / 8` bytes at `off[b]`
    pub res: &'a mut [u8],
    /// `exc_off[b] .. exc_off[b + 1]`
    pub pos: &'a mut [u16], pub raw: &'a mut [u8],
}

// ---- A7: coc.rs ----
/// `COC_NUL` of the element type: `INT16_MIN`, `INT32_MIN`, `INT64_MIN`; `u8` has none, so `INT64_MIN` there never matches.
pub fn nul<T: Elt>() -> i64 { if size_of::<T>() == 1 { i64::MIN } else { i64::MIN >> (64 - 8 * size_of::<T>()) } }
/// coc.rs `pack_block`: `nb` elements of `src` minus `base` into `dst` at `w` bits, the first ⌈nb*w/8⌉ bytes of it.
pub fn pack_block<T: Elt>(dst: &mut [u8], src: &[T], nb: usize, base: i64, w: u8) {
    let r = |v: &T| (v.i() as u64).wrapping_sub(base as u64);
    let src = &src[..nb];
    #[inline(always)]
    fn pack_at<T: Elt, const W: u32>(dst: &mut [u8], src: &[T], base: i64) {
        let (r, w) = (|v: &T| (v.i() as u64).wrapping_sub(base as u64), W as usize);
        match W {
            0 => {}
            // 8/w residuals to a byte, built then stored so the buffer needs no zeroing
            1 | 2 | 4 => {
                let byte = |g: &[T]| g.iter().enumerate().fold(0u8, |a, (t, v)| a | ((r(v) & ((1 << W) - 1)) << (t * w)) as u8);
                let ch = src.chunks_exact(8 / w);
                let (tail, k) = (ch.remainder(), src.len() / (8 / w));
                for (o, g) in dst.iter_mut().zip(ch) { *o = byte(g) }
                if !tail.is_empty() { dst[k] = byte(tail) }
            }
            _ => for (o, v) in dst.chunks_exact_mut(w / 8).zip(src) { o.copy_from_slice(&r(v).to_le_bytes()[..w / 8]) },
        }
    }
    // a lane width through `by_width!`; an odd one packed by `simd::res_pack`
    if w & w.wrapping_sub(1) == 0 { return crate::by_width!(w, pack_at::<T>(dst, src, base)) }
    let mut v = crate::pod::Scr::<u64>::new(nb.next_multiple_of(64));
    for (o, x) in v.iter_mut().zip(src) { *o = r(x) }
    crate::simd::res_pack(&v, w, nb, dst)
}
/// coc.rs `encode_meta_blk`: block metadata with no patch list.
pub fn encode_meta_blk<T: Elt>(m: &mut EncMeta, x: &[T], nb: usize) {
    let x = &x[..nb];
    let (mn, mx) = x.iter().fold((x[0].i(), x[0].i()), |(a, b), v| (a.min(v.i()), b.max(v.i())));
    let s = if mn == nul::<T>() { x.iter().map(|v| v.i()).filter(|&v| v != nul::<T>()).fold(0i64, i64::wrapping_add) }
            else { x.iter().fold(0i64, |a, v| a.wrapping_add(v.i())) };
    *m.base = mn; *m.maxv = mx; *m.bsum = s;
    *m.width = crate::bits::width_for((mx as u64).wrapping_sub(mn as u64));
}
// ---- A8: coc.rs ----
/// coc.rs `pack_exc_blk`: residuals and the block's `ne` patches — an element below the frame or past `2 ^ width` above
/// it, Lean `Coc.outside` — their slots set to the frame.
pub fn pack_exc_blk<T: Elt>(p: &mut EncPack, x: &[T], ne: u32) {
    let (base, w, x) = (p.frame as i64, p.width, &x[..p.nb]);
    if ne == 0 { return pack_block(p.res, x, p.nb, base, w) }
    let (mut ys, mut k) = (crate::pod::Scr::<T>::filled(p.nb, T::wrap(base as u64)), 0);
    let y: &mut [T] = &mut ys; // the one deref, outside the element loop
    for (i, &v) in x.iter().enumerate() {
        // below the frame, `r` wraps past every width but 64, where the frame is the minimum
        let r = (v.i() as u64).wrapping_sub(base as u64);
        if w < 64 && r >> w != 0 {
            let mut e = [v];
            p.raw[k * size_of::<T>()..][..size_of::<T>()].copy_from_slice(crate::pod::bytes_mut(&mut e));
            p.pos[k] = i as u16;
            k += 1;
        } else { y[i] = v }
    }
    pack_block(p.res, y, p.nb, base, w)
}
/// coc.rs `decode`: the whole column into `out` (`n` long).
pub fn decode<T: Elt>(c: &Coc, out: &mut [T]) {
    let s = crate::blocks::Blocks::from(*c);
    for (b, lo, nb) in s.walk() { s.load(b, nb, &mut out[lo..lo + nb]) }
}

// ---- A16: coc.rs, the block steps of `coc_enc` ----
/// `x` as `nb` elements of `T`; C read them through a typed pointer, so a misaligned source is a bug there too.
pub fn elts<'b, T: crate::pod::Pod>(x: &'b [u8], what: &str) -> &'b [T] {
    crate::pod::cast::<T>(x).unwrap_or_else(|| panic!("qlean {what}: a block of {} bytes is misaligned for {}-byte elements", x.len(), size_of::<T>()))
}
/// coc.rs `coc_enc_for_meta`: the FoR meta step over block `b`'s `nb` elements `x` at `width` bytes each.
pub fn for_meta(m: &mut EncMeta, x: &[u8], width: usize, nb: usize) {
    fn go<T: Elt>(m: &mut EncMeta, x: &[u8], nb: usize) { for_blk(m, elts::<T>(x, "coc_enc_for_meta"), nb); }
    crate::by_width!(int width, go(m, x, nb))
}
/// The writer's FoR block, Lean `Coc.planOf`: of the widths `d` in `0 ..= W` (`W` the bit length of `max - min`), the
/// one whose cost `⌈nb·d/8⌉ + (2 + esz)·patches` is least, the narrower on a tie, at the frame patching fewest, the
/// lowest of those; answers the patch count. With `m.patch` off, `W` from the minimum, which patches nothing.
pub fn for_blk<T: Elt>(m: &mut EncMeta, x: &[T], nb: usize) -> u32 {
    encode_meta_blk(m, x, nb);
    let (mn, top, esz) = (*m.base, *m.width as usize, size_of::<T>());
    if !m.patch {
        *m.frm.as_deref_mut().expect("for_blk: a Frame of Reference column keeps its frames") = 0;
        *m.nexc = 0;
        return 0
    }
    let (d, f, np) = plan(&x[..nb], mn, top, esz);
    *m.frm.as_deref_mut().expect("for_blk: a Frame of Reference column keeps its frames") = (f as u64).wrapping_sub(mn as u64);
    (*m.width, *m.nexc) = (d as u8, np as u32);
    np as u32
}
/// `Coc.planOf`'s width, frame and patch count for the keys `x` of minimum `mn`, `top` the bit length of their range:
/// the least `(cost, d)`. A width is searched with `frame_at` only while a lower bound on its cost does not already
/// lose to the best found, so a random block costs a histogram and no sort.
fn plan<T: Elt>(x: &[T], mn: i64, top: usize, esz: usize) -> (usize, i64, usize) {
    let (nb, pc) = (x.len(), 2 + esz);
    let bits = |d: usize| (nb * d).div_ceil(8);
    // lo[d] <= the patches at width d. Residuals in buckets of 2 ^ b, at most 64: a window of 2 ^ d >= 2 ^ b from a
    // key spans at most `span` buckets, so leaves at least the keys outside the fullest run of `span`. No more buckets
    // than keys (⌈log2 nb⌉ bits of them), so the table below costs what the block does
    let b = top.saturating_sub((usize::BITS - nb.saturating_sub(1).leading_zeros()).min(6) as usize);
    let nbk = 1usize << (top - b);
    // a key's bucket is below `nbk` <= 64, its residual being below `2 ^ top`. Four histograms, as one would chain the
    // increments of a run of keys in one bucket through memory
    let mut h4 = [[0u32; 65]; 4];
    let at = |v: &T| 1 + (((v.i() as u64).wrapping_sub(mn as u64) >> b) & 63) as usize;
    let ch = x.chunks_exact(4);
    for v in ch.remainder() { h4[0][at(v)] += 1 }
    for g in ch { for (h, v) in h4.iter_mut().zip(g) { h[at(v)] += 1 } }
    let mut h = [0usize; 65];
    for k in 1..=nbk { h[k] = h[k - 1] + h4.iter().map(|g| g[k] as usize).sum::<usize>() } // prefix sums
    let mut lo = [0usize; 65];
    for d in b..top {
        let span = (((1u64 << d) - 1).div_ceil(1u64 << b) as usize + 1).min(nbk); // no overflow at b = d = 63
        lo[d] = nb - (span..=nbk).map(|e| h[e] - h[e - span]).max().unwrap_or(nb);
    }
    for d in 0..b { lo[d] = lo[b] } // patches only grow as the width narrows
    // the widest width patches nothing at frame `mn`; widths `a .. z` are still open
    let (mut best, mut pick, mut a, mut z, mut up) = (bits(top), (top, mn, 0usize), 0, top, false);
    let mut s: Option<crate::pod::Scr<u64>> = None;
    loop {
        let open = |d: usize, lo: &[usize; 65]| { let c = bits(d) + lo[d] * pc; c < best || c == best && d < pick.0 };
        while a < z && !open(a, &lo) { a += 1 }
        while z > a && !open(z - 1, &lo) { z -= 1 }
        if a >= z { return pick }
        // alternate ends: a narrow width lowers `best`, a wide one's patches bound every narrower width's
        let d = if up { a } else { z - 1 };
        up = !up;
        let s = s.get_or_insert_with(|| {
            let mut s = crate::pod::Scr::<u64>::new(nb);
            for (o, v) in s.iter_mut().zip(x) { *o = (v.i() as u64).wrapping_sub(mn as u64) }
            s.sort_unstable(); // an LSD radix sort measured no faster
            s
        });
        // `need` patches close `d`. If every `nb - need + 1` consecutive sorted keys spread at least `2 ^ e`, no window
        // of `2 ^ e` holds that many, so width `e` patches at least `need`: `need` subtractions close every such `e`
        let need = if d < pick.0 { (best - bits(d)) / pc + 1 } else { (best - bits(d)).div_ceil(pc) };
        if need <= nb {
            let k = nb - need;
            let spread = (0..need).map(|i| s[i + k] - s[i]).min().unwrap_or(0);
            if spread >> d != 0 {
                for e in 0..64 - spread.leading_zeros() as usize { lo[e] = lo[e].max(need) }
                continue
            }
        }
        let (f, np) = frame_at(&s[..], d);
        let c = bits(d) + np * pc;
        if c < best || c == best && d < pick.0 { (best, pick) = (c, (d, (f as i64).wrapping_add(mn), np)) }
        for e in 0..=d { lo[e] = lo[e].max(np) }
    }
}
/// `Coc.frameAt` over the sorted residuals `s`: a window of `2 ^ d` from each distinct one, its far end `j` only moving
/// forward; answers the frame's residual and the patches it leaves.
fn frame_at(s: &[u64], d: usize) -> (u64, usize) {
    let (nb, mut best, mut j) = (s.len(), (s[0], usize::MAX), 0);
    for i in 0..nb {
        if i > 0 && s[i] == s[i - 1] { continue }
        while j < nb && (d >= 64 || (s[j] - s[i]) >> d == 0) { j += 1 }
        if nb - (j - i) < best.1 { best = (s[i], nb - (j - i)) }
    }
    best
}
/// coc.rs `coc_enc_for_pack`: `p.pos` holds the block's patches, `exc_off[b + 1] - exc_off[b]` of them.
pub fn for_pack(p: &mut EncPack, x: &[u8], width: usize) {
    fn go<T: Elt>(p: &mut EncPack, x: &[u8]) { let ne = p.pos.len() as u32; pack_exc_blk(p, elts::<T>(x, "coc_enc_for_pack"), ne) }
    crate::by_width!(int width, go(p, x))
}
/// coc.rs `coc_sumnul`: the null the writer's block sums skip, which its trailer records: the element type's own.
pub fn coc_sumnul(width: usize) -> i64 {
    if width == 1 || width == 8 { i64::MIN } else if width == 2 { i16::MIN as i64 } else { i32::MIN as i64 }
}
/// Row `i` of a column is null: bit `i` of the bitmap `nul` (Lean `Column.bitAt`; a bit past `nul` is 0).
pub fn is_nul(nul: &[u8], i: usize) -> bool { nul.get(i >> 3).is_some_and(|b| b >> (i & 7) & 1 != 0) }
/// Lean `Coc.nulBlock`, the null branch of the writer's block step `Coc.planBlock`: block `m.b`'s `nb` elements `x`
/// (rows `lo ..`), some null. Base, maximum and sum over the rows that are not null, the width one wider than the range
/// where a value sits at the top residual `2 ^ d - 1`, flagged (`coc::NUL_FLAG`); its frame the base, nothing patched.
pub fn nul_meta(m: &mut EncMeta, x: &[u8], width: usize, nb: usize, nul: &[u8], lo: usize) {
    fn go<T: Elt>(m: &mut EncMeta, x: &[u8], nb: usize, nul: &[u8], lo: usize) {
        let (mut mn, mut mx, mut s, mut any) = (0i64, 0i64, 0i64, false);
        for (i, v) in elts::<T>(x, "coc_enc_nul_meta")[..nb].iter().enumerate() {
            if is_nul(nul, lo + i) { continue }
            let k = v.i();
            if any { (mn, mx) = (mn.min(k), mx.max(k)) } else { (mn, mx, any) = (k, k, true) }
            if k != self::nul::<T>() { s = s.wrapping_add(k) }
        }
        let r = (mx as u64).wrapping_sub(mn as u64);
        let mut d = crate::bits::width_for(r);
        if any && d < 64 && r == (1u64 << d) - 1 { d += 1 }
        (*m.base, *m.maxv, *m.bsum, *m.width, *m.nexc) = (mn, mx, s, d | crate::coc::NUL_FLAG, 0);
        if let Some(f) = m.frm.as_deref_mut() { *f = 0 }
    }
    crate::by_width!(int width, go(m, x, nb, nul, lo))
}
/// The residuals of a block `nul_meta` planned: a null row's the top one `2 ^ d - 1`, every other row's its key less
/// the base, so the null is tested on the block and never decoded.
pub fn nul_pack(p: &mut EncPack, x: &[u8], width: usize, nul: &[u8], lo: usize) {
    fn go<T: Elt>(p: &mut EncPack, x: &[u8], nul: &[u8], lo: usize) {
        let (d, nb) = (p.width & crate::coc::WIDTH_MASK, p.nb);
        if d == 0 { return }
        let top = if d == 64 { u64::MAX } else { (1u64 << d) - 1 };
        let mut v = crate::pod::Scr::<u64>::new(nb.next_multiple_of(64));
        for (i, (o, x)) in v.iter_mut().zip(&elts::<T>(x, "coc_enc_nul_pack")[..nb]).enumerate() {
            *o = if is_nul(nul, lo + i) { top } else { (x.i() as u64).wrapping_sub(p.frame) }
        }
        // `pack_block` at base 0, not `res_pack`: a null block's width may be a lane width (1, 2, 4, …), which only
        // `pack_block`'s `by_width!` arm packs
        pack_block::<u64>(p.res, &v[..nb], nb, 0, d)
    }
    crate::by_width!(int width, go(p, x, nul, lo))
}

// ---- A17: coc.rs ----
/// coc.rs `coc_narrow`: `v` narrowed to `width` bytes into `out` (`v` itself when `width` is 8).
pub fn narrow<'b>(width: usize, v: &'b [i64], out: &'b mut [u8]) -> &'b [u8] {
    fn put<'b, T: Elt>(v: &'b [i64], out: &'b mut [u8]) -> &'b [u8] {
        if T::W == 8 { return crate::pod::bytes(v) }
        let out = &mut out[..T::W * v.len()];
        for (o, &x) in out.chunks_exact_mut(T::W).zip(v) { o.copy_from_slice(&x.to_ne_bytes()[..T::W]) }
        out
    }
    assert!(matches!(width, 1 | 2 | 4 | 8), "qlean: a Frame of Reference element of {width} bytes; the writer has 1, 2, 4 and 8");
    crate::by_width!(int width, put(v, out))
}
/// coc.rs `move_meta`, the branch where block `pb` of the column `p` is taken whole: its metadata is the block's,
/// and its patch count is what the layout prefix-sums. Answers it, and leaves it in `m.nexc`.
pub fn move_meta(m: &mut EncMeta, p: &Coc, pb: usize) -> u32 {
    (*m.base, *m.maxv, *m.bsum, *m.width) = (p.meta.base[pb], p.meta.maxv[pb], p.meta.bsum[pb], p.meta.width[pb]);
    if let Some(fr) = m.frm.as_deref_mut() { *fr = p.fdelta.map_or(0, |d| d[pb]) }
    let ne = p.blk_nexc(pb) as u32;
    *m.nexc = ne;
    ne
}
/// coc.rs `move_pack`, the taken branch: block `pb` of `c`'s residuals (`p.res` is the whole `blk * width / 8`
/// bytes, a pack shorter than its widths claim reading zeros past its end, `Column.resAt`'s convention) and its patch
/// list, whose positions move unchanged. `esz` is the written column's element size.
pub fn move_pack(p: &mut EncPack, c: &Coc, pb: usize, esz: usize) {
    let (bytes, so) = (c.meta.blk() * c.meta.width[pb] as usize / 8, c.meta.off[pb] as usize);
    let src = c.pack.get(so..).unwrap_or(&[]);
    let avail = src.len().min(bytes);
    p.res[..avail].copy_from_slice(&src[..avail]);
    p.res[avail..bytes].fill(0);
    if let Some(e) = c.exc.filter(|e| !e.pos.is_empty()) {
        // the element's first `esz` bytes: a patch of a wider column is truncated as the written column is
        for (q, j) in (e.off[pb] as usize..e.off[pb + 1] as usize).enumerate() {
            p.pos[q] = e.pos[j];
            p.raw[q * esz..(q + 1) * esz].copy_from_slice(&e.raw[j * e.esz..j * e.esz + esz]);
        }
    }
}

// ---- K24b: coc.rs's writer orchestration that needs no raw pointer; ffi.rs keeps the Lean objects, the pool and the C callbacks ----
/// coc.rs `src_run`'s lower bound on a sized block's share of the encoded size: its residuals and its patches' bytes.
pub fn block_bytes(lg: u32, width_b: u8, nexc: u32, width: usize) -> usize { (1usize << lg) * width_b as usize / 8 + nexc as usize * (width + 2) }
/// coc.rs `coc_enc_layout`'s patch list header: `nexc` and `w` in its first 16 bytes, the rest of `t` zero.
pub fn exc_header(t: &mut [u8], nexc: usize, w: u64) {
    t.fill(0);
    t[..8].copy_from_slice(&(nexc as u64).to_ne_bytes());
    t[8..16].copy_from_slice(&w.to_ne_bytes());
}
/// coc.rs `coc_enc_plan`'s tail: the bytes after the residuals, the patch list of Frame of Reference (with its frames when
/// `frm`); 0 for a column with none.
pub fn tail_bytes(nexc: usize, frm: bool, width: usize, nblk: usize) -> usize {
    use crate::layout::{exc_layout, Tail};
    if nexc == 0 { return 0 }
    exc_layout(nblk, nexc, width, if frm { Tail::Frames } else { Tail::None }).expect("qlean: the exception layout overflows").size
}
/// coc.rs `alp_offsets`: per-block patch counts in `exc_off[1..=nblk]` into prefix sums; answers the total.
pub fn exc_offsets(exc_off: &mut [u32], nblk: usize) -> usize {
    exc_off[0] = 0;
    for b in 0..nblk { exc_off[b + 1] = exc_off[b + 1].wrapping_add(exc_off[b]) }
    exc_off[nblk] as usize
}

/// What a `Sink` (`ffi.rs`) writes, a block of its grid at a time: the block's elements, or, where the answer holds whole
/// blocks of a column already in the writer's form, the block itself (`take`).
pub trait Producer: Sync {
    /// Elements `lo .. lo + nb` (block `b` of the writer's grid) at `w` bytes each: a slice of the producer's own memory, or
    /// written into `buf` (`16 * nb` bytes, 8-aligned).
    fn block<'s>(&'s self, b: usize, lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8];
    /// Block `pb` of a column in the writer's own form that answer block `b` equals, with `pb`.
    fn take(&self, _b: usize) -> Option<(Coc<'_>, usize)> { None }
}
/// A kernel's `fill` (elements `i0 .. i0 + v.len()` as `i64`) narrowed to the writer's `w` bytes, in `buf`.
pub fn filled<'s>(fill: impl FnOnce(&mut [i64], usize), lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8] {
    let (v, o) = buf.split_at_mut(8 * nb);
    let v = crate::pod::cast_mut::<i64>(v).expect("qlean Sink: a block buffer is misaligned for i64");
    fill(v, lo);
    narrow(w, v, o)
}
/// A closure is a producer with no `take`: the form every kernel that computes an answer a block at a time uses.
impl<F: Fn(&mut [i64], usize) + Sync> Producer for F {
    fn block<'s>(&'s self, _: usize, lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8] { filled(self, lo, nb, w, buf) }
}
/// A column read as the writer's elements: the encoder's input where it is dense, a transcode where it is not. A span on
/// the column's own grid is read in place where it lies, any other is cut from the blocks it crosses.
impl Producer for crate::blocks::Blocks<'_> {
    fn block<'s>(&'s self, _: usize, lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8] {
        let b = lo >> self.lg();
        if self.span(b) == (lo, nb) { self.view(b, w, buf) } else { self.range(lo, nb, w, buf) }
    }
}
/// coc.rs `move_meta` then `move_pack`: block `m.b` of the producer `mv`, its metadata into `m`, then its residuals and patches
/// into `pack(whole)` (asked once, after `m` is written; `whole` for a taken block's full `blk * width / 8` residual region),
/// so whatever the producer computes for the block it computes once. A moved block's metadata, residuals and patch list are its
/// column's (the positions are the block's own), which the writer's own step would choose for the same elements. Else the
/// writer's own steps, reading `x`, rows `lo ..` null where `nul` says (Lean `Coc.planBlock`): a block holding a null is
/// `nul_meta`'s, any other `for_meta`'s.
pub fn move_blk<'a, 'b>(mv: &(impl Producer + ?Sized), m: &mut EncMeta, pack: impl FnOnce(bool) -> EncPack<'b>, x: impl FnOnce() -> &'a [u8],
                        nb: usize, width: usize, nul: &[u8], lo: usize) {
    if let Some((c, pb)) = mv.take(m.b) { move_meta(m, &c, pb); return move_pack(&mut pack(true), &c, pb, width) }
    let x = x();
    if (lo..lo + nb).any(|i| is_nul(nul, i)) { nul_meta(m, x, width, nb, nul, lo); return nul_pack(&mut pack(false), x, width, nul, lo) }
    for_meta(m, x, width, nb);
    for_pack(&mut pack(false), x, width)
}

#[cfg(test)]
mod a17_tests {
    use super::*;
    // Expected values come from running the original C (coc_narrow, coc_enc_blk_meta) on these vectors, /data/tmp/qrs/A17/one.c;
    // the random comparison of those and of move_meta, move_pack, alp_patch_blk is /data/tmp/qrs/A17/diff.c.
    #[test] fn narrow_truncates() {
        let v = [1, -1, 0x1_0000_0001, i64::MIN, i64::MAX];
        let mut o = [0u8; 40];
        assert_eq!(narrow(1, &v, &mut o), [1, 255, 1, 0, 255]);
        assert_eq!(narrow(2, &v, &mut o), [1, 0, 255, 255, 1, 0, 0, 0, 255, 255]);
        assert_eq!(narrow(4, &v, &mut o), [1, 0, 0, 0, 255, 255, 255, 255, 1, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255]);
        assert_eq!(narrow(8, &v, &mut o).as_ptr(), v.as_ptr().cast::<u8>());
    }
    #[test] #[should_panic(expected = "a Frame of Reference element of 3 bytes; the writer has 1, 2, 4 and 8")]
    fn narrow_refuses_an_odd_width() { narrow(3, &[0], &mut [0; 8]); }
    /// `for_blk`'s answer on `v` as elements of `width` bytes: (patches, base, maxv, bsum, residual width, frame)
    fn meta(v: &[i64], width: usize) -> (u32, i64, i64, i64, u8, u64) {
        let (mut base, mut maxv, mut width_, mut bsum, mut nexc, mut frm) = (0, 0, 0, 0, 0, 7u64);
        let mut m = EncMeta { b: 0, base: &mut base, maxv: &mut maxv, width: &mut width_, bsum: &mut bsum, frm: Some(&mut frm),
                              nexc: &mut nexc, patch: true };
        let ne = match width {
            2 => for_blk(&mut m, &v.iter().map(|&x| x as i16).collect::<Vec<_>>(), v.len()),
            4 => for_blk(&mut m, &v.iter().map(|&x| x as i32).collect::<Vec<_>>(), v.len()),
            _ => for_blk(&mut m, v, v.len()),
        };
        (ne, base, maxv, bsum, width_, frm)
    }
    #[test] fn blk_meta_at_each_width() {
        let u = [i16::MIN as i64, 3, 9, -2];
        // the null is the minimum, as in `Coc.blockOf`, and patched at 4 bytes: width 4 from frame -2, 2 + 4 bytes
        assert_eq!(meta(&u, 2), (1, -32768, 9, 10, 4, 32766));
        // width 2 from frame 100000 and width 17 from 500 both cost 7 bytes: the narrower wins
        assert_eq!(meta(&[500, 100000, 100003], 4), (1, 500, 100003, 200503, 2, 99500));
        // at 8 bytes a patch costs 10, more than width 16's 8 bytes
        assert_eq!(meta(&u, 8), (0, -32768, 9, -32758, 16, 0));
    }
    #[test] fn move_pack_zero_pads_a_short_pack() {
        // block 0 of width 8 whose pack holds 3 of its 1024 bytes: the rest reads as zeros, `Column.resAt`'s convention
        let (base, z, off, width) = ([5i64], [0i64], [0u64], [8u8]);
        let meta = crate::coc::Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &z, off: &off, bsum: &z, width: &width, n: 3, nblk: 1, mblk: 1 };
        let c = Coc { meta, pack: &[1, 2, 3], exc: None, fdelta: None };
        let mut res = [0xa5u8; crate::BLK];
        let mut p = EncPack { nb: 3, frame: 5, width: 8, res: &mut res, pos: &mut [], raw: &mut [] };
        move_pack(&mut p, &c, 0, 2);
        assert_eq!(&res[..4], [1, 2, 3, 0]);
        assert!(res[3..].iter().all(|&x| x == 0));
    }
}

#[cfg(test)]
mod a7_tests {
    use super::*;
    // Expected values come from running the original C (pack_block_i16, frame_pick_i64) on these inputs; the 8M-check
    // comparison over every width, nulls and frames is /data/tmp/qrs/A7/diff.c.
    #[test] fn pack_block_widths() {
        let x: [i16; 10] = [5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        for (w, want) in [(1u8, &[170u8, 2][..]), (2, &[228, 228, 4]), (3, &[136, 198, 250, 8]), (4, &[16, 50, 84, 118, 152]),
                          (5, &[32, 136, 65, 138, 57, 40, 1])] {
            let mut d = [0u8; 8];
            pack_block(&mut d[..want.len()], &x, 10, 5, w);
            assert_eq!(&d[..want.len()], want, "w {w}");
        }
        let mut d = [0u8; 20];
        pack_block(&mut d, &x, 10, 5, 16);
        assert_eq!(d, [0, 0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 6, 0, 7, 0, 8, 0, 9, 0]);
    }
    #[test] fn for_blk_lifts_over_low_outliers() {
        // 24 zeros under 100000 .. 100255: width 8 from frame 100000 and 24 patches (1000 + 240 bytes), not width 17
        // from 0 (2125 bytes)
        let x: [i64; 1000] = core::array::from_fn(|i| if i < 24 { 0 } else { 100000 + (i & 255) as i64 });
        let (mut base, mut maxv, mut width, mut bsum, mut nexc, mut frm) = (0, 0, 0, 0, 0, 0u64);
        let mut m = EncMeta { b: 0, base: &mut base, maxv: &mut maxv, width: &mut width, bsum: &mut bsum, frm: Some(&mut frm),
                              nexc: &mut nexc, patch: true };
        assert_eq!(for_blk(&mut m, &x, 1000), 24);
        assert_eq!((base, width, frm), (0, 8, 100000));
        // patching off (a column of `2 ^ 32` elements or more): width 17 from the minimum, no patch, no frame
        let mut m = EncMeta { b: 0, base: &mut base, maxv: &mut maxv, width: &mut width, bsum: &mut bsum, frm: Some(&mut frm),
                              nexc: &mut nexc, patch: false };
        assert_eq!(for_blk(&mut m, &x, 1000), 0);
        assert_eq!((base, width, frm, nexc), (0, 17, 0, 0));
    }
    #[test] fn encode_meta_blk_nulls() {
        let x: [i16; 4] = [i16::MIN, 3, 9, -2];
        let (mut base, mut maxv, mut width, mut bsum, mut nexc) = (0, 0, 0, 0, 0);
        let mut m = EncMeta { b: 0, base: &mut base, maxv: &mut maxv, width: &mut width, bsum: &mut bsum, frm: None, nexc: &mut nexc,
                              patch: true };
        encode_meta_blk(&mut m, &x, 4);
        // the null is the minimum, so the sum skips it
        assert_eq!((base, maxv, width, bsum), (i16::MIN as i64, 9, 16, 10));
    }
    #[test] fn nul_pack_lane_widths() {
        // row 2 null; keys {0} give width 1 (the null at the top residual 1), keys {0, 1} width 2 (top 3)
        for (x, d, want) in [([0i64, 0, 0, 0], 1u8, 0b0100u8), ([0, 1, 0, 0], 2, 0b00_11_01_00)] {
            let mut res = [0u8; 8];
            let mut p = EncPack { nb: 4, frame: 0, width: d, res: &mut res, pos: &mut [], raw: &mut [] };
            nul_pack(&mut p, crate::pod::bytes(&x), 8, &[0b0100], 0);
            assert_eq!(res[0], want, "d {d}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BLK;
    // encode with patches, decode the whole column: the round trip, for a column of low outliers and nulls, so the
    // frame is lifted and the patch list is non-empty; the C comparison is /data/tmp/qrs/A8/diff.c
    fn round<T: Elt + PartialEq + core::fmt::Debug>(x: &[T]) -> u32 {
        let n = x.len();
        let (mut base, mut maxv, mut bsum, mut width, mut frm) = (vec![0i64; 2], vec![0i64; 2], vec![0i64; 2], vec![0u8; 2], vec![0u64; 2]);
        let mut ne = vec![0u32; 2];
        for b in 0..n.div_ceil(BLK) {
            let mut nx = 0;
            let mut m = EncMeta { b, base: &mut base[b], maxv: &mut maxv[b], width: &mut width[b], bsum: &mut bsum[b],
                                  frm: Some(&mut frm[b]), nexc: &mut nx, patch: true };
            let nb = BLK.min(n - b * BLK);
            ne[b] = for_blk(&mut m, &x[b * BLK..], nb);
        }
        let (mut off, mut pack, mut at) = (vec![0u64; 2], vec![0u8; 2 * BLK * 8], 0usize);
        let (mut pos, mut raw) = (vec![0u16; ne.iter().sum::<u32>() as usize], vec![0u8; ne.iter().sum::<u32>() as usize * size_of::<T>()]);
        let mut eo = vec![0u32; 3];
        for b in 0..n.div_ceil(BLK) {
            off[b] = at as u64;
            let nb = BLK.min(n - b * BLK);
            let (e0, e1) = (eo[b] as usize, (eo[b] + ne[b]) as usize);
            eo[b + 1] = eo[b] + ne[b];
            let mut p = EncPack { nb, frame: (base[b] as u64).wrapping_add(frm[b]), width: width[b],
                                  res: &mut pack[at..at + (nb * width[b] as usize).div_ceil(8)],
                                  pos: &mut pos[e0..e1], raw: &mut raw[e0 * size_of::<T>()..e1 * size_of::<T>()] };
            pack_exc_blk(&mut p, &x[b * BLK..], ne[b]);
            at += BLK * width[b] as usize / 8;
        }
        let nbk = n.div_ceil(BLK);
        let c = Coc { meta: crate::coc::Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &maxv, off: &off, bsum: &bsum, width: &width,
                                                n, nblk: nbk, mblk: 2 },
                      pack: &pack, exc: Some(crate::coc::Exc { off: &eo, pos: &pos, raw: &raw, esz: size_of::<T>(), asc: crate::coc::ascending(&eo, &pos) }),
                      fdelta: Some(&frm) };
        let mut out = vec![T::wrap(0); n];
        decode(&c, &mut out);
        assert_eq!(out, x);
        ne.iter().sum()
    }
    #[test] fn decode_round_trip_with_patches() {
        let mut x: Vec<i64> = (0..BLK as i64 + 300).map(|i| 1_000_000 + (i * 37) % 500).collect();
        x[3] = -5; x[900] = 1 << 40; x[1100] = i64::MIN; x[1200] = 7;
        assert!(round(&x) >= 4);
        let y: Vec<i16> = (0..2000).map(|i| if i % 97 == 0 { i16::MIN } else { 300 + (i % 11) as i16 }).collect();
        assert!(round(&y) > 0);
        let z: Vec<u8> = (0..BLK as u32 + 5).map(|i| if i == 5 { 0 } else { 200 + (i % 5) as u8 }).collect();
        round(&z);
        round(&[i32::MIN; 7]);
    }
    /// The search `plan` replaced: `frame_at` at every width `0 ..= top`, the first least cost winning.
    fn plan_ref<T: Elt>(x: &[T], top: usize) -> (usize, i64, usize) {
        // the old `Coc.frameAt` over the sorted keys
        fn frame(s: &[i64], d: usize) -> (i64, usize) {
            let (nb, mut best, mut j) = (s.len(), (s[0], usize::MAX), 0);
            for i in 0..nb {
                if i > 0 && s[i] == s[i - 1] { continue }
                while j < nb && (d >= 64 || (s[j] as u64).wrapping_sub(s[i] as u64) >> d == 0) { j += 1 }
                if nb - (j - i) < best.1 { best = (s[i], nb - (j - i)) }
            }
            best
        }
        let mut s: Vec<i64> = x.iter().map(|v| v.i()).collect();
        s.sort_unstable();
        let (mut best, mut pick) = (usize::MAX, (0, s[0], 0));
        for d in 0..=top {
            let (f, np) = frame(&s, d);
            let c = (x.len() * d).div_ceil(8) + np * (2 + size_of::<T>());
            if c < best { (best, pick) = (c, (d, f, np)) }
        }
        pick
    }
    // `plan` against `plan_ref` on random, sorted, outlier, constant and few-valued blocks of every element type and
    // of short lengths, where cost ties between widths are common
    fn plans<T: Elt>(seed: u64) -> usize {
        let mut s = seed;
        let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        let mut n = 0;
        for k in 0..=64u32 {
            for nb in (1usize..=64).chain([65, 100, 255, 256, 1000, BLK]) {
                for kind in 0..7 {
                    let m = if k == 64 { u64::MAX } else { (1u64 << k) - 1 };
                    let base = rnd();
                    let mut x: Vec<u64> = (0..nb).map(|i| base.wrapping_add(match kind {
                        0 => rnd() & m,                                        // random over 2 ^ k
                        1 => rnd() & m & 7,                                    // few values: ties
                        2 => 0,                                                // constant
                        // a ramp with far outliers, as a scatter into timestamps: the histogram bounds only wide widths
                        6 => if rnd() % 100 == 0 { rnd() & m } else { ((i as u64) << 4 | rnd() & 15) & m },
                        _ => if rnd() % [0, 0, 0, 3, 40, 300][kind] == 0 { rnd() & m } else { rnd() & 15 }, // outliers
                    })).collect();
                    if kind == 4 { x.sort_unstable() }
                    let x: Vec<T> = x.into_iter().map(T::wrap).collect();
                    let (mn, mx) = x.iter().fold((i64::MAX, i64::MIN), |(a, b), v| (a.min(v.i()), b.max(v.i())));
                    let top = crate::bits::width_for((mx as u64).wrapping_sub(mn as u64)) as usize;
                    assert_eq!(plan(&x, mn, top, size_of::<T>()), plan_ref(&x, top), "k {k} nb {nb} kind {kind} x {:?}", &x.iter().map(|v| v.i()).collect::<Vec<_>>()[..nb.min(20)]);
                    n += 1;
                }
            }
        }
        n
    }
    #[test] fn plan_is_the_full_search() { assert!(plans::<u8>(1) + plans::<i16>(2) + plans::<i32>(3) + plans::<i64>(4) + plans::<i64>(5) > 0) }
    // `for_blk` called `reps` times on `x`, for `perf stat` (`cargo test --release -- --ignored bench_for_blk_<shape>`)
    fn bench(x: &[i64], reps: usize) -> u64 {
        let (mut base, mut maxv, mut width, mut bsum, mut nexc, mut frm, mut t) = (0, 0, 0, 0, 0, 0u64, 0u64);
        for _ in 0..reps {
            let mut m = EncMeta { b: 0, base: &mut base, maxv: &mut maxv, width: &mut width, bsum: &mut bsum, frm: Some(&mut frm),
                                  nexc: &mut nexc, patch: true };
            t += for_blk(&mut m, core::hint::black_box(x), x.len()) as u64 + width as u64;
        }
        t
    }
    #[test] #[ignore] fn bench_for_blk_small() { assert!(bench(&(0..16).map(|i| 100 + i * 3).collect::<Vec<_>>(), 2_000_000) > 0) }
    // a sorted key column: long runs of one histogram bucket
    #[test] #[ignore] fn bench_for_blk_sorted() { assert!(bench(&(0..BLK as i64).map(|i| 1000 + i / 7).collect::<Vec<_>>(), 100_000) > 0) }
    #[test] #[ignore] fn bench_for_blk_random() {
        let mut s = 7u64;
        assert!(bench(&(0..BLK).map(|_| { s ^= s << 13; s ^= s >> 7; s ^= s << 17; (s & 0xfff) as i64 }).collect::<Vec<_>>(), 100_000) > 0)
    }
}

#[cfg(test)]
mod a16_tests {
    use super::*;
    // Expected values come from running the original C loops of coc.rs and coc.rs (/data/tmp/qrs/A16/diff.c
    // compares the block steps over 12,000 columns).
    #[test] fn sumnul() {
        assert_eq!([1, 2, 4, 8].map(coc_sumnul), [i64::MIN, i16::MIN as i64, i32::MIN as i64, i64::MIN]);
    }
}
