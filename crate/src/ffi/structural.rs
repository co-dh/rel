//! structural.c's Lean exports, and the helpers every other export of that file reads a Lean argument through (the C
//! `count_at`, `row_at`, `rows_at`, `alp_view`, `mk_pair`; `take_first` and `sarray_room` are `ffi::`'s, which owns the
//! raw objects). The logic is `crate::structural`; an encoded answer is `ffi::encode_fill` over a `Producer`.
#![deny(unsafe_code)]
use crate::alp::Cocf;
use crate::coc::{Coc, Meta};
use crate::ffi::{Producer, bytes_room, concat_own, encode_alp, encode_fill, sarray_room, take_first};
use crate::lean::{B, O, SArr, box_usize_o, boxed, ctor, export};
use crate::{BLK, c, pod, structural};
use alloc::vec::Vec;

fn die(args: core::fmt::Arguments) -> ! {
    crate::os::eprint(args).expect("qlean: stderr");
    crate::os::exit(1)
}
/// coc.h `mk_pair`: a `Prod`, constructor 0 with two fields.
pub fn pair(a: O, b: O) -> O { ctor(0, [a, b], &[]) }
/// The bytes of each `ByteArray` of an `Array ByteArray`.
pub fn bytes_of<'a>(a: &[B<'a>]) -> Vec<&'a [u8]> { a.iter().map(|b| b.bytes()).collect() }
/// An element count out of an `Array Nat`, whose elements are tagged scalars. A `Nat` above 2^63 would be a bignum
/// pointer; it cannot occur, a count being bounded by the payload it describes, and it stops rather than being read as one.
pub fn count_at(counts: &[B], i: usize) -> usize {
    let o = counts[i];
    if !o.is_scalar() {
        die(format_args!("qlean structural: count {i} is a bignum; a count is bounded by the column it describes and cannot reach 2^63\n"))
    }
    o.unbox()
}
/// coc.h `coc_view`: the metadata sections and the pack over the buffers a Lean caller owns, the count clamped to what the
/// block grid can hold. A tail that does not size a patch list is a bug and stops.
pub fn coc_view<'a>(mv: B<'a>, pv: B<'a>, n: usize) -> Coc<'a> {
    let (m, p) = (mv.bytes(), pv.bytes());
    let Some(meta) = Meta::new(m, n) else { die(format_args!("qlean: {} metadata bytes are not 33 a block and a 16-byte trailer, 8-aligned\n", m.len())) };
    let (e, mb) = (meta.res_end(), meta.mblk);
    Coc::attach(meta, p).unwrap_or_else(|| die(format_args!(
        "qlean: a Frame of Reference pack of {} bytes whose residuals end at {e} holds no patch list of {mb} blocks after them\n", p.len())))
}
/// structural.c `alp_view`: an ALP column's metadata, blob and pack, `n` clamped to what the blocks hold.
pub fn alp_view<'a>(mv: B<'a>, pv: B<'a>, av: B<'a>, n: usize) -> Cocf<'a> {
    let Some(mut f) = Cocf::meta_view(mv.bytes(), av.bytes(), n) else { die(format_args!("qlean: an ALP column's metadata of {} bytes or its blob of {} are short or misaligned\n", mv.bytes().len(), av.bytes().len())) };
    f.c.pack = pv.bytes();
    f
}

/// `reverse` of a column as the writer's producer: structural.c `rev_fill`.
struct Rev<'a, 'b>(&'a Coc<'b>);
impl Producer for Rev<'_, '_> { fn fill(&self, buf: &mut [i64], i0: usize) { structural::rev_fill(self.0, buf, i0) } }
/// `,` of the parts `parts` starting at `start[j]` (`start` holds the part count + 1 entries) of element width `w`: structural.c
/// `cat_fill` and `cat_take`.
struct Cat<'a, 'b> { parts: &'a [Coc<'b>], start: &'a [usize], w: usize }
impl Producer for Cat<'_, '_> {
    fn fill(&self, buf: &mut [i64], i0: usize) {
        structural::cat_fill(&|i| structural::plain(&self.parts[i]), self.start, self.w, false, buf, i0)
    }
    fn take(&self, b: usize) -> Option<(Cocf<'_>, usize)> {
        let (p, j) = structural::cat_take(self.start, b)?;
        structural::cat_part_ok(&self.parts[p], self.w, false).then(|| (structural::plain(&self.parts[p]), j))
    }
}

/// The cycling slice of a column: structural.c `cycle_fill`; `off` is below the count.
struct Cycle<'a, 'b> { c: &'a Coc<'b>, off: usize }
impl Producer for Cycle<'_, '_> { fn fill(&self, buf: &mut [i64], i0: usize) { structural::cycle_fill(self.c, self.off, 0, buf, i0) } }
/// A column shifted by `k`, `fill` entering: structural.c `shift_fill`.
struct Shift<'a, 'b> { c: &'a Coc<'b>, k: i64, fill: i64 }
impl Producer for Shift<'_, '_> { fn fill(&self, buf: &mut [i64], i0: usize) { structural::shift_fill(self.c, self.k, self.fill, buf, i0) } }

/// The hint callbacks all answer the exponent and the patch limit the walk leaves in `lim`.
fn hinted(h: impl FnOnce(&mut u32) -> i32) -> Option<(i32, u32)> { let mut lim = 0; let e = h(&mut lim); Some((e, lim)) }
/// `,` of ALP parts: structural.c `cat_fill_alp`, `cat_take`, `cat_hint`, `cat_ints`.
struct CatAlp<'a, 'b> { parts: &'a [Cocf<'b>], start: &'a [usize], w: usize }
impl Producer for CatAlp<'_, '_> {
    fn fill(&self, buf: &mut [i64], i0: usize) { structural::cat_fill_alp(&|i| self.parts[i], self.start, self.w, buf, i0) }
    fn take(&self, b: usize) -> Option<(Cocf<'_>, usize)> {
        let (p, j) = structural::cat_take(self.start, b)?;
        structural::cat_part_ok(&self.parts[p].c, self.w, true).then(|| (self.parts[p], j))
    }
    fn hint(&self, b: usize) -> Option<(i32, u32)> { hinted(|l| structural::cat_hint(&|i| self.parts[i], self.start, b, l)) }
    fn ints(&self, b: usize, out: Option<&mut structural::Ints>) -> i32 { structural::cat_ints(&|i| self.parts[i], self.start, b, out) }
}
/// `reverse` of an ALP column: structural.c `rev_fill_alp`, `rev_hint`, `rev_ints`.
struct RevAlp<'a, 'b>(&'a Cocf<'b>);
impl Producer for RevAlp<'_, '_> {
    fn fill(&self, buf: &mut [i64], i0: usize) { structural::rev_fill_alp(self.0, buf, i0) }
    fn hint(&self, b: usize) -> Option<(i32, u32)> { hinted(|l| structural::rev_hint(self.0, b, l)) }
    fn ints(&self, b: usize, out: Option<&mut structural::Ints>) -> i32 { structural::rev_ints(self.0, b, out) }
}
/// The cycling slice of an ALP column, `m` elements from `off` (below the count): structural.c `cycle_fill_alp` and its hints.
struct CycleAlp<'a, 'b> { f: &'a Cocf<'b>, off: usize, m: usize }
impl Producer for CycleAlp<'_, '_> {
    fn fill(&self, buf: &mut [i64], i0: usize) { structural::cycle_fill_alp(self.f, self.off, self.m, buf, i0) }
    fn hint(&self, b: usize) -> Option<(i32, u32)> { hinted(|l| structural::cycle_hint(self.f, self.off, self.m, b, l)) }
    fn ints(&self, b: usize, out: Option<&mut structural::Ints>) -> i32 { structural::cycle_ints(self.f, self.off, self.m, b, out) }
}
/// An ALP column shifted by `k`, `fill` entering: structural.c `shift_fill_alp` and its hints.
struct ShiftAlp<'a, 'b> { f: &'a Cocf<'b>, k: i64, fill: i64 }
impl Producer for ShiftAlp<'_, '_> {
    fn fill(&self, buf: &mut [i64], i0: usize) { structural::shift_fill_alp(self.f, self.k, self.fill, buf, i0) }
    fn hint(&self, b: usize) -> Option<(i32, u32)> { hinted(|l| structural::shift_hint(self.f, self.k, b, l)) }
    fn ints(&self, b: usize, out: Option<&mut structural::Ints>) -> i32 { structural::shift_ints_at(self.f, self.k, &self.fill, b, out) }
}

/// structural.c `reverse_foR_move`: the blocks in reverse order, each keeping its base, maximum and width, its residuals
/// reversed inside it.
fn reverse_moved(col: &Coc) -> O {
    let mut mo = SArr::new(1, 33 * col.meta.nblk + 16);
    let mut po = SArr::new(1, structural::reverse_meta(col, mo.bytes_mut()));
    structural::reverse_enc(c::pool(), col, po.bytes_mut());
    pair(mo.into(), po.into())
}
/// structural.c `concat_foR_move`: the parts' four metadata sections in turn and their packs end to end, `n` elements.
fn concat_moved(ms: &[&[u8]], ps: &[&[u8]], n: usize, w: usize) -> O {
    let mut mo = SArr::new(1, 33 * ms.iter().map(|m| m.len() / 33).sum::<usize>() + 16);
    let mut po = SArr::new(1, ps.iter().map(|p| p.len()).sum());
    structural::concat_move(ms, ps, n, w, mo.bytes_mut(), po.bytes_mut());
    pair(mo.into(), po.into())
}
/// structural.c `concat_foR`: the answer, or `Err` of the append `qlean_structural_concat_foR` makes in the first part's own
/// objects, with their sizes. Nothing here changes an argument, so every view lives only inside it.
fn concat(w: usize, nsv: B, metasv: &O, packsv: &O) -> Result<O, (structural::Grow, usize, usize)> {
    let (ms, ps, nb) = (metasv.borrow().array(), packsv.borrow().array(), nsv.bytes());
    // `zip` in the specification truncates to the shortest array, so the loop takes the same minimum
    let k = ms.len().min(ps.len()).min(nb.len() / 8);
    let ns: &[u64] = pod::cast(&nb[..k * 8]).expect("qlean concatFoR: the counts are not 8-aligned");
    let parts: Vec<Coc> = (0..k).map(|i| coc_view(ms[i], ps[i], ns[i] as usize)).collect();
    let (mut start, mut at) = (Vec::with_capacity(k + 1), 0);
    for p in &parts { start.push(at); at += p.meta.n }
    start.push(at);
    let (mb, pb) = (bytes_of(&ms[..k]), bytes_of(&ps[..k]));
    if structural::cat_aligned(k, ns, w, |i| parts[i]) { return Ok(concat_moved(&mb, &pb, start[k], w)) }
    if let Some(g) = structural::append_plan(&parts, &start, w) { return Err((g, mb[0].len(), pb[0].len())) }
    Ok(encode_fill(start[k], w, &Cat { parts: &parts, start: &start, w }))
}

export! {
    /// Spec: the aligned half of `reverseFoR metadata pack n` is the metadata with the blocks in reverse order, each keeping
    /// its base, maximum and width, and the pack with the blocks in reverse order and each block's residuals reversed inside
    /// it; a column that is not aligned is re-encoded through the writer. `w` is the element's own width in bytes, which
    /// decides the null a block's sums skip and the size of a patched element.
    fn qlean_structural_reverse_foR(w: usize, mv: B, pv: B, n: usize) -> O {
        let col = coc_view(mv, pv, n);
        // a patch list's positions are the block's own, so a patched column is re-encoded, not moved, and so is one with a
        // block past its count, which would come first
        if n % BLK == 0 && col.std(n) && col.pack.len() == col.meta.res_end() && structural::trailer_ok(&col, col.meta.n, w, false) {
            return reverse_moved(&col);
        }
        encode_fill(col.meta.n, w, &Rev(&col))
    }

    /// Spec: `concatFoR ns metas packs`: the four metadata sections of each part in turn, `off` recomputed from the
    /// concatenated widths, and the packs concatenated where every part but the last fills its blocks; the first part's own
    /// last block grown in place where that is all the others add to; else re-encoded. `metas` and `packs` are owned so that
    /// the first part, when nothing else holds it, is grown in place.
    fn qlean_structural_concat_foR(w: usize, nsv: B, metasv: O, packsv: O) -> O {
        match concat(w, nsv, &metasv, &packsv) {
            Ok(r) => r,
            Err((g, msz, packbytes)) => {
                let ((_ma, m0), (_pa, p0)) = (take_first(metasv), take_first(packsv));
                let (mut mo, mut po) = (sarray_room(m0, msz), sarray_room(p0, packbytes));
                g.put(mo.exclusive().expect("qlean concatFoR: an answer room holds one reference"), po.exclusive().expect("qlean concatFoR: an answer room holds one reference"));
                pair(mo, po)
            }
        }
    }
}

export! {
    /// Spec: `tilLongs n` is `0 .. n - 1` as little-endian `Int64`s. `til 0` is the empty long vector and `til 5` is
    /// `0 1 2 3 4`, measured; a negative count and `0N` are `'domain` and `tilColumn` declines them, so nothing here
    /// has to represent one.
    fn qlean_structural_til(n: usize) -> O {
        let mut a = SArr::new(1, n * 8);
        structural::til(c::pool(), pod::cast_mut(a.bytes_mut()).expect("til: a ByteArray's data is 8-aligned"));
        a.into()
    }
}

export! {
    /// Spec: `concatALP w ns metas packs alps`. `concatFoR`'s rule at ALP: an answer block that is one part's own block on the
    /// grid moves -- metadata, residuals, exponent and exceptions -- and only the blocks straddling a part boundary are
    /// restored and handed to ALP's block steps. So appending `m` elements to `n` re-encodes the last partial block and the
    /// `m`, and copies the rest, where decoding every part and encoding the join was the whole column.
    fn qlean_structural_concat_alp(w: usize, nsv: B, metasv: B, packsv: B, alpsv: B) -> O {
        let (ms, ps, als, nb) = (metasv.array(), packsv.array(), alpsv.array(), nsv.bytes());
        let k = ms.len().min(ps.len()).min(als.len()).min(nb.len() / 8);
        if w != 4 && w != 8 { die(format_args!("qlean concatALP: element width {w} is not a float's\n")) }
        let ns: &[u64] = pod::cast(&nb[..k * 8]).expect("qlean concatALP: the counts are not 8-aligned");
        let parts: Vec<Cocf> = (0..k).map(|i| {
            let f = alp_view(ms[i], ps[i], als[i], ns[i] as usize);
            if f.f32 != (w == 4) { die(format_args!("qlean concatALP: part {i} holds {}-byte floats, the answer {w}\n", if f.f32 { 4 } else { 8 })) }
            f
        }).collect();
        let (mut start, mut at) = (Vec::with_capacity(k + 1), 0);
        for p in &parts { start.push(at); at += p.c.meta.n }
        start.push(at);
        encode_alp(at, w, &CatAlp { parts: &parts, start: &start, w })
    }

    /// Spec: `cycleFoR metadata pack n off m` is the round trip `Coc.encode 8 (cycleBytes (· * 8) n off m (Coc.decode 8
    /// metadata pack n))` -- `m` elements from `off`, cycling, with neither the source nor the answer ever dense. `off < n`
    /// and `0 < n`: `sliceColumn` reduces the one and substitutes a one-element null source for an empty column.
    fn qlean_structural_cycle_foR(w: usize, mv: B, pv: B, n: usize, off: usize, m: usize) -> O {
        let col = coc_view(mv, pv, n);
        let nn = col.meta.n;
        encode_fill(if nn != 0 { m } else { 0 }, w, &Cycle { c: &col, off: if nn != 0 { off % nn } else { 0 } })
    }

    /// Spec: `shiftFoR metadata pack n k fill` is the round trip `Coc.encode 8 (shiftBytes 8 fill k (Coc.decode 8 metadata
    /// pack n))` -- the answer's element `j` is the source's `j - k`, and `fill` where that is off either end. No
    /// aligned-move case: a shift lines the 1024-element grid up only when `k` is a multiple of 1024.
    fn qlean_structural_shift_foR(w: usize, mv: B, pv: B, n: usize, k: u64, fill: u64) -> O {
        let col = coc_view(mv, pv, n);
        encode_fill(col.meta.n, w, &Shift { c: &col, k: k as i64, fill: fill as i64 })
    }

    /// Spec: `reverseALP`, `cycleALP` and `shiftALP`, the round trips through ALP's decode and encoder. The FoR moves at ALP:
    /// each answer block is restored from the at most two source blocks it is drawn from and handed to ALP's block steps,
    /// with those blocks' largest exponent as the hint, so a reversed block keeps its exponent and skips the search.
    fn qlean_structural_reverse_alp(mv: B, pv: B, av: B, n: usize) -> O {
        let f = alp_view(mv, pv, av, n);
        encode_alp(f.c.meta.n, if f.f32 { 4 } else { 8 }, &RevAlp(&f))
    }

    fn qlean_structural_cycle_alp(mv: B, pv: B, av: B, n: usize, off: usize, m: usize) -> O {
        let f = alp_view(mv, pv, av, n);
        let nn = f.c.meta.n;
        let m = if nn != 0 { m } else { 0 };
        encode_alp(m, if f.f32 { 4 } else { 8 }, &CycleAlp { f: &f, off: if nn != 0 { off % nn } else { 0 }, m })
    }

    fn qlean_structural_shift_alp(mv: B, pv: B, av: B, n: usize, k: u64, fill: u64) -> O {
        let f = alp_view(mv, pv, av, n);
        encode_alp(f.c.meta.n, if f.f32 { 4 } else { 8 }, &ShiftAlp { f: &f, k: k as i64, fill: fill as i64 })
    }
}

/// A fresh payload of `n` bytes, zeroed: structural.c `zeroed_bits` and `ids_alloc`, whose unwritten tail bits must be 0
/// for two equal columns to hold the same bytes.
fn zeroed(n: usize) -> SArr {
    let mut a = SArr::new(1, n);
    a.bytes_mut().fill(0);
    a
}
/// The fields `ids` holds at `w` bits, `n` clamped to them: structural.c `ids_avail`, where width 0 holds any count.
fn ids_n(n: usize, ids: &[u8], w: usize) -> usize { n.min(if w != 0 { ids.len() * 8 / w } else { usize::MAX }) }
/// A fresh `ByteArray` of the `n` elements of `w` bytes `f` writes, as structural.c's `lean_alloc_sarray(1, n * w, n * w)`.
fn fresh(n: usize, f: impl FnOnce(&mut [u8])) -> O {
    let mut a = SArr::new(1, n);
    f(a.bytes_mut());
    a.into()
}

export! {
    /// Spec: `reverseIds n w ids` is element `n - 1 - j` at each `j`, the fields being `w` bits.
    fn qlean_structural_reverse_ids(n: usize, w: usize, idsv: B) -> O {
        let (ids, n) = (idsv.bytes(), ids_n(n, idsv.bytes(), w));
        let mut a = zeroed(crate::ids::ids_bytes(n, w as u32));
        structural::reverse_ids(n, w as u32, ids, a.bytes_mut());
        a.into()
    }

    /// Spec: `cycleIds n off m w ids` is `m` fields from `off`, cycling. Not `cycleBytes`' extract and concatenate: at a
    /// sub-byte width a slice can start inside a byte, so the fields move one at a time.
    fn qlean_structural_cycle_ids(n: usize, off: usize, m: usize, w: usize, idsv: B) -> O {
        let mut a = zeroed(crate::ids::ids_bytes(m, w as u32));
        structural::cycle_ids(ids_n(n, idsv.bytes(), w), off, m, w as u32, idsv.bytes(), a.bytes_mut());
        a.into()
    }

    /// Spec: `reverse w b` is its `n = size / w` elements in reverse order. `n * w` and not the payload size: a payload that is
    /// not a whole number of elements would otherwise leave its trailing bytes uninitialised.
    fn qlean_structural_reverse(w: usize, bv: B) -> O {
        let n = bv.bytes().len() / w;
        fresh(n * w, |o| structural::reverse(c::pool(), w, &bv.bytes()[..n * w], n, o))
    }

    /// Spec: `reverseSegs w b offs`, each slice of `b` between consecutive byte offsets reversed at element width `w` and
    /// every byte outside them kept; `none` where an offset is boxed, not a multiple of `w`, past `b` or below the one before it.
    fn qlean_structural_reverse_segs(w: usize, bv: B, offs: B) -> O {
        let (src, offs) = (bv.bytes(), offs.array());
        let Some(offs) = offs.iter().map(|o| o.is_scalar().then(|| o.unbox())).collect::<Option<Vec<usize>>>() else { return boxed(0) };
        if !structural::segs_ok(w, src.len(), &offs) { return boxed(0) }
        ctor(1, [fresh(src.len(), |o| { o.copy_from_slice(src); structural::reverse_segs(w, &offs, o) })], &[])
    }

    /// Spec: `reverseBits n b` is bit `j` set exactly when `Column.bitAt b (n - 1 - j)`.
    fn qlean_structural_reverse_bits(n: usize, bv: B) -> O {
        let mut a = zeroed(n.div_ceil(8));
        structural::reverse_bits(n, bv.bytes(), a.bytes_mut());
        a.into()
    }

    /// Spec: `shiftBytes w fill k b` is element `j - k` of `b` at each `j`, and `fill` where `j - k` is outside `[0, n)`. `k`
    /// is signed on the way in because `xprev` takes it from q and both signs are ordinary there.
    fn qlean_structural_shift(w: usize, fill: u64, k: u64, bv: B) -> O {
        let n = bv.bytes().len() / w;
        fresh(n * w, |o| structural::shift(c::pool(), w, fill, k as i64, &bv.bytes()[..n * w], n, o))
    }

    /// Spec: `shiftBits n fill k b` is bit `j` set to `Column.bitAt b (j - k)` when `j - k` is inside `[0, n)` and to `fill`'s low
    /// bit otherwise. The fill is not `boolean`'s null: `&`'s prior seeds with `1b` and q's `(&':)1011b` is `1001b`.
    fn qlean_structural_shift_bits(n: usize, fill: u64, k: u64, bv: B) -> O {
        let mut a = zeroed(n.div_ceil(8));
        structural::shift_bits(n, fill, k as i64, bv.bytes(), a.bytes_mut());
        a.into()
    }

    /// Spec: `trimBlanks left right b` is the first byte that is not the blank and one past the last, with `max lo hi` on the
    /// right so an all-blank payload answers an empty slice rather than a negative one.
    fn qlean_structural_trim_bounds(left: u8, right: u8, bv: B) -> O {
        let (lo, hi) = structural::trim_bounds(left != 0, right != 0, bv.bytes());
        pair(box_usize_o(lo), box_usize_o(hi))
    }

    /// Spec: `translateBytes tab b` is `tab[b[i]]` at each `i`, where `tab` is 256 bytes.
    fn qlean_structural_translate(tabv: B, bv: B) -> O {
        fresh(bv.bytes().len(), |o| structural::translate(c::pool(), tabv.bytes(), bv.bytes(), o))
    }

    /// Spec: `cycleBits n off m b` is bit `j` of `m` set exactly when `Column.bitAt b ((off + j) % n)`. `sliceColumn` reduces
    /// `off` into `[0, n)` and substitutes a one-element null source for an empty one, so `n` of zero arrives only with `m` of zero.
    fn qlean_structural_cycle_bits(n: usize, off: usize, m: usize, bv: B) -> O {
        let mut a = zeroed(m.div_ceil(8));
        structural::cycle_bits(n, off, m, bv.bytes(), a.bytes_mut());
        a.into()
    }

    /// Spec: `concatBytes parts` is `parts.foldl (init := ByteArray.empty) (· ++ ·)`, in one pass to size the answer and one to
    /// fill it, where the fold copies the prefix once per part. `parts` is owned: the first part, when nothing else holds it,
    /// is grown in place; else every part, the first included, is copied by one split pass.
    fn qlean_structural_concat(parts: O) -> O {
        let (parts, cap0) = concat_own(parts);
        let (total, len0, k) = { let ps = parts.borrow().array(); (ps.iter().map(|p| p.bytes().len()).sum::<usize>(), ps.first().map_or(0, |p| p.bytes().len()), ps.len()) };
        if k == 0 { return bytes_room(0, 0) }
        let from = cap0.is_some_and(|c| c >= total);
        let (parts, first) = if from { let (a, f) = take_first(parts); (a, Some(f)) } else { (parts, None) };
        let mut res = match first { Some(f) => sarray_room(f, total), None => bytes_room(total, if cap0.is_some() { 2 * total } else { total }) };
        let rest: Vec<&[u8]> = parts.borrow().array()[from as usize..].iter().map(|p| p.bytes()).collect();
        let out = res.exclusive().expect("qlean concat: an answer holds one reference");
        let pre = if from { len0 } else { 0 };
        structural::concat(c::pool(), &rest, &mut out[pre..]);
        res
    }

    /// Spec: `concatBits counts parts` is every part's `counts[i]` bits in turn, packed LSB first from bit 0 of the answer, so a
    /// part starts where the one before it ended and not on a byte boundary. It reads `min (counts.size / 8) parts.size` parts.
    fn qlean_structural_concat_bits(countsv: B, parts: B) -> O {
        let (cb, ps) = (countsv.bytes(), parts.array());
        let k = (cb.len() / 8).min(ps.len());
        let cs: &[usize] = pod::cast(&cb[..k * 8]).expect("qlean concatBits: the counts are not 8-aligned");
        let mut a = zeroed(cs.iter().sum::<usize>().div_ceil(8));
        structural::concat_bits(cs, &bytes_of(&ps[..k]), a.bytes_mut());
        a.into()
    }
}
