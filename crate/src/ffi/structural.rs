//! structural.rs's Lean exports, and the helpers every other export of that file reads a Lean argument through (the C
//! `count_at`, `row_at`, `rows_at`, `alp_view`, `mk_pair`; `take_first` and `sarray_room` are `ffi::`'s, which owns the
//! raw objects). The logic is `crate::structural`; an encoded answer is `ffi::encode_fill` over a `Producer`.
#![deny(unsafe_code)]
use crate::alp::Cocf;
use crate::coc::Coc;
use crate::exports::coc::{alp_view, view};
use crate::exports::reduce::elems;
use crate::ffi::{Producer, SdPart, amend, array_boxed, concat_own, encode_alp, encode_fill, encode_scatter, sarray_room, sd_concat, sd_part, syms_of, take_first, take_ids0};
use crate::ids::ids_bytes;
use crate::lean::{B, O, SArr, box_, box_usize_o, boxed, ctor, export};
use crate::{c, pod, structural};
use crate::structural::{STR_BLK, rows_at};
use alloc::vec::Vec;

fn die(args: core::fmt::Arguments) -> ! {
    crate::os::eprint(args).expect("qlean: stderr");
    crate::os::exit(1)
}
/// coc.rs `mk_pair`: a `Prod`, constructor 0 with two fields.
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

/// `reverse` of a column as the writer's producer: structural.rs `rev_fill`.
struct Rev<'a, 'b>(&'a Coc<'b>);
impl Producer for Rev<'_, '_> { fn fill(&self, buf: &mut [i64], i0: usize) { structural::rev_fill(self.0, buf, i0) } }
/// `,` of the parts `parts` starting at `start[j]` (`start` holds the part count + 1 entries) of element width `w`: structural.rs
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

/// The cycling slice of a column: structural.rs `cycle_fill`; `off` is below the count.
struct Cycle<'a, 'b> { c: &'a Coc<'b>, off: usize }
impl Producer for Cycle<'_, '_> { fn fill(&self, buf: &mut [i64], i0: usize) { structural::cycle_fill(self.c, self.off, 0, buf, i0) } }
/// A column shifted by `k`, `fill` entering: structural.rs `shift_fill`.
struct Shift<'a, 'b> { c: &'a Coc<'b>, k: i64, fill: i64 }
impl Producer for Shift<'_, '_> { fn fill(&self, buf: &mut [i64], i0: usize) { structural::shift_fill(self.c, self.k, self.fill, buf, i0) } }

/// The hint callbacks all answer the exponent and the patch limit the walk leaves in `lim`.
fn hinted(h: impl FnOnce(&mut u32) -> i32) -> Option<(i32, u32)> { let mut lim = 0; let e = h(&mut lim); Some((e, lim)) }
/// `,` of ALP parts: structural.rs `cat_fill_alp`, `cat_take`, `cat_hint`, `cat_ints`.
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
/// `reverse` of an ALP column: structural.rs `rev_fill_alp`, `rev_hint`, `rev_ints`.
struct RevAlp<'a, 'b>(&'a Cocf<'b>);
impl Producer for RevAlp<'_, '_> {
    fn fill(&self, buf: &mut [i64], i0: usize) { structural::rev_fill_alp(self.0, buf, i0) }
    fn hint(&self, b: usize) -> Option<(i32, u32)> { hinted(|l| structural::rev_hint(self.0, b, l)) }
    fn ints(&self, b: usize, out: Option<&mut structural::Ints>) -> i32 { structural::rev_ints(self.0, b, out) }
}
/// The cycling slice of an ALP column, `m` elements from `off` (below the count): structural.rs `cycle_fill_alp` and its hints.
struct CycleAlp<'a, 'b> { f: &'a Cocf<'b>, off: usize, m: usize }
impl Producer for CycleAlp<'_, '_> {
    fn fill(&self, buf: &mut [i64], i0: usize) { structural::cycle_fill_alp(self.f, self.off, self.m, buf, i0) }
    fn hint(&self, b: usize) -> Option<(i32, u32)> { hinted(|l| structural::cycle_hint(self.f, self.off, self.m, b, l)) }
    fn ints(&self, b: usize, out: Option<&mut structural::Ints>) -> i32 { structural::cycle_ints(self.f, self.off, self.m, b, out) }
}
/// An ALP column shifted by `k`, `fill` entering: structural.rs `shift_fill_alp` and its hints.
struct ShiftAlp<'a, 'b> { f: &'a Cocf<'b>, k: i64, fill: i64 }
impl Producer for ShiftAlp<'_, '_> {
    fn fill(&self, buf: &mut [i64], i0: usize) { structural::shift_fill_alp(self.f, self.k, self.fill, buf, i0) }
    fn hint(&self, b: usize) -> Option<(i32, u32)> { hinted(|l| structural::shift_hint(self.f, self.k, b, l)) }
    fn ints(&self, b: usize, out: Option<&mut structural::Ints>) -> i32 { structural::shift_ints_at(self.f, self.k, &self.fill, b, out) }
}

/// structural.rs `reverse_foR_move`: the blocks in reverse order, each keeping its base, maximum and width, its residuals
/// reversed inside it.
fn reverse_moved(col: &Coc) -> O {
    let mut mo = SArr::new(1, 33 * col.meta.nblk + 24);
    let mut po = SArr::new(1, structural::reverse_meta(col, mo.bytes_mut()));
    structural::reverse_enc(c::pool(), col, po.bytes_mut());
    pair(mo.into(), po.into())
}
/// structural.rs `concat_foR_move`: the parts' four metadata sections in turn and their packs end to end, `n` elements.
fn concat_moved(ms: &[&[u8]], ps: &[&[u8]], n: usize, w: usize) -> O {
    let mut mo = SArr::new(1, 33 * ms.iter().map(|m| m.len() / 33).sum::<usize>() + 24);
    let mut po = SArr::new(1, ps.iter().map(|p| p.len()).sum());
    structural::concat_move(crate::coc::Meta::new(ms[0], 0).map_or(crate::DEFAULT_LG, |m| m.lg), ms, ps, n, w, mo.bytes_mut(), po.bytes_mut());
    pair(mo.into(), po.into())
}
/// structural.rs `concat_foR`: the answer, or `Err` of the append `qlean_structural_concat_foR` makes in the first part's own
/// objects, with their sizes. Nothing here changes an argument, so every view lives only inside it.
fn concat(w: usize, nsv: B, metasv: &O, packsv: &O) -> Result<O, (structural::Grow, usize, usize)> {
    let (ms, ps, nb) = (metasv.borrow().array(), packsv.borrow().array(), nsv.bytes());
    // `zip` in the specification truncates to the shortest array, so the loop takes the same minimum
    let k = ms.len().min(ps.len()).min(nb.len() / 8);
    let ns: &[u64] = pod::cast(&nb[..k * 8]).expect("qlean concatFoR: the counts are not 8-aligned");
    let parts: Vec<Coc> = (0..k).map(|i| view("qlean structural", ms[i], ps[i], ns[i] as usize)).collect();
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
        let col = view("qlean structural", mv, pv, n);
        // a patch list's positions are the block's own, so a patched column is re-encoded, not moved, and so is one with a
        // block past its count, which would come first
        if n % col.meta.blk() == 0 && col.std(n) && col.pack.len() == col.meta.res_end() && structural::trailer_ok(&col, col.meta.n, w, false) {
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
        let col = view("qlean structural", mv, pv, n);
        let nn = col.meta.n;
        encode_fill(if nn != 0 { m } else { 0 }, w, &Cycle { c: &col, off: if nn != 0 { off % nn } else { 0 } })
    }

    /// Spec: `shiftFoR metadata pack n k fill` is the round trip `Coc.encode 8 (shiftBytes 8 fill k (Coc.decode 8 metadata
    /// pack n))` -- the answer's element `j` is the source's `j - k`, and `fill` where that is off either end. No
    /// aligned-move case: a shift lines the 1024-element grid up only when `k` is a multiple of 1024.
    fn qlean_structural_shift_foR(w: usize, mv: B, pv: B, n: usize, k: u64, fill: u64) -> O {
        let col = view("qlean structural", mv, pv, n);
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

/// A fresh payload of `n` bytes, zeroed: structural.rs `zeroed_bits` and `ids_alloc`, whose unwritten tail bits must be 0
/// for two equal columns to hold the same bytes.
fn zeroed(n: usize) -> SArr {
    let mut a = SArr::new(1, n);
    a.bytes_mut().fill(0);
    a
}
/// The fields `ids` holds at `w` bits, `n` clamped to them: structural.rs `ids_avail`, where width 0 holds any count.
fn ids_n(n: usize, ids: &[u8], w: usize) -> usize { n.min(if w != 0 { ids.len() * 8 / w } else { usize::MAX }) }
/// A fresh `ByteArray` of the `n` elements of `w` bytes `f` writes, as structural.rs's `lean_alloc_sarray(1, n * w, n * w)`.
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
        if k == 0 { return SArr::with_capacity(1, 0, 0).into() }
        let from = cap0.is_some_and(|c| c >= total);
        let (parts, first) = if from { let (a, f) = take_first(parts); (a, Some(f)) } else { (parts, None) };
        let mut res = match first { Some(f) => sarray_room(f, total), None => SArr::with_capacity(1, total, if cap0.is_some() { 2 * total } else { total }).into() };
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

export! {
    /// Spec: `enumIds n d nullId w b` is `b`'s 8-byte domain indices packed at `w`, `0Nj` sent to `nullId`, and the first
    /// element that is neither an index below `d` nor `0Nj` (`n` when every one of them is). The domain is the dictionary and
    /// these are the ids, so no element is resolved to a symbol.
    fn qlean_structural_enum_ids(n: usize, d: usize, nullid: usize, w: usize, bv: B) -> O {
        let mut ids = SArr::new(1, crate::ids::ids_bytes(n, w as u32));
        let bad = structural::enum_ids(n, d, nullid, w as u32, bv.bytes(), ids.bytes_mut());
        pair(ids.into(), box_usize_o(bad))
    }

    /// Spec: `enumIdsFoR n d nullId w meta pack = enumIds n d nullId w (decode 8 meta pack n)`, packed a block at a time from
    /// the encoded column, which is never decoded whole.
    fn qlean_structural_enum_ids_for(n: usize, d: usize, nullid: usize, w: usize, mv: B, pv: B) -> O {
        let col = view("qlean structural", mv, pv, n);
        let mut ids = SArr::new(1, crate::ids::ids_bytes(n, w as u32));
        let bad = structural::enum_ids_enc(n, d, nullid, w as u32, &col, ids.bytes_mut());
        pair(ids.into(), box_usize_o(bad))
    }
}

/// The `Int64`s of an answer payload, written in place.
fn longs_mut(a: &mut SArr) -> &mut [i64] { pod::cast_mut(a.bytes_mut()).expect("qlean structural: a ByteArray's data is 8-aligned") }
/// The symbols a dictionary's starts describe: `n + 1` starts are `n` symbols and an empty table is none (sym.rs `sym_count`).
fn sym_count(offs: B) -> usize { offs.array().len().saturating_sub(1) }

export! {
    /// Spec: `allBelow n idx` -- every index, unsigned, below `n`.
    fn qlean_structural_all_below(n: usize, idxv: B) -> u8 { structural::all_below(n, elems::<i64>(idxv)) as u8 }

    /// Spec: `gatherBytes w fill src idx` is element `idx[j]` of `src` for each of the `idx.size / 8` little-endian `Int64`s in
    /// `idx`, and `fill` wherever `gatherAt (src.size / w) idx j` is `none`. One unsigned compare rejects all three of q's
    /// misses at once: `(til 10)@9 10 -1 0N` is `9 0N 0N 0N`, `0N` being `Int64.minValue`, whose unsigned value is 2^63.
    fn qlean_structural_gather(w: usize, fill: u64, srcv: B, idxv: B) -> O {
        let idx = elems::<i64>(idxv);
        fresh(idx.len() * w, |o| structural::gather(c::pool(), w, fill, srcv.bytes(), idx, o))
    }

    /// Spec: `gatherFoR w fill smeta spack n idx` is `gatherBytes w fill (Coc.decode w smeta spack n) idx` -- the same answer
    /// with the source left encoded, a gather reading only the blocks its index names.
    fn qlean_structural_gather_foR(w: usize, fill: u64, smv: B, spv: B, n: usize, idxv: B) -> O {
        let src = view("qlean structural", smv, spv, n);
        let idx = elems::<i64>(idxv);
        fresh(idx.len() * w, |o| structural::gather_enc(c::pool(), w, fill, &src, idx, o))
    }

    /// Spec: `gatherFoRIdx w fill smeta spack n imeta ipack m` is `gatherFoR w fill smeta spack n (Coc.decode 8 imeta ipack m)`
    /// -- the same answer with the index left encoded as well.
    fn qlean_structural_gather_foR_idx(w: usize, fill: u64, smv: B, spv: B, n: usize, imv: B, ipv: B, count: usize) -> O {
        let (src, ix) = (view("qlean structural", smv, spv, n), view("qlean structural", imv, ipv, count));
        fresh(ix.meta.n * w, |o| structural::gather_enc_idx(c::pool(), w, fill, &src, &ix, o))
    }

    /// Spec: `gatherBits n bits idx` is bit `j` set exactly when `gatherAt n idx j` is `some i` and `Column.bitAt bits i` --
    /// `101b@0 5` is `10b`, measured, so a miss is `0b` and not a dropped element.
    fn qlean_structural_gather_bits(n: usize, bitsv: B, idxv: B) -> O {
        let idx = elems::<i64>(idxv);
        let mut a = zeroed(idx.len().div_ceil(8));
        structural::gather_bits(c::pool(), n, bitsv.bytes(), idx, a.bytes_mut());
        a.into()
    }

    /// Spec: `splitBytes d b` is `(blob, offs)` for the pieces `b` falls into around the non-overlapping occurrences of `d`,
    /// left to right -- the separator dropped, no NUL added, and `k` occurrences giving `k + 1` pieces. An empty `d` occurs
    /// nowhere and answers the whole payload as one piece.
    fn qlean_structural_split(dv: B, bv: B) -> O {
        let (d, b) = (dv.bytes(), bv.bytes());
        let cuts = structural::split_cuts(d, b);
        let mut nb = SArr::new(1, b.len() - cuts * d.len());
        let no = array_boxed(cuts + 2, |offs| structural::split(d, b, nb.bytes_mut(), offs));
        pair(nb.into(), no)
    }

    /// Spec: `longBytes rows` is those row numbers as little-endian `Int64`s: the one place a row list becomes a payload.
    fn qlean_structural_longs_of(rowsv: B) -> O {
        let rows = rowsv.array();
        let mut a = SArr::new(1, rows.len() * 8);
        for (i, o) in longs_mut(&mut a).iter_mut().enumerate() { *o = count_at(rows, i) as i64 }
        a.into()
    }

    /// Spec: `spreadBytes ws` is index `i` repeated `ws[i]` times, as little-endian `Int64`s.
    fn qlean_structural_spread(wv: B) -> O {
        let ws = elems::<u64>(wv);
        let mut a = SArr::new(1, ws.iter().fold(0usize, |t, &c| t.wrapping_add(c as usize)) * 8);
        structural::spread(ws, longs_mut(&mut a));
        a.into()
    }

    /// Spec: `expandBytes w fill src ws` is `gatherBytes w fill src (spreadBytes ws)` -- element `i` of `src` repeated `ws[i]`
    /// times (a negative count is a run of none), and `fill` for a run past the end of `src`; the index is never built.
    fn qlean_structural_expand(w: usize, fill: u64, srcv: B, wv: B) -> O {
        let ws = elems::<i64>(wv);
        fresh(ws.iter().map(|&x| x.max(0) as usize).sum::<usize>() * w, |o| structural::expand(c::pool(), w, fill, srcv.bytes(), ws, o))
    }

    /// Spec: `gaussJordan a aug` is the augmented half of `[a | aug]` once `a` has been reduced to the identity, `n` rows of
    /// `w` doubles laid out row by row, or that many q float nulls where `a` is singular; `aug` empty is the identity of order
    /// `n`. Swapping only on an exact-zero pivot is the Lean body's rule, and what finds `inv(1 2 3f;4 5 6f;7 8 9f)` singular.
    fn qlean_structural_gauss_jordan(av: B, augv: B) -> O {
        let (a, aug) = (bytes_of(av.array()), bytes_of(augv.array()));
        let w = structural::gauss_width(&a, &aug);
        let mut o = SArr::new(1, a.len() * w * 8);
        structural::gauss_jordan(&a, &aug, w, pod::cast_mut(o.bytes_mut()).expect("qlean gaussJordan: a ByteArray's data is 8-aligned"));
        o.into()
    }

    /// Spec: `complementBytes n idx` is the row numbers below `n` that `idx` does not name, in order. Nothing needs `idx`
    /// sorted, and a row named twice is dropped once.
    fn qlean_structural_complement(n: usize, bv: B) -> O {
        let (seen, gone) = structural::complement_seen(n, elems::<i64>(bv));
        let mut a = SArr::new(1, (n - gone) * 8);
        structural::complement_fill(&seen, longs_mut(&mut a));
        a.into()
    }

    /// Spec: `longRows b` is the inverse of `longBytes`, those little-endian `Int64`s as row numbers. One that does not fit a
    /// boxed scalar stops rather than being truncated into a valid-looking row.
    fn qlean_structural_rows_of(bv: B) -> O {
        let b = bv.bytes();
        array_boxed(b.len() / 8, |o| { structural::rows_of(b, o); })
    }

    /// Spec: `gatherSyms blob offs ix` is the blob and offset table of the symbols `ix` names, with a miss answering the empty
    /// symbol -- `` `a`b@0 5 ``, `` `a`b@0 -1 `` and `` `a`b@0 0N `` are all `` `a` ``.
    fn qlean_structural_gather_syms(blobv: B, offsv: B, idxv: B) -> O {
        let (s, idx) = (syms_of(blobv, offsv), elems::<i64>(idxv));
        let mut nb = SArr::new(1, structural::gather_syms_len(&s, idx));
        let no = array_boxed(idx.len() + 1, |o| structural::gather_syms(&s, idx, nb.bytes_mut(), o));
        pair(nb.into(), no)
    }

    /// Spec: `gatherPacked n w wout fill src idx` is `gatherBytes` over an interned column's ids: the same one unsigned compare
    /// that folds past-the-end, negative and `0N` into one miss, on a payload of `w`-bit fields. The answer is at `wout`
    /// because a miss is the empty symbol, which `gatherIds` appends when the dictionary has none and can widen the ids.
    fn qlean_structural_gather_ids(n: usize, w: usize, wout: usize, fill: u64, srcv: B, idxv: B) -> O {
        let (src, idx) = (srcv.bytes(), elems::<i64>(idxv));
        let n = ids_n(n, src, w);
        let mut a = zeroed(crate::ids::ids_bytes(idx.len(), wout as u32));
        structural::gather_ids(c::pool(), w as u32, wout as u32, fill, &src[..crate::ids::ids_bytes(n, w as u32)], n, idx, a.bytes_mut());
        a.into()
    }

    /// Spec: `gatherPackedFoR n w wout fill src imeta ipack m` is `gatherPacked n w wout fill src (Coc.decode 8 imeta ipack m)`,
    /// the index left encoded.
    fn qlean_structural_gather_ids_foR(n: usize, w: usize, wout: usize, fill: u64, srcv: B, imv: B, ipv: B, count: usize) -> O {
        let src = srcv.bytes();
        let n = ids_n(n, src, w);
        let ix = view("qlean structural", imv, ipv, count);
        let mut a = zeroed(crate::ids::ids_bytes(ix.meta.n, wout as u32));
        structural::gather_ids_enc(c::pool(), w as u32, wout as u32, fill, &src[..crate::ids::ids_bytes(n, w as u32)], n, &ix, a.bytes_mut());
        a.into()
    }

    /// Spec: `concatIds wout counts widths maps parts` is every part's ids read through its own map and laid down end to end,
    /// packed at `wout`. It reads `min counts.size parts.size` parts; `widths` and `maps` are reached with `!`, so a part
    /// they do not reach is width `0` and the empty map, both of which answer id `0`.
    fn qlean_structural_concat_ids(wout: usize, countsv: B, widthsv: B, mapsv: B, partsv: B) -> O {
        let (counts, parts) = (elems::<usize>(countsv), partsv.array());
        let k = counts.len().min(parts.len());
        let widths: Vec<u32> = (0..widthsv.array().len().min(k)).map(|i| count_at(widthsv.array(), i) as u32).collect();
        // a whole-byte width is written end to end by the parts, so only a sub-byte one needs the zeroed tail bits
        let n = crate::ids::ids_bytes(counts[..k].iter().sum(), wout as u32);
        let mut a = if wout % 8 == 0 { SArr::new(1, n) } else { zeroed(n) };
        structural::concat_ids(wout as u32, &counts[..k], &widths, &bytes_of(mapsv.array()), &bytes_of(&parts[..k]), a.bytes_mut());
        a.into()
    }

    /// Spec: `Kernel.hashConcat ps` is `concatEnum`'s interned answer when the first part's dictionary holds no symbol twice,
    /// and `none` otherwise. The first part's ids are then its own -- the joined dictionary is its dictionary with the new
    /// symbols after it -- and are copied, or widened when the joined dictionary needs more bits; every other part's go through
    /// the map its entries resolved to. `ps` is owned and handed back on a decline (`.error ps`), so that the caller's fallback
    /// needs no reference of its own and the first part's ids, when nothing else holds them, are grown in place.
    fn qlean_symdict_concat(ps: O) -> O {
        match symdict_concat(&ps) {
            None => ctor(0, [ps], &[]),
            Some(r) => ctor(1, [r], &[]),
        }
    }
}

/// The interned answer `(dict, (offs, ids))` of `ps`, or `None` where the dictionary half declines.
fn symdict_concat(ps: &O) -> Option<O> {
    let k = ps.borrow().array().len();
    if k == 0 { return None }
    let pt: Vec<SdPart> = (0..k).map(|i| sd_part(ps.borrow(), i)).collect();
    let total: usize = pt.iter().map(|p| p.n).sum();
    // the first part's own width: its ids are copied as they are, whichever dictionary is the base
    let (n0, w0) = (pt[0].n, crate::ids::id_width(sym_count(pt[0].offs)));
    let sz0 = pt[0].ids.bytes().len();
    let (db, dbo, cnt, maps) = sd_concat(&pt.iter().map(|p| (p.dict, p.offs)).collect::<Vec<_>>())?;
    let w = crate::ids::id_width(cnt);
    let all = crate::ids::ids_bytes(total, w);
    let mut res = if w == w0 { sarray_room(take_ids0(ps), all) } else { zeroed(all).into() };
    let out = res.exclusive().expect("qlean symdict_concat: an answer holds one reference");
    if w == w0 {
        // the first part's ids are the answer's first `n0`, so they stay where they are; every bit past them is cleared,
        // which `ids_place` writes over and two equal columns compare
        let nb = n0 * w as usize;
        let keep = (nb / 8).min(sz0);
        if keep < all {
            let tail = if keep < sz0 && nb % 8 != 0 { out[keep] & ((1u8 << (nb % 8)) - 1) } else { 0 };
            out[keep..].fill(0);
            out[keep] = tail;
        }
    } else {
        let p0 = structural::row_at(&[pt[0].ids.bytes()], 0, crate::ids::ids_bytes(n0, w0));
        structural::ids_place(out, 0, w, n0, w0, &p0, None, usize::MAX);
    }
    let mut at = n0;
    for (i, p) in pt.iter().enumerate().skip(1) {
        let (wi, nm) = (crate::ids::id_width(sym_count(p.offs)), sym_count(p.offs));
        let pp = structural::row_at(&[p.ids.bytes()], 0, crate::ids::ids_bytes(p.n, wi));
        structural::ids_place(out, at, w, p.n, wi, &pp, maps[i].as_deref(), nm);
        at += p.n;
    }
    Some(pair(db, pair(dbo, res)))
}

// ---- T2: from `qlean_structural_til_foR` to the end: `til`, `string`, `mmu`, the transposes, the amends and the scatters ----
/// A `Nat` array of the `n` values `f(i)`, as tagged scalars (a count below 2^63).
fn boxed_array(n: usize, f: impl Fn(usize) -> usize) -> O {
    array_boxed(n, |o| for (i, x) in o.iter_mut().enumerate() { *x = box_(f(i)) as usize })
}
/// The `Int64`s of an index column, `size / 8` of them.
fn longs<'a, T: pod::Pod>(b: B<'a>) -> &'a [T] {
    let b = b.bytes();
    pod::cast(&b[..b.len() / 8 * 8]).expect("qlean structural: an index column is not 8-aligned")
}
/// An `Array ByteArray` of rows, each at `want` bytes (a short one zero-padded, `Column.bitsAt`'s convention), as the `f64`s
/// the specification reads.
fn f64_rows<'a>(rows: &'a structural::Rows<'_, '_>, k: usize) -> Vec<&'a [f64]> {
    (0..k).map(|i| pod::cast(rows.get(i)).expect("qlean mmu: a padded row is not 8-aligned")).collect()
}

export! {
    /// Spec: `tilFoR n` is `Coc.encode 8 (tilLongs n)`. The ramp is handed to the writer a block at a time, so the dense column is
    /// never built.
    fn qlean_structural_til_foR(n: usize) -> O { encode_fill(n, 8, &structural::til_fill) }

    /// Spec: `stringDigits w n x` is `(blob, offs)` where `offs` is the `n + 1` starts and the bytes between `offs[i]` and
    /// `offs[i+1]` are `atomText` of element `i` -- its decimal spelling, and the empty string where it is that width's null. `w` is
    /// 2, 4 or 8; anything else aborts rather than answering an empty pair and dropping a column's contents silently.
    fn qlean_structural_string_digits(width: u8, n: usize, x: B) -> O {
        let w = width as usize;
        if !matches!(w, 2 | 4 | 8) { die(format_args!("qlean_structural_string_digits: width {width} is not 2, 4 or 8\n")) }
        let n = n.min(x.bytes().len() / w);
        let src = &x.bytes()[..n * w];
        let mut at = alloc::vec![0usize; n.div_ceil(STR_BLK) + 1];
        let total = structural::str_count(c::pool(), w, src, n, &mut at);
        let mut blob = SArr::new(1, total);
        let offs = array_boxed(n + 1, |o| structural::str_write(c::pool(), w, src, n, &at, blob.bytes_mut(), o));
        pair(blob.into(), offs)
    }

    /// Spec: `mmuF64 a b` is the n * p products of n rows of m against m rows of p, row by row, each a strict left fold over k:
    /// float addition is not associative, so the order is part of the specification. A row is read at the width `b` fixes (`m`
    /// doubles for `a`, `p` for `b`), a short one as zeros.
    fn qlean_structural_mmu(av: B, bv: B) -> O {
        let (a, b) = (av.array(), bv.array());
        let (n, m) = (a.len(), b.len());
        let p = if m != 0 { b[0].bytes().len() / 8 } else { 0 };
        let (ab, bb) = (bytes_of(a), bytes_of(b));
        let (rb, ra) = (rows_at(&bb, p * 8), rows_at(&ab, m * 8));
        // the answer is allocated up to a whole number of blocks so that the last block is a whole block
        let mut res = SArr::with_capacity(1, n * p * 8, n.div_ceil(4) * 4 * p * 8);
        structural::mmu(&f64_rows(&ra, n), &f64_rows(&rb, m), p, pod::cast_mut(res.capacity_mut()).expect("qlean mmu: the answer is not 8-aligned"));
        res.into()
    }

    /// Spec: `transpose w n k cols` is `(blob, offs)` where `offs` is `0, k*w, 2*k*w, ...` -- the `n + 1` boundaries of `n` rows of
    /// `k` elements -- and the bytes of row `i` are element `i` of each of the `k` columns in order, `w` bytes each. Every column
    /// is read at the `n` the caller gives and not at its own length.
    fn qlean_structural_transpose(w: u8, n: usize, cols: B) -> O {
        let (wd, cs) = (w as usize, bytes_of(cols.array()));
        let stride = cs.len() * wd;
        let rows = rows_at(&cs, n * wd);
        let cv: Vec<&[u8]> = (0..cs.len()).map(|j| rows.get(j)).collect();
        let mut blob = SArr::new(1, n * stride);
        structural::transpose(wd, n, &cv, blob.bytes_mut());
        pair(blob.into(), boxed_array(n + 1, |i| i * stride))
    }

    /// Spec: `untranspose w offs b` is `some (blob, cuts)` where `b` holds `n` rows of `k` cells of `w` bytes -- which is what `offs`
    /// says exactly when it is `0, s, 2s, ...` for `s = k * w` -- and `blob` is the `k` columns laid end to end with `cuts` the
    /// `k + 1` boundaries between them. `none` at any other `offs`, which is a ragged slices value and not a matrix.
    fn qlean_structural_untranspose(w: u8, offsv: B, bv: B) -> O {
        let (ofs, wd) = (offsv.array(), w as usize);
        if wd == 0 || ofs.len() < 2 { return boxed(0) }
        let n = ofs.len() - 1;
        let Some(k) = structural::uniform_stride(wd, n, bv.bytes().len(), |i| count_at(ofs, i)) else { return boxed(0) };
        let mut blob = SArr::new(1, n * k * wd);
        structural::untranspose(wd, n, k, bv.bytes(), blob.bytes_mut());
        ctor(1, [pair(blob.into(), boxed_array(k + 1, |j| j * n * wd))], &[])
    }

    /// Spec: the answer `transpose` would give for the two columns `l[k / m]` and `r[k % m]`, without building either: every row is
    /// one element of `l` beside one of `r`.
    fn qlean_structural_cross(w: u8, n: usize, m: usize, l: B, r: B) -> O {
        let (wd, rows) = (w as usize, n * m);
        let stride = 2 * wd;
        let mut blob = SArr::new(1, rows * stride);
        structural::cross(wd, n, m, l.bytes(), r.bytes(), blob.bytes_mut());
        pair(blob.into(), boxed_array(rows + 1, |i| i * stride))
    }

    /// Spec: `amendRounds n wi ranked idx`. Word 0 is the round count, or all ones when an index misses `[0, n)` -- q's `'length`,
    /// `0N` and negatives included -- with that index in word 1. Ranked and repeated, the round ends and the positions grouped by
    /// round follow; an index narrower than a long follows widened.
    fn qlean_structural_amend_rounds(n: usize, wi: usize, ranked: u8, idxv: B) -> O {
        amend_of(n, wi, ranked, false, idxv).0
    }

    /// Spec: `amendIndex n wi ranked idx` -- `amendRounds` and, when no index misses, `amendCompact` of the indices widened, both
    /// empty when one does.
    fn qlean_structural_amend_index(n: usize, wi: usize, ranked: u8, idxv: B) -> O {
        let (res, dom, rank) = amend_of(n, wi, ranked, true, idxv);
        let empty = || SArr::new(1, 0).into();
        pair(res, pair(dom.unwrap_or_else(empty), rank.unwrap_or_else(empty)))
    }

    /// Spec: `scatterPacked wb dst idx src soff bcast` -- for each long `idx[k]` in order, the field at it in `dst` becomes field
    /// `soff + k` of `src`, or field `soff` for every `k` under `bcast`; fields are `wb` bits, packed low field first below a byte.
    /// In order, so the last write to a repeated index is the one that stays, which is q's `:`. An index past `dst` writes nothing;
    /// `amendRounds` raised it.
    fn qlean_structural_scatter(wb: usize, dst: O, idxv: B, srcv: B, soff: usize, bcast: u8) -> O {
        scatter(wb, dst, idxv, srcv, soff, bcast)
    }

    /// Spec: `scatterIds wa wb n ids idx yids bcast` is `scatterPacked wb` of the `n` ids widened from `wa` bits to `wb` -- an id
    /// past the payload reading `0`, `Column.idAt`'s convention -- and the ids themselves where the widths agree, which `scatter`
    /// writes in place when nothing else holds them.
    fn qlean_structural_scatter_ids(wa: usize, wb: usize, n: usize, ids: O, idxv: B, yv: B, bcast: u8) -> O {
        let ids = if wa == wb { ids } else {
            let mut o = SArr::new(1, ids_bytes(n, wb as u32));
            structural::widen_ids(n, wa as u32, wb as u32, ids.borrow().bytes(), o.bytes_mut());
            drop(ids); // as the C `lean_dec`: the wider copy is the only one the scatter holds
            o.into()
        };
        scatter(wb, ids, idxv, yv, 0, bcast)
    }

    /// Spec: `scatterSyms b o idx yb yo bcast` -- element `idx[k]` of the blob replaced, in order, by symbol `k` of `y` (`0` under
    /// `bcast`), the last write to a repeated index kept. Symbols have no fixed width, so the blob is rebuilt rather than written
    /// in place.
    fn qlean_structural_scatter_syms(bv: B, ov: B, idxv: B, ybv: B, yov: B, bcast: u8) -> O {
        let (b, y) = (syms_of(bv, ov), syms_of(ybv, yov));
        let src = structural::scatter_sources(b.count(), y.count(), longs::<u64>(idxv), bcast != 0);
        let mut blob = SArr::new(1, structural::scatter_syms_total(&src, &b, &y));
        let offs = array_boxed(src.len() + 1, |o| structural::scatter_syms_write(&src, &b, &y, blob.bytes_mut(), o));
        pair(blob.into(), offs)
    }

    /// Spec: `amendCompact n idx` -- `(u, rk)`: `u` the distinct longs of `idx` ascending, `rk[k]` the position of `idx[k]` in `u`.
    /// Every index is below `n`; `amendRounds` raised one that is not. An amend's rounds run over `x@u`, so the column takes one
    /// sorted scatter at the end rather than being decoded whole for a few writes.
    fn qlean_structural_amend_compact(n: usize, idxv: B) -> O {
        let ix = longs::<u64>(idxv);
        let cp = structural::Compact::new(n, ix)
            .unwrap_or_else(|k| die(format_args!("qlean amend: index {} of a column of {n} reached the compaction\n", ix[k])));
        let (mut u, mut rk) = (SArr::new(1, cp.count * 8), SArr::new(1, ix.len() * 8));
        cp.fill(ix, pod::cast_mut(u.bytes_mut()).expect("qlean amend: u is not 8-aligned"), pod::cast_mut(rk.bytes_mut()).expect("qlean amend: rk is not 8-aligned"));
        pair(u.into(), rk.into())
    }

    /// Spec: `scatterFoR w meta pack n ix vals` -- `Coc.encode w (scatterPacked (8 * w) (Coc.decode w meta pack n) ix vals 0 false)`,
    /// `ix` ascending, distinct and below `n` (`amendCompact`'s `u`), re-encoding only the blocks an index lands in.
    fn qlean_structural_scatter_for(w: usize, meta: B, pack: B, n: usize, idxv: B, valv: B) -> O {
        encode_scatter(w, meta.bytes(), pack.bytes(), None, n, idxv.bytes(), valv.bytes())
    }

    /// Spec: `scatterALP`, `scatterFoR` through ALP's encode and decode; the exponents `alpv` are the ALP part of the column.
    fn qlean_structural_scatter_alp(w: usize, meta: B, pack: B, alpv: B, n: usize, idxv: B, valv: B) -> O {
        encode_scatter(w, meta.bytes(), pack.bytes(), Some(alpv.bytes()), n, idxv.bytes(), valv.bytes())
    }
}

/// `amend`'s arrays for an index column, its width checked: 1, 2, 4 and 8 are read.
fn amend_of(n: usize, wi: usize, ranked: u8, compact: bool, idxv: B) -> (O, Option<O>, Option<O>) {
    if !matches!(wi, 1 | 2 | 4 | 8) { die(format_args!("qlean amend: index width {wi}; 1, 2, 4 and 8 are read\n")) }
    amend(n, wi, ranked != 0, compact, idxv.bytes())
}
/// `scatterPacked` in the answer `dst` itself where this reference holds it alone, a copy otherwise.
fn scatter(wb: usize, dst: O, idxv: B, srcv: B, soff: usize, bcast: u8) -> O {
    if wb == 0 { return dst }
    let mut dst = dst.into_exclusive();
    structural::scatter_packed(wb, dst.bytes_mut(), longs::<i64>(idxv), srcv.bytes(), soff, bcast != 0);
    dst.into()
}
