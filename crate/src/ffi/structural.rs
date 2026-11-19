//! structural.rs's Lean exports, and the helpers every other export of that file reads a Lean argument through (the C
//! `count_at`, `row_at`, `rows_at`, `alp_view`, `mk_pair`; `take_first` and `sarray_room` are `ffi::`'s, which owns the
//! raw objects). The logic is `crate::structural`; an encoded answer is a `ffi::Sink` over an `enc::Producer`.
#![deny(unsafe_code)]
use crate::alp::Cocf;
use crate::coc::Coc;
use crate::exports::coc::view;
use crate::enc::{Producer, filled, filled_into};
use crate::ffi::{Form, SdPart, Sink, ints_at, sarray_room, sd_concat, sd_part, take_ids0};
use crate::lean::{B, O, SArr, ctor, export};
use crate::{pod, structural};
use alloc::vec::Vec;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {crate::exports::coc::alp_view, crate::exports::reduce::elems, crate::ffi::{concat_own, syms_of, take_first}, crate::lean::box_usize_o, crate::{c, lean}};

pub fn die(args: core::fmt::Arguments) -> ! {
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

/// `,` of the parts `parts` starting at `start[j]` (`start` holds the part count + 1 entries) of element width `w`: structural.rs
/// `cat_fill` and `cat_take`.
pub struct Cat<'a, 'b> { parts: &'a [Coc<'b>], start: &'a [usize], w: usize }
impl Cat<'_, '_> { fn elems(&self, v: &mut [i64], i0: usize) { structural::cat_fill(&|i| structural::plain(&self.parts[i]), self.start, self.w, false, v, i0) } }
impl Producer for Cat<'_, '_> {
    fn block<'s>(&'s self, _: usize, lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8] { filled(|v, i0| self.elems(v, i0), lo, nb, w, buf) }
    fn block_into(&self, _: usize, lo: usize, nb: usize, w: usize, buf: &mut [u8], out: &mut [u8]) { filled_into(|v, i0| self.elems(v, i0), lo, nb, w, buf, out) }
    fn take(&self, b: usize) -> Option<(Cocf<'_>, usize)> {
        let (p, j) = structural::cat_take(self.start, b)?;
        structural::cat_part_ok(&self.parts[p], self.w, false).then(|| (structural::plain(&self.parts[p]), j))
    }
}

/// A column shifted by `k`, `fill` entering: structural.rs `shift_fill`.
pub struct Shift<'a, 'b> { c: &'a Coc<'b>, k: i64, fill: i64 }
impl Shift<'_, '_> { fn elems(&self, v: &mut [i64], i0: usize) { structural::shift_fill(self.c, self.k, self.fill, v, i0) } }
impl Producer for Shift<'_, '_> {
    fn block<'s>(&'s self, _: usize, lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8] { filled(|v, i0| self.elems(v, i0), lo, nb, w, buf) }
    fn block_into(&self, _: usize, lo: usize, nb: usize, w: usize, buf: &mut [u8], out: &mut [u8]) { filled_into(|v, i0| self.elems(v, i0), lo, nb, w, buf, out) }
}

/// The hint callbacks all answer the exponent and the patch limit the walk leaves in `lim`.
pub fn hinted(h: impl FnOnce(&mut u32) -> i32) -> Option<(i32, u32)> { let mut lim = 0; let e = h(&mut lim); Some((e, lim)) }
/// `,` of ALP parts: structural.rs `cat_fill_alp`, `cat_take`, `cat_hint`, `cat_ints`.
pub struct CatAlp<'a, 'b> { parts: &'a [Cocf<'b>], start: &'a [usize], w: usize }
impl CatAlp<'_, '_> { fn elems(&self, v: &mut [i64], i0: usize) { structural::cat_fill_alp(&|i| self.parts[i], self.start, self.w, v, i0) } }
impl Producer for CatAlp<'_, '_> {
    fn block<'s>(&'s self, _: usize, lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8] { filled(|v, i0| self.elems(v, i0), lo, nb, w, buf) }
    fn block_into(&self, _: usize, lo: usize, nb: usize, w: usize, buf: &mut [u8], out: &mut [u8]) { filled_into(|v, i0| self.elems(v, i0), lo, nb, w, buf, out) }
    fn take(&self, b: usize) -> Option<(Cocf<'_>, usize)> {
        let (p, j) = structural::cat_take(self.start, b)?;
        structural::cat_part_ok(&self.parts[p].c, self.w, true).then(|| (self.parts[p], j))
    }
    fn hint(&self, b: usize) -> Option<(i32, u32)> { hinted(|l| structural::cat_hint(&|i| self.parts[i], self.start, b, l)) }
    fn ints(&self, b: usize, nb: usize, d: &mut [i64], ee: &mut [i8], raw: Option<&mut [u8]>) -> Option<i32> {
        ints_at(|o| structural::cat_ints(&|i| self.parts[i], self.start, b, o), nb, self.w, d, ee, raw)
    }
}

/// structural.rs `concat_foR_move`: the parts' four metadata sections in turn and their packs end to end, `n` elements.
pub fn concat_moved(ms: &[&[u8]], ps: &[&[u8]], n: usize, w: usize) -> O {
    let mut mo = SArr::new(1, 33 * ms.iter().map(|m| m.len() / 33).sum::<usize>() + 24);
    let mut po = SArr::new(1, ps.iter().map(|p| p.len()).sum());
    structural::concat_move(crate::coc::Meta::new(ms[0], 0).map_or(crate::DEFAULT_LG, |m| m.lg), ms, ps, n, w, mo.bytes_mut(), po.bytes_mut());
    pair(mo.into(), po.into())
}
/// structural.rs `concat_foR`: the answer, or `Err` of the append `qlean_structural_concat_foR` makes in the first part's own
/// objects, with their sizes. Nothing here changes an argument, so every view lives only inside it.
pub fn concat(w: usize, nsv: B, metasv: &O, packsv: &O) -> Result<O, (structural::Grow, usize, usize)> {
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
    Ok(Sink::new(start[k], w, Form::For).answer(&Cat { parts: &parts, start: &start, w }))
}

export! {

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
    /// Spec: `enlistLong n` is the one little-endian long `n`.
    fn qlean_structural_enlist(n: usize) -> O {
        let mut a = SArr::new(1, 8);
        a.bytes_mut().copy_from_slice(&(n as u64).to_le_bytes());
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
        Sink::new(at, w, Form::Alp).answer(&CatAlp { parts: &parts, start: &start, w })
    }


}

/// A fresh payload of `n` bytes, zeroed: structural.rs `zeroed_bits` and `ids_alloc`, whose unwritten tail bits must be 0
/// for two equal columns to hold the same bytes.
pub fn zeroed(n: usize) -> SArr {
    let mut a = SArr::new(1, n);
    a.bytes_mut().fill(0);
    a
}
/// The fields `ids` holds at `w` bits, `n` clamped to them: structural.rs `ids_avail`, where width 0 holds any count.
pub fn ids_n(n: usize, ids: &[u8], w: usize) -> usize { n.min(if w != 0 { ids.len() * 8 / w } else { usize::MAX }) }
/// A fresh `ByteArray` of the `n` elements of `w` bytes `f` writes, as structural.rs's `lean_alloc_sarray(1, n * w, n * w)`.
pub fn fresh(n: usize, f: impl FnOnce(&mut [u8])) -> O {
    let mut a = SArr::new(1, n);
    f(a.bytes_mut());
    a.into()
}

export! {

    /// Spec: `cycleIds n off m w ids` is `m` fields from `off`, cycling. Not `cycleBytes`' extract and concatenate: at a
    /// sub-byte width a slice can start inside a byte, so the fields move one at a time.
    fn qlean_structural_cycle_ids(n: usize, off: usize, m: usize, w: usize, idsv: B) -> O {
        let mut a = zeroed(crate::ids::ids_bytes(m, w as u32));
        structural::cycle_ids(ids_n(n, idsv.bytes(), w), off, m, w as u32, idsv.bytes(), a.bytes_mut());
        a.into()
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

    /// Spec: `bitsOfFoR meta pack n` is `packOf n` of each element's low bit, the rows past the blocks `0`: a boolean
    /// `foR` (`u1`) as the bitmap `concatBits` joins, read a block at a time.
    fn qlean_structural_bits_of_for(mv: B, pv: B, n: usize) -> O {
        let c = view("qlean_structural_bits_of_for", mv, pv, n);
        let mut a = zeroed(n.div_ceil(8));
        structural::bits_of_enc(&c, a.bytes_mut());
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

/// The symbols a dictionary's starts describe: `n + 1` starts are `n` symbols and an empty table is none (sym.rs `sym_count`).
pub fn sym_count(offs: B) -> usize { offs.array().len().saturating_sub(1) }

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


    /// Spec: `gatherBits n bits idx` is bit `j` set exactly when `gatherAt n idx j` is `some i` and `Column.bitAt bits i` --
    /// `101b@0 5` is `10b`, measured, so a miss is `0b` and not a dropped element.
    fn qlean_structural_gather_bits(n: usize, bitsv: B, idxv: B) -> O {
        let idx = elems::<i64>(idxv);
        let mut a = zeroed(idx.len().div_ceil(8));
        structural::gather_bits(c::pool(), n, bitsv.bytes(), idx, a.bytes_mut());
        a.into()
    }




    /// Spec: `expandBytes w fill src ws` is `gatherBytes w fill src (spreadBytes ws)` -- element `i` of `src` repeated `ws[i]`
    /// times (a negative count is a run of none), and `fill` for a run past the end of `src`; the index is never built.
    fn qlean_structural_expand(w: usize, fill: u64, srcv: B, wv: B) -> O {
        let ws = elems::<i64>(wv);
        fresh(ws.iter().map(|&x| x.max(0) as usize).sum::<usize>() * w, |o| structural::expand(c::pool(), w, fill, srcv.bytes(), ws, o))
    }



    /// Spec: `gatherSyms blob offs ix` is the blob and offset table of the symbols `ix` names, with a miss answering the empty
    /// symbol -- `` `a`b@0 5 ``, `` `a`b@0 -1 `` and `` `a`b@0 0N `` are all `` `a` ``.
    fn qlean_structural_gather_syms(blobv: B, offsv: B, idxv: B) -> O {
        let (s, idx) = (syms_of(blobv, offsv), elems::<i64>(idxv));
        let mut nb = SArr::new(1, structural::gather_syms_len(&s, idx));
        let no = lean::arr_words(idx.len() + 1, |o| structural::gather_syms(&s, idx, nb.bytes_mut(), o));
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
pub fn symdict_concat(ps: &O) -> Option<O> {
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

/// The `Int64`s of an index column, `size / 8` of them.
pub fn longs<'a, T: pod::Pod>(b: B<'a>) -> &'a [T] {
    let b = b.bytes();
    pod::cast(&b[..b.len() / 8 * 8]).expect("qlean structural: an index column is not 8-aligned")
}

export! {








    /// Spec: `scatterPacked wb dst idx src soff bcast` -- for each long `idx[k]` in order, the field at it in `dst` becomes field
    /// `soff + k` of `src`, or field `soff` for every `k` under `bcast`; fields are `wb` bits, packed low field first below a byte.
    /// In order, so the last write to a repeated index is the one that stays, which is q's `:`. An index past `dst` writes nothing;
    /// `amendRounds` raised it.
    fn qlean_structural_scatter(wb: usize, dst: O, idxv: B, srcv: B, soff: usize, bcast: u8) -> O {
        scatter(wb, dst, idxv, srcv, soff, bcast)
    }

}

/// `scatterPacked` in the answer `dst` itself where this reference holds it alone, a copy otherwise.
pub fn scatter(wb: usize, dst: O, idxv: B, srcv: B, soff: usize, bcast: u8) -> O {
    if wb == 0 { return dst }
    let mut dst = dst.into_exclusive();
    structural::scatter_packed(wb, dst.bytes_mut(), longs::<i64>(idxv), srcv.bytes(), soff, bcast != 0);
    dst.into()
}
