//! structural.c's Lean exports, and the helpers every other export of that file reads a Lean argument through (the C
//! `count_at`, `row_at`, `rows_at`, `alp_view`, `mk_pair`; `take_first` and `sarray_room` are `ffi::`'s, which owns the
//! raw objects). The logic is `crate::structural`; an encoded answer is `ffi::encode_fill` over a `Producer`.
#![deny(unsafe_code)]
use crate::alp::Cocf;
use crate::coc::{Coc, Meta};
use crate::ffi::{Producer, encode_fill, sarray_room, take_first};
use crate::lean::{B, O, SArr, ctor, export};
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
