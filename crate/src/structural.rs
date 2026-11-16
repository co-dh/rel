#![forbid(unsafe_code)]
//! Column (a), structural.c: bit helpers and the encoded-column readers (A34), the encoder sources of reverse,
//! cycle, shift and concat (A35), concat of encoded columns (A36), gathers (A37–A38), cycles, concats and
//! enumerations (A39), the symbol dictionary table (A40), dictionary concat (A41a), `til` and `scatter` (A41b).
//! The `qlean_structural_*` entries and the `sd_*` dictionary cache (which holds `lean_object`s) stay C (§1).
//! An encoder source (`coc_fill`, `coc_hint`, `coc_ints`, coc.h:2001-2018) is a Rust fn here over views; its C
//! callback keeps a one-line body that unpacks its `ctx` and calls the `qrs_*` shim.

use alloc::vec::Vec;
use core::sync::atomic::{AtomicU8, AtomicUsize, Ordering::{Relaxed, SeqCst}};
use crate::alp::{Cocf, Flt};
use crate::enc::{EncMeta, EncPack};
use crate::c::Runner;
use crate::coc::Coc;
use crate::sym::{sym_eq, sym_hash, Syms};
use crate::{pod, BLK};

// ---- A34: structural.c:56-374 ----
/// structural.c:56 `bit_set`
pub fn bit_set(out: &mut [u8], i: usize) { out[i >> 3] |= 1u8 << (i & 7) }
/// structural.c:72 `bits64_at`: 64 bits from bit `i`, zeros past the end.
pub fn bits64_at(b: &[u8], i: usize) -> u64 {
    let (byte, sh) = (i >> 3, i & 7);
    let rd = |k: usize| b.get(byte + k).map_or(0, |&x| x as u64);
    let lo = if b.len() >= byte + 8 { u64::from_le_bytes(b[byte..byte + 8].try_into().unwrap()) }
             else { (0..8).fold(0, |a, k| a | rd(k) << (8 * k)) };
    if sh == 0 { lo } else { lo >> sh | rd(8) << (64 - sh) }
}
/// structural.c:84 `or_bits`: the low `cnt` bits of `w` or-ed in at bit `at`.
pub fn or_bits(out: &mut [u8], at: usize, w: u64, cnt: usize) {
    let w = if cnt < 64 { w & ((1u64 << cnt) - 1) } else { w };
    let (byte, v) = (at >> 3, (w as u128) << (at & 7));
    if byte + 9 <= out.len() {
        let lo = u64::from_le_bytes(out[byte..byte + 8].try_into().unwrap()) | v as u64;
        out[byte..byte + 8].copy_from_slice(&lo.to_le_bytes());
        out[byte + 8] |= (v >> 64) as u8;
    } else {
        for k in 0..(at + cnt).div_ceil(8) - byte { out[byte + k] |= (v >> (8 * k)) as u8 }
    }
}
/// structural.c:99 `copy_bits`: `len` bits of `b` from bit `from` to bit `at` of `out`.
pub fn copy_bits(out: &mut [u8], at: usize, b: &[u8], from: usize, len: usize) {
    for t in (0..len).step_by(64) { or_bits(out, at + t, bits64_at(b, from + t), (len - t).min(64)) }
}
/// structural.c:106 `set_bits`
pub fn set_bits(out: &mut [u8], at: usize, len: usize) {
    for t in (0..len).step_by(64) { or_bits(out, at + t, !0, (len - t).min(64)) }
}
/// structural.c:112 `bitrev64`
pub fn bitrev64(x: u64) -> u64 { x.reverse_bits() }
/// structural.c:1079 `qlean_structural_reverse_bits`: bit `j` of `out` is bit `n - 1 - j` of `b` (answer bits
/// `[j, j + cnt)` are source bits `[n - j - cnt, n - j)` reversed).
pub fn reverse_bits(n: usize, b: &[u8], out: &mut [u8]) {
    for j in (0..n).step_by(64) {
        let cnt = (n - j).min(64);
        let w = bits64_at(b, n - j - cnt);
        let w = if cnt < 64 { w & ((1u64 << cnt) - 1) } else { w };
        or_bits(out, j, bitrev64(w) >> (64 - cnt), cnt);
    }
}
/// structural.c:1120 `qlean_structural_shift_bits`: bit `j` of `out` is bit `j - k` of `b` inside `[0, n)` and the low
/// bit of `fill` outside.
pub fn shift_bits(n: usize, fill: u64, k: i64, b: &[u8], out: &mut [u8]) {
    // `|k|` clamped to `n` without negating `k`, which overflows at `i64::MIN`
    let m = k.unsigned_abs().min(n as u64) as usize;
    // a right shift fills `[0, m)` and moves `[0, n - m)` up; a left one moves `[m, n)` down
    let (lo, at, from) = if k < 0 { (n - m, 0, m) } else { (0, m, 0) };
    copy_bits(out, at, b, from, n - m);
    if fill != 0 { set_bits(out, lo, m) }
}
/// structural.c:194 `rev_fields`: a byte's `w`-bit fields reversed.
pub fn rev_fields(x: u8, w: u8) -> u8 {
    match w {
        4 => x.rotate_left(4),
        2 => (x >> 6) | ((x >> 2) & 0x0c) | ((x << 2) & 0x30) | (x << 6),
        _ => x.reverse_bits(),
    }
}
/// structural.c:210 `rev_block`: a full block's `w`-bit residuals reversed.
pub fn rev_block(dp: &mut [u8], sp: &[u8], w: u8) {
    if w == 0 { return }
    let nbytes = crate::BLK * w as usize / 8;
    if w & (w - 1) != 0 {
        // on the stack, as the C packs straight from `res_get`: a heap vector per block was an allocation per block
        let mut v = [0u64; crate::BLK];
        for (i, e) in v.iter_mut().enumerate() { *e = crate::res::res_get(sp, w, crate::BLK - 1 - i) }
        return crate::simd::res_pack(&v, w, crate::BLK, dp);
    }
    // a fixed element size per call, so the copy is one load and one store
    fn rev_el<const E: usize>(dp: &mut [u8], sp: &[u8]) {
        for (d, s) in dp.chunks_exact_mut(E).zip(sp.chunks_exact(E).rev()) { d.copy_from_slice(s) }
    }
    let (dp, sp) = (&mut dp[..nbytes], &sp[..nbytes]);
    if w >= 8 {
        match w / 8 {
            1 => rev_el::<1>(dp, sp), 2 => rev_el::<2>(dp, sp), 4 => rev_el::<4>(dp, sp), 8 => rev_el::<8>(dp, sp),
            e => panic!("qlean structural: reverse of an encoded column got element width {e}; the kernels are instantiated at 1, 2, 4, 8 and 16 bytes"),
        }
        return;
    }
    for (d, &s) in dp.iter_mut().zip(sp.iter().rev()) { *d = rev_fields(s, w) }
}
/// structural.c:225 `reverse_foR_run`: every block's residuals reversed into `pack` (the moved column's), threaded.
/// `c` is the source column; answer block `b` is its block `nb - 1 - b`, and `pack` holds the answer's blocks in order.
pub fn reverse_enc(run: Runner, c: &Coc, pack: &mut [u8]) {
    let (nb, blk) = (c.meta.mblk, crate::BLK);
    // the answer's offsets from the reversed widths, `Column.blockStarts`' recomputation
    let ob: alloc::vec::Vec<usize> = core::iter::once(0)
        .chain((0..nb).scan(0, |t, b| { *t += blk * c.meta.width[nb - 1 - b] as usize / 8; Some(*t) })).collect();
    let total = ob[nb];
    assert_eq!(pack.len(), total, "reverse_enc: {} answer bytes for blocks of {total} bytes", pack.len());
    // the pool cuts the answer's bytes, not its blocks (a block's size is its width's); a block straddling two cuts
    // is reversed whole into a scratch and each cut keeps its part
    crate::c::run_map(run, pack, total, 1, crate::QLEAN_COST_COPY, 8, &|lo, hi, o: &mut [u8]| {
        let mut b = ob.partition_point(|&x| x <= lo) - 1;
        let (mut buf, mut tmp) = ([0u8; crate::BLK * 8], [0u8; crate::BLK * 8]);
        while b < nb && ob[b] < hi {
            let (w, nbytes) = (c.meta.width[nb - 1 - b], ob[b + 1] - ob[b]);
            if nbytes > 0 {
                let so = total - ob[b] - nbytes;
                // a pack shorter than its widths claim reads zeros past its end, `Column.bitsAt`'s convention
                let avail = c.pack.len().saturating_sub(so).min(nbytes);
                let sp = if avail == nbytes { &c.pack[so..so + nbytes] } else {
                    if avail > 0 { buf[..avail].copy_from_slice(&c.pack[so..so + avail]) } buf[avail..nbytes].fill(0); &buf[..nbytes]
                };
                let (s, e) = (ob[b].max(lo), ob[b + 1].min(hi));
                if s == ob[b] && e == ob[b + 1] { rev_block(&mut o[s - lo..e - lo], sp, w) }
                else { rev_block(&mut tmp[..nbytes], sp, w); o[s - lo..e - lo].copy_from_slice(&tmp[s - ob[b]..e - ob[b]]) }
            }
            b += 1;
        }
    });
}
/// coc.h:138's layout over a writer's metadata of `nb` blocks: base, maxv, off, bsum (8 bytes a block each), the
/// trailer's two words, then the widths.
fn meta_parts(m: &mut [u8], nb: usize) -> [&mut [u8]; 6] {
    assert_eq!(m.len(), 33 * nb + 16, "qlean structural: {} metadata bytes for {nb} blocks of 33 and a 16-byte trailer", m.len());
    let (base, m) = m.split_at_mut(8 * nb);
    let (maxv, m) = m.split_at_mut(8 * nb);
    let (off, m) = m.split_at_mut(8 * nb);
    let (bsum, m) = m.split_at_mut(8 * nb);
    let (sums, width) = m.split_at_mut(16);
    [base, maxv, off, bsum, sums, width]
}
fn put64(d: &mut [u8], i: usize, v: u64) { d[8 * i..8 * i + 8].copy_from_slice(&v.to_ne_bytes()) }
/// structural.c:197 `reverse_foR_move`'s metadata: the blocks in reverse order, each keeping its base, maximum, width
/// and sum (a reversed block holds the same elements), `off` recomputed from the widths, the trailer the source's.
/// `out` is `33 * mblk + 16` bytes; answers the pack's length, `Σ BLK * width / 8`.
pub fn reverse_meta(c: &Coc, out: &mut [u8]) -> usize {
    let (m, nb) = (&c.meta, c.meta.mblk);
    let [base, maxv, off, bsum, sums, width] = meta_parts(out, nb);
    let mut at = 0;
    for b in 0..nb {
        let s = nb - 1 - b;
        put64(base, b, m.base[s] as u64);
        put64(maxv, b, m.maxv[s] as u64);
        put64(bsum, b, m.bsum[s] as u64);
        width[b] = m.width[s];
        put64(off, b, at as u64);
        at += BLK * m.width[s] as usize / 8;
    }
    put64(sums, 0, m.sumnul as u64);
    put64(sums, 1, m.sumn);
    at
}
/// structural.c:220 `concat_foR_move`: the four metadata sections of each part in turn, `off` recomputed from the
/// concatenated widths, the trailer the writer's for `n` elements of `w` bytes, and the packs end to end.
/// `mo`/`po` are `33 * Σ nblk + 16` and `Σ pack` bytes.
pub fn concat_move(ms: &[&[u8]], ps: &[&[u8]], n: usize, w: usize, mo: &mut [u8], po: &mut [u8]) {
    let nbs: alloc::vec::Vec<usize> = ms.iter().map(|m| m.len() / 33).collect();
    let nb: usize = nbs.iter().sum();
    let [base, maxv, off, bsum, sums, width] = meta_parts(mo, nb);
    let mut at = 0;
    for (m, &k) in ms.iter().zip(&nbs) {
        assert!(m.len() >= 33 * k + 16, "qlean structural: {} metadata bytes for {k} blocks of 33 and a 16-byte trailer", m.len());
        // the part's own sections are the byte ranges coc.h:138 gives, so no alignment is asked of them
        base[8 * at..8 * (at + k)].copy_from_slice(&m[..8 * k]);
        maxv[8 * at..8 * (at + k)].copy_from_slice(&m[8 * k..16 * k]);
        bsum[8 * at..8 * (at + k)].copy_from_slice(&m[24 * k..32 * k]);
        width[at..at + k].copy_from_slice(&m[32 * k + 16..33 * k + 16]);
        at += k;
    }
    put64(sums, 0, crate::enc::coc_sumnul(w, false) as u64);
    put64(sums, 1, n as u64);
    let mut o = 0;
    for b in 0..nb { put64(off, b, o as u64); o += BLK * width[b] as usize / 8 }
    assert_eq!(po.len(), ps.iter().map(|p| p.len()).sum::<usize>(), "qlean structural: concat pack of {} bytes", po.len());
    let mut at = 0;
    for p in ps { po[at..at + p.len()].copy_from_slice(p); at += p.len() }
}
/// structural.c:469 `concat_foR`'s test: every part but the last fills its blocks, and each is in the writer's form
/// (a patch list's positions and offsets are its own column's; a block past the count or a short pack would carry into
/// the answer). `part(i)` is part `i`'s view and `ns[i]` its count.
pub fn cat_aligned<'a>(k: usize, ns: &[u64], w: usize, part: impl Fn(usize) -> Coc<'a>) -> bool {
    (0..k).all(|i| {
        let c = part(i);
        !(i + 1 < k && c.meta.n % BLK != 0) && c.std(ns[i] as usize) && c.pack.len() == c.meta.res_end()
            && trailer_ok(&c, c.meta.n, w, false)
    })
}
/// structural.c:320 `trailer_ok`: `c`'s trailer fits `n` elements of `w` bytes (`alp`: an ALP column's).
pub fn trailer_ok(c: &Coc, n: usize, w: usize, alp: bool) -> bool {
    c.meta.sumn == n as u64 && c.meta.sumnul == crate::enc::coc_sumnul(w, alp)
}
/// structural.c:327 `res_bytes`: block `s`'s residuals as whole bytes, from the pack or restored into `buf`.
pub fn res_bytes<'b>(c: &Coc<'b>, s: usize, buf: &'b mut [u8]) -> &'b [u8] {
    let (nbytes, so) = (crate::BLK * c.meta.width[s] as usize / 8, c.meta.off[s] as usize);
    if so + nbytes <= c.pack.len() { return &c.pack[so..so + nbytes] }
    // a pack shorter than its widths claim reads zeros past its end, `Column.resAt`'s convention
    let avail = c.pack.len().saturating_sub(so);
    let b = &mut buf[..nbytes];
    if avail > 0 { b[..avail].copy_from_slice(&c.pack[so..so + avail]) }
    b[avail..].fill(0);
    b
}
/// structural.c:343 `unpack_run`: elements `lo .. lo + dst.len()` of block `s` (reversed when `rev`) into `dst`.
pub fn unpack_run(dst: &mut [i64], c: &Coc, s: usize, lo: usize, rev: bool) {
    let (cnt, base) = (dst.len(), c.meta.base[s] as u64);
    if c.blk_nexc(s) > 0 {      // a patched block is decoded, its slots reading as base
        let mut x = [0i64; crate::BLK];
        c.decode_blk(s, lo + cnt, &mut x);
        for j in 0..cnt { dst[if rev { cnt - 1 - j } else { j }] = x[lo + j] }
        return;
    }
    // the direction is the iteration order, so it stays one loop per width
    fn put<F: Fn(usize) -> u64>(dst: &mut [i64], base: u64, rev: bool, f: F) {
        if rev { for (j, d) in dst.iter_mut().rev().enumerate() { *d = base.wrapping_add(f(j)) as i64 } }
        else { for (j, d) in dst.iter_mut().enumerate() { *d = base.wrapping_add(f(j)) as i64 } }
    }
    let (mut w, mut buf) = (c.meta.width[s], [0u8; crate::BLK * 8]);
    // a short run at an odd width reads its own fields: lanes would unpack every field before it
    if w & w.wrapping_sub(1) != 0 && cnt * 8 < lo + cnt {
        let q = res_bytes(c, s, &mut buf);
        return put(dst, base, rev, |j| crate::res::res_get(q, w, lo + j));
    }
    let mut lb = [0u64; crate::BLK];
    let p = crate::coc::lanes(res_bytes(c, s, &mut buf), &mut w, lo + cnt, crate::pod::bytes_mut(&mut lb));
    match w {
        0 => put(dst, base, rev, |_| 0),
        8 => put(dst, base, rev, |j| p[lo + j] as u64),
        16 => put(dst, base, rev, |j| u16::from_ne_bytes([p[2 * (lo + j)], p[2 * (lo + j) + 1]]) as u64),
        32 => put(dst, base, rev, |j| u32::from_ne_bytes(p[4 * (lo + j)..4 * (lo + j) + 4].try_into().unwrap()) as u64),
        64 => put(dst, base, rev, |j| u64::from_ne_bytes(p[8 * (lo + j)..8 * (lo + j) + 8].try_into().unwrap())),
        // 1, 2 or 4: fields share a byte
        _ => put(dst, base, rev, |j| (p[((lo + j) * w as usize) >> 3] as u64 >> (((lo + j) * w as usize) & 7)) & ((1u64 << w) - 1)),
    }
}

// ---- A35: structural.c:377-610, the encoder sources ----
/// structural.c:377 `blk_count`: the elements in block `b` of a column of `n`, a full block except the last.
pub fn blk_count(n: usize, b: usize) -> usize { if (b + 1) * BLK <= n { BLK } else { n - b * BLK } }

/// One piece of an answer block: `len` elements from `lo` of block `b` of part `p` landing at `at`, or a hole.
#[derive(Clone, Copy)]
enum Seg { Run { p: usize, b: usize, lo: usize, len: usize, at: usize }, Hole { at: usize, len: usize } }
/// A verb's walk over the source runs an answer block is made of (structural.c's `*_WALK`), written once and used by
/// every pass, so the passes cannot disagree about which elements a block holds.
type Walk<'w> = &'w dyn Fn(&mut dyn FnMut(Seg));

/// `reverse`: the answer's element `i` is the source's `n - 1 - i`, so the source indices descend from `n - 1 - i0`.
fn rev_walk(n: usize, i0: usize, cnt: usize, g: &mut dyn FnMut(Seg)) {
    let (mut top, mut k) = (n.wrapping_sub(1 + i0), 0);
    while k < cnt {
        let take = (top % BLK + 1).min(cnt - k);
        g(Seg::Run { p: 0, b: top / BLK, lo: top % BLK + 1 - take, len: take, at: k });
        k += take;
        top = top.wrapping_sub(take);
    }
}
/// `,`: `start[p]` is where part `p` begins and the last entry is the answer's own count; a binary search finds the
/// part holding `i0`, and an empty part is stepped over by the test that advances across a full one.
fn cat_walk(start: &[usize], i0: usize, cnt: usize, g: &mut dyn FnMut(Seg)) {
    let (np, mut k) = (start.len() - 1, 0);
    let (mut pi, mut hi) = (0, np);
    while pi + 1 < hi { let mid = (pi + hi) / 2; if start[mid] <= i0 { pi = mid } else { hi = mid } }
    while k < cnt {
        while pi + 1 < np && start[pi + 1] <= i0 + k { pi += 1 }
        let mut j = i0 + k - start[pi];
        let mut take = (start[pi + 1] - start[pi] - j).min(cnt - k);
        while take > 0 {
            let t = (BLK - j % BLK).min(take);
            g(Seg::Run { p: pi, b: j / BLK, lo: j % BLK, len: t, at: k });
            k += t; j += t; take -= t;
        }
    }
}
/// The cycling slice `n#x`, `n_x`, `x sublist y` and `rotate` share: the answer's element `j` is the source's
/// `(off + j) % n`, a run advancing forward and wrapping at most once per lap.
fn cycle_walk(n: usize, off: usize, i0: usize, cnt: usize, g: &mut dyn FnMut(Seg)) {
    if cnt == 0 { return }
    let (mut j, mut k) = ((off + i0) % n, 0);
    while k < cnt {
        let t = (BLK - j % BLK).min(n - j).min(cnt - k);
        g(Seg::Run { p: 0, b: j / BLK, lo: j % BLK, len: t, at: k });
        k += t; j += t;
        if j == n { j = 0 }
    }
}
/// A shift: the answer's element `j` is the source's `j - k`, so what the source can serve of a run is one forward
/// stretch across at most two blocks and the rest is a hole at both ends.
fn shift_walk(n: usize, k: i64, i0: usize, cnt: usize, g: &mut dyn FnMut(Seg)) {
    let from = (i0 as i64).wrapping_sub(k);
    let head = (if from < 0 { from.unsigned_abs() as usize } else { 0 }).min(cnt);
    let mut tail = cnt;
    if from.wrapping_add(cnt as i64) > n as i64 { tail = if from >= n as i64 { head } else { (n as i64 - from) as usize } }
    let tail = tail.max(head);
    if head > 0 { g(Seg::Hole { at: 0, len: head }) }
    if tail < cnt { g(Seg::Hole { at: tail, len: cnt - tail }) }
    let (mut at, mut j) = (head, from.wrapping_add(head as i64) as usize);
    while at < tail {
        let t = (BLK - j % BLK).min(tail - at);
        g(Seg::Run { p: 0, b: j / BLK, lo: j % BLK, len: t, at });
        at += t; j += t;
    }
}

/// An integer column as the view the ALP-aware passes take, its ALP part empty.
pub fn plain<'a>(c: &Coc<'a>) -> Cocf<'a> { Cocf { c: *c, exp: &[], exc_off: &[], exc_pos: &[], exc_raw: &[], f32: false } }

/// One run of `buf`, filled from block `b` of the part `f`: its decimals' integers, or at `alp` its elements' bits.
fn fill_run(f: &Cocf, alp: bool, out: &mut [i64], b: usize, lo: usize, rev: bool) {
    if alp { alp_run(out, f, b, lo, rev) } else { unpack_run(out, &f.c, b, lo, rev) }
}
/// Every fill below, its walk and its holes (`hole` entering where the source cannot serve).
fn fill<'a>(part: &dyn Fn(usize) -> Cocf<'a>, alp: bool, rev: bool, hole: i64, buf: &mut [i64], walk: Walk) {
    walk(&mut |s| match s {
        Seg::Run { p, b, lo, len, at } => fill_run(&part(p), alp, &mut buf[at..at + len], b, lo, rev),
        Seg::Hole { at, len } => buf[at..at + len].fill(hole),
    })
}
/// structural.c:425 `rev_fill`: elements `i0 ..` of `reverse c` into `buf`.
pub fn rev_fill(c: &Coc, buf: &mut [i64], i0: usize) {
    let (f, cnt) = (plain(c), buf.len());
    fill(&|_| f, false, true, 0, buf, &|g: &mut dyn FnMut(Seg)| rev_walk(c.meta.n, i0, cnt, g))
}
/// structural.c:473 `cycle_fill`: of `m` elements rotated by `off` (already below the count); `m` only a hint asks.
pub fn cycle_fill(c: &Coc, off: usize, _m: usize, buf: &mut [i64], i0: usize) {
    let (f, cnt) = (plain(c), buf.len());
    fill(&|_| f, false, false, 0, buf, &|g: &mut dyn FnMut(Seg)| cycle_walk(c.meta.n, off, i0, cnt, g))
}
/// structural.c:478 `shift_fill`: of `c` shifted by `k`, `fill` entering.
pub fn shift_fill(c: &Coc, k: i64, fill_v: i64, buf: &mut [i64], i0: usize) {
    let (f, cnt) = (plain(c), buf.len());
    fill(&|_| f, false, false, fill_v, buf, &|g: &mut dyn FnMut(Seg)| shift_walk(c.meta.n, k, i0, cnt, g))
}
/// structural.c:483 `cat_fill`: of the parts `part(j)` starting at `start[j]`; `start` holds the part count + 1
/// entries, the last the answer's count. `w` is the element width, which only the take step asks.
pub fn cat_fill<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], _w: usize, alp: bool, buf: &mut [i64], i0: usize) {
    let cnt = buf.len();
    fill(part, alp, false, 0, buf, &|g: &mut dyn FnMut(Seg)| cat_walk(start, i0, cnt, g))
}
/// structural.c:491 `alp_run`: the elements' IEEE bits (what the writer's ALP steps read back at `w` bytes) of
/// elements `lo .. lo + out.len()` of block `b`, restored exceptions included; only the run is restored.
pub fn alp_run(out: &mut [i64], f: &Cocf, b: usize, lo: usize, rev: bool) {
    let (len, mut tmp, mut lb) = (out.len(), [0u64; BLK], [0u64; BLK]);
    let (p, w, _) = f.lanes(b, lo + len, pod::bytes_mut(&mut lb));
    let tb = pod::bytes_mut(&mut tmp);
    f.load_range(b, p, w, lo, lo + len, tb);
    let tb: &[u8] = tb;
    for i in 0..len {
        let v = if f.f32 { u32::from_ne_bytes(tb[4 * (lo + i)..4 * (lo + i) + 4].try_into().unwrap()) as i64 }
                else { i64::from_ne_bytes(tb[8 * (lo + i)..8 * (lo + i) + 8].try_into().unwrap()) };
        out[if rev { len - 1 - i } else { i }] = v;
    }
}
/// structural.c:511 `cat_fill_alp`
pub fn cat_fill_alp<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], w: usize, buf: &mut [i64], i0: usize) {
    cat_fill(part, start, w, true, buf, i0)
}
/// structural.c:516 `rev_fill_alp`
pub fn rev_fill_alp(f: &Cocf, buf: &mut [i64], i0: usize) {
    let cnt = buf.len();
    fill(&|_| *f, true, true, 0, buf, &|g: &mut dyn FnMut(Seg)| rev_walk(f.c.meta.n, i0, cnt, g))
}
/// structural.c:521 `cycle_fill_alp`
pub fn cycle_fill_alp(f: &Cocf, off: usize, _m: usize, buf: &mut [i64], i0: usize) {
    let cnt = buf.len();
    fill(&|_| *f, true, false, 0, buf, &|g: &mut dyn FnMut(Seg)| cycle_walk(f.c.meta.n, off, i0, cnt, g))
}
/// structural.c:527 `shift_fill_alp`; `fill_v` is the hole's bits (the stub had no such parameter, C's `x->fill`).
pub fn shift_fill_alp(f: &Cocf, k: i64, fill_v: i64, buf: &mut [i64], i0: usize) {
    let cnt = buf.len();
    fill(&|_| *f, true, false, fill_v, buf, &|g: &mut dyn FnMut(Seg)| shift_walk(f.c.meta.n, k, i0, cnt, g))
}

/// structural.c:543 `HINT_RUN`: the largest exponent among the source blocks answer block is drawn from, and their
/// exceptions: every element exact at its own block's exponent is exact at the largest one short of `2^53`, which
/// `alp_meta_at`'s re-check catches. A shift's hole is `fill`, which may be `0n` and so an exception at any exponent;
/// it is counted as one, the re-check holding the answer to the real count.
fn hint<'a>(part: &dyn Fn(usize) -> Cocf<'a>, lim: &mut u32, walk: Walk) -> i32 {
    let mut e = -1;
    *lim = 0;
    walk(&mut |s| match s {
        Seg::Run { p, b, .. } => { let f = part(p); e = e.max(f.exp[b] as i32); *lim += f.exc_off[b + 1] - f.exc_off[b] }
        Seg::Hole { len, .. } => *lim += len as u32,
    });
    e
}
/// structural.c:543 `cat_hint`: answer block `b`'s exponent hint and patch limit `lim`; -1 = no hint.
pub fn cat_hint<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], b: usize, lim: &mut u32) -> i32 {
    let (s, n) = (b * BLK, start[start.len() - 1]);
    hint(part, lim, &|g: &mut dyn FnMut(Seg)| cat_walk(start, s, (n - s).min(BLK), g))
}
/// structural.c:555 `rev_hint`
pub fn rev_hint(f: &Cocf, b: usize, lim: &mut u32) -> i32 {
    hint(&|_| *f, lim, &|g: &mut dyn FnMut(Seg)| rev_walk(f.c.meta.n, b * BLK, blk_count(f.c.meta.n, b), g))
}
/// structural.c:563 `cycle_hint`: `m` is the answer's count.
pub fn cycle_hint(f: &Cocf, off: usize, m: usize, b: usize, lim: &mut u32) -> i32 {
    hint(&|_| *f, lim, &|g: &mut dyn FnMut(Seg)| cycle_walk(f.c.meta.n, off, b * BLK, blk_count(m, b), g))
}
/// structural.c:572 `shift_hint`
pub fn shift_hint(f: &Cocf, k: i64, b: usize, lim: &mut u32) -> i32 {
    hint(&|_| *f, lim, &|g: &mut dyn FnMut(Seg)| shift_walk(f.c.meta.n, k, b * BLK, blk_count(f.c.meta.n, b), g))
}

/// The writer's second form of an answer block, `coc_ints`'s outputs: the decimals `d`, `ee[i] < 0` at each exception
/// and, with `raw`, `raw[i]` the address of its bits (in a source's patch list, or the hole's).
pub struct Ints<'b> { pub d: &'b mut [i64], pub ee: &'b mut [i8], pub raw: Option<&'b mut [*const u8]> }
/// structural.c:584 `alp_ints_run`: decimals `d` and `ee` of elements `lo ..` of block `s` (reversed when `rev`),
/// each source exception carried to its place in the answer.
pub fn alp_ints_run(d: &mut [i64], ee: &mut [i8], mut raw: Option<&mut [*const u8]>, f: &Cocf, s: usize, lo: usize, rev: bool) {
    let len = d.len();
    unpack_run(d, &f.c, s, lo, rev);
    ee.fill(0);
    let esz = if f.f32 { 4 } else { 8 };
    for j in f.exc_off[s] as usize..f.exc_off[s + 1] as usize {
        let p = f.exc_pos[j] as usize;
        if p < lo || p >= lo + len { continue }
        let i = if rev { lo + len - 1 - p } else { p - lo };
        ee[i] = -1;
        if let Some(r) = raw.as_deref_mut() { r[i] = f.exc_raw[j * esz..].as_ptr() }
    }
}
/// Pass 1 of a verb's `coc_ints`: the one exponent the source blocks hold, -1 where they differ or there are none.
fn ints_exp<'a>(part: &dyn Fn(usize) -> Cocf<'a>, walk: Walk) -> i32 {
    let (mut e, mut one) = (-1, true);
    walk(&mut |s| if let Seg::Run { p, b, .. } = s {
        let x = part(p).exp[b] as i32;
        if e < 0 { e = x } else if e != x { one = false }
    });
    if one { e } else { -1 }
}
/// Pass 2: the integers at that exponent, a hole being `hole` = (its integer, its `ee`, the address of its bits).
fn ints_fill<'a>(part: &dyn Fn(usize) -> Cocf<'a>, rev: bool, hole: (i64, i8, *const u8), out: &mut Ints, walk: Walk) {
    walk(&mut |s| match s {
        Seg::Run { p, b, lo, len, at } => alp_ints_run(&mut out.d[at..at + len], &mut out.ee[at..at + len],
            out.raw.as_deref_mut().map(|r| &mut r[at..at + len]), &part(p), b, lo, rev),
        Seg::Hole { at, len } => for z in at..at + len {
            out.d[z] = hole.0; out.ee[z] = hole.1;
            if let Some(r) = out.raw.as_deref_mut() { r[z] = hole.2 }
        },
    })
}
/// The verbs with no hole: both passes, the second only with `out`; the exponent, -1 = the general path.
fn ints<'a>(part: &dyn Fn(usize) -> Cocf<'a>, rev: bool, out: Option<&mut Ints>, walk: Walk) -> i32 {
    let e = ints_exp(part, walk);
    if let (Some(o), true) = (out, e >= 0) { ints_fill(part, rev, (0, 0, core::ptr::null()), o, walk) }
    e
}
/// structural.c:602 `cat_ints`: answer block `b` of the concat as decimals; -1 = take the general path.
pub fn cat_ints<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], b: usize, out: Option<&mut Ints>) -> i32 {
    let (s, n) = (b * BLK, start[start.len() - 1]);
    ints(part, false, out, &|g: &mut dyn FnMut(Seg)| cat_walk(start, s, (n - s).min(BLK), g))
}
/// structural.c:612 `rev_ints`
pub fn rev_ints(f: &Cocf, b: usize, out: Option<&mut Ints>) -> i32 {
    ints(&|_| *f, true, out, &|g: &mut dyn FnMut(Seg)| rev_walk(f.c.meta.n, b * BLK, blk_count(f.c.meta.n, b), g))
}
/// structural.c:622 `cycle_ints`: `m` is the answer's count.
pub fn cycle_ints(f: &Cocf, off: usize, m: usize, b: usize, out: Option<&mut Ints>) -> i32 {
    ints(&|_| *f, false, out, &|g: &mut dyn FnMut(Seg)| cycle_walk(f.c.meta.n, off, b * BLK, blk_count(m, b), g))
}
/// structural.c:635 `shift_ints`' pass 1. The hole's integer needs `dat` (A9), so C computes it from this exponent
/// and calls `shift_ints` for pass 2.
pub fn shift_exp(f: &Cocf, k: i64, b: usize) -> i32 {
    ints_exp(&|_| *f, &|g: &mut dyn FnMut(Seg)| shift_walk(f.c.meta.n, k, b * BLK, blk_count(f.c.meta.n, b), g))
}
/// structural.c:635 `shift_ints`' pass 2: a hole is `hole` = (`fill`'s integer at the exponent, its `ee`, `&fill`).
pub fn shift_ints(f: &Cocf, k: i64, b: usize, hole: (i64, i8, *const u8), out: &mut Ints) {
    ints_fill(&|_| *f, false, hole, out, &|g: &mut dyn FnMut(Seg)| shift_walk(f.c.meta.n, k, b * BLK, blk_count(f.c.meta.n, b), g))
}

/// structural.c `shift_ints`: both passes of a shift's `coc_ints`. A hole is `fill`, its integer at the exponent where it is
/// exact there and an exception holding its bits where not (the low four bytes of `fill` at a real, as the fill's own
/// narrowing reads them); `dat` leaves the integer alone where it refuses, so that is 0.
pub fn shift_ints_at(f: &Cocf, k: i64, fill: &i64, b: usize, out: Option<&mut Ints>) -> i32 {
    let e = shift_exp(f, k, b);
    let Some(out) = out.filter(|_| e >= 0) else { return e };
    let (mut d, mut ok) = ([0i64], [0u8]);
    if f.f32 { crate::alp::dat_blk(&[f32::from_bits(*fill as u32)], e, &mut d, &mut ok) } else { crate::alp::dat_blk(&[f64::from_bits(*fill as u64)], e, &mut d, &mut ok) }
    let (hd, hx) = if ok[0] != 0 { (d[0], 0) } else { (0, -1) };
    shift_ints(f, k, b, (hd, hx, core::ptr::from_ref(fill).cast()), out);
    e
}
// ---- A36: structural.c:684-760 (the rest of the concat entries is Lean glue) ----
/// structural.c:684 `cat_take`: the part holding block `b` and its block there.
pub fn cat_take(start: &[usize], b: usize) -> Option<(usize, usize)> {
    let k = start.len().checked_sub(1).filter(|&k| k > 0)?;
    let (s, n) = (b * BLK, start[k]);
    let (mut pi, mut hi) = (0, k);
    while pi + 1 < hi { let mid = (pi + hi) / 2; if start[mid] <= s { pi = mid } else { hi = mid } }
    let j = s - start[pi];
    if j % BLK != 0 || (s + BLK).min(n) > start[pi + 1] { return None }
    Some((pi, j / BLK))
}
/// structural.c:699 `cat_take`'s test of the part itself: a part moves whole only in the writer's trailer, and a plain
/// one only when its patch list's elements are the answer's width.
pub fn cat_part_ok(c: &Coc, w: usize, alp: bool) -> bool {
    trailer_ok(c, c.meta.n, w, alp) && (alp || c.exc.is_none_or(|x| x.pos.is_empty() || x.esz == w))
}
/// structural.c:704 `put_res`: `v` minus `base` at `w` bits into `p` from field `lo`.
pub fn put_res(p: &mut [u8], w: u8, lo: usize, v: &[i64], base: u64) {
    match w {
        0 => {}      // every element of the block is the base, and only those were let through
        8 | 16 | 32 | 64 => {
            let k = w as usize / 8;
            for (o, &x) in p[lo * k..].chunks_exact_mut(k).zip(v) { o.copy_from_slice(&(x as u64).wrapping_sub(base).to_le_bytes()[..k]) }
        }
        _ => for (j, &x) in v.iter().enumerate() { crate::res::res_put(p, w, lo + j, (x as u64).wrapping_sub(base)) },
    }
}

// ---- K23: structural.c `fsc_*`, `fsx_check`: scatter into an encoded column ----
/// `scatterFoR` and `scatterALP`, one engine for both encodings, because the block is what they share: a block no index
/// lands in keeps its metadata entries, residual bytes, exponent and exceptions as they are (`move_meta`, `move_pack`); a
/// block some index lands in is decoded, written and handed to the writer's block steps for its encoding. The kept
/// entries are only kept when the block sums were taken the way the writer takes them (`coc_sumnul`, `sumn`), and a
/// Frame of Reference patch list at another element width is not copied; either one re-encodes every block instead.
pub struct Scatter<'a> {
    old: Cocf<'a>, alp: bool, w: usize, keep: bool, ix: &'a [u64], vals: &'a [u8],
    /// block `b`'s writes are `ix[at[b] .. at[b + 1]]`; written once each by the slice that holds the first index of `b`
    at: Vec<AtomicUsize>,
    /// ALP: pass 1 kept the old exponent and patched the block, so pass 2 takes the same road
    patched: Vec<AtomicU8>,
}
fn die(args: core::fmt::Arguments) -> ! {
    crate::os::eprint(args).expect("qlean: stderr");
    crate::os::exit(1)
}
/// structural.c `fsx_check`: the checks and block cursors in one pass off the pool. The first offending position is the
/// least one any slice saw, which is the one a serial loop reports, and since `ix` ascends, the blocks from just past
/// `ix[k - 1]`'s up to `ix[k]`'s are exactly those whose first index is `k`, so each cursor is written once, by the slice
/// holding that `k`, and no count is taken. `Err(k)` = `ix[k]` is not ascending, distinct and below `n`.
fn cursors(run: Runner, ix: &[u64], n: usize, nblk: usize) -> Result<Vec<AtomicUsize>, usize> {
    let m = ix.len();
    let at: Vec<AtomicUsize> = (0..n.div_ceil(BLK).max(nblk) + 1).map(|_| AtomicUsize::new(0)).collect();
    let bad = AtomicUsize::new(m);
    crate::c::run_map(run, &mut [], m, 0, crate::QLEAN_COST_COPY, 16, &|lo, hi, _: &mut [u8]| {
        for k in lo..hi {
            if ix[k] >= n as u64 || (k > 0 && ix[k] <= ix[k - 1]) { bad.fetch_min(k, SeqCst); return }
            for b in (if k > 0 { ix[k - 1] / BLK as u64 + 1 } else { 0 })..=ix[k] / BLK as u64 { at[b as usize].store(k, Relaxed) }
        }
    });
    let bad = bad.into_inner();
    if bad < m { return Err(bad) }
    for b in (if m > 0 { ix[m - 1] as usize / BLK + 1 } else { 0 })..=nblk { at[b].store(m, Relaxed) }
    Ok(at)
}
/// Block `b`'s writes into a decoded block: `W`-byte values at the positions `ix` names.
fn put_vals<const W: usize>(out: &mut [u8], b: usize, ix: &[u64], vals: &[u8]) {
    let (o, v) = (out.as_chunks_mut::<W>().0, vals.as_chunks::<W>().0);
    for (&i, &x) in ix.iter().zip(v) { o[i as usize - b * BLK] = x }
}
impl<'a> Scatter<'a> {
    /// structural.c `fsc_scatter`'s views and refusals: metadata `m`, pack `pk`, the ALP part `a` for an ALP column, `n`
    /// elements of `w` bytes, the ascending distinct indices `ix` (`amendCompact`'s `u`) and their `w`-byte `vals`.
    /// A refusal names itself and exits, as the C did.
    pub fn new(run: Runner, w: usize, m: &'a [u8], pk: &'a [u8], a: Option<&'a [u8]>, n: usize, ix: &'a [u8], vals: &'a [u8]) -> Self {
        let alp = a.is_some();
        let old = match a {
            Some(a) => {
                let mut f = Cocf::meta_view(m, a, n).expect("qlean scatter: the ALP sections are misaligned or short");
                f.c.pack = pk;
                f
            }
            None => {
                let meta = crate::coc::Meta::new(m, n).expect("qlean scatter: the metadata is misaligned or short");
                plain(&Coc::attach(meta, pk).unwrap_or_else(|| die(format_args!(
                    "qlean: a Frame of Reference pack of {} bytes whose residuals end at {} holds no patch list of {} blocks after them\n",
                    pk.len(), meta.res_end(), meta.mblk))))
            }
        };
        if if alp { (w != 4 && w != 8) || (w == 4) != old.f32 } else { w != 2 && w != 4 && w != 8 } {
            die(format_args!("qlean scatter{}: element width {w} is not one this encoding holds\n", if alp { "ALP" } else { "FoR" }))
        }
        let ix = pod::cast::<u64>(&ix[..ix.len() / 8 * 8]).expect("qlean scatter: the index vector is misaligned");
        let nw = ix.len();
        if vals.len() < nw * w { die(format_args!("qlean scatter: {nw} values of {w} bytes asked of {} bytes\n", vals.len())) }
        let at = cursors(run, ix, n, old.c.meta.nblk).unwrap_or_else(|k| die(format_args!(
            "qlean scatter: index {} at {k} is not ascending, distinct and below {n}\n", ix[k])));
        let c = &old.c;
        let keep = c.meta.sumnul == crate::enc::coc_sumnul(w, alp) && c.meta.sumn == n as u64 && c.exc.is_none_or(|e| e.pos.is_empty() || e.esz == w);
        let patched = (0..if alp { c.meta.nblk } else { 0 }).map(|_| AtomicU8::new(0)).collect();
        Scatter { old, alp, w, keep, ix, vals, at, patched }
    }
    /// A block no index lands in, whose old entries are the new ones.
    pub fn kept(&self, b: usize) -> bool { self.keep && self.span(b).is_empty() }
    fn span(&self, b: usize) -> core::ops::Range<usize> { self.at[b].load(Relaxed)..self.at[b + 1].load(Relaxed) }
    fn nb(&self, b: usize) -> usize { blk_count(self.old.c.meta.n, b) }
    /// structural.c `fsc_load`: block `b` decoded at `w` bytes an element into `out` (8-aligned), its writes applied.
    fn load(&self, b: usize, nb: usize, out: &mut [u8]) {
        if self.alp { self.old.load_blk(b, nb, out) } else { load_blk_at(&self.old.c, b, nb, self.w, out) }
        let r = self.span(b);
        let (ix, v) = (&self.ix[r.clone()], &self.vals[r.start * self.w..r.end * self.w]);
        match self.w { 2 => put_vals::<2>(out, b, ix, v), 4 => put_vals::<4>(out, b, ix, v), _ => put_vals::<8>(out, b, ix, v) }
    }
    /// Block `b`'s writes: the positions and the floats.
    fn writes<F: Flt>(&self, b: usize) -> (&[u64], &[F]) {
        let r = self.span(b);
        (&self.ix[r.clone()], pod::cast::<F>(&self.vals[r.start * self.w..r.end * self.w]).expect("qlean scatter: the values are misaligned"))
    }
    /// structural.c `fsc_patch`: pass 1's integers with the writes at the block's OLD exponent (`alp_patch_blk`).
    fn patch<F: Flt>(&self, b: usize, nb: usize, d: &mut [i64], ee: &mut [i8]) -> i32 {
        let (ix, v) = self.writes::<F>(b);
        crate::alp::alp_patch_blk(&self.old, b, nb, ix, v, d, ee)
    }
    /// structural.c `fsc_meta` for block `b`: what the meta pass writes into `m`.
    pub fn meta(&self, m: &mut EncMeta, b: usize) {
        let nb = self.nb(b);
        if self.kept(b) { crate::enc::move_meta(m, &self.old, b); return }
        let mut buf = [0u64; BLK];
        if !self.alp {
            let bytes = pod::bytes_mut(&mut buf);
            self.load(b, nb, bytes);
            return crate::enc::for_meta(m, bytes, self.w, nb)
        }
        if self.w == 4 { self.meta_alp::<f32>(m, b, nb, &mut buf) } else { self.meta_alp::<f64>(m, b, nb, &mut buf) }
    }
    /// An ALP block with writes: the patch, unless the search's exponent leaves fewer exceptions; each costs its raw bytes
    /// and a position, more than the residual bits a higher exponent adds.
    fn meta_alp<F: Flt>(&self, m: &mut EncMeta, b: usize, nb: usize, buf: &mut [u64; BLK]) {
        let (mut d, mut ee) = ([0i64; BLK], [0i8; BLK]);
        let alt = self.patch::<F>(b, nb, &mut d, &mut ee);
        let np = ee[..nb].iter().filter(|&&e| e < 0).count() as u32;
        self.patched[b].store(1, Relaxed);
        if alt >= 0 {
            let bytes = pod::bytes_mut(buf);
            self.load(b, nb, bytes);
            let x = pod::cast::<F>(&bytes[..nb * self.w]).expect("qlean scatter: the block buffer is misaligned");
            if crate::alp::alp_exc_at(x, alt, np) < np {
                self.patched[b].store(0, Relaxed);
                *m.nexc = crate::alp::alp_meta_exp(m, x, nb, alt);
                return;
            }
        }
        *m.nexc = crate::alp::alp_fin_blk(m, self.old.exp[b] as i32, &mut d, &ee, nb);
    }
    /// structural.c `fsc_pack` for block `b`; `p` is cut whole (`BLK * width / 8` residual bytes) when `kept(b)`.
    pub fn pack(&self, p: &mut EncPack, b: usize) {
        let nb = self.nb(b);
        if self.kept(b) { crate::enc::move_pack(p, &self.old, b, self.alp, self.w); return }
        if self.alp && self.patched[b].load(Relaxed) != 0 {
            return if self.w == 4 { self.pack_patched::<f32>(p, b, nb) } else { self.pack_patched::<f64>(p, b, nb) }
        }
        let mut buf = [0u64; BLK];
        let bytes = pod::bytes_mut(&mut buf);
        self.load(b, nb, bytes);
        if self.alp { crate::enc::alp_pack(p, bytes, self.w) } else { crate::enc::for_pack(p, bytes, self.w) }
    }
    /// Pass 2 for a block pass 1 patched at the old exponent, with the same writes.
    fn pack_patched<F: Flt>(&self, p: &mut EncPack, b: usize, nb: usize) {
        let (mut d, mut ee) = ([0i64; BLK], [0i8; BLK]);
        self.patch::<F>(b, nb, &mut d, &mut ee);
        let (ix, v) = self.writes::<F>(b);
        let raw = core::mem::take(&mut p.raw);
        crate::alp::alp_patch_pack(p, &self.old, ix, v, &mut d, &ee, pod::cast_mut::<F>(raw).expect("qlean scatter: misaligned patch bits"))
    }
}

#[cfg(test)]
mod k23_tests {
    use super::*;
    use crate::c::qlean_run_c;
    fn at(ix: &[u64], n: usize) -> Result<Vec<usize>, usize> {
        cursors(qlean_run_c, ix, n, n.div_ceil(BLK)).map(|v| v.iter().map(|a| a.load(Relaxed)).collect())
    }
    // Expected values come from running the original C (`fsx_check` and its tail loop, /data/tmp/qrs/K23/diff.c)
    #[test] fn cursors_start_each_block_at_its_first_index() {
        // block 0 holds indices 0, 5 (positions 0, 1); block 1 holds 1024 (2); block 2 holds 3000 (3); block 3 has none
        assert_eq!(at(&[0, 5, 1024, 3000], 4000), Ok(vec![0, 2, 3, 4, 4]));
        assert_eq!(at(&[], 2000), Ok(vec![0, 0, 0]));
    }
    #[test] fn cursors_name_the_first_offender() {
        assert_eq!(at(&[3, 3], 4000), Err(1));
        assert_eq!(at(&[2, 9, 8, 7], 4000), Err(2));
        assert_eq!(at(&[0, 4000], 4000), Err(1));
    }
}

// ---- A37: structural.c:594-830 ----
/// `(T)v` of structural.c's kernels: the low `W` bytes of `v`, zero-extended past 8.
fn word<const W: usize>(v: u64) -> [u8; W] { let b = v.to_le_bytes(); core::array::from_fn(|k| if k < 8 { b[k] } else { 0 }) }
/// structural.c's `WIDTHS`: the kernels exist at these element widths only, and say so before any worker starts.
fn check_w(w: usize, who: &str) {
    assert!(matches!(w, 1 | 2 | 4 | 8 | 16),
            "qlean structural: {who} got element width {w}; the kernels are instantiated at 1, 2, 4, 8 and 16 bytes");
}
/// The entry's refusal for an encoded source: besides `check_w`, a column whose blocks disagree (`one_width` 255) has
/// no 16-byte reader. Said here, before any worker starts, as `check_w` does.
fn check_enc(w: usize, sw: u8, who: &str) {
    check_w(w, who);
    assert!(!(sw == 255 && w == 16), "qlean structural: {who} of an encoded column with unequal blocks has no width-16 reader");
}
/// structural.c `GATHER_DECODE`: indices in one block in a row that make decoding the block cheaper than reading each.
const GATHER_DECODE: usize = crate::BLK / 8;
/// structural.c `GATHER_AHEAD`: how far ahead of the index being read the source is prefetched.
const GATHER_AHEAD: usize = 16;
/// structural.c:619 `qlean_structural_all_below`: every index, read unsigned, is below `n`.
pub fn all_below(n: usize, idx: &[i64]) -> bool { idx.is_empty() || idx.iter().fold(0u64, |m, &x| m.max(x as u64)) < n as u64 }
// One unsigned compare rejects all three of q's misses (past the end, negative, `0N` = 2^63 unsigned), as `get` does.
fn gather_w<const W: usize>(run: Runner, fill: u64, src: &[u8], idx: &[i64], out: &mut [u8]) {
    let (sc, f) = (src.as_chunks::<W>().0, word::<W>(fill));
    crate::c::run_map(run, out, idx.len(), W, crate::QLEAN_COST_GATHER, W + 8, &|lo, hi, o: &mut [u8]| {
        for (d, &i) in o.as_chunks_mut::<W>().0.iter_mut().zip(&idx[lo..hi]) { *d = sc.get(i as usize).copied().unwrap_or(f) }
    });
}
/// structural.c:609 `gather_run` and its entry: `src[idx[i]]` (`w` bytes) into `out`, `fill` out of range. `idx.len()`
/// is the slicing unit and `w + 8` its cost: the index is read as well as the element, so the element alone left a
/// million-element gather under the threshold and on one thread.
pub fn gather(run: Runner, w: usize, fill: u64, src: &[u8], idx: &[i64], out: &mut [u8]) {
    check_w(w, "gather");
    match w {
        1 => gather_w::<1>(run, fill, src, idx, out),
        2 => gather_w::<2>(run, fill, src, idx, out),
        4 => gather_w::<4>(run, fill, src, idx, out),
        8 => gather_w::<8>(run, fill, src, idx, out),
        _ => gather_w::<16>(run, fill, src, idx, out),
    }
}
/// coc.h `coc_load_blk_at`: block `b`'s first `nb` elements decoded at `w` bytes (4 and below, else 8) into `out`.
fn load_blk_at(c: &Coc, b: usize, nb: usize, w: usize, out: &mut [u8]) {
    match w {
        1 => c.decode_blk::<u8>(b, nb, out),
        2 => c.decode_blk::<i16>(b, nb, crate::pod::cast_mut(out).expect("load_blk_at: the buffer is not aligned for the width")),
        4 => c.decode_blk::<i32>(b, nb, crate::pod::cast_mut(out).expect("load_blk_at: the buffer is not aligned for the width")),
        _ => c.decode_blk::<i64>(b, nb, crate::pod::cast_mut(out).expect("load_blk_at: the buffer is not aligned for the width")),
    }
}
// One width for the whole column makes the pack a flat array of residuals, so `u * width / 8` is the address and the
// block structure cancels out of it: one scaled index plus the block's base, which stays in L1.
fn flat<const W: usize>(c: &Coc, sw: u8, f: [u8; W], ix: &[i64], o: &mut [u8], rd: impl Fn(usize) -> u64) {
    let sn = c.meta.n as u64;
    for (j, (d, &i)) in o.as_chunks_mut::<W>().0.iter_mut().zip(ix).enumerate() {
        // `coc_prefetch`'s reason at the flat address; a wild one is skipped, where C's is a hint that never faults
        if let Some(&a) = ix.get(j + GATHER_AHEAD) {
            if let Some(r) = c.pack.get(((a as u64).wrapping_mul(sw as u64) >> 3) as usize) { crate::simd::prefetch(r) }
        }
        let u = i as u64;
        *d = if u < sn { word(rd(u as usize)) } else { f };
    }
}
// A column whose blocks disagree, or that carries a patch list, has no flat form: a run of indices in one block that
// is `GATHER_DECODE` long decodes the block once, a shorter one is read through `get`.
fn runs<const W: usize>(c: &Coc, f: [u8; W], ix: &[i64], o: &mut [u8]) {
    let sn = c.meta.n;
    let mut buf = [0u64; crate::BLK];
    let bb = crate::pod::bytes_mut(&mut buf);
    let d = o.as_chunks_mut::<W>().0;
    let mut j = 0;
    while j < ix.len() {
        let u0 = ix[j] as u64;
        if u0 >= sn as u64 { d[j] = f; j += 1; continue }
        let (b, blo) = (u0 as usize / crate::BLK, u0 as usize / crate::BLK * crate::BLK);
        let mut e = j + 1;
        while e < ix.len() && ix[e] as u64 / crate::BLK as u64 == b as u64 { e += 1 }
        if e - j < GATHER_DECODE {
            for k in j..e {
                if let Some(&a) = ix.get(k + GATHER_AHEAD) { c.prefetch(a as usize) }
                let u = ix[k] as u64;
                d[k] = if u < sn as u64 { word(c.get(u as usize) as u64) } else { f };
            }
        } else {
            load_blk_at(c, b, (sn - blo).min(crate::BLK), W, bb);
            for k in j..e {
                let u = ix[k] as u64;
                d[k] = if u < sn as u64 { bb[(u as usize - blo) * W..][..W].try_into().unwrap() } else { f };
            }
        }
        j = e;
    }
}
// One slice of `gather_enc`: `sw` is the source's one width, decided by the entry once rather than per slice.
fn enc_w<const W: usize>(c: &Coc, sw: u8, fill: u64, ix: &[i64], o: &mut [u8]) {
    let f = word::<W>(fill);
    let (sb, sp) = (c.meta.base, c.pack);
    let base = |u: usize| sb[u / crate::BLK] as u64;
    let at = |k: usize, n: usize| &sp[k..k + n];
    match sw {
        0 => flat(c, sw, f, ix, o, base),
        1 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add((sp[u >> 3] >> (u & 7) & 1) as u64)),
        2 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add((sp[u >> 2] >> ((u & 3) * 2) & 3) as u64)),
        4 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add((sp[u >> 1] >> ((u & 1) * 4) & 15) as u64)),
        8 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(sp[u] as u64)),
        16 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(u16::from_ne_bytes(at(2 * u, 2).try_into().unwrap()) as u64)),
        32 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(u32::from_ne_bytes(at(4 * u, 4).try_into().unwrap()) as u64)),
        64 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(u64::from_ne_bytes(at(8 * u, 8).try_into().unwrap()))),
        // `check_enc` refused width 16 here at the entry: coc.h `coc_load_blk_at` decodes at 8 bytes, which C misreads as a `u128`
        255 if W <= 8 => runs(c, f, ix, o),
        255 => unreachable!("an unequal-blocks gather at width {W} is refused at the entry"),
        _ => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(crate::res::res_get_in(sp, sw, u, sp.len()))),
    }
}
fn enc(w: usize, c: &Coc, sw: u8, fill: u64, ix: &[i64], o: &mut [u8]) {
    match w {
        1 => enc_w::<1>(c, sw, fill, ix, o),
        2 => enc_w::<2>(c, sw, fill, ix, o),
        4 => enc_w::<4>(c, sw, fill, ix, o),
        8 => enc_w::<8>(c, sw, fill, ix, o),
        _ => enc_w::<16>(c, sw, fill, ix, o),
    }
}
/// structural.c:728 `gather_foR_run` and its entry: from an encoded column, which a gather reads only where its index
/// points, so the source is never decoded whole.
pub fn gather_enc(run: Runner, w: usize, fill: u64, c: &Coc, idx: &[i64], out: &mut [u8]) {
    let sw = c.one_width();
    check_enc(w, sw, "gather_foR");
    crate::c::run_map(run, out, idx.len(), w, crate::QLEAN_COST_GATHER, w + 8,
                      &|lo, hi, o: &mut [u8]| enc(w, c, sw, fill, &idx[lo..hi], o));
}
/// structural.c:767 `gather_foR_idx_run`: encoded column, encoded indices (`ic.meta.n` of them, `count` cut to the
/// grid), the index decoded a block at a time and never whole.
pub fn gather_enc_idx(run: Runner, w: usize, fill: u64, c: &Coc, ic: &Coc, out: &mut [u8]) {
    let sw = c.one_width();
    check_enc(w, sw, "gather_foR");
    crate::c::run_map(run, out, ic.meta.n, w, crate::QLEAN_COST_GATHER, w + 8, &|lo, hi, o: &mut [u8]| {
        let mut buf = [0i64; crate::BLK];
        let mut at = lo;
        while at < hi {
            let blo = at / crate::BLK * crate::BLK;
            let end = (blo + crate::BLK).min(hi);
            ic.decode_blk(at / crate::BLK, end - blo, &mut buf);
            enc(w, c, sw, fill, &buf[at - blo..end - blo], &mut o[(at - lo) * w..(end - lo) * w]);
            at = end;
        }
    });
}
/// structural.c:805 `gather_bits_run` and its entry: bit `j` of `out` is bit `idx[j]` of `bits`, `0` for a miss. The unit
/// is an output byte (`out` arrives zeroed): two slices sharing a byte would lose each other's bits.
pub fn gather_bits(run: Runner, n: usize, bits: &[u8], idx: &[i64], out: &mut [u8]) {
    let hit = |&i: &i64| (i as u64) < n as u64 && bits.get((i as u64 >> 3) as usize).is_some_and(|b| b >> (i & 7) & 1 == 1);
    crate::c::run_map(run, out, idx.len().div_ceil(8), 1, crate::QLEAN_COST_GATHER, 64, &|lo, _, o: &mut [u8]| {
        for (d, ch) in o.iter_mut().zip(idx[lo * 8..].chunks(8)) {
            *d |= ch.iter().enumerate().fold(0u8, |a, (k, i)| a | (hit(i) as u8) << k)
        }
    });
}

// ---- A38: structural.c:1278-1608 ----
// One width of `expand`: `fill` is the C's `(T)fill`, its low `W` bytes (zero-extended past 8).
fn expand_w<const W: usize>(run: Runner, fill: u64, src: &[u8], at: &[usize], out: &mut [u8]) {
    let (k, m, ns) = (at.len() - 1, at[at.len() - 1], src.len() / W);
    let (mut f, fb) = ([0u8; W], fill.to_le_bytes());
    f[..W.min(8)].copy_from_slice(&fb[..W.min(8)]);
    // each slice bisects the prefix sums for the run its `lo` falls in, then walks forward: threaded over the answer
    crate::c::run_map(run, out, m, W, crate::QLEAN_COST_COPY, W, &|lo, hi, o: &mut [u8]| {
        let (mut g, mut gh) = (0, k);
        while g + 1 < gh { let mid = (g + gh) / 2; if at[mid] <= lo { g = mid } else { gh = mid } }
        let mut i = lo;
        while i < hi {
            while at[g + 1] <= i { g += 1 }
            let end = at[g + 1].min(hi);
            let v: [u8; W] = if g < ns { src[g * W..g * W + W].try_into().unwrap() } else { f };
            o[(i - lo) * W..(end - lo) * W].chunks_exact_mut(W).for_each(|c| c.copy_from_slice(&v));
            i = end;
        }
    });
}
/// structural.c:1278 `expand_run` and its entry: `src[i]` repeated `wv[i]` times (a negative count is none),
/// `fill` for a run past the end of `src`; `out` is the `Σ max(wv[i], 0)` elements of `w` bytes.
pub fn expand(run: Runner, w: usize, fill: u64, src: &[u8], wv: &[i64], out: &mut [u8]) {
    // sized up front: `scan` gives `collect` no length, so it grew the vector by doubling, copying it each time
    let mut at = alloc::vec::Vec::with_capacity(wv.len() + 1);
    at.push(0usize);
    wv.iter().fold(0usize, |t, &c| { let t = t + c.max(0) as usize; at.push(t); t });
    assert_eq!(out.len(), at[wv.len()] * w, "expand: {} output bytes for {} elements of {w} bytes", out.len(), at[wv.len()]);
    if at[wv.len()] == 0 { return }
    match w {
        1 => expand_w::<1>(run, fill, src, &at, out),
        2 => expand_w::<2>(run, fill, src, &at, out),
        4 => expand_w::<4>(run, fill, src, &at, out),
        8 => expand_w::<8>(run, fill, src, &at, out),
        16 => expand_w::<16>(run, fill, src, &at, out),
        _ => panic!("qlean structural: expand got element width {w}; the kernels are instantiated at 1, 2, 4, 8 and 16 bytes"),
    }
}
/// structural.c:1363 `qlean_structural_rows_of` past the unboxing: each little-endian `i64` of `b` as the boxed
/// word `lean_box` makes of it, into `out` (C passes `lean_array_cptr`); answers the count.
pub fn rows_of(b: &[u8], out: &mut [i64]) -> usize {
    let n = b.len() / 8;
    for (i, (c, o)) in b.chunks_exact(8).zip(out.iter_mut()).enumerate() {
        let u = u64::from_le_bytes(c.try_into().unwrap());
        if u >> 62 != 0 {
            panic!("qlean_structural_rows_of: row {i} is {u}, which no column is long enough to hold and no boxed natural can carry")
        }
        *o = (u << 1 | 1) as i64;
    }
    n
}
// A row past `s` (an unsigned compare: negative and `0N` too) is the empty symbol.
fn gathered<'a>(s: &Syms<'a>, u: i64) -> &'a [u8] { if (u as u64) < s.count() as u64 { s.at(u as usize) } else { &[] } }
/// structural.c:1381 `qlean_structural_gather_syms`: the gathered column's blob length, one NUL a symbol.
pub fn gather_syms_len(s: &Syms, idx: &[i64]) -> usize { idx.iter().map(|&u| gathered(s, u).len() + 1).sum() }
/// structural.c:1381: the gathered blob and its `idx.len() + 1` starts, written boxed as C's `lean_array_cptr` holds them.
pub fn gather_syms(s: &Syms, idx: &[i64], blob: &mut [u8], offs: &mut [usize]) {
    let (mut at, boxed) = (0, |at: usize| at << 1 | 1);
    offs[0] = boxed(0);
    for (j, &u) in idx.iter().enumerate() {
        let t = gathered(s, u);
        blob[at..at + t.len()].copy_from_slice(t);
        at += t.len();
        blob[at] = 0;
        at += 1;
        offs[j + 1] = boxed(at);
    }
}
// One id gathered: a miss (an unsigned compare folds past-the-end, negative and `0N`) is `fill`.
fn gathered_id(src: &[u8], w: u32, n: usize, fill: u64, u: i64) -> u64 {
    if (u as u64) < n as u64 { crate::ids::id_at(src, w, u as usize) as u64 } else { fill }
}
/// structural.c:1428 `gather_ids_run` and its entry: ids at `w` gathered to `wout` bits; `n` is the source count
/// (already cut to what `src` holds). Sliced on whole bytes of the answer, `slice_elems` elements to a unit.
pub fn gather_ids(run: Runner, w: u32, wout: u32, fill: u64, src: &[u8], n: usize, idx: &[i64], out: &mut [u8]) {
    let (g, m) = (crate::ids::slice_elems(wout), idx.len());
    crate::c::run_map(run, out, m.div_ceil(g), crate::ids::ids_bytes(g, wout), crate::QLEAN_COST_GATHER, g * 9,
                      &|lo, hi, o: &mut [u8]| {
        let (lo, hi) = (lo * g, (hi * g).min(m));
        for j in lo..hi { crate::ids::id_put(o, wout, j - lo, gathered_id(src, w, n, fill, idx[j])) }
    });
}
/// structural.c:1465 `gather_ids_foR_run`: encoded indices, `ic.meta.n` of them (`count`, cut to the grid).
pub fn gather_ids_enc(run: Runner, w: u32, wout: u32, fill: u64, src: &[u8], n: usize, ic: &Coc, out: &mut [u8]) {
    let (g, m) = (crate::ids::slice_elems(wout), ic.meta.n);
    crate::c::run_map(run, out, m.div_ceil(g), crate::ids::ids_bytes(g, wout), crate::QLEAN_COST_GATHER, g * 9,
                      &|lo8, hi8, o: &mut [u8]| {
        // a slice starts on a whole byte of the answer and each block of the index on a multiple of `BLK`
        let (lo, hi) = (lo8 * g, (hi8 * g).min(m));
        let mut v = [0i64; crate::BLK];
        let mut at = lo;
        while at < hi {
            let blo = at / crate::BLK * crate::BLK;
            let end = (blo + crate::BLK).min(hi);
            ic.decode_blk(at / crate::BLK, end - blo, &mut v);
            for j in at..end { crate::ids::id_put(o, wout, j - lo, gathered_id(src, w, n, fill, v[j - blo])) }
            at = end;
        }
    });
}
/// structural.c:1537 `qlean_structural_cycle_ids`: `m` fields of `ids` from `off`, cycling over `n`; `out` arrives zeroed.
pub fn cycle_ids(n: usize, off: usize, m: usize, w: u32, ids: &[u8], out: &mut [u8]) {
    // a payload shorter than the count claims leaves no lap to take, and the loop below would not end at `n = 0`
    if off >= n { return }
    let (mut done, mut si, w) = (0, off, w as usize);
    while done < m {
        let take = (n - si).min(m - done);
        crate::ids::bitcopy(out, done * w, ids, si * w, take * w);
        done += take;
        si += take;
        if si == n { si = 0 }
    }
}

// ---- A39: structural.c:1792-2008 ----
/// An enumerated element as an id: `0Nj` is `nullid`, a negative index reads `0`, any other is itself (`enum_ids`
/// finds the out-of-range first in the C entry).
fn enum_id(v: i64, nullid: usize) -> u64 { if v == i64::MIN { nullid as u64 } else { v.max(0) as u64 } }
/// structural.c:1792 `qlean_structural_cycle_bits`
pub fn cycle_bits(n: usize, off: usize, m: usize, b: &[u8], out: &mut [u8]) {
    if m == 0 || n == 0 { return }
    // a run of the source up to its end at a time, the read index wrapped once per lap rather than divided
    let (mut j, mut i) = (0, off % n);
    while j < m { let len = (m - j).min(n - i); copy_bits(out, j, b, i, len); j += len; i = 0 }
}
/// structural.c:1820 `concat_run` and its entry: the parts end to end into `out`.
pub fn concat(run: Runner, parts: &[&[u8]], out: &mut [u8]) {
    let k = parts.len();
    let at: alloc::vec::Vec<usize> = core::iter::once(0).chain(parts.iter().scan(0, |t, p| { *t += p.len(); Some(*t) })).collect();
    assert_eq!(out.len(), at[k], "concat: {} output bytes for {} bytes of parts", out.len(), at[k]);
    if k == 0 { return }
    // each slice bisects the start offsets for its first part, so a slice does not walk every lap of a cycle
    crate::c::run_map(run, out, at[k], 1, crate::QLEAN_COST_COPY, 1, &|lo, hi, o: &mut [u8]| {
        let (mut i, mut j) = (0, k);
        while j - i > 1 { let m = i + (j - i) / 2; if at[m] <= lo { i = m } else { j = m } }
        while i < k && at[i] < hi {
            let (s, e) = (at[i].max(lo), at[i + 1].min(hi));
            if s < e { o[s - lo..e - lo].copy_from_slice(&parts[i][s - at[i]..e - at[i]]) }
            i += 1;
        }
    });
}
/// structural.c:1863 `qlean_structural_concat_bits`: `counts[j]` bits of `parts[j]`.
pub fn concat_bits(counts: &[usize], parts: &[&[u8]], out: &mut [u8]) {
    let mut at = 0;
    for (&cn, p) in counts.iter().zip(parts) { copy_bits(out, at, p, 0, cn); at += cn }
}
/// structural.c:1885 `enum_at`: element `i` of a payload of `have` bytes per element.
pub fn enum_at(src: &[u8], have: usize, i: usize) -> i64 {
    if i >= have { 0 } else { i64::from_le_bytes(src[i * 8..i * 8 + 8].try_into().unwrap()) }
}
/// An element out of range of the domain `0 .. d`: neither `0Nj` nor an index below `d`.
fn enum_bad(v: i64, d: usize) -> bool { v != i64::MIN && (v < 0 || v as u64 >= d as u64) }
/// structural.c:1898 `qlean_structural_enum_ids`: values as ids into `0 .. d` at `w` bits, `nullid` outside; answers the
/// first element that is neither an index below `d` nor `0Nj` (`n` when every one is).
pub fn enum_ids(n: usize, d: usize, nullid: usize, w: u32, b: &[u8], out: &mut [u8]) -> usize {
    let mut bad = n;
    for i in 0..n {
        let v = enum_at(b, b.len() / 8, i);
        if bad == n && enum_bad(v, d) { bad = i }
        crate::ids::id_put(out, w, i, enum_id(v, nullid))
    }
    bad
}
/// structural.c:1924 `qlean_structural_enum_ids_for`: from an encoded column.
pub fn enum_ids_enc(n: usize, d: usize, nullid: usize, w: u32, c: &Coc, out: &mut [u8]) -> usize {
    let (mut v, mut bad) = ([0i64; crate::BLK], n);
    for b in 0..n.div_ceil(crate::BLK) {
        let (lo, nb) = (b * crate::BLK, crate::BLK.min(n - b * crate::BLK));
        c.decode_blk(b, nb, &mut v);
        for (i, &x) in v[..nb].iter().enumerate() {
            if bad == n && enum_bad(x, d) { bad = lo + i }
            crate::ids::id_put(out, w, lo + i, enum_id(x, nullid))
        }
    }
    bad
}
/// structural.c `ids_place`: `cn` ids at `w` bits from `pp`, each read through `tab` (`nm + 1` entries, the last `0`, so an id at or past `nm` reads `0` with no branch;
/// `None` reads each id as itself: a part whose dictionary is a prefix of the answer's), packed at `wout` into `out`
/// from field `at`. A part that lands byte aligned is packed straight into the answer; one that does not is packed
/// into its own buffer and then bit-copied, so no store crosses into the part before it.
pub fn ids_place(out: &mut [u8], at: usize, wout: u32, cn: usize, w: u32, pp: &[u8], tab: Option<&[usize]>, nm: usize) {
    // The source width is matched once, outside the loop. A whole-byte answer is written through `unpack`, which walks
    // the source a word at a time with no per-id bounds test (`id_at` at a running index has one); a sub-byte answer
    // packs a word of fields in a register.
    #[inline(always)]
    fn go<const W: u32>(dst: &mut [u8], wout: u32, cn: usize, pp: &[u8], val: impl Fn(usize) -> u64) {
        #[inline(always)]
        fn whole<const W: u32, const K: usize>(dst: &mut [u8], cn: usize, pp: &[u8], val: impl Fn(usize) -> u64) {
            crate::ids::unpack::<W, [u8; K]>(pp, &mut dst.as_chunks_mut::<K>().0[..cn], |_, e, v| *e = word::<K>(val(v)));
        }
        match wout {
            8 => whole::<W, 1>(dst, cn, pp, val), 16 => whole::<W, 2>(dst, cn, pp, val),
            32 => whole::<W, 4>(dst, cn, pp, val), 64 => whole::<W, 8>(dst, cn, pp, val),
            _ => crate::ids::pack(dst, wout, cn, |j| val(crate::ids::id_at(pp, W, j))),
        }
    }
    #[inline(always)]
    fn by<const W: u32>(dst: &mut [u8], wout: u32, cn: usize, pp: &[u8], tab: Option<&[usize]>, nm: usize) {
        match tab {
            Some(t) => { let t = &t[..=nm]; go::<W>(dst, wout, cn, pp, |i| t[i.min(nm)] as u64) }
            None => go::<W>(dst, wout, cn, pp, |i| if i < nm { i as u64 } else { 0 }),
        }
    }
    let put = |dst: &mut [u8]| match w {
        0 => by::<0>(dst, wout, cn, pp, tab, nm), 1 => by::<1>(dst, wout, cn, pp, tab, nm), 2 => by::<2>(dst, wout, cn, pp, tab, nm),
        4 => by::<4>(dst, wout, cn, pp, tab, nm), 8 => by::<8>(dst, wout, cn, pp, tab, nm), 16 => by::<16>(dst, wout, cn, pp, tab, nm),
        32 => by::<32>(dst, wout, cn, pp, tab, nm), _ => by::<64>(dst, wout, cn, pp, tab, nm),
    };
    if (at * wout as usize) & 7 == 0 {
        put(&mut out[at * wout as usize / 8..]);
    } else {
        let mut tmp = alloc::vec![0u8; crate::ids::ids_bytes(cn, wout) + 1];
        put(&mut tmp);
        crate::ids::bitcopy(out, at * wout as usize, &tmp, 0, cn * wout as usize);
    }
}
/// A part's renaming read out once into a dictionary-sized table (`remap_ids`' reason: `d` entries where the column is
/// millions, and the map's width stays out of the loop): the ids of `map` at `wout` bits, then a `0`.
fn remap_table(map: &[u8], wout: u32) -> alloc::vec::Vec<usize> {
    let nm = if wout == 0 { 0 } else { map.len() * 8 / wout as usize };
    let mut tab = alloc::vec![0usize; nm + 1];
    macro_rules! at { ($($w:literal)*) => { match wout { 0 => {} $($w => crate::ids::unpack::<$w, usize>(map, &mut tab[..nm], |_, e, v| *e = v),)* _ => crate::ids::unpack::<64, usize>(map, &mut tab[..nm], |_, e, v| *e = v) } } }
    at!(1 2 4 8 16 32);
    tab
}
/// structural.c `qlean_structural_concat_ids`: each part's ids through its map (`maps[i]` the ids of the renaming at
/// `wout` bits), laid end to end. `widths` and `maps` are reached with `!` in the specification and not zipped: a part
/// they do not reach is width `0` and the empty map, both of which answer id `0`.
pub fn concat_ids(wout: u32, counts: &[usize], widths: &[u32], maps: &[&[u8]], parts: &[&[u8]], out: &mut [u8]) {
    let k = counts.len().min(parts.len());
    let mut at = 0;
    for i in 0..k {
        // the part is read at the `cn` ids `counts` claims and the `w` `widths` claims; short of that it is zeros
        let w = widths.get(i).copied().unwrap_or(0);
        let need = crate::ids::ids_bytes(counts[i], w);
        let padded;
        let pp = if parts[i].len() >= need { parts[i] } else { padded = [parts[i], &alloc::vec![0u8; need - parts[i].len()]].concat(); &padded[..] };
        let tab = remap_table(maps.get(i).copied().unwrap_or(&[]), wout);
        ids_place(out, at, wout, counts[i], w, pp, Some(&tab), tab.len() - 1);
        at += counts[i];
    }
}

// ---- K19: structural.c `split`, `reverse`, `shift`, `translate` ----
/// structural.c `next_byte`: the first index at or after `i`, below `lim`, holding byte `c`, or `lim`. Eight bytes a
/// step off the SWAR zero-byte test, because a `memchr` pays a fresh SIMD prologue per call and a separator every five
/// bytes calls it once per five.
#[inline(always)]
fn next_byte(b: &[u8], lim: usize, mut i: usize, c: u8) -> usize {
    let rep = 0x0101010101010101u64 * c as u64;
    while i + 8 <= lim {
        let v = u64::from_le_bytes(b[i..i + 8].try_into().unwrap()) ^ rep;
        let m = v.wrapping_sub(0x0101010101010101) & !v & 0x8080808080808080;
        if m != 0 { return i + (m.trailing_zeros() >> 3) as usize }
        i += 8;
    }
    while i < lim && b[i] != c { i += 1 }
    i
}
/// structural.c `copy_piece`: a split's piece, short far more often than not -- a `memcpy` of a runtime length is a
/// call and a size dispatch per field where four bytes are a single load and store.
#[inline(always)]
fn copy_piece(d: &mut [u8], s: &[u8]) {
    let n = d.len();
    if n >= 32 { d.copy_from_slice(s); return }
    let mut i = 0;
    while i + 8 <= n { d[i..i + 8].copy_from_slice(&s[i..i + 8]); i += 8 }
    while i < n { d[i] = s[i]; i += 1 }
}
/// The starts of the occurrences of `d` in `b`, left to right and not overlapping. An empty `d` occurs nowhere.
fn cuts<'a>(d: &'a [u8], b: &'a [u8]) -> impl Iterator<Item = usize> + 'a {
    let dn = d.len();
    // the last index a match may start at, plus one: past it there is not room for the delimiter
    let lim = if dn != 0 && dn <= b.len() { b.len() - dn + 1 } else { 0 };
    let mut i = 0;
    core::iter::from_fn(move || loop {
        if i >= lim { return None }
        i = next_byte(b, lim, i, d[0]);
        if i == lim { return None }
        if dn == 1 || &b[i..i + dn] == d { let at = i; i += dn; return Some(at) }
        i += 1;
    })
}
/// structural.c `qlean_structural_split`, first pass: how many cuts `d` makes in `b`.
pub fn split_cuts(d: &[u8], b: &[u8]) -> usize { cuts(d, b).count() }
/// structural.c `qlean_structural_split`, second pass: the pieces end to end into `out` (`b.len() - cuts * d.len()`
/// bytes) and their `cuts + 2` boxed starts into `offs`.
pub fn split(d: &[u8], b: &[u8], out: &mut [u8], offs: &mut [usize]) {
    let boxed = |at: usize| at << 1 | 1;
    let (mut at, mut from, mut k) = (0, 0, 0);
    offs[0] = boxed(0);
    for i in cuts(d, b) {
        copy_piece(&mut out[at..at + i - from], &b[from..i]);
        at += i - from;
        k += 1;
        offs[k] = boxed(at);
        from = i + d.len();
    }
    out[at..at + b.len() - from].copy_from_slice(&b[from..]);
    at += b.len() - from;
    offs[k + 1] = boxed(at);
}
/// `reverseBytes w b`: element `n - 1 - j` of `b` at each `j`, `n` elements of `W` bytes.
fn reverse_w<const W: usize>(run: Runner, src: &[u8], n: usize, out: &mut [u8]) {
    let sc = src.as_chunks::<W>().0;
    crate::c::run_map(run, out, n, W, crate::QLEAN_COST_COPY, W, &|lo, hi, o: &mut [u8]| {
        for (d, s) in o.as_chunks_mut::<W>().0.iter_mut().zip(sc[n - hi..n - lo].iter().rev()) { *d = *s }
    });
}
/// structural.c `reverse_run` and `qlean_structural_reverse`.
pub fn reverse(run: Runner, w: usize, src: &[u8], n: usize, out: &mut [u8]) {
    check_w(w, "reverse");
    match w { 1 => reverse_w::<1>(run, src, n, out), 2 => reverse_w::<2>(run, src, n, out), 4 => reverse_w::<4>(run, src, n, out),
              8 => reverse_w::<8>(run, src, n, out), _ => reverse_w::<16>(run, src, n, out) }
}
/// `shiftBytes w fill k b`: element `j - k` at each `j`, `fill` where `j - k` is outside `[0, n)`. The in-range
/// middle of a slice is one copy and the two ends are fill, where the C tests every element with one unsigned compare.
fn shift_w<const W: usize>(run: Runner, fill: u64, k: i64, src: &[u8], n: usize, out: &mut [u8]) {
    let (f, sc) = (word::<W>(fill), src.as_chunks::<W>().0);
    crate::c::run_map(run, out, n, W, crate::QLEAN_COST_COPY, W, &|lo, hi, o: &mut [u8]| {
        // output index `j` reads `j - k`, in range for `j` in `[k, k + n)`; i128 holds both ends of every `i64` `k`
        let s = (k as i128).clamp(lo as i128, hi as i128) as usize;
        let e = (k as i128 + n as i128).clamp(s as i128, hi as i128) as usize;
        let o = o.as_chunks_mut::<W>().0;
        o[..s - lo].fill(f);
        if e > s { o[s - lo..e - lo].copy_from_slice(&sc[(s as i128 - k as i128) as usize..(e as i128 - k as i128) as usize]) }
        o[e - lo..].fill(f);
    });
}
/// structural.c `shift_run` and `qlean_structural_shift`.
pub fn shift(run: Runner, w: usize, fill: u64, k: i64, src: &[u8], n: usize, out: &mut [u8]) {
    check_w(w, "shift");
    match w { 1 => shift_w::<1>(run, fill, k, src, n, out), 2 => shift_w::<2>(run, fill, k, src, n, out),
              4 => shift_w::<4>(run, fill, k, src, n, out), 8 => shift_w::<8>(run, fill, k, src, n, out),
              _ => shift_w::<16>(run, fill, k, src, n, out) }
}
/// structural.c `translate_run` and `qlean_structural_translate`: `tab[src[i]]` at each `i`, `tab` 256 bytes.
pub fn translate(run: Runner, tab: &[u8], src: &[u8], out: &mut [u8]) {
    let t: &[u8; 256] = tab.try_into().unwrap_or_else(|_| panic!("qlean structural: translate got a table of {} bytes, not 256", tab.len()));
    crate::c::run_map(run, out, src.len(), 1, crate::QLEAN_COST_GATHER, 1, &|lo, hi, o: &mut [u8]| {
        for (d, &s) in o.iter_mut().zip(&src[lo..hi]) { *d = t[s as usize] }
    });
}

/// structural.c `qlean_structural_reverse_ids`: `n` fields of `w` bits reversed into the zeroed `out`. Where a byte holds a
/// whole number of fields, reversing the column is reversing the bytes and then the fields inside each one, a 256-entry
/// table read; a count that leaves the last byte part-full shifts every field and takes the general pack.
pub fn reverse_ids(n: usize, w: u32, ids: &[u8], out: &mut [u8]) {
    if w != 0 && w < 8 && n % (8 / w as usize) == 0 {
        let (per, msk) = (8 / w, (1u32 << w) - 1);
        let rev: [u8; 256] = core::array::from_fn(|b| (0..per).fold(0u32, |v, j| v | ((b as u32 >> (j * w)) & msk) << ((per - 1 - j) * w)) as u8);
        let bytes = crate::ids::ids_bytes(n, w);
        for (k, o) in out[..bytes].iter_mut().enumerate() { *o = rev[ids[bytes - 1 - k] as usize] }
    } else {
        crate::ids::pack(out, w, n, |j| crate::ids::id_at(ids, w, n - 1 - j) as u64)
    }
}
/// structural.c `qlean_structural_reverse_segs`'s validation, the spec's own `any`: every offset a multiple of `w`, within
/// the `sz` bytes and not below the one before it.
pub fn segs_ok(w: usize, sz: usize, offs: &[usize]) -> bool {
    w != 0 && offs.iter().enumerate().all(|(s, &o)| o % w == 0 && o <= sz && (s == 0 || o >= offs[s - 1]))
}
/// `reverseSegs w b offs` over `out`, the copy of `b`: each slice between consecutive offsets reversed at element width `w`.
pub fn reverse_segs(w: usize, offs: &[usize], out: &mut [u8]) {
    for p in offs.windows(2) {
        let seg = &mut out[p[0]..p[1]];
        match w {
            1 => seg.reverse(), 2 => seg.as_chunks_mut::<2>().0.reverse(), 4 => seg.as_chunks_mut::<4>().0.reverse(),
            8 => seg.as_chunks_mut::<8>().0.reverse(),
            _ => { let m = seg.len() / w; for i in 0..m / 2 { let (a, b) = seg.split_at_mut((m - 1 - i) * w); a[i * w..(i + 1) * w].swap_with_slice(&mut b[..w]) } }
        }
    }
}
/// structural.c `qlean_structural_trim_bounds`: the first byte that is not a blank and one past the last, `hi` held at `lo`
/// so an all-blank payload answers an empty slice.
pub fn trim_bounds(left: bool, right: bool, b: &[u8]) -> (usize, usize) {
    let lo = if left { b.iter().position(|&x| x != 32).unwrap_or(b.len()) } else { 0 };
    let hi = if right { b.iter().rposition(|&x| x != 32).map_or(0, |i| i + 1) } else { b.len() };
    (lo, hi.max(lo))
}
// ---- A40: structural.c:2039-2170, the symbol dictionary's hash table ----
/// structural.c:2044 `symview`: a dictionary being extended: the base's first `d0` symbols, then new ones in `tb`
/// at the (unboxed) starts `to`.
#[derive(Clone, Copy)]
pub struct Symview<'a> { pub base: Syms<'a>, pub d0: usize, pub tb: &'a [u8], pub to: &'a [usize] }
/// structural.c:2039 `symtab` without its reference count (the `sd_*` cache's): `slot` is `mask + 1` ids + 1.
pub struct Symtab<'a> { pub cnt: usize, pub mask: usize, pub stale: usize, pub slot: &'a mut [u32] }
impl<'a> Symview<'a> {
    /// structural.c:2046 `symview_at`
    pub fn at(&self, i: usize) -> &'a [u8] {
        if i < self.d0 { return self.base.at(i) }
        let (lo, hi) = (self.to[i - self.d0], self.to[i - self.d0 + 1]);
        &self.tb[lo..hi - 1]
    }
}
/// structural.c:2053 `symtab_find`: the id of `k` among the first `d`, or `d`.
pub fn symtab_find(slot: &[u32], mask: usize, v: &Symview, d: usize, k: &[u8]) -> usize {
    let mut s = sym_hash(k) as usize & mask;
    while slot[s] != 0 {
        let e = slot[s] as usize - 1;
        if e < d && sym_eq(v.at(e), k) { return e }
        s = (s + 1) & mask;
    }
    d
}
impl<'a> Symtab<'a> {
    /// structural.c:2061 `symtab_put`
    pub fn put(&mut self, _v: &Symview, k: &[u8], id: usize) {
        let mut s = sym_hash(k) as usize & self.mask;
        while self.slot[s] != 0 { s = (s + 1) & self.mask }
        self.slot[s] = (id + 1) as u32;
    }
    /// structural.c:2069-2100 `symtab_fit`/`symtab_build` after the slots are allocated: the `cnt` entries of
    /// `v`, both areas, hashed into empty slots.
    pub fn fill(&mut self, v: &Symview) { for i in 0..self.cnt { self.put(v, v.at(i), i) } }
    /// structural.c:2105 `symtab_fork` after the allocation: `s`'s slots copied (`scnt` entries, `sstale` stale ones), the
    /// entries at or past `d` counted stale on top of `s`'s. O(1) beyond the copy, as the C: the counts are passed in.
    pub fn fork(&mut self, s: &[u32], scnt: usize, sstale: usize, d: usize) {
        assert!(d <= scnt, "qlean structural: symtab_fork of {d} entries from a table of {scnt}");
        self.slot.copy_from_slice(s);
        (self.mask, self.cnt, self.stale) = (s.len() - 1, d, sstale + (scnt - d));
    }
}

// ---- A41a: structural.c:2203-2370 ----
/// structural.c:2223 `symdict_concat`'s per-part step: the symbols of `part` from `from` interned into `t` over the
/// base `base` (`d0` entries) and the new-symbol area `tb`/`to` (the starts, `to[0] == 0`), each one's id into
/// `map`. A new symbol is appended to `tb`/`to`. The slots cannot grow here, so it returns the index it stopped at
/// when the next insert would pass half full (`symtab_fit`'s test), and `map.len()` when the part is done.
pub fn symdict_intern(t: &mut Symtab, base: &Syms, d0: usize, tb: &mut [u8], to: &mut [usize], part: &Syms,
                      map: &mut [usize], from: usize) -> usize {
    for j in from..map.len() {
        let (s, cnt) = (part.at(j), t.cnt);
        let e = symtab_find(t.slot, t.mask, &Symview { base: *base, d0, tb: &*tb, to: &*to }, cnt, s);
        if e == cnt {
            if 2 * (cnt + 1 + t.stale) > t.mask + 1 { return j }
            let at = to[cnt - d0];
            tb[at..at + s.len()].copy_from_slice(s);
            tb[at + s.len()] = 0;
            to[cnt - d0 + 1] = at + s.len() + 1;
            t.put(&Symview { base: *base, d0, tb: &*tb, to: &*to }, s, cnt);
            t.cnt = cnt + 1;
        }
        map[j] = e;
    }
    map.len()
}

// ---- A41b: structural.c:2373-2384, 3005-3030 ----
/// structural.c:2373 `til_run` and its entry: `0 .. out.len()`.
pub fn til(run: Runner, out: &mut [i64]) {
    let n = out.len();
    crate::c::run_map(run, crate::pod::bytes_mut(out), n, 8, crate::QLEAN_COST_COPY, 8, &|lo, hi, o: &mut [u8]| {
        for (i, b) in (lo..hi).zip(o.chunks_exact_mut(8)) { b.copy_from_slice(&(i as i64).to_le_bytes()) }
    });
}
/// structural.c:3005 `qlean_structural_scatter` past the unboxing: `dst[idx[i]] = src[soff + i]` (`bcast`: `src[soff]`)
/// at `wb` bytes; false = an index out of range. Such an index writes nothing, as in C; the rest are written in order,
/// so the last write to a repeated index stays.
pub fn scatter(wb: usize, dst: &mut [u8], idx: &[i64], src: &[u8], soff: usize, bcast: bool) -> bool {
    // one instance per width C's WIDTHS offers, so the copy is a single move
    fn go<const W: usize>(dst: &mut [u8], idx: &[i64], src: &[u8], soff: usize, bcast: bool) -> bool {
        let (d, s) = (dst.as_chunks_mut::<W>().0, src.as_chunks::<W>().0);
        let mut ok = true;
        for (k, &x) in idx.iter().enumerate() {
            let u = x as u64;
            if u >= d.len() as u64 { ok = false; continue }
            d[u as usize] = s[soff + if bcast { 0 } else { k }];
        }
        ok
    }
    match wb {
        1 => go::<1>(dst, idx, src, soff, bcast),
        2 => go::<2>(dst, idx, src, soff, bcast),
        4 => go::<4>(dst, idx, src, soff, bcast),
        8 => go::<8>(dst, idx, src, soff, bcast),
        16 => go::<16>(dst, idx, src, soff, bcast),
        _ => panic!("qlean structural: scatter got element width {wb}; the kernels are instantiated at 1, 2, 4, 8 and 16 bytes"),
    }
}
/// structural.c:2071 `symtab_build` past the slot allocation: the `d` entries of the plain dictionary `v` (`d0 == d`,
/// no new-symbol area) hashed in order, `cnt` following; false = one repeats an earlier one, the table then unusable.
pub fn symtab_build(t: &mut Symtab, v: &Symview, d: usize) -> bool {
    for i in 0..d {
        let k = v.at(i);
        if symtab_find(t.slot, t.mask, v, i, k) != i { return false }
        t.put(v, k, i);
        t.cnt = i + 1;
    }
    true
}


// ---- K21: structural.c `til_fill`, `str_*`, `mmu_block`, `transpose_cells`, `transpose_rows` ----
/// `til_fill`: the `cnt = buf.len()` elements of `til` from `i0`, the block the encoder asks for.
pub fn til_fill(buf: &mut [i64], i0: usize) { for (j, b) in buf.iter_mut().enumerate() { *b = (i0 + j) as i64 } }

/// `STR_BLK`: the unit of both passes of `string`, so the prefix sum between them is over `n / STR_BLK` numbers.
pub(crate) const STR_BLK: usize = 4096;
const STR_PAIR: &[u8; 200] = b"0001020304050607080910111213141516171819202122232425262728293031323334353637383940414243444546474849\
5051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899";
const STR_POW10: [u64; 20] = [1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000, 10000000000, 100000000000,
    1000000000000, 10000000000000, 100000000000000, 1000000000000000, 10000000000000000, 100000000000000000, 1000000000000000000,
    10000000000000000000];
/// `str_len`: digits in `m`, at least one. `77/256` is `log10(2)` from below, so the estimate is right or one short and
/// the one table compare corrects it; `m | 1` gives zero a digit of its own.
#[inline(always)]
fn str_len(m: u64) -> usize {
    let t = ((63 - (m | 1).leading_zeros() as usize) * 77) >> 8;
    t + (m >= STR_POW10[t + 1]) as usize + 1
}
/// `str_one`: the decimal spelling of `v` at the start of `out`, two digits a division, written where they land; answers
/// its length.
#[inline(always)]
fn str_one(out: &mut [u8], v: i64) -> usize {
    let mut m = v.unsigned_abs();
    let (neg, len) = ((v < 0) as usize, str_len(m));
    let out = &mut out[..neg + len];
    if neg == 1 { out[0] = b'-' }
    let mut e = out.len();
    while m >= 100 {
        let d = (m % 100) as usize;
        m /= 100;
        e -= 2;
        out[e..e + 2].copy_from_slice(&STR_PAIR[2 * d..2 * d + 2]);
    }
    if m >= 10 { out[e - 2..e].copy_from_slice(&STR_PAIR[2 * m as usize..2 * m as usize + 2]) } else { out[e - 1] = b'0' + m as u8 }
    neg + len
}
/// The elements of block `b` of `n`: `STR_BLK` of them, the last block the rest.
fn str_blk(n: usize, b: usize) -> core::ops::Range<usize> { b * STR_BLK..((b + 1) * STR_BLK).min(n) }
/// `str_count_run` for one width: the bytes each block spells, a null (`null`, that width's minimum) nothing.
fn str_count_w<T: pod::Pod + Into<i64> + Sync>(run: Runner, src: &[u8], n: usize, at: &mut [usize], null: i64) {
    let q = &pod::cast::<T>(src).expect("string digits: a misaligned column")[..n];
    let w = size_of::<T>();
    let nb = n.div_ceil(STR_BLK);
    crate::c::run_map(run, pod::bytes_mut(&mut at[..nb]), nb, 8, crate::QLEAN_COST_ARITH * STR_BLK as u32, w + 8, &|lo, hi, o: &mut [u8]| {
        let o = pod::cast_mut::<usize>(o).expect("string digits: a misaligned block table");
        for (b, o) in (lo..hi).zip(o) {
            *o = q[str_blk(n, b)].iter().map(|&x| { let v: i64 = x.into(); if v == null { 0 } else { (v < 0) as usize + str_len(v.unsigned_abs()) } }).sum();
        }
    });
}
/// The `stringDigits` count pass: turns `at[..nb]`, `nb = ceil(n / STR_BLK)`, into where block `b`'s spellings start in
/// the blob, `at[nb]` the blob's length, which it answers. `w` is 2, 4 or 8, the width of the integers in `src`.
pub fn str_count(run: Runner, w: usize, src: &[u8], n: usize, at: &mut [usize]) -> usize {
    match w {
        2 => str_count_w::<i16>(run, src, n, at, i16::MIN as i64),
        4 => str_count_w::<i32>(run, src, n, at, i32::MIN as i64),
        8 => str_count_w::<i64>(run, src, n, at, i64::MIN),
        _ => panic!("qlean structural: string digits got width {w}; it takes 2, 4 or 8"),
    }
    let mut total = 0;
    for b in at[..n.div_ceil(STR_BLK)].iter_mut() { let t = *b; *b = total; total += t }
    at[n.div_ceil(STR_BLK)] = total;
    total
}
/// `str_write_run` for one width: the spellings into `blob` and, for every element, where it ends (`lean_box` of the
/// offset, a tagged scalar) into `offs[1..]`; `offs[0]` is the box of 0.
fn str_write_w<T: pod::Pod + Into<i64> + Sync>(run: Runner, src: &[u8], n: usize, at: &[usize], blob: &mut [u8], offs: &mut [usize], null: i64) {
    let q = &pod::cast::<T>(src).expect("string digits: a misaligned column")[..n];
    let nb = n.div_ceil(STR_BLK);
    offs[0] = 1;
    crate::c::run_map2(run, blob, &|k| at[k], pod::bytes_mut(&mut offs[1..=n]), STR_BLK * 8, nb, crate::QLEAN_COST_ARITH * STR_BLK as u32,
                       size_of::<T>() + 8, &|lo, hi, o: &mut [u8], ob: &mut [u8]| {
        let mut ob = pod::cast_mut::<usize>(ob).expect("string digits: a misaligned offsets array").iter_mut();
        let mut here = at[lo];
        for &x in &q[lo * STR_BLK..(hi * STR_BLK).min(n)] {
            let v: i64 = x.into();
            if v != null { here += str_one(&mut o[here - at[lo]..], v) }
            *ob.next().unwrap() = here << 1 | 1;
        }
    });
}
/// The `stringDigits` write pass over `str_count`'s `at`: `blob` is `at[nb]` bytes, `offs` `n + 1` words.
pub fn str_write(run: Runner, w: usize, src: &[u8], n: usize, at: &[usize], blob: &mut [u8], offs: &mut [usize]) {
    match w {
        2 => str_write_w::<i16>(run, src, n, at, blob, offs, i16::MIN as i64),
        4 => str_write_w::<i32>(run, src, n, at, blob, offs, i32::MIN as i64),
        8 => str_write_w::<i64>(run, src, n, at, blob, offs, i64::MIN),
        _ => panic!("qlean structural: string digits got width {w}; it takes 2, 4 or 8"),
    }
}

/// `MMU_ROWS`: rows of the left matrix per pass over the right one; at this width the `j` loop still vectorises (measured:
/// one row 73us at 100 by 100, two 62, four 40, five 35, six 128 under C's compiler).
const MMU_ROWS: usize = 4;
/// `mmu_block`: the product rows of `MMU_ROWS` rows of `a` into `o`, `MMU_ROWS * p` numbers. `j` innermost is what vectorises;
/// each element still sums `k` ascending, the order the specification fixes, and Rust never fuses `x * b + o`, as q does not.
fn mmu_block(ra: [&[f64]; MMU_ROWS], rb: &[&[f64]], p: usize, o: &mut [f64]) {
    o.fill(0.0);
    let (o0, o) = o.split_at_mut(p);
    let (o1, o) = o.split_at_mut(p);
    let (o2, o3) = o.split_at_mut(p);
    for (k, bk) in rb.iter().enumerate() {
        let (x0, x1, x2, x3) = (ra[0][k], ra[1][k], ra[2][k], ra[3][k]);
        for ((((b, a0), a1), a2), a3) in bk[..p].iter().zip(&mut *o0).zip(&mut *o1).zip(&mut *o2).zip(&mut *o3) {
            *a0 += x0 * b; *a1 += x1 * b; *a2 += x2 * b; *a3 += x3 * b;
        }
    }
}
/// `qlean_structural_mmu` past the unboxing: `out` holds the `n * p` products of `n` rows `a` of `m` against `m` rows `b` of
/// `p`, and room for the rows up to a whole block, which the last block writes (reading row 0 of `a` for its unasked-for rows).
pub fn mmu(a: &[&[f64]], b: &[&[f64]], p: usize, out: &mut [f64]) {
    let n = a.len();
    assert!(out.len() >= n.div_ceil(MMU_ROWS) * MMU_ROWS * p, "mmu: {} slots for {n} rows of {p}", out.len());
    for (i, o) in (0..n).step_by(MMU_ROWS).zip(out.chunks_mut(MMU_ROWS * p.max(1))) {
        mmu_block(core::array::from_fn(|t| *a.get(i + t).unwrap_or(&a[0])), b, p, &mut o[..MMU_ROWS * p]);
    }
}

/// `TRANSPOSE_BLOCK`: bytes of the answer a block of rows may span, inside this machine's L2 with room for the source lines.
const TRANSPOSE_BLOCK: usize = 128 * 1024;
/// `transpose_rows`: rows per pass of the blocked transpose, sized in bytes (`stride` a row's) and not in rows.
fn transpose_rows(stride: usize, n: usize) -> usize { if stride == 0 { n } else { (TRANSPOSE_BLOCK / stride).max(1) } }
/// `transpose_cells`: cell `i` of a column at stride `ss` into stride `ds`, for the width `W`, so each is one typed move.
fn cells<const W: usize>(d: &mut [u8], ds: usize, s: &[u8], ss: usize, n: usize) {
    let (d, s) = (d.as_chunks_mut::<W>().0, s.as_chunks::<W>().0);
    if n == 0 { return }
    // exactly one side is strided (a transpose writes at `stride`, its inverse reads at it): the first `n - 1` cells of it
    // start a whole chunk of `stride / W` cells (`chunks_exact` has no short chunk to test for), the last has no row after it
    if ss == W {
        let (rows, last) = d[..(n - 1) * (ds / W) + 1].split_at_mut((n - 1) * (ds / W));
        for (d, s) in rows.chunks_exact_mut(ds / W).zip(s) { d[0] = *s }
        last[0] = s[n - 1];
    } else {
        let (rows, last) = s[..(n - 1) * (ss / W) + 1].split_at((n - 1) * (ss / W));
        for (d, s) in d.iter_mut().zip(rows.chunks_exact(ss / W)) { *d = s[0] }
        d[n - 1] = last[0];
    }
}
/// One column of a transpose in either direction: `n` cells of `w` bytes read at stride `ss` and written at stride `ds`
/// (both multiples of `w`); the width is switched outside the loop, `memcpy` of a run-time width being a call per cell.
fn transpose_cells(d: &mut [u8], ds: usize, s: &[u8], ss: usize, w: usize, n: usize) {
    match w {
        0 => {}
        1 => cells::<1>(d, ds, s, ss, n),
        2 => cells::<2>(d, ds, s, ss, n),
        4 => cells::<4>(d, ds, s, ss, n),
        8 => cells::<8>(d, ds, s, ss, n),
        16 => cells::<16>(d, ds, s, ss, n),
        _ => for (d, s) in d.chunks_mut(ds).zip(s.chunks(ss)).take(n) { d[..w].copy_from_slice(&s[..w]) },
    }
}
/// One block of `cnt` rows from row `i0`, for `K` columns of `W`-byte cells, in the row-major direction: every cell is a
/// constant offset into a row, so the copy is an interleave of `K` streams. Strided per-column stores of the same cells
/// compile to an AVX-512 scatter, which runs at half the speed of the C's scalar loop.
fn rows_k<const W: usize, const K: usize>(out: &mut [u8], cols: &[&[u8]], i0: usize, cnt: usize) {
    let cs: [&[[u8; W]]; K] = core::array::from_fn(|j| &cols[j].as_chunks::<W>().0[i0..i0 + cnt]);
    let o = &mut out.as_chunks_mut::<W>().0.as_chunks_mut::<K>().0[i0..i0 + cnt];
    for i in 0..cnt { for j in 0..K { o[i][j] = cs[j][i] } }
}
/// `rows_k` the other way: `src` rows of `K` cells into `K` columns of `n` cells.
fn cols_k<const W: usize, const K: usize>(out: &mut [u8], src: &[u8], n: usize, i0: usize, cnt: usize) {
    let mut it = out.chunks_exact_mut(n * W);
    let cs: [&mut [[u8; W]]; K] = core::array::from_fn(|_| &mut it.next().expect("transpose: fewer columns than K").as_chunks_mut::<W>().0[i0..i0 + cnt]);
    let s = &src.as_chunks::<W>().0.as_chunks::<K>().0[i0..i0 + cnt];
    for i in 0..cnt { for j in 0..K { cs[j][i] = s[i][j] } }
}
/// `f::<W, K>` for the widths and column counts that `rows_k` and `cols_k` are instantiated at; false = neither is.
macro_rules! by_wk {
    ($w:expr, $k:expr, $f:ident($($a:expr),*)) => { match ($w, $k) {
        (1, 2) => $f::<1, 2>($($a),*), (2, 2) => $f::<2, 2>($($a),*), (4, 2) => $f::<4, 2>($($a),*), (8, 2) => $f::<8, 2>($($a),*),
        (1, 3) => $f::<1, 3>($($a),*), (2, 3) => $f::<2, 3>($($a),*), (4, 3) => $f::<4, 3>($($a),*), (8, 3) => $f::<8, 3>($($a),*),
        (1, 4) => $f::<1, 4>($($a),*), (2, 4) => $f::<2, 4>($($a),*), (4, 4) => $f::<4, 4>($($a),*), (8, 4) => $f::<8, 4>($($a),*),
        _ => return false,
    } };
}
fn block_rows(w: usize, cols: &[&[u8]], out: &mut [u8], i0: usize, cnt: usize) -> bool { by_wk!(w, cols.len(), rows_k(out, cols, i0, cnt)); true }
fn block_cols(w: usize, k: usize, src: &[u8], out: &mut [u8], n: usize, i0: usize, cnt: usize) -> bool { by_wk!(w, k, cols_k(out, src, n, i0, cnt)); true }
/// `qlean_structural_transpose`: `out` the `n` rows of `k = cols.len()` cells of `w` bytes, cell `j` of row `i` being element `i`
/// of `cols[j]` (each at least `n * w` bytes). A block of rows at a time: a pass down one column touches every cache line of
/// the answer, a read-modify-write of all of it once per column.
pub fn transpose(w: usize, n: usize, cols: &[&[u8]], out: &mut [u8]) {
    let (k, stride) = (cols.len(), cols.len() * w);
    let rows = transpose_rows(stride, n);
    for i0 in (0..n).step_by(rows.max(1)) {
        let cnt = rows.min(n - i0);
        if !block_rows(w, cols, out, i0, cnt) {
            for (j, c) in cols.iter().enumerate() { transpose_cells(&mut out[(i0 * k + j) * w..], stride, &c[i0 * w..], w, w, cnt) }
        }
    }
}
/// `qlean_structural_untranspose`'s copy: `src` the `n` rows of `k` cells of `w` bytes into `out`, the `k` columns end to end.
pub fn untranspose(w: usize, n: usize, k: usize, src: &[u8], out: &mut [u8]) {
    let stride = k * w;
    let rows = transpose_rows(stride, n);
    for i0 in (0..n).step_by(rows.max(1)) {
        let cnt = rows.min(n - i0);
        if !block_cols(w, k, src, out, n, i0, cnt) {
            for j in 0..k { transpose_cells(&mut out[(j * n + i0) * w..], w, &src[(i0 * k + j) * w..], stride, w, cnt) }
        }
    }
}

#[cfg(test)]
mod symtab_tests {
    use super::*;
    fn offs(ss: &[&[u8]]) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (Vec::new(), Vec::new());
        for s in ss { o.push(b.len() << 1 | 1); b.extend_from_slice(s); b.push(0) }
        o.push(b.len() << 1 | 1);
        (b, o)
    }
    #[test]
    fn view_find_put_fill_fork() {
        let (b, o) = offs(&[b"a", b"", b"bc"]);
        let base = Syms { blob: &b, offs: &o };
        let (tb, to) = (b"xyz\0q\0".to_vec(), vec![0usize, 4, 6]);
        let v = Symview { base, d0: 3, tb: &tb, to: &to };
        assert_eq!((v.at(0), v.at(1), v.at(2), v.at(3), v.at(4)), (&b"a"[..], &b""[..], &b"bc"[..], &b"xyz"[..], &b"q"[..]));
        let mut slot = vec![0u32; 16];
        let mut t = Symtab { cnt: 5, mask: 15, stale: 0, slot: &mut slot };
        t.fill(&v);
        for i in 0..5 { assert_eq!(symtab_find(t.slot, 15, &v, 5, v.at(i)), i) }
        assert_eq!(symtab_find(t.slot, 15, &v, 5, b"nope"), 5);
        assert_eq!(symtab_find(t.slot, 15, &v, 3, b"xyz"), 3); // at or past `d` is absent
        let s = t.slot.to_vec();
        let mut slot2 = vec![0u32; 16];
        let mut f = Symtab { cnt: 0, mask: 0, stale: 0, slot: &mut slot2 };
        f.fork(&s, 5, 0, 3);
        assert_eq!((f.cnt, f.mask, f.stale), (3, 15, 2));
        assert_eq!(f.slot, &s[..]);
        // a table that already carries 4 stale slots: they stay counted, and the 2 entries past `d` join them
        f.fork(&s, 5, 4, 3);
        assert_eq!(f.stale, 6);
    }
    #[test]
    fn intern_dedupes_and_stops_for_a_fit() {
        let (b, o) = offs(&[b"a", b"", b"bc"]);
        let base = Syms { blob: &b, offs: &o };
        let (pb, po) = offs(&[b"bc", b"x", b"a", b"x", b"y"]);
        let part = Syms { blob: &pb, offs: &po };
        let (mut tb, mut to) = (vec![0u8; 8], vec![0usize; 5]);
        let mut slot = vec![0u32; 16];
        let mut t = Symtab { cnt: 3, mask: 15, stale: 0, slot: &mut slot };
        t.fill(&Symview { base, d0: 3, tb: &[], to: &[] });
        let mut map = vec![0usize; 5];
        assert_eq!(symdict_intern(&mut t, &base, 3, &mut tb, &mut to, &part, &mut map, 0), 5);
        assert_eq!((t.cnt, &map[..], &to[..3], &tb[..5]), (5, &[2, 3, 0, 3, 4][..], &[0, 2, 4][..], &b"x\0y\0\0"[..]));
        // half full: 2 * (3 + 1) > 4 + 1 stops before the first new symbol
        let mut slot = vec![0u32; 4];
        let mut t = Symtab { cnt: 3, mask: 3, stale: 0, slot: &mut slot };
        t.fill(&Symview { base, d0: 3, tb: &[], to: &[] });
        let mut map = vec![0usize; 5];
        assert_eq!(symdict_intern(&mut t, &base, 3, &mut tb, &mut to, &part, &mut map, 0), 1);
        assert_eq!((t.cnt, map[0]), (3, 2));
    }
}

#[cfg(test)]
mod a39_tests {
    use super::*;
    use crate::ids::{id_at, ids_bytes};
    fn rng(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }
    fn bit(b: &[u8], i: usize) -> bool { b.get(i / 8).is_some_and(|x| x >> (i % 8) & 1 == 1) }

    #[test] fn concat_is_the_fold_of_append() {
        let mut s = 0x9E3779B97F4A7C15;
        for _ in 0..500 {
            let parts: Vec<Vec<u8>> = (0..rng(&mut s) % 12).map(|_| (0..rng(&mut s) % 40).map(|_| rng(&mut s) as u8).collect()).collect();
            let want = parts.concat();
            let ps: Vec<&[u8]> = parts.iter().map(|p| &p[..]).collect();
            let mut out = vec![0u8; want.len()];
            concat(crate::c::qlean_run_c, &ps, &mut out);
            assert_eq!(out, want);
        }
    }
    // the entry refuses an unequal-blocks source at width 16 by name; every other width and shape passes
    #[test] fn unequal_blocks_at_width_16_is_refused_at_the_entry() {
        assert!(std::panic::catch_unwind(|| check_enc(16, 255, "gather_foR")).is_err());
        for (w, sw) in [(16, 0), (16, 64), (8, 255), (1, 255)] { check_enc(w, sw, "gather_foR") }
        assert!(std::panic::catch_unwind(|| check_enc(3, 0, "gather_foR")).is_err());
    }
    #[test] fn enum_at_reads_zero_past_the_payload() {
        let b: Vec<u8> = [5i64, -3].iter().flat_map(|x| x.to_le_bytes()).collect();
        assert_eq!((enum_at(&b, 2, 0), enum_at(&b, 2, 1), enum_at(&b, 2, 2), enum_at(&b, 2, 99)), (5, -3, 0, 0));
    }
    #[test] fn enum_ids_nulls_negatives_and_short_payload() {
        let mut s = 7;
        for w in [0u32, 1, 2, 4, 8, 16, 32, 64] {
            let vals: Vec<i64> = (0..37).map(|_| match rng(&mut s) % 5 { 0 => i64::MIN, 1 => -1, _ => (rng(&mut s) % 3) as i64 }).collect();
            let b: Vec<u8> = vals[..30].iter().flat_map(|x| x.to_le_bytes()).collect();
            let mut out = vec![0u8; ids_bytes(37, w)];
            let bad = enum_ids(37, 3, 2, w, &b, &mut out);
            assert_eq!(bad, vals[..30].iter().position(|&v| v == -1).unwrap_or(37), "w {w} bad");
            for i in 0..37 {
                let v = vals.get(i).filter(|_| i < 30).copied().unwrap_or(0);
                let want = if v == i64::MIN { 2 } else { v.max(0) as u64 };
                if w != 0 { assert_eq!(id_at(&out, w, i) as u64, want & (u64::MAX >> (64 - w.min(64))), "w {w} i {i}") }
            }
        }
    }
    #[test] fn enum_ids_enc_is_enum_ids_of_the_decoded_column() {
        let n = 1500;
        let pack: Vec<u8> = (0..2 * crate::BLK * 2).map(|i| (i * 7 % 251) as u8).collect();
        let (base, z, off, width) = ([10i64, -4], [0i64; 2], [0u64, 2048], [16u8; 2]);
        let meta = crate::coc::Meta { base: &base, maxv: &z, off: &off, bsum: &z, width: &width, sumnul: 0, sumn: 0, n, nblk: 2, mblk: 2 };
        let c = Coc { meta, pack: &pack, exc: None, fdelta: None };
        let mut v = vec![0i64; 2 * crate::BLK];
        for b in 0..2 { c.decode_blk(b, crate::BLK, &mut v[b * crate::BLK..]) }
        v.truncate(n);
        let raw: Vec<u8> = v.iter().flat_map(|x| x.to_le_bytes()).collect();
        for w in [8u32, 16, 32] {
            let (mut a, mut b) = (vec![0u8; ids_bytes(n, w)], vec![0u8; ids_bytes(n, w)]);
            for d in [3usize, 1 << 20] {
                let (ba, bb) = (enum_ids(n, d, 0, w, &raw, &mut a), enum_ids_enc(n, d, 0, w, &c, &mut b));
                assert_eq!((&a, ba), (&b, bb), "w {w} d {d}");
                assert_eq!(ba, v.iter().position(|&x| x < 0 || x as u64 >= d as u64).unwrap_or(n), "w {w} d {d} bad");
            }
        }
    }
    #[test] fn ids_place_and_concat_ids_read_through_each_map() {
        let mut s = 11;
        for _ in 0..400 {
            let wout = [1u32, 2, 4, 8, 16, 32][rng(&mut s) as usize % 6];
            let k = rng(&mut s) as usize % 5;
            let (mut counts, mut widths, mut maps, mut raw) = (vec![], vec![], vec![], vec![]);
            for _ in 0..k {
                let w = [1u32, 2, 4, 8, 16][rng(&mut s) as usize % 5];
                let cn = rng(&mut s) as usize % 50;
                let mut p = vec![0u8; ids_bytes(cn, w)];
                for j in 0..cn { crate::ids::id_put(&mut p, w, j, rng(&mut s)) }
                counts.push(cn); widths.push(w); raw.push(p);
                maps.push((0..rng(&mut s) % 9).map(|_| rng(&mut s) as usize % (1 << wout.min(20))).collect::<Vec<usize>>());
            }
            let total: usize = counts.iter().sum();
            let mut out = vec![0u8; ids_bytes(total, wout)];
            let packed: Vec<Vec<u8>> = maps.iter().map(|m| { let mut b = vec![0u8; ids_bytes(m.len(), wout)]; for (j, &v) in m.iter().enumerate() { crate::ids::id_put(&mut b, wout, j, v as u64) } b }).collect();
            let (mr, pr): (Vec<&[u8]>, Vec<&[u8]>) = (packed.iter().map(|m| &m[..]).collect(), raw.iter().map(|p| &p[..]).collect());
            concat_ids(wout, &counts, &widths, &mr, &pr, &mut out);
            let mut at = 0;
            for i in 0..k {
                for j in 0..counts[i] {
                    let want = maps[i].get(id_at(&raw[i], widths[i], j)).copied().unwrap_or(0);
                    assert_eq!(id_at(&out, wout, at + j), want, "wout {wout} part {i} j {j}");
                }
                at += counts[i];
            }
        }
    }
    #[test] fn cycle_bits_and_concat_bits_match_bit_definitions() {
        let mut s = 5;
        for _ in 0..300 {
            let n = 1 + rng(&mut s) as usize % 150;
            let b: Vec<u8> = (0..n.div_ceil(8)).map(|_| rng(&mut s) as u8).collect();
            let (off, m) = (rng(&mut s) as usize % 400, rng(&mut s) as usize % 300);
            let mut out = vec![0u8; m.div_ceil(8)];
            cycle_bits(n, off % n, m, &b, &mut out);
            for j in 0..m { assert_eq!(bit(&out, j), bit(&b, (off % n + j) % n), "n {n} off {off} j {j}") }
            let counts = [rng(&mut s) as usize % 70, rng(&mut s) as usize % 70, rng(&mut s) as usize % 70];
            let parts: Vec<Vec<u8>> = counts.iter().map(|&c| (0..c.div_ceil(8)).map(|_| rng(&mut s) as u8).collect()).collect();
            let pr: Vec<&[u8]> = parts.iter().map(|p| &p[..]).collect();
            let total: usize = counts.iter().sum();
            let mut o = vec![0u8; total.div_ceil(8)];
            concat_bits(&counts, &pr, &mut o);
            let mut at = 0;
            for (i, &c) in counts.iter().enumerate() { for j in 0..c { assert_eq!(bit(&o, at + j), bit(&parts[i], j)) } at += c }
        }
    }
}

#[cfg(test)]
mod til_scatter_build_tests {
    use super::*;
    #[test]
    fn til_counts_up() {
        for n in [0usize, 1, 5, 1000] {
            let mut out = alloc::vec![-1i64; n];
            til(crate::c::qlean_run_c, &mut out);
            assert!(out.iter().enumerate().all(|(i, &x)| x == i as i64));
        }
    }
    #[test]
    fn scatter_last_write_wins_and_out_of_range_writes_nothing() {
        let mut dst = [0u8; 8]; // four 2-byte fields
        let src = [1u8, 1, 2, 2, 3, 3];
        assert!(!scatter(2, &mut dst, &[1, 9, 1, -1], &src, 0, false));
        assert_eq!(dst, [0, 0, 3, 3, 0, 0, 0, 0]); // field 1 got source 0, then source 2
        let mut dst = [0u8; 4];
        assert!(scatter(1, &mut dst, &[3, 0], &src, 2, true));
        assert_eq!(dst, [2, 0, 0, 2]);
    }
    #[test]
    fn build_refuses_a_repeat() {
        let (b, o) = (b"a\0b\0a\0".to_vec(), alloc::vec![1usize, 5, 9, 13]); // boxed starts 0, 2, 4, 6
        let v = Symview { base: Syms { blob: &b, offs: &o }, d0: 3, tb: &[], to: &[] };
        let mut slot = alloc::vec![0u32; 16];
        assert!(!symtab_build(&mut Symtab { cnt: 0, mask: 15, stale: 0, slot: &mut slot }, &v, 3));
        let v = Symview { base: Syms { blob: &b, offs: &o }, d0: 2, tb: &[], to: &[] };
        let mut slot = alloc::vec![0u32; 16];
        let mut t = Symtab { cnt: 0, mask: 15, stale: 0, slot: &mut slot };
        assert!(symtab_build(&mut t, &v, 2));
        assert_eq!(t.cnt, 2);
    }
}

#[cfg(test)]
mod a34_tests {
    use super::*;
    use crate::res::res_get;
    use crate::BLK;
    fn rng(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }
    fn bit(b: &[u8], i: usize) -> bool { b.get(i / 8).is_some_and(|x| x >> (i % 8) & 1 == 1) }

    #[test] fn bit_helpers_match_the_bitwise_definitions() {
        let mut s = 0x1234_5678_9abc_def1;
        for _ in 0..2000 {
            let n = 1 + rng(&mut s) as usize % 200;
            let b: Vec<u8> = (0..n.div_ceil(8)).map(|_| rng(&mut s) as u8).collect();
            let i = rng(&mut s) as usize % (8 * b.len() + 80);
            let w = bits64_at(&b, i);
            for k in 0..64 { assert_eq!(w >> k & 1 == 1, bit(&b, i + k), "bits64_at n {n} i {i} k {k}") }
            let (at, cnt, v) = (rng(&mut s) as usize % 100, 1 + rng(&mut s) as usize % 64, rng(&mut s));
            let mut o: Vec<u8> = (0..(at + cnt).div_ceil(8) + rng(&mut s) as usize % 12).map(|_| rng(&mut s) as u8 & rng(&mut s) as u8).collect();
            let was = o.clone();
            or_bits(&mut o, at, v, cnt);
            for k in 0..8 * o.len() {
                let want = bit(&was, k) || (k >= at && k < at + cnt && v >> (k - at) & 1 == 1);
                assert_eq!(bit(&o, k), want, "or_bits at {at} cnt {cnt} k {k}");
            }
            let (from, len, at) = (rng(&mut s) as usize % 150, rng(&mut s) as usize % 200, rng(&mut s) as usize % 100);
            let mut o = vec![0u8; (at + len).div_ceil(8)];
            copy_bits(&mut o, at, &b, from, len);
            for k in 0..8 * o.len() { assert_eq!(bit(&o, k), k >= at && k < at + len && bit(&b, from + k - at), "copy_bits k {k}") }
            let mut o = vec![0u8; (at + len).div_ceil(8)];
            set_bits(&mut o, at, len);
            for k in 0..8 * o.len() { assert_eq!(bit(&o, k), k >= at && k < at + len, "set_bits k {k}") }
            let mut o = vec![0u8; b.len()];
            bit_set(&mut o, i % (8 * b.len()));
            assert_eq!(o.iter().map(|x| x.count_ones()).sum::<u32>(), 1);
        }
        assert_eq!(bitrev64(1), 1 << 63);
    }
    #[test] fn reverse_and_shift_bits_match_the_bitwise_definitions() {
        let mut s = 0xfeed_beef_1234_5678;
        for _ in 0..2000 {
            let n = rng(&mut s) as usize % 300;
            let b: Vec<u8> = (0..rng(&mut s) as usize % (n.div_ceil(8) + 3)).map(|_| rng(&mut s) as u8).collect();
            let mut o = vec![0u8; n.div_ceil(8)];
            reverse_bits(n, &b, &mut o);
            for j in 0..8 * o.len() { assert_eq!(bit(&o, j), j < n && bit(&b, n - 1 - j), "reverse n {n} j {j}") }
            let (k, fill) = (rng(&mut s) as i64 % (n as i64 + 70) * if rng(&mut s) & 1 == 1 { -1 } else { 1 }, rng(&mut s) & 3);
            let mut o = vec![0u8; n.div_ceil(8)];
            shift_bits(n, fill, k, &b, &mut o);
            for j in 0..8 * o.len() {
                let i = j as i64 - k;
                let want = j < n && if 0 <= i && (i as usize) < n { bit(&b, i as usize) } else { fill != 0 };
                assert_eq!(bit(&o, j), want, "shift n {n} k {k} j {j}");
            }
        }
        let mut o = vec![0u8; 8];
        shift_bits(5, 1, i64::MIN, &[0], &mut o[..1]);
        assert_eq!(o[0], 0b11111);
    }
    #[test] fn reverse_and_concat_moves_keep_blocks_and_recompute_offsets() {
        // two parts of 2 and 1 blocks: widths 3, 8 | 0
        let part = |bases: &[i64], ws: &[u8], sum: i64| -> Vec<u8> {
            let mut m = Vec::new();
            for &b in bases { m.extend(b.to_ne_bytes()) }
            for (i, _) in bases.iter().enumerate() { m.extend((b'a' as i64 + i as i64).to_ne_bytes()) }
            for _ in bases { m.extend(0u64.to_ne_bytes()) }
            for _ in bases { m.extend(sum.to_ne_bytes()) }
            m.extend([0u8; 16]);
            m.extend(ws);
            m
        };
        let (m0, m1) = (part(&[10, 20], &[3, 8], 7), part(&[30], &[0], 9));
        let (p0, p1): (Vec<u8>, Vec<u8>) = ((0..384 + 1024).map(|i| i as u8).collect(), vec![]);
        let (mut mo, mut po) = (vec![0u8; 33 * 3 + 16], vec![0u8; p0.len()]);
        concat_move(&[&m0, &m1], &[&p0, &p1], 3 * BLK, 8, &mut mo, &mut po);
        assert_eq!(po, p0);
        let c = Coc { meta: crate::coc::Meta::new(&mo, usize::MAX).unwrap(), pack: &po, exc: None, fdelta: None };
        assert_eq!((c.meta.base, c.meta.bsum, c.meta.width, c.meta.off), (&[10, 20, 30][..], &[7, 7, 9][..], &[3, 8, 0][..], &[0, 384, 1408][..]));
        assert_eq!((c.meta.sumnul, c.meta.sumn), (i64::MIN, 3 * BLK as u64));
        let mut r = vec![0u8; 33 * 3 + 16];
        assert_eq!(reverse_meta(&c, &mut r), 1408);
        let rc = crate::coc::Meta::new(&r, usize::MAX).unwrap();
        assert_eq!((rc.base, rc.width, rc.off, rc.sumn), (&[30, 20, 10][..], &[0, 8, 3][..], &[0, 0, 1024][..], 3 * BLK as u64));
    }
    #[test] fn rev_fields_reverses_the_fields_of_a_byte() {
        for w in [1u8, 2, 4] {
            for x in 0..=255u8 {
                let y = rev_fields(x, w);
                for k in 0..8 / w { assert_eq!(y >> (k * w) & ((1 << w) - 1), x >> ((8 / w - 1 - k) * w) & ((1 << w) - 1), "w {w} x {x}") }
            }
        }
    }
    #[test] fn rev_block_reverses_the_residuals_at_every_width() {
        let mut s = 99;
        for w in 1..=64u8 {
            let nbytes = BLK * w as usize / 8;
            let sp: Vec<u8> = (0..nbytes).map(|_| rng(&mut s) as u8).collect();
            let mut dp = vec![0u8; nbytes];
            rev_block(&mut dp, &sp, w);
            for j in 0..BLK { assert_eq!(res_get(&dp, w, j), res_get(&sp, w, BLK - 1 - j), "w {w} j {j}") }
        }
    }
    fn column<'a>(base: &'a [i64], off: &'a [u64], width: &'a [u8], z: &'a [i64], pack: &'a [u8], n: usize) -> Coc<'a> {
        let m = base.len();
        let meta = crate::coc::Meta { base, maxv: z, off, bsum: z, width, sumnul: i64::MIN, sumn: n as u64, n, nblk: m, mblk: m };
        Coc { meta, pack, exc: None, fdelta: None }
    }
    #[test] fn reverse_enc_moves_blocks_and_reverses_residuals() {
        let mut s = 7;
        for widths in [vec![3u8, 8, 0, 13, 1], vec![16, 16, 16], vec![5], vec![0, 0], vec![2, 64, 4, 7, 32, 9, 12, 6]] {
            let nb = widths.len();
            let (mut off, mut t) = (vec![], 0u64);
            for &w in &widths { off.push(t); t += (BLK * w as usize / 8) as u64 }
            let pack: Vec<u8> = (0..t).map(|_| rng(&mut s) as u8).collect();
            let (base, z) = (vec![0i64; nb], vec![0i64; nb]);
            let c = column(&base, &off, &widths, &z, &pack, nb * BLK);
            let mut out = vec![0u8; t as usize];
            reverse_enc(crate::c::qlean_run_c, &c, &mut out);
            let mut at = 0;
            for b in 0..nb {
                let (w, sb) = (widths[nb - 1 - b], nb - 1 - b);
                for j in 0..BLK {
                    assert_eq!(res_get(&out[at..], w, j), res_get(&pack[off[sb] as usize..], w, BLK - 1 - j), "{widths:?} b {b} j {j}");
                }
                at += BLK * w as usize / 8;
            }
        }
    }
    #[test] fn unpack_run_widens_a_run_forward_and_reversed() {
        let mut s = 31;
        for w in [0u8, 1, 2, 3, 4, 5, 8, 11, 16, 24, 32, 47, 64] {
            let nbytes = BLK * w as usize / 8;
            let pack: Vec<u8> = (0..nbytes).map(|_| rng(&mut s) as u8).collect();
            let (base, z, off) = ([rng(&mut s) as i64], [0i64], [0u64]);
            let ws = [w];
            let c = column(&base, &off, &ws, &z, &pack, BLK);
            for _ in 0..40 {
                let cnt = 1 + rng(&mut s) as usize % BLK;
                let lo = rng(&mut s) as usize % (BLK - cnt + 1);
                for rev in [false, true] {
                    let mut d = vec![0i64; cnt];
                    unpack_run(&mut d, &c, 0, lo, rev);
                    for j in 0..cnt {
                        let want = (base[0] as u64).wrapping_add(res_get(&pack, w, lo + j)) as i64;
                        assert_eq!(d[if rev { cnt - 1 - j } else { j }], want, "w {w} lo {lo} cnt {cnt} rev {rev} j {j}");
                    }
                }
            }
        }
    }
    #[test] fn res_bytes_zero_pads_a_short_pack() {
        let pack = vec![0xffu8; 100];
        let (base, z, off) = ([0i64], [0i64], [60u64]);
        let ws = [8u8];
        let c = column(&base, &off, &ws, &z, &pack, BLK);
        let mut buf = [1u8; BLK * 8];
        let r = res_bytes(&c, 0, &mut buf);
        assert_eq!((r.len(), r[..40].iter().all(|&x| x == 0xff), r[40..].iter().all(|&x| x == 0)), (BLK, true, true));
    }
    #[test] fn trailer_ok_reads_the_writers_form() {
        let (base, z, off) = ([0i64], [0i64], [0u64]);
        let ws = [0u8];
        let mut c = column(&base, &off, &ws, &z, &[], 5);
        assert!(trailer_ok(&c, 5, 8, false) && !trailer_ok(&c, 6, 8, false) && trailer_ok(&c, 5, 1, true));
        c.meta.sumnul = i16::MIN as i64;
        assert!(trailer_ok(&c, 5, 2, false) && !trailer_ok(&c, 5, 4, false));
    }
}

#[cfg(test)]
mod a35_tests {
    use super::*;
    /// Every answer position 0..cnt is served exactly once, by a run or a hole, and the source index of each is the verb's.
    fn cover(cnt: usize, rev: bool, walk: impl Fn(&mut dyn FnMut(Seg)), src: impl Fn(usize) -> Option<(usize, usize)>) {
        let mut seen = vec![0; cnt];
        walk(&mut |s| match s {
            Seg::Run { p, b, lo, len, at } => for j in 0..len { seen[at + j] += 1; assert_eq!(src(at + j), Some((p, b * BLK + lo + if rev { len - 1 - j } else { j })), "at {}", at + j) },
            Seg::Hole { at, len } => for j in 0..len { seen[at + j] += 1; assert_eq!(src(at + j), None) },
        });
        assert!(seen.iter().all(|&x| x == 1));
    }
    #[test] fn blk_count_is_full_except_the_last() {
        assert_eq!((blk_count(2048, 0), blk_count(2048, 1), blk_count(2049, 2), blk_count(1, 0)), (BLK, BLK, 1, 1));
    }
    #[test] fn walks_serve_every_position_once() {
        let n = 2500;
        for i0 in [0, 1, 1023, 1024, 2400] {
            let cnt = 100.min(n - i0);
            cover(cnt, true, |g| rev_walk(n, i0, cnt, g), |a| Some((0, n - 1 - (i0 + a))));
            cover(cnt, false, |g| cycle_walk(n, 7, i0, cnt, g), |a| Some((0, (7 + i0 + a) % n)));
            for k in [0i64, 1, -1, 3000, -3000, 2499, 2500] {
                cover(cnt, false, |g| shift_walk(n, k, i0, cnt, g), |a| { let f = (i0 + a) as i64 - k; (0 <= f && f < n as i64).then_some((0, f as usize)) });
            }
        }
        // parts of 5, 0, 1030 and 7 elements, an empty one stepped over
        let start = [0, 5, 5, 1035, 1042];
        let which = |i: usize| { let p = (0..4).rev().find(|&p| start[p] <= i && start[p + 1] > i).unwrap(); (p, i - start[p]) };
        for i0 in [0, 3, 5, 1000, 1030, 1041] {
            let cnt = 12.min(1042 - i0);
            cover(cnt, false, |g| cat_walk(&start, i0, cnt, g), |a| Some(which(i0 + a)));
        }
    }
}

#[cfg(test)]
mod a38_tests {
    use super::*;
    use crate::c::qlean_run_c;
    #[test] fn expand_repeats_skips_negative_and_fills_past_the_source() {
        // runs 2, -1, 0, 3 over two 2-byte elements: run 3 has no element, so it takes `fill`
        let mut out = [0u8; 10];
        expand(qlean_run_c, 2, 0x0807, &[1, 2, 3, 4], &[2, -1, 0, 3], &mut out);
        assert_eq!(out, [1, 2, 1, 2, 7, 8, 7, 8, 7, 8]);
        expand(qlean_run_c, 1, 0x1ff, &[9], &[0, -3], &mut []);
    }
    #[test] fn gather_ids_misses_take_fill_and_are_cut_to_wout() {
        let mut out = [0u8; 3];
        // four 2-bit ids 0 1 2 3; 4, -1 and `0N` are misses, `fill` 9 at 4 bits
        gather_ids(qlean_run_c, 2, 4, 9, &[0b1110_0100], 4, &[3, -1, 0, 4, i64::MIN], &mut out);
        assert_eq!(out, [0x93, 0x90, 0x09]);
    }
    // C's own comment: `(til 10)@9 10 -1 0N` is `9 0N 0N 0N`; a 16-byte element zero-extends `fill`
    #[test] fn gather_misses_all_take_fill() {
        let src: alloc::vec::Vec<u8> = (0u8..10).collect();
        let mut out = [0u8; 4];
        gather(qlean_run_c, 1, 0xff, &src, &[9, 10, -1, i64::MIN], &mut out);
        assert_eq!(out, [9, 0xff, 0xff, 0xff]);
        let mut o16 = [1u8; 16];
        gather(qlean_run_c, 16, 0x0102, &[7; 16], &[1], &mut o16);
        assert_eq!(o16, [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    }
    #[test] #[should_panic(expected = "gather got element width 3")]
    fn gather_refuses_a_width_it_has_no_kernel_for() { gather(qlean_run_c, 3, 0, &[0; 6], &[0], &mut [0; 3]) }
    // C's own comment: `101b@0 5` is `10b`, so a miss is `0b` and not a dropped element
    #[test] fn gather_bits_miss_is_zero() {
        let mut out = [0u8];
        gather_bits(qlean_run_c, 3, &[0b101], &[0, 5], &mut out);
        assert_eq!(out, [0b01]);
        let mut out = [0u8; 2];
        // a bit past the payload reads 0 though `n` says it exists
        gather_bits(qlean_run_c, 100, &[0xff], &(0..10).collect::<alloc::vec::Vec<i64>>(), &mut out);
        assert_eq!(out, [0xff, 0]);
    }
    #[test] fn all_below_is_unsigned_and_empty_is_true() {
        assert!(all_below(0, &[]) && all_below(3, &[0, 2]) && !all_below(3, &[0, 3]) && !all_below(3, &[-1]));
    }
    #[test] fn cycle_ids_takes_the_run_to_the_end_then_laps() {
        let mut out = [0u8; 2];
        cycle_ids(3, 1, 5, 2, &[0b00_10_01_00], &mut out); // ids 0 1 2 from 1: 1 2 0 1 2
        assert_eq!(out, [0x49, 0x02]);
    }
    #[test] fn rows_of_boxes_and_gather_syms_writes_boxed_starts() {
        let mut o = [0i64; 2];
        assert_eq!(rows_of(&[5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], &mut o), 2);
        assert_eq!(o, [11, 1]);
        let s = Syms { blob: b"ab\0c\0", offs: &[1, 7, 11] };
        let (mut blob, mut offs) = ([0u8; 6], [0usize; 4]);
        assert_eq!(gather_syms_len(&s, &[1, 5, 0]), 6);
        gather_syms(&s, &[1, 5, 0], &mut blob, &mut offs); // "c", a miss, "ab"
        assert_eq!((blob, offs), (*b"c\0\0ab\0", [1, 5, 7, 13]));
    }
    #[test] #[should_panic(expected = "qlean_structural_rows_of: row 0 is 4611686018427387904")]
    fn rows_of_refuses_a_row_no_boxed_natural_carries() { rows_of(&(1u64 << 62).to_le_bytes(), &mut [0]); }
}

#[cfg(test)]
mod a36_tests {
    use super::*;
    #[test] fn put_res_writes_whole_fields_and_shared_bits_and_nothing_at_width_0() {
        let mut p = [0xffu8; 8];
        put_res(&mut p, 8, 1, &[10, 11], 4);
        assert_eq!(p, [0xff, 6, 7, 0xff, 0xff, 0xff, 0xff, 0xff]);
        let mut p = [0u8; 4];
        put_res(&mut p, 3, 1, &[5, 6], 4);     // fields 1 and 2 of 3 bits: 1 and 2
        assert_eq!(p, [0x88, 0, 0, 0]);
        let mut p = [7u8; 2];
        put_res(&mut p, 0, 3, &[1], 0);
        assert_eq!(p, [7, 7]);
    }
    #[test] fn cat_take_needs_a_whole_block_of_one_part() {
        assert_eq!(cat_take(&[0, 1024, 2048, 2100], 0), Some((0, 0)));
        assert_eq!(cat_take(&[0, 1024, 2048, 2100], 2), Some((2, 0)));
        assert_eq!(cat_take(&[0, 1500, 2100], 1), None);    // straddles the parts
        assert_eq!(cat_take(&[0, 1500, 2100], 2), None);    // starts inside part 1
        assert_eq!(cat_take(&[0, 2048], 1), Some((0, 1)));
        assert_eq!(cat_take(&[0], 0), None);
    }
}

// ---- K22: structural.c:1860-2105 `amend_index` ----
/// structural.c:1887 `AMSEG`: the indices or bitmap words of one segment of a compaction.
const AMSEG: usize = 4096;
/// The three Lean arrays `amend_index` asks its caller to allocate, in this order: `Dom` (`nd` words, only when
/// compacting and no index misses), `Rank` (`m` words, likewise), `Res` (the answer).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AmOut { Dom, Rank, Res }
fn seg_hi(s: usize, lim: usize) -> usize { ((s + 1) * AMSEG).min(lim) }
/// structural.c:1994 `amx_scan`: the prefix of `sc` into `so` (`so[0] = 0`).
fn seg_scan(so: &mut [usize], sc: &[usize]) {
    so[0] = 0;
    for (s, c) in sc.iter().enumerate() { so[s + 1] = so[s] + c }
}
/// structural.c:2004 `amend_index`: `amendRounds` of the `idx` indices (`wi` bytes each) into `n` slots, and with
/// `compact` also `amendCompact` of them widened, out of one bitmap of `n` bits. Word 0 of `Res` is the round count (all
/// ones on a miss, whose index is word 1), then the round ends, the positions grouped by round, and a widened index
/// column. `alloc` makes each output array of the given number of words; it is called for `Dom` and `Rank` only when
/// `compact` and no index misses, and for `Res` once, last.
#[allow(clippy::too_many_arguments)]
pub fn amend_index<'o>(run: Runner, n: usize, wi: usize, ranked: bool, compact: bool, idx: &[u8],
                       alloc: &mut dyn FnMut(AmOut, usize) -> &'o mut [i64]) {
    use alloc::{vec, vec::Vec};
    use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
    use crate::{QLEAN_COST_COPY as COPY, QLEAN_COST_GATHER as GATHER};
    let m = idx.len() / wi;
    let mut wid: Vec<i64> = if wi == 8 { Vec::new() } else { pod::uninit(m) };
    let miss_at = AtomicUsize::new(m);
    // keep the least position whose index misses `[0, n)`: q reports the first one
    // a chunk is tested without an early exit so the test vectorises; only a chunk that holds a miss is searched
    let first_miss = |lo: usize, v: &[i64]| {
        for (c, ch) in v.chunks(256).enumerate() {
            if ch.iter().fold(false, |a, &x| a | (x as u64 >= n as u64)) {
                let k = ch.iter().position(|&x| x as u64 >= n as u64).unwrap();
                miss_at.fetch_min(lo + c * 256 + k, Relaxed);
                return;
            }
        }
    };
    if wi == 8 {
        let ix = pod::cast::<i64>(idx).expect("amend_index: the 8-byte index column is misaligned");
        crate::c::run_map(run, &mut [], m, 0, COPY, 16, &|lo, hi, _| first_miss(lo, &ix[lo..hi]));
    } else {
        macro_rules! widen { ($t:ty) => {{
            let src = pod::cast::<$t>(idx).expect("amend_index: the index column is misaligned");
            crate::c::run_map(run, pod::bytes_mut(&mut wid), m, 8, COPY, 16, &|lo, hi, o| {
                let o = pod::cast_mut::<i64>(o).expect("amend_index: widened slice");
                for (d, &x) in o.iter_mut().zip(&src[lo..hi]) { *d = x as i64 }
                first_miss(lo, o)
            })
        }}; }
        match wi { 1 => widen!(i8), 2 => widen!(i16), 4 => widen!(i32), _ => panic!("qlean amend: index width {wi}; 1, 2, 4 and 8 are read") };
    }
    let ix: &[i64] = if wi == 8 { pod::cast(idx).unwrap() } else { &wid };
    let miss = miss_at.load(Relaxed) < m;
    let bad = if miss { ix[miss_at.load(Relaxed)] } else { 0 };
    let mut rounds = m.min(1);
    let (bw, ns) = (n.div_ceil(64), m.div_ceil(AMSEG));
    let nsw = bw.div_ceil(AMSEG);
    let compacting = compact && !miss;
    let (mut seen, mut dup): (Vec<i64>, Vec<i64>) = (Vec::new(), Vec::new());
    let rep = AtomicBool::new(false);
    if !miss && ((ranked && m > 1) || compact) {
        seen = vec![0i64; bw.max(1)];
        if ranked { dup = vec![0i64; bw.max(1)] }
        // atomic only when the pass was split: a lock prefix a bit on one thread is what the split was meant to save
        let (sa, da) = (pod::atomics(&mut seen), pod::atomics(&mut dup));
        crate::c::run_map(run, &mut [], m, 0, GATHER, 16, &|lo, hi, _| {
            let whole = lo == 0 && hi == m;
            let mut again = false;
            for &x in &ix[lo..hi] {
                let (w, bit) = ((x as u64 >> 6) as usize, 1u64 << (x as u64 & 63));
                let old = if whole { let o = sa[w].load(Relaxed) as u64; sa[w].store((o | bit) as i64, Relaxed); o }
                          else { sa[w].fetch_or(bit as i64, Relaxed) as u64 };
                if ranked && old & bit != 0 {
                    again = true;
                    if whole { da[w].store(da[w].load(Relaxed) | bit as i64, Relaxed) } else { da[w].fetch_or(bit as i64, Relaxed); }
                }
            }
            if again { rep.store(true, Relaxed) }
        });
    }
    let rep = rep.load(Relaxed);
    let (mut sc, mut so): (Vec<usize>, Vec<usize>) = (Vec::new(), Vec::new());
    let (mut ll, mut lr): (Vec<i64>, Vec<u32>) = (Vec::new(), Vec::new());
    if rep || compacting {
        let nsm = nsw.max(ns);
        sc = vec![0usize; nsm + 1];
        so = vec![0usize; nsm + 1];
        let mut pre: Vec<i64> = pod::uninit(bw.max(1));
        crate::c::run_map(run, pod::bytes_mut(&mut sc[..nsw]), nsw, 8, COPY * AMSEG as u32, 64, &|lo, hi, o| {
            let o = pod::cast_mut::<usize>(o).expect("amend_index: counts");
            for (s, c) in (lo..hi).zip(o) { *c = (s * AMSEG..seg_hi(s, bw)).map(|w| (seen[w] as u64).count_ones() as usize).sum() }
        });
        let sc0 = sc[..nsw].to_vec();
        seg_scan(&mut so, &sc0);
        let nd = so[nsw];
        let mut dvec: Vec<i64>;
        let (dom, d): (&mut [i64], &mut [i64]) = if compacting { let dom = alloc(AmOut::Dom, nd); (dom, alloc(AmOut::Rank, m)) }
                                                 else { dvec = pod::uninit(m.max(1)); (&mut [], &mut dvec) };
        // the popcount prefix of a word, and with `compacting` the distinct indices themselves, ascending
        let doma = pod::atomics(dom);
        crate::c::run_map(run, pod::bytes_mut(&mut pre[..bw]), nsw, AMSEG * 8, GATHER * AMSEG as u32, 64, &|lo, hi, o| {
            let o = pod::cast_mut::<i64>(o).expect("amend_index: prefix");
            for s in lo..hi {
                let mut j = so[s];
                for w in s * AMSEG..seg_hi(s, bw) {
                    o[w - lo * AMSEG] = j as i64;
                    let mut x = seen[w] as u64;
                    if compacting { while x != 0 { doma[j].store((w as u64 * 64 + x.trailing_zeros() as u64) as i64, Relaxed); j += 1; x &= x - 1 } }
                    else { j += x.count_ones() as usize }
                }
            }
        });
        // an index's position among the distinct ones: the popcount prefix of its word and the bits under it
        crate::c::run_map(run, pod::bytes_mut(&mut d[..m]), m, 8, GATHER, 16, &|lo, hi, o| {
            let o = pod::cast_mut::<i64>(o).expect("amend_index: ranks");
            for (&x, r) in ix[lo..hi].iter().zip(o) {
                let (w, u) = ((x as u64 >> 6) as usize, x as u64 & 63);
                *r = (pre[w] as u64 + (seen[w] as u64 & ((1u64 << u) - 1)).count_ones() as u64) as i64;
            }
        });
        if rep {
            let isdup = |x: i64| dup[(x as u64 >> 6) as usize] as u64 >> (x as u64 & 63) & 1;
            crate::c::run_map(run, pod::bytes_mut(&mut sc[..ns]), ns, 8, GATHER * AMSEG as u32, 64, &|lo, hi, o| {
                let o = pod::cast_mut::<usize>(o).expect("amend_index: counts");
                for (s, c) in (lo..hi).zip(o) { *c = ix[s * AMSEG..seg_hi(s, m)].iter().map(|&x| isdup(x) as usize).sum() }
            });
            let sc0 = sc[..ns].to_vec();
            seg_scan(&mut so, &sc0);
            let nl = so[ns];
            ll = pod::uninit(nl);
            lr = pod::uninit(nl);
            let la = pod::atomics(&mut ll);
            crate::c::run_map(run, &mut [], ns, 0, GATHER * AMSEG as u32, 64, &|lo, hi, _| {
                for s in lo..hi {
                    let mut j = so[s];
                    for k in s * AMSEG..seg_hi(s, m) { if isdup(ix[k]) != 0 { la[j].store(k as i64, Relaxed); j += 1 } }
                }
            });
            // ranks stay serial: proportional to the repeats alone
            let mut cnt = vec![0u32; nd.max(1)];
            rounds = 1;
            for (r, &k) in lr.iter_mut().zip(&ll) {
                let c = &mut cnt[d[k as usize] as usize];
                *r = *c;
                *c += 1;
                rounds = rounds.max(*c as usize);
            }
        }
    }
    drop((seen, dup));
    let tail = if rounds > 1 { rounds + m } else { 0 };
    let o = alloc(AmOut::Res, 2 + tail + if wi != 8 && !miss { m } else { 0 });
    o[0] = if miss { -1 } else { rounds as i64 };
    o[1] = bad;
    let (head, rest) = o[2..].split_at_mut(if rounds > 1 { rounds } else { 0 });
    let rest = if rounds > 1 {
        let (ends, pos) = (head, &mut rest[..m]);
        let nl = ll.len();
        ends.fill(0);
        // round 0 is every position but the later occurrences of a repeat; each segment's share of it is its
        // length less those, so the fill knows where to start
        for s in 0..ns { sc[s] = seg_hi(s, m) - s * AMSEG - (so[s + 1] - so[s]) }
        for (&r, &k) in lr.iter().zip(&ll) { ends[r as usize] += 1; if r == 0 { sc[k as usize / AMSEG] += 1 } }
        let mut t = 0;
        for c in &mut sc[..ns] { let v = *c; *c = t; t += v }
        ends[0] += (m - nl) as i64;
        for r in 1..rounds { ends[r] += ends[r - 1] }
        let pa = pod::atomics(pos);
        crate::c::run_map(run, &mut [], ns, 0, COPY * AMSEG as u32, 64, &|lo, hi, _| {
            for s in lo..hi {
                let (mut c, mut j) = (so[s], sc[s]);
                for k in s * AMSEG..seg_hi(s, m) {
                    if c < so[s + 1] && ll[c] as usize == k { if lr[c] == 0 { pa[j].store(k as i64, Relaxed); j += 1 } c += 1 }
                    else { pa[j].store(k as i64, Relaxed); j += 1 }
                }
            }
        });
        // the later rounds hold only repeats, few by construction: fill each from the previous round's end
        let mut at: Vec<i64> = (0..rounds).map(|r| if r == 0 { 0 } else { ends[r - 1] }).collect();
        for (&r, &k) in lr.iter().zip(&ll) {
            if r != 0 { pa[at[r as usize] as usize].store(k, Relaxed); at[r as usize] += 1 }
        }
        &mut rest[m..]
    } else { rest };
    if wi != 8 && !miss { rest[..m].copy_from_slice(ix) }
}

#[cfg(test)]
mod k19_tests {
    use super::*;
    use crate::c::qlean_run_c;
    fn rng(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }
    // `splitBytes` read off the definition: pieces between non-overlapping left-to-right occurrences of `d`
    fn split_ref(d: &[u8], b: &[u8]) -> Vec<Vec<u8>> {
        let (mut ps, mut cur, mut i) = (vec![], vec![], 0);
        while i < b.len() {
            if !d.is_empty() && b[i..].starts_with(d) { ps.push(core::mem::take(&mut cur)); i += d.len() } else { cur.push(b[i]); i += 1 }
        }
        ps.push(cur);
        ps
    }
    #[test] fn split_cuts_and_pieces_match_the_definition() {
        let mut s = 5;
        for _ in 0..600 {
            let alpha = 1 + rng(&mut s) % 3;
            let d: Vec<u8> = (0..rng(&mut s) % 4).map(|_| (rng(&mut s) % alpha) as u8).collect();
            let b: Vec<u8> = (0..rng(&mut s) % 150).map(|_| (rng(&mut s) % alpha) as u8).collect();
            let cuts = split_cuts(&d, &b);
            let (mut out, mut offs) = (vec![0u8; b.len() - cuts * d.len()], vec![0usize; cuts + 2]);
            split(&d, &b, &mut out, &mut offs);
            let want = split_ref(&d, &b);
            assert_eq!(cuts + 1, want.len(), "d {d:?} b {b:?}");
            for (k, p) in want.iter().enumerate() { assert_eq!(&out[offs[k] >> 1..offs[k + 1] >> 1], &p[..], "d {d:?} b {b:?} piece {k}") }
            assert_eq!((offs[0], offs[cuts + 1] >> 1), (1, out.len()));
        }
    }
    #[test] fn reverse_shift_translate_match_the_definition() {
        let mut s = 9;
        for _ in 0..300 {
            let w = [1usize, 2, 4, 8, 16][rng(&mut s) as usize % 5];
            let n = rng(&mut s) as usize % 200;
            let src: Vec<u8> = (0..n * w).map(|_| rng(&mut s) as u8).collect();
            let el = |j: usize| &src[j * w..(j + 1) * w];
            let mut out = vec![0u8; n * w];
            reverse(qlean_run_c, w, &src, n, &mut out);
            for j in 0..n { assert_eq!(&out[j * w..(j + 1) * w], el(n - 1 - j), "reverse w {w} n {n} j {j}") }
            let fill = rng(&mut s);
            for k in [0i64, 1, -1, n as i64, -(n as i64), n as i64 + 1, 1 - n as i64, i64::MAX, i64::MIN, rng(&mut s) as i64 % 300] {
                shift(qlean_run_c, w, fill, k, &src, n, &mut out);
                for j in 0..n {
                    let i = (j as u64).wrapping_sub(k as u64);
                    let mut f = [0u8; 16];
                    f[..8].copy_from_slice(&fill.to_le_bytes());
                    let want = if i < n as u64 { el(i as usize) } else { &f[..w] };
                    assert_eq!(&out[j * w..(j + 1) * w], want, "shift w {w} n {n} k {k} j {j}");
                }
            }
            let tab: Vec<u8> = (0..256).map(|_| rng(&mut s) as u8).collect();
            let mut o = vec![0u8; src.len()];
            translate(qlean_run_c, &tab, &src, &mut o);
            assert!(src.iter().zip(&o).all(|(&b, &t)| t == tab[b as usize]));
        }
    }
    #[test] fn ids_place_with_no_table_reads_each_id_as_itself_below_nm() {
        // ids 0 1 2 3 at 2 bits placed at 4 bits from field 1 (unaligned: through the part's own buffer); `nm` 3 drops id 3
        let mut out = [0u8; 3];
        ids_place(&mut out, 1, 4, 4, 2, &[0b11_10_01_00], None, 3);
        assert_eq!(out, [0x00, 0x21, 0x00]);
        // aligned, whole-byte answer, through a table with its trailing zero
        let mut o8 = [0u8; 4];
        ids_place(&mut o8, 0, 8, 4, 2, &[0b11_10_01_00], Some(&[7, 8, 9, 0]), 3);
        assert_eq!(o8, [7, 8, 9, 0]);
    }
}

#[cfg(test)]
mod k21_tests {
    use super::*;
    use crate::c::qlean_run_c;
    // expected spellings are the C's: a null is empty, INT64_MIN + 1 keeps its sign
    #[test] fn digits_of_every_width() {
        let v = [i64::MIN, i64::MIN + 1, -1, 0, 9, 10, 99, 100, i64::MAX];
        let src: alloc::vec::Vec<u8> = v.iter().flat_map(|x| x.to_le_bytes()).collect();
        let mut at = [0usize; 2];
        let total = str_count(qlean_run_c, 8, &src, v.len(), &mut at);
        let (mut blob, mut offs) = (alloc::vec![0u8; total], [0usize; 10]);
        str_write(qlean_run_c, 8, &src, v.len(), &at, &mut blob, &mut offs);
        assert_eq!(core::str::from_utf8(&blob).unwrap(), "-9223372036854775807-10910991009223372036854775807");
        assert_eq!(offs[0], 1);
        assert_eq!(offs.iter().map(|o| o >> 1).collect::<alloc::vec::Vec<_>>(), [0, 0, 20, 22, 23, 24, 26, 28, 31, 50]);
        let src: alloc::vec::Vec<u8> = [i16::MIN, -7, 300].iter().flat_map(|x| x.to_le_bytes()).collect();
        let mut at = [0usize; 2];
        let total = str_count(qlean_run_c, 2, &src, 3, &mut at);
        assert_eq!(total, 5);
    }
    #[test] fn mmu_is_the_left_fold_with_slack_rows() {
        let (a0, a1, a2) = ([1.0, 2.0], [3.0, 4.0], [5.0, 6.0]);
        let (b0, b1) = ([1.0, 0.0, 2.0], [0.0, 1.0, 3.0]);
        let mut out = [9.0; 12 * 1];
        out.fill(9.0);
        mmu(&[&a0, &a1, &a2], &[&b0, &b1], 3, &mut out);
        assert_eq!(&out[..9], &[1.0, 2.0, 8.0, 3.0, 4.0, 18.0, 5.0, 6.0, 28.0]);
    }
    #[test] fn transpose_and_back() {
        let (c0, c1) = ([1u8, 2, 3, 4, 5, 6], [7u8, 8, 9, 10, 11, 12]);
        let mut rows = [0u8; 12];
        transpose(2, 3, &[&c0, &c1], &mut rows);
        assert_eq!(rows, [1, 2, 7, 8, 3, 4, 9, 10, 5, 6, 11, 12]);
        let mut cols = [0u8; 12];
        untranspose(2, 3, 2, &rows, &mut cols);
        assert_eq!(cols, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
        // width 3 takes the run-time path, width 0 and no columns move nothing
        let mut o3 = [0u8; 6];
        transpose(3, 1, &[&[1, 2, 3], &[4, 5, 6]], &mut o3);
        assert_eq!(o3, [1, 2, 3, 4, 5, 6]);
        transpose(0, 5, &[&[], &[]], &mut []);
        transpose(4, 5, &[], &mut []);
    }
    #[test] fn til_fill_counts_from_the_block_start() {
        let mut b = [0i64; 3];
        til_fill(&mut b, 1022);
        assert_eq!(b, [1022, 1023, 1024]);
    }
}

#[cfg(test)]
mod k22_tests {
    use super::*;
    use crate::c::qlean_run_c;
    // `amendRounds` and `amendCompact` read off their definitions: the round of a position is how many earlier
    // positions hold the same index; the compaction is the sorted distinct indices and each index's place in them
    fn spec(n: usize, ix: &[i64]) -> (Vec<i64>, Vec<i64>, Vec<i64>) {
        if let Some(&b) = ix.iter().find(|&&x| x as u64 >= n as u64) { return (vec![-1, b], vec![], vec![]) }
        let rk: Vec<usize> = (0..ix.len()).map(|k| ix[..k].iter().filter(|&&x| x == ix[k]).count()).collect();
        let rounds = rk.iter().map(|r| r + 1).max().unwrap_or(0);
        let mut res = vec![rounds as i64, 0];
        let mut ends = vec![];
        let mut pos = vec![];
        for r in 0..rounds { pos.extend((0..ix.len()).filter(|&k| rk[k] == r).map(|k| k as i64)); ends.push(pos.len() as i64) }
        if rounds > 1 { res.extend(ends); res.extend(pos) }
        let mut dom: Vec<i64> = ix.to_vec();
        dom.sort_unstable();
        dom.dedup();
        let ranks = ix.iter().map(|x| dom.binary_search(x).unwrap() as i64).collect();
        (res, dom, ranks)
    }
    #[test] fn amend_index_matches_the_definition() {
        let mut s = 0x9e3779b97f4a7c15u64;
        let mut rng = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        for (m, n, dist) in [(0usize, 5usize, 1u64), (1, 1, 1), (7, 4, 3), (9000, 300000, 100), (9000, 300000, 100000), (5000, 70, 70)] {
            for miss in [false, true] {
                let mut ix: Vec<i64> = (0..m).map(|_| (rng() % dist % n.max(1) as u64) as i64).collect();
                if miss && m > 0 { ix[m / 2] = n as i64 }
                for wi in [1usize, 2, 4, 8] {
                    if wi < 8 && ix.iter().any(|&x| x > 127) { continue }
                    let bytes: Vec<u8> = ix.iter().flat_map(|x| x.to_le_bytes()[..wi].to_vec()).collect();
                    for ranked in [false, true] {
                        let (sres, sdom, srk) = spec(n, &ix);
                        let mut bufs = [vec![0i64; m + 1], vec![0i64; m + 1], vec![0i64; 3 * m + 3]];
                        let sizes = core::cell::Cell::new([0usize; 3]);
                        let [b0, b1, b2] = &mut bufs;
                        let mut free = [Some(&mut b0[..]), Some(&mut b1[..]), Some(&mut b2[..])];
                        amend_index(qlean_run_c, n, wi, ranked, true, &bytes, &mut |o, w| {
                            let mut z = sizes.get();
                            z[o as usize] = w;
                            sizes.set(z);
                            free[o as usize].take().unwrap().split_at_mut(w).0
                        });
                        let z = sizes.get();
                        let (dom, rk, res) = (&bufs[0][..z[0]], &bufs[1][..z[1]], &bufs[2][..z[2]]);
                        if ranked || sres[0] <= 1 {
                            let tail = if wi != 8 && sres[0] >= 0 { ix.clone() } else { vec![] };
                            let want: Vec<i64> = sres.iter().copied().chain(tail).collect();
                            assert_eq!(res, &want[..], "m {m} n {n} wi {wi} dist {dist} miss {miss} ranked {ranked}");
                        }
                        assert_eq!(dom, &sdom[..], "dom m {m} n {n} wi {wi}");
                        assert_eq!(rk, &srk[..], "rk m {m} n {n} wi {wi}");
                    }
                }
            }
        }
    }
}

// ---- B28: structural.c:1-467, the part of the Lean boundary that holds no object ----
/// What `concat_foR_append` found: the first part's last block grown in place by the parts after it. `put` writes it into
/// the first part's own metadata and pack once Lean has handed them over.
pub struct Grow {
    /// the block grown, how many of its elements are the first part's own, the first part's count, and the elements added
    b: usize, lo: usize, n: usize, m: usize,
    /// the block's residual width, where its residuals start in the pack, its base and its sum once grown
    w: u8, s: usize, base: u64, sum: i64,
    /// elements `lo ..` of the grown block are the added ones
    buf: [i64; BLK],
}
/// structural.c:414 `concat_foR_append`'s decision and block: `Some` only where the writer, asked about the grown block,
/// keeps its base, maximum and width with no exception, and the first part was the writer's to begin with. `parts` are the
/// `k >= 1` parts' views, `start` their `k + 1` boundaries, `ew` the element width; `None` is `none`, and the caller re-encodes.
pub fn append_plan(parts: &[Coc], start: &[usize], ew: usize) -> Option<Grow> {
    let (h, k) = (parts.first()?, parts.len());
    let (n, lo, b, m) = (h.meta.n, h.meta.n % BLK, h.meta.n / BLK, start[k] - h.meta.n);
    // `h.meta.n` is the part's own count wherever `lo != 0`: only a count past the grid is clamped, to a block boundary. The
    // writer's form covers the block; a patch list rides along in the pack's tail untouched where block `b` has no exception,
    // every one then lying before the append point; `put_res` measures from the base, so a block whose frame is above it declines.
    if lo == 0 || lo + m > BLK || !h.std(n) || h.blk_nexc(b) != 0 || h.frame(b) != h.meta.base[b] as u64 || !trailer_ok(h, n, ew, false) {
        return None;
    }
    let mut buf = [0i64; BLK];
    unpack_run(&mut buf[..lo], h, b, 0, false);
    cat_fill(&|i| plain(&parts[i]), start, ew, false, &mut buf[lo..lo + m], n);
    let (mut mn, mut mx, mut sum, mut w, mut fd, mut nexc) = (0i64, 0i64, 0i64, 0u8, 0u64, 0u32);
    let (lb, over) = (AtomicUsize::new(0), core::sync::atomic::AtomicI32::new(0));
    let mut meta = EncMeta { b: 0, base: &mut mn, maxv: &mut mx, width: &mut w, bsum: &mut sum, frm: Some(&mut fd), nexc: &mut nexc,
                             exp: None, below: 0, lb: &lb, over: &over };
    if crate::enc::blk_meta(&mut meta, &buf[..lo + m], ew) != 0 || fd != 0 || mn != h.meta.base[b] || mx != h.meta.maxv[b] || w != h.meta.width[b] {
        return None;
    }
    Some(Grow { b, lo, n, m, w, s: h.meta.off[b] as usize, base: mn as u64, sum, buf })
}
impl Grow {
    /// The first part's own metadata and pack (`33 * nblk + 16` bytes, and its pack) with the block's sum and the trailer's
    /// count brought up to the grown column and the added residuals written into the block.
    pub fn put(&self, meta: &mut [u8], pack: &mut [u8]) {
        let (nb, at) = (meta.len() / 33, 24 * (meta.len() / 33) + 8 * self.b);
        meta[at..at + 8].copy_from_slice(&self.sum.to_ne_bytes());
        meta[32 * nb + 8..32 * nb + 16].copy_from_slice(&((self.n + self.m) as u64).to_ne_bytes());
        put_res(&mut pack[self.s..self.s + BLK * self.w as usize / 8], self.w, self.lo, &self.buf[self.lo..self.lo + self.m], self.base);
    }
}

/// structural.c:87 `row_at`: part `i` of `rs` read at `want` bytes -- where it lies when it is long enough, else a copy of
/// what it has followed by zeros (`Column.bitsAt`'s convention), and a part the array does not have at all is all zeros.
pub fn row_at<'a>(rs: &[&'a [u8]], i: usize, want: usize) -> alloc::borrow::Cow<'a, [u8]> {
    match rs.get(i) {
        Some(r) if r.len() >= want => alloc::borrow::Cow::Borrowed(&r[..want]),
        r => { let mut v = alloc::vec![0u8; want]; copy_row(&mut v, r.copied()); alloc::borrow::Cow::Owned(v) }
    }
}
fn copy_row(dst: &mut [u8], r: Option<&[u8]>) { let t = r.map_or(0, |r| r.len().min(dst.len())); if let Some(r) = r { dst[..t].copy_from_slice(&r[..t]) } }
/// structural.c:96 `rows_at`: every row of a matrix at `want` bytes; one short row pads all of them into a single buffer.
pub struct Rows<'a, 'b> { rs: &'b [&'a [u8]], want: usize, pad: Option<Vec<u8>> }
pub fn rows_at<'a, 'b>(rs: &'b [&'a [u8]], want: usize) -> Rows<'a, 'b> {
    let pad = rs.iter().any(|r| r.len() < want).then(|| {
        let mut v = alloc::vec![0u8; rs.len() * want];
        if want != 0 { for (d, r) in v.chunks_exact_mut(want).zip(rs) { copy_row(d, Some(r)) } }
        v
    });
    Rows { rs, want, pad }
}
impl Rows<'_, '_> {
    /// row `i`, `want` bytes
    pub fn get(&self, i: usize) -> &[u8] {
        match &self.pad { Some(p) => &p[i * self.want..(i + 1) * self.want], None => &self.rs[i][..self.want] }
    }
}

#[cfg(test)]
mod b28_tests {
    use super::*;
    #[test] fn short_parts_read_as_zeros_and_nothing_is_copied_when_none_is_short() {
        let (a, b): (&[u8], &[u8]) = (&[1, 2, 3, 4], &[9]);
        let rs = [a, b];
        assert!(matches!(row_at(&rs, 0, 3), alloc::borrow::Cow::Borrowed(r) if r == [1, 2, 3]));
        assert_eq!(&*row_at(&rs, 1, 3), &[9, 0, 0]);
        assert_eq!(&*row_at(&rs, 2, 3), &[0, 0, 0]);
        let m = rows_at(&rs, 3);
        assert_eq!((m.get(0), m.get(1)), (&[1u8, 2, 3][..], &[9u8, 0, 0][..]));
        let m = rows_at(&rs[..1], 3);
        assert!(m.pad.is_none() && m.get(0) == [1, 2, 3]);
        assert_eq!(rows_at(&[], 5).pad.as_deref(), None);
    }
}
