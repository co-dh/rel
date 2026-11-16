#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), structural.c: bit helpers and the encoded-column readers (A34), the encoder sources of reverse,
//! cycle, shift and concat (A35), concat of encoded columns (A36), gathers (A37–A38), cycles, concats and
//! enumerations (A39), the symbol dictionary table (A40), dictionary concat (A41a), `til` and `scatter` (A41b).
//! The `qlean_structural_*` entries and the `sd_*` dictionary cache (which holds `lean_object`s) stay C (§1).
//! An encoder source (`coc_fill`, `coc_hint`, `coc_ints`, coc.h:2001-2018) is a Rust fn here over views; its C
//! callback keeps a one-line body that unpacks its `ctx` and calls the `qrs_*` shim.

use crate::alp::Cocf;
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
        let v: alloc::vec::Vec<u64> = (0..crate::BLK).map(|i| crate::res::res_get(sp, w, crate::BLK - 1 - i)).collect();
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
/// coc.h:1864 `coc_sumnul`: the null the writer's block sums skip, which its trailer records. C keeps its copy until
/// A16 ports the writer.
fn coc_sumnul(w: usize, alp: bool) -> i64 {
    if alp || w == 1 || w == 8 { i64::MIN } else if w == 2 { i16::MIN as i64 } else { i32::MIN as i64 }
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
/// structural.c:320 `trailer_ok`: `c`'s trailer fits `n` elements of `w` bytes (`alp`: an ALP column's).
pub fn trailer_ok(c: &Coc, n: usize, w: usize, alp: bool) -> bool {
    c.meta.sumn == n as u64 && c.meta.sumnul == coc_sumnul(w, alp)
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

// ---- A37: structural.c:926-1146 ----
/// structural.c:936 `qlean_structural_all_below`: every index is below `n`.
pub fn all_below(n: usize, idx: &[i64]) -> bool { unimplemented!("A37: qlean_structural_all_below") }
/// structural.c:926 `gather_run` and its entry: `src[idx[i]]` (`w` bytes) into `out`, `fill` out of range.
pub fn gather(run: Runner, w: usize, fill: u64, src: &[u8], idx: &[i64], out: &mut [u8]) { unimplemented!("A37: gather_run") }
/// structural.c:1045 `gather_foR_run`: from an encoded column.
pub fn gather_enc(run: Runner, w: usize, fill: u64, c: &Coc, idx: &[i64], out: &mut [u8]) { unimplemented!("A37: gather_foR_run") }
/// structural.c:1084 `gather_foR_idx_run`: encoded column, encoded indices (`count` of them).
pub fn gather_enc_idx(run: Runner, w: usize, fill: u64, c: &Coc, ic: &Coc, count: usize, out: &mut [u8]) {
    unimplemented!("A37: gather_foR_idx_run")
}
/// structural.c:1122 `gather_bits_run`
pub fn gather_bits(run: Runner, n: usize, bits: &[u8], idx: &[i64], out: &mut [u8]) { unimplemented!("A37: gather_bits_run") }

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
    let at: alloc::vec::Vec<usize> =
        core::iter::once(0).chain(wv.iter().scan(0usize, |t, &c| { *t += c.max(0) as usize; Some(*t) })).collect();
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
pub fn gather_ids_enc(run: Runner, w: u32, wout: u32, fill: u64, src: &[u8], n: usize, ic: &Coc, count: usize, out: &mut [u8]) {
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
/// structural.c:1898 `qlean_structural_enum_ids`: values as ids into `0 .. d` at `w` bits, `nullid` outside.
pub fn enum_ids(n: usize, d: usize, nullid: usize, w: u32, b: &[u8], out: &mut [u8]) {
    for i in 0..n { crate::ids::id_put(out, w, i, enum_id(enum_at(b, b.len() / 8, i), nullid)) }
}
/// structural.c:1924 `qlean_structural_enum_ids_for`: from an encoded column.
pub fn enum_ids_enc(n: usize, d: usize, nullid: usize, w: u32, c: &Coc, out: &mut [u8]) {
    let mut v = [0i64; crate::BLK];
    for b in 0..n.div_ceil(crate::BLK) {
        let (lo, nb) = (b * crate::BLK, crate::BLK.min(n - b * crate::BLK));
        c.decode_blk(b, nb, &mut v);
        for (i, &x) in v[..nb].iter().enumerate() { crate::ids::id_put(out, w, lo + i, enum_id(x, nullid)) }
    }
}
/// structural.c:1949 `ids_place`: `cn` ids at `w` mapped by `tab` (`nm` entries) to `wout` bits at `at`.
pub fn ids_place(out: &mut [u8], at: usize, wout: u32, cn: usize, w: u32, pp: &[u8], tab: &[usize]) {
    let val = |j: usize| tab.get(crate::ids::id_at(pp, w, j)).map_or(0, |&t| t as u64);
    if (at * wout as usize) & 7 == 0 {
        let dst = &mut out[at * wout as usize / 8..];
        for j in 0..cn { crate::ids::id_put(dst, wout, j, val(j)) }
    } else {
        // packed into its own buffer and bit-copied, so no store crosses into the part before it
        let mut tmp = alloc::vec![0u8; crate::ids::ids_bytes(cn, wout) + 1];
        for j in 0..cn { crate::ids::id_put(&mut tmp, wout, j, val(j)) }
        crate::ids::bitcopy(out, at * wout as usize, &tmp, 0, cn * wout as usize);
    }
}
/// structural.c:1969 `qlean_structural_concat_ids`: each part's ids through its map.
pub fn concat_ids(wout: u32, counts: &[usize], widths: &[u32], maps: &[&[usize]], parts: &[&[u8]], out: &mut [u8]) {
    let k = counts.len().min(parts.len());
    let mut at = 0;
    for i in 0..k {
        // the part is read at the `cn` ids `counts` claims and the `w` `widths` claims; short of that it is zeros
        let w = widths.get(i).copied().unwrap_or(0);
        let need = crate::ids::ids_bytes(counts[i], w);
        let padded;
        let pp = if parts[i].len() >= need { parts[i] } else { padded = [parts[i], &alloc::vec![0u8; need - parts[i].len()]].concat(); &padded[..] };
        ids_place(out, at, wout, counts[i], w, pp, maps.get(i).copied().unwrap_or(&[]));
        at += counts[i];
    }
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
    /// structural.c:2105 `symtab_fork` after the allocation: `s`'s slots copied, entries at or past `d` counted stale.
    pub fn fork(&mut self, s: &[u32], d: usize) {
        // every non-empty slot is an entry of the chain or a stale one, so `s`'s count + stale is their number
        let used = s.iter().filter(|&&x| x != 0).count();
        self.slot.copy_from_slice(s);
        (self.mask, self.cnt, self.stale) = (s.len() - 1, d, used.saturating_sub(d));
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
        f.fork(&s, 3);
        assert_eq!((f.cnt, f.mask, f.stale), (3, 15, 2));
        assert_eq!(f.slot, &s[..]);
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
            enum_ids(37, 3, 2, w, &b, &mut out);
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
            enum_ids(n, 1 << 20, 0, w, &raw, &mut a);
            enum_ids_enc(n, 1 << 20, 0, w, &c, &mut b);
            assert_eq!(a, b, "w {w}");
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
            let (mr, pr): (Vec<&[usize]>, Vec<&[u8]>) = (maps.iter().map(|m| &m[..]).collect(), raw.iter().map(|p| &p[..]).collect());
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
