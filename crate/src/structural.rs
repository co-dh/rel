#![forbid(unsafe_code)]
//! Column (a), structural.rs: bit helpers and the encoded-column readers (A34), the encoder sources of reverse,
//! cycle, shift and concat (A35), concat of encoded columns (A36), gathers (A37–A38), cycles, concats and
//! enumerations (A39), the symbol dictionary table (A40), dictionary concat (A41a), `til` and `scatter` (A41b).
//! The `qlean_structural_*` entries and the `sd_*` dictionary cache (which holds `lean_object`s) stay C (§1).
//! An encoder source (`coc_fill`, `coc_hint`, `coc_ints`, coc.rs) is a Rust fn here over views; its C
//! callback keeps a one-line body that unpacks its `ctx` and calls the `qrs_*` shim.

use alloc::vec::Vec;
use core::sync::atomic::{AtomicUsize, Ordering::{Relaxed, SeqCst}};
use crate::alp::Cocf;
use crate::pod::Elt;
use crate::enc::{EncMeta, EncPack};
use crate::c::Runner;
use crate::blocks::Blocks;
use crate::coc::Coc;
use crate::sym::{sym_eq, sym_hash, Syms};
use crate::pod;
/// The answer grid every producer here writes: the writer's block size (`DEFAULT_LG`, until the writer picks one). A SOURCE column's
/// blocks are read at its own `meta.lg`.
pub const WBLK: usize = 1 << crate::DEFAULT_LG;

// ---- A34: structural.rs ----
/// structural.rs `bits64_at`: 64 bits from bit `i`, zeros past the end.
pub fn bits64_at(b: &[u8], i: usize) -> u64 {
    let (byte, sh) = (i >> 3, i & 7);
    let rd = |k: usize| b.get(byte + k).map_or(0, |&x| x as u64);
    let lo = if b.len() >= byte + 8 { u64::from_le_bytes(b[byte..byte + 8].try_into().unwrap()) }
             else { (0..8).fold(0, |a, k| a | rd(k) << (8 * k)) };
    if sh == 0 { lo } else { lo >> sh | rd(8) << (64 - sh) }
}
/// structural.rs `or_bits`: the low `cnt` bits of `w` or-ed in at bit `at`.
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
/// structural.rs `copy_bits`: `len` bits of `b` from bit `from` to bit `at` of `out`.
pub fn copy_bits(out: &mut [u8], at: usize, b: &[u8], from: usize, len: usize) {
    for t in (0..len).step_by(64) { or_bits(out, at + t, bits64_at(b, from + t), (len - t).min(64)) }
}
/// coc.rs's layout over a writer's metadata of `nb` blocks: base, maxv, off, bsum (8 bytes a block each), the
/// trailer's three words (sumnul, sumn, lg), then the widths.
pub fn meta_parts(m: &mut [u8], nb: usize) -> [&mut [u8]; 6] {
    assert_eq!(m.len(), 33 * nb + 24, "qlean structural: {} metadata bytes for {nb} blocks of 33 and a 24-byte trailer", m.len());
    let (base, m) = m.split_at_mut(8 * nb);
    let (maxv, m) = m.split_at_mut(8 * nb);
    let (off, m) = m.split_at_mut(8 * nb);
    let (bsum, m) = m.split_at_mut(8 * nb);
    let (sums, width) = m.split_at_mut(24);
    [base, maxv, off, bsum, sums, width]
}
pub fn put64(d: &mut [u8], i: usize, v: u64) { d[8 * i..8 * i + 8].copy_from_slice(&v.to_ne_bytes()) }
/// structural.rs `concat_foR_move`: the four metadata sections of each part in turn, `off` recomputed from the
/// concatenated widths, the trailer the writer's for `n` elements of `w` bytes, and the packs end to end.
/// `mo`/`po` are `33 * Σ nblk + 24` and `Σ pack` bytes; every part and the answer are at block size `1 << lg`.
pub fn concat_move(lg: u32, ms: &[&[u8]], ps: &[&[u8]], n: usize, w: usize, mo: &mut [u8], po: &mut [u8]) {
    let nbs: alloc::vec::Vec<usize> = ms.iter().map(|m| m.len() / 33).collect();
    let nb: usize = nbs.iter().sum();
    let [base, maxv, off, bsum, sums, width] = meta_parts(mo, nb);
    let mut at = 0;
    for (m, &k) in ms.iter().zip(&nbs) {
        assert!(m.len() >= 33 * k + 24, "qlean structural: {} metadata bytes for {k} blocks of 33 and a 24-byte trailer", m.len());
        // the part's own sections are the byte ranges coc.rs gives, so no alignment is asked of them
        base[8 * at..8 * (at + k)].copy_from_slice(&m[..8 * k]);
        maxv[8 * at..8 * (at + k)].copy_from_slice(&m[8 * k..16 * k]);
        bsum[8 * at..8 * (at + k)].copy_from_slice(&m[24 * k..32 * k]);
        width[at..at + k].copy_from_slice(&m[32 * k + 24..33 * k + 24]);
        at += k;
    }
    put64(sums, 0, crate::enc::coc_sumnul(w, false) as u64);
    put64(sums, 1, n as u64);
    put64(sums, 2, lg as u64);
    let mut o = 0;
    for b in 0..nb { put64(off, b, o as u64); o += (1usize << lg) * width[b] as usize / 8 }
    assert_eq!(po.len(), ps.iter().map(|p| p.len()).sum::<usize>(), "qlean structural: concat pack of {} bytes", po.len());
    let mut at = 0;
    for p in ps { po[at..at + p.len()].copy_from_slice(p); at += p.len() }
}
/// structural.rs `concat_foR`'s test: every part but the last fills its blocks, and each is in the writer's form
/// (a patch list's positions and offsets are its own column's; a block past the count or a short pack would carry into
/// the answer). `part(i)` is part `i`'s view and `ns[i]` its count.
pub fn cat_aligned<'a>(k: usize, ns: &[u64], w: usize, part: impl Fn(usize) -> Coc<'a>) -> bool {
    // the blocks move as they are, so the parts must share one block size, which the answer then has
    (0..k).all(|i| {
        let c = part(i);
        c.meta.lg == part(0).meta.lg && !(i + 1 < k && c.meta.n % c.meta.blk() != 0) && c.std(ns[i] as usize) && c.pack.len() == c.meta.res_end()
            && trailer_ok(&c, c.meta.n, w, false)
    })
}
/// structural.rs `trailer_ok`: `c`'s trailer fits `n` elements of `w` bytes (`alp`: an ALP column's).
pub fn trailer_ok(c: &Coc, n: usize, w: usize, alp: bool) -> bool {
    c.meta.sumn == n as u64 && c.meta.sumnul == crate::enc::coc_sumnul(w, alp)
}
/// structural.rs `res_bytes`: block `s`'s residuals as whole bytes, from the pack or restored into `buf`.
pub fn res_bytes<'b>(c: &Coc<'b>, s: usize, buf: &'b mut [u8]) -> &'b [u8] {
    let (nbytes, so) = (c.meta.blk() * c.meta.width[s] as usize / 8, c.meta.off[s] as usize);
    if so + nbytes <= c.pack.len() { return &c.pack[so..so + nbytes] }
    // a pack shorter than its widths claim reads zeros past its end, `Column.resAt`'s convention
    let avail = c.pack.len().saturating_sub(so);
    let b = &mut buf[..nbytes];
    if avail > 0 { b[..avail].copy_from_slice(&c.pack[so..so + avail]) }
    b[avail..].fill(0);
    b
}
/// structural.rs `unpack_run`: elements `lo .. lo + dst.len()` of block `s` (reversed when `rev`) into `dst`.
pub fn unpack_run(dst: &mut [i64], c: &Coc, s: usize, lo: usize, rev: bool) {
    let (cnt, base) = (dst.len(), c.meta.base[s] as u64);
    if c.blk_nexc(s) > 0 {      // a patched block is decoded, its slots reading as base
        let mut x = pod::Scr::<i64>::new(c.meta.blk());
        c.decode_blk(s, lo + cnt, &mut x);
        for j in 0..cnt { dst[if rev { cnt - 1 - j } else { j }] = x[lo + j] }
        return;
    }
    // the direction is the iteration order, so it stays one loop per width
    fn put<F: Fn(usize) -> u64>(dst: &mut [i64], base: u64, rev: bool, f: F) {
        if rev { for (j, d) in dst.iter_mut().rev().enumerate() { *d = base.wrapping_add(f(j)) as i64 } }
        else { for (j, d) in dst.iter_mut().enumerate() { *d = base.wrapping_add(f(j)) as i64 } }
    }
    let (mut w, mut buf) = (c.meta.width[s], pod::Scr::<u8, 8192>::new(c.meta.blk() * 8));
    // a short run at an odd width reads its own fields: lanes would unpack every field before it
    if w & w.wrapping_sub(1) != 0 && cnt * 8 < lo + cnt {
        let q = res_bytes(c, s, &mut buf);
        return put(dst, base, rev, |j| crate::res::res_get(q, w, lo + j));
    }
    let mut lb = pod::Scr::<u64>::new(c.meta.blk());
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


/// One piece of an answer block: `len` elements from `lo` of block `b` of part `p` landing at `at`, or a hole.
#[derive(Clone, Copy)]
pub enum Seg { Run { p: usize, b: usize, lo: usize, len: usize, at: usize }, Hole { at: usize, len: usize } }
/// A verb's walk over the source runs an answer block is made of (structural.rs's `*_WALK`), written once and used by
/// every pass, so the passes cannot disagree about which elements a block holds.
pub type Walk<'w> = &'w dyn Fn(&mut dyn FnMut(Seg));

/// `,`: `start[p]` is where part `p` begins and the last entry is the answer's own count; a binary search finds the
/// part holding `i0`, and an empty part is stepped over by the test that advances across a full one.
pub fn cat_walk(lg: &dyn Fn(usize) -> u32, start: &[usize], i0: usize, cnt: usize, g: &mut dyn FnMut(Seg)) {
    let (np, mut k) = (start.len() - 1, 0);
    let (mut pi, mut hi) = (0, np);
    while pi + 1 < hi { let mid = (pi + hi) / 2; if start[mid] <= i0 { pi = mid } else { hi = mid } }
    while k < cnt {
        while pi + 1 < np && start[pi + 1] <= i0 + k { pi += 1 }
        let mut j = i0 + k - start[pi];
        let mut take = (start[pi + 1] - start[pi] - j).min(cnt - k);
        while take > 0 {
            let (l, blk) = (lg(pi), 1usize << lg(pi));
            let t = (blk - (j & (blk - 1))).min(take);
            g(Seg::Run { p: pi, b: j >> l, lo: j & (blk - 1), len: t, at: k });
            k += t; j += t; take -= t;
        }
    }
}
/// A shift: the answer's element `j` is the source's `j - k`, so what the source can serve of a run is one forward
/// stretch across at most two blocks and the rest is a hole at both ends.
pub fn shift_walk(lg: u32, n: usize, k: i64, i0: usize, cnt: usize, g: &mut dyn FnMut(Seg)) {
    let blk = 1usize << lg;
    let from = (i0 as i64).wrapping_sub(k);
    let head = (if from < 0 { from.unsigned_abs() as usize } else { 0 }).min(cnt);
    let mut tail = cnt;
    if from.wrapping_add(cnt as i64) > n as i64 { tail = if from >= n as i64 { head } else { (n as i64 - from) as usize } }
    let tail = tail.max(head);
    if head > 0 { g(Seg::Hole { at: 0, len: head }) }
    if tail < cnt { g(Seg::Hole { at: tail, len: cnt - tail }) }
    let (mut at, mut j) = (head, from.wrapping_add(head as i64) as usize);
    while at < tail {
        let t = (blk - (j & (blk - 1))).min(tail - at);
        g(Seg::Run { p: 0, b: j >> lg, lo: j & (blk - 1), len: t, at });
        at += t; j += t;
    }
}

/// An integer column as the view the ALP-aware passes take, its ALP part empty.
pub fn plain<'a>(c: &Coc<'a>) -> Cocf<'a> { Cocf { c: *c, exp: &[], exc_off: &[], exc_pos: &[], exc_raw: &[], f32: false } }

/// One run of `buf`, filled from block `b` of the part `f`: its decimals' integers, or at `alp` its elements' bits.
pub fn fill_run(f: &Cocf, alp: bool, out: &mut [i64], b: usize, lo: usize, rev: bool) {
    if alp { alp_run(out, f, b, lo, rev) } else { unpack_run(out, &f.c, b, lo, rev) }
}
/// Every fill below, its walk and its holes (`hole` entering where the source cannot serve).
pub fn fill<'a>(part: &dyn Fn(usize) -> Cocf<'a>, alp: bool, rev: bool, hole: i64, buf: &mut [i64], walk: Walk) {
    walk(&mut |s| match s {
        Seg::Run { p, b, lo, len, at } => fill_run(&part(p), alp, &mut buf[at..at + len], b, lo, rev),
        Seg::Hole { at, len } => buf[at..at + len].fill(hole),
    })
}
/// structural.rs `shift_fill`: of `c` shifted by `k`, `fill` entering.
pub fn shift_fill(c: &Coc, k: i64, fill_v: i64, buf: &mut [i64], i0: usize) {
    let (f, cnt) = (plain(c), buf.len());
    fill(&|_| f, false, false, fill_v, buf, &|g: &mut dyn FnMut(Seg)| shift_walk(c.meta.lg, c.meta.n, k, i0, cnt, g))
}
/// structural.rs `cat_fill`: of the parts `part(j)` starting at `start[j]`; `start` holds the part count + 1
/// entries, the last the answer's count. `w` is the element width, which only the take step asks.
pub fn cat_fill<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], _w: usize, alp: bool, buf: &mut [i64], i0: usize) {
    let cnt = buf.len();
    fill(part, alp, false, 0, buf, &|g: &mut dyn FnMut(Seg)| cat_walk(&|p| part(p).c.meta.lg, start, i0, cnt, g))
}
/// structural.rs `alp_run`: the elements' IEEE bits (what the writer's ALP steps read back at `w` bytes) of
/// elements `lo .. lo + out.len()` of block `b`, restored exceptions included; only the run is restored.
pub fn alp_run(out: &mut [i64], f: &Cocf, b: usize, lo: usize, rev: bool) {
    let (len, mut tmp, mut lb) = (out.len(), pod::Scr::<u64>::new(f.c.meta.blk()), pod::Scr::<u64>::new(f.c.meta.blk()));
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
/// structural.rs `cat_fill_alp`
pub fn cat_fill_alp<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], w: usize, buf: &mut [i64], i0: usize) {
    cat_fill(part, start, w, true, buf, i0)
}

/// structural.rs `HINT_RUN`: the largest exponent among the source blocks answer block is drawn from, and their
/// exceptions: every element exact at its own block's exponent is exact at the largest one short of `2^53`, which
/// `alp_meta_at`'s re-check catches. A shift's hole is `fill`, which may be `0n` and so an exception at any exponent;
/// it is counted as one, the re-check holding the answer to the real count.
pub fn hint<'a>(part: &dyn Fn(usize) -> Cocf<'a>, lim: &mut u32, walk: Walk) -> i32 {
    let mut e = -1;
    *lim = 0;
    walk(&mut |s| match s {
        Seg::Run { p, b, .. } => { let f = part(p); e = e.max(f.exp[b] as i32); *lim += f.exc_off[b + 1] - f.exc_off[b] }
        Seg::Hole { len, .. } => *lim += len as u32,
    });
    e
}
/// structural.rs `cat_hint`: answer block `b`'s exponent hint and patch limit `lim`; -1 = no hint.
pub fn cat_hint<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], b: usize, lim: &mut u32) -> i32 {
    let (s, n) = (b * WBLK, start[start.len() - 1]);
    hint(part, lim, &|g: &mut dyn FnMut(Seg)| cat_walk(&|p| part(p).c.meta.lg, start, s, (n - s).min(WBLK), g))
}

/// The writer's second form of an answer block, `coc_ints`'s outputs: the decimals `d`, `ee[i] < 0` at each exception
/// and, with `raw`, `raw[i]` the address of its bits (in a source's patch list, or the hole's).
pub struct Ints<'b> { pub d: &'b mut [i64], pub ee: &'b mut [i8], pub raw: Option<&'b mut [*const u8]> }
/// structural.rs `alp_ints_run`: decimals `d` and `ee` of elements `lo ..` of block `s` (reversed when `rev`),
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
pub fn ints_exp<'a>(part: &dyn Fn(usize) -> Cocf<'a>, walk: Walk) -> i32 {
    let (mut e, mut one) = (-1, true);
    walk(&mut |s| if let Seg::Run { p, b, .. } = s {
        let x = part(p).exp[b] as i32;
        if e < 0 { e = x } else if e != x { one = false }
    });
    if one { e } else { -1 }
}
/// Pass 2: the integers at that exponent, a hole being `hole` = (its integer, its `ee`, the address of its bits).
pub fn ints_fill<'a>(part: &dyn Fn(usize) -> Cocf<'a>, rev: bool, hole: (i64, i8, *const u8), out: &mut Ints, walk: Walk) {
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
pub fn ints<'a>(part: &dyn Fn(usize) -> Cocf<'a>, rev: bool, out: Option<&mut Ints>, walk: Walk) -> i32 {
    let e = ints_exp(part, walk);
    if let (Some(o), true) = (out, e >= 0) { ints_fill(part, rev, (0, 0, core::ptr::null()), o, walk) }
    e
}
/// structural.rs `cat_ints`: answer block `b` of the concat as decimals; -1 = take the general path.
pub fn cat_ints<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], b: usize, out: Option<&mut Ints>) -> i32 {
    let (s, n) = (b * WBLK, start[start.len() - 1]);
    ints(part, false, out, &|g: &mut dyn FnMut(Seg)| cat_walk(&|p| part(p).c.meta.lg, start, s, (n - s).min(WBLK), g))
}

// ---- A36: structural.rs (the rest of the concat entries is Lean glue) ----
/// structural.rs `cat_take`: the part holding block `b` and its block there.
pub fn cat_take(start: &[usize], b: usize) -> Option<(usize, usize)> {
    let k = start.len().checked_sub(1).filter(|&k| k > 0)?;
    let (s, n) = (b * WBLK, start[k]);
    let (mut pi, mut hi) = (0, k);
    while pi + 1 < hi { let mid = (pi + hi) / 2; if start[mid] <= s { pi = mid } else { hi = mid } }
    let j = s - start[pi];
    if j % WBLK != 0 || (s + WBLK).min(n) > start[pi + 1] { return None }
    Some((pi, j / WBLK))
}
/// structural.rs `cat_take`'s test of the part itself: a part moves whole only in the writer's trailer, and a plain
/// one only when its patch list's elements are the answer's width.
pub fn cat_part_ok(c: &Coc, w: usize, alp: bool) -> bool {
    c.meta.lg == crate::DEFAULT_LG && trailer_ok(c, c.meta.n, w, alp) && (alp || c.exc.is_none_or(|x| x.pos.is_empty() || x.esz == w))
}
/// structural.rs `put_res`: `v` minus `base` at `w` bits into `p` from field `lo`.
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

pub fn die(args: core::fmt::Arguments) -> ! {
    crate::os::eprint(args).expect("qlean: stderr");
    crate::os::exit(1)
}


// ---- A37: structural.rs ----
/// `(T)v` of structural.rs's kernels: the low `W` bytes of `v`, zero-extended past 8.
pub fn word<const W: usize>(v: u64) -> [u8; W] { let b = v.to_le_bytes(); core::array::from_fn(|k| if k < 8 { b[k] } else { 0 }) }
/// structural.rs's `WIDTHS`: the kernels exist at these element widths only, and say so before any worker starts.
pub fn check_w(w: usize, who: &str) {
    assert!(matches!(w, 1 | 2 | 4 | 8 | 16),
            "qlean structural: {who} got element width {w}; the kernels are instantiated at 1, 2, 4, 8 and 16 bytes");
}
/// The entry's refusal for an encoded source: besides `check_w`, a column whose blocks disagree (`one_width` 255) has
/// no 16-byte reader. Said here, before any worker starts, as `check_w` does.
pub fn check_enc(w: usize, sw: u8, who: &str) {
    check_w(w, who);
    assert!(!(sw == 255 && w == 16), "qlean structural: {who} of an encoded column with unequal blocks has no width-16 reader");
}
/// structural.rs `GATHER_AHEAD`: how far ahead of the index being read the source is prefetched.
pub const GATHER_AHEAD: usize = 16;
/// structural.rs `qlean_structural_all_below`: every index, read unsigned, is below `n`.
pub fn all_below(n: usize, idx: &[i64]) -> bool { idx.is_empty() || idx.iter().fold(0u64, |m, &x| m.max(x as u64)) < n as u64 }
// One unsigned compare rejects all three of q's misses (past the end, negative, `0N` = 2^63 unsigned), as `get` does.
pub fn gather_w<const W: usize>(run: Runner, fill: u64, src: &[u8], idx: &[i64], out: &mut [u8]) {
    let (sc, f) = (src.as_chunks::<W>().0, word::<W>(fill));
    crate::c::run_map(run, out, idx.len(), W, crate::QLEAN_COST_GATHER, W + 8, &|lo, hi, o: &mut [u8]| {
        for (d, &i) in o.as_chunks_mut::<W>().0.iter_mut().zip(&idx[lo..hi]) { *d = sc.get(i as usize).copied().unwrap_or(f) }
    });
}
/// structural.rs `gather_run` and its entry: `src[idx[i]]` (`w` bytes) into `out`, `fill` out of range. `idx.len()`
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
// One width for the whole column makes the pack a flat array of residuals, so `u * width / 8` is the address and the
// block structure cancels out of it: one scaled index plus the block's base, which stays in L1.
pub fn flat<const W: usize>(c: &Coc, sw: u8, f: [u8; W], ix: &[i64], o: &mut [u8], rd: impl Fn(usize) -> u64) {
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
// is an eighth of a block long decodes the block once into the scratch (on the source's own grid, whatever its `lg`;
// allocated at the first such run, so a gather of short runs never zeroes it), a shorter one is read through `get`.
pub fn runs<const W: usize>(c: &Coc, f: [u8; W], ix: &[i64], o: &mut [u8]) {
    let (sn, lg) = (c.meta.n, c.meta.lg);
    let mut buf: Option<crate::pod::Scr<u64>> = None;
    let d = o.as_chunks_mut::<W>().0;
    let mut j = 0;
    while j < ix.len() {
        let u0 = ix[j] as u64;
        if u0 >= sn as u64 { d[j] = f; j += 1; continue }
        let (b, blo) = (u0 as usize >> lg, u0 as usize >> lg << lg);
        let mut e = j + 1;
        while e < ix.len() && ix[e] as u64 >> lg == b as u64 { e += 1 }
        if e - j < c.meta.blk() / 8 {
            for k in j..e {
                if let Some(&a) = ix.get(k + GATHER_AHEAD) { c.prefetch(a as usize) }
                let u = ix[k] as u64;
                d[k] = if u < sn as u64 { word(c.get(u as usize) as u64) } else { f };
            }
        } else {
            let s = Blocks::new(crate::blocks::Src::For(*c), sn);
            let bb = s.load_w(b, s.span(b).1, W, crate::pod::bytes_mut(buf.get_or_insert_with(|| crate::pod::Scr::new(c.meta.blk() * W.div_ceil(8)))));
            for k in j..e {
                let u = ix[k] as u64;
                d[k] = if u < sn as u64 { bb[(u as usize - blo) * W..][..W].try_into().unwrap() } else { f };
            }
        }
        j = e;
    }
}
// One slice of `gather_enc`: `sw` is the source's one width, decided by the entry once rather than per slice.
pub fn enc_w<const W: usize>(c: &Coc, sw: u8, fill: u64, ix: &[i64], o: &mut [u8]) {
    let f = word::<W>(fill);
    // the block of `u` on the source's own grid: a column of any `lg` the layout admits
    let (sb, sp, lg) = (c.meta.base, c.pack, c.meta.lg);
    let base = |u: usize| sb[u >> lg] as u64;
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
        // `check_enc` refused width 16 here at the entry: coc.rs `coc_load_blk_at` decodes at 8 bytes, which C misreads as a `u128`
        255 if W <= 8 => runs(c, f, ix, o),
        255 => unreachable!("an unequal-blocks gather at width {W} is refused at the entry"),
        _ => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(crate::res::res_get_in(sp, sw, u, sp.len()))),
    }
}
pub fn enc(w: usize, c: &Coc, sw: u8, fill: u64, ix: &[i64], o: &mut [u8]) {
    match w {
        1 => enc_w::<1>(c, sw, fill, ix, o),
        2 => enc_w::<2>(c, sw, fill, ix, o),
        4 => enc_w::<4>(c, sw, fill, ix, o),
        8 => enc_w::<8>(c, sw, fill, ix, o),
        _ => enc_w::<16>(c, sw, fill, ix, o),
    }
}
/// structural.rs `gather_foR_run` and its entry: from an encoded column, which a gather reads only where its index
/// points, so the source is never decoded whole.
pub fn gather_enc(run: Runner, w: usize, fill: u64, c: &Coc, idx: &[i64], out: &mut [u8]) {
    let sw = c.one_width();
    check_enc(w, sw, "gather_foR");
    crate::c::run_map(run, out, idx.len(), w, crate::QLEAN_COST_GATHER, w + 8,
                      &|lo, hi, o: &mut [u8]| enc(w, c, sw, fill, &idx[lo..hi], o));
}
/// structural.rs `gather_bits_run` and its entry: bit `j` of `out` is bit `idx[j]` of `bits`, `0` for a miss. The unit
/// is an output byte (`out` arrives zeroed): two slices sharing a byte would lose each other's bits.
pub fn gather_bits(run: Runner, n: usize, bits: &[u8], idx: &[i64], out: &mut [u8]) {
    let hit = |&i: &i64| (i as u64) < n as u64 && bits.get((i as u64 >> 3) as usize).is_some_and(|b| b >> (i & 7) & 1 == 1);
    crate::c::run_map(run, out, idx.len().div_ceil(8), 1, crate::QLEAN_COST_GATHER, 64, &|lo, _, o: &mut [u8]| {
        for (d, ch) in o.iter_mut().zip(idx[lo * 8..].chunks(8)) {
            *d |= ch.iter().enumerate().fold(0u8, |a, (k, i)| a | (hit(i) as u8) << k)
        }
    });
}

// ---- A38: structural.rs ----
// One width of `expand`: `fill` is the C's `(T)fill`, its low `W` bytes (zero-extended past 8).
pub fn expand_w<const W: usize>(run: Runner, fill: u64, src: &[u8], at: &[usize], out: &mut [u8]) {
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
/// structural.rs `expand_run` and its entry: `src[i]` repeated `wv[i]` times (a negative count is none),
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
// A row past `s` (an unsigned compare: negative and `0N` too) is the empty symbol.
pub fn gathered<'a>(s: &Syms<'a>, u: i64) -> &'a [u8] { if (u as u64) < s.count() as u64 { s.at(u as usize) } else { &[] } }
/// structural.rs `qlean_structural_gather_syms`: the gathered column's blob length, one NUL a symbol.
pub fn gather_syms_len(s: &Syms, idx: &[i64]) -> usize { idx.iter().map(|&u| gathered(s, u).len() + 1).sum() }
/// structural.rs: the gathered blob and its `idx.len() + 1` starts, written boxed as C's `lean_array_cptr` holds them.
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
pub fn gathered_id(src: &[u8], w: u32, n: usize, fill: u64, u: i64) -> u64 {
    if (u as u64) < n as u64 { crate::ids::id_at(src, w, u as usize) as u64 } else { fill }
}
/// structural.rs `gather_ids_run` and its entry: ids at `w` gathered to `wout` bits; `n` is the source count
/// (already cut to what `src` holds). Sliced on whole bytes of the answer, `slice_elems` elements to a unit.
pub fn gather_ids(run: Runner, w: u32, wout: u32, fill: u64, src: &[u8], n: usize, idx: &[i64], out: &mut [u8]) {
    let (g, m) = (crate::ids::slice_elems(wout), idx.len());
    crate::c::run_map(run, out, m.div_ceil(g), crate::ids::ids_bytes(g, wout), crate::QLEAN_COST_GATHER, g * 9,
                      &|lo, hi, o: &mut [u8]| {
        let (lo, hi) = (lo * g, (hi * g).min(m));
        for j in lo..hi { crate::ids::id_put(o, wout, j - lo, gathered_id(src, w, n, fill, idx[j])) }
    });
}
/// structural.rs `qlean_structural_cycle_ids`: `m` fields of `ids` from `off`, cycling over `n`; `out` arrives zeroed.
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

// ---- A39: structural.rs ----
/// An enumerated element as an id: `0Nj` is `nullid`, a negative index reads `0`, any other is itself (`enum_ids`
/// finds the out-of-range first in the C entry).
pub fn enum_id(v: i64, nullid: usize) -> u64 { if v == i64::MIN { nullid as u64 } else { v.max(0) as u64 } }
/// structural.rs `qlean_structural_cycle_bits`
pub fn cycle_bits(n: usize, off: usize, m: usize, b: &[u8], out: &mut [u8]) {
    if m == 0 || n == 0 { return }
    // a run of the source up to its end at a time, the read index wrapped once per lap rather than divided
    let (mut j, mut i) = (0, off % n);
    while j < m { let len = (m - j).min(n - i); copy_bits(out, j, b, i, len); j += len; i = 0 }
}
/// structural.rs `concat_run` and its entry: the parts end to end into `out`.
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
/// structural.rs `qlean_structural_concat_bits`: `counts[j]` bits of `parts[j]`.
pub fn concat_bits(counts: &[usize], parts: &[&[u8]], out: &mut [u8]) {
    let mut at = 0;
    for (&cn, p) in counts.iter().zip(parts) { copy_bits(out, at, p, 0, cn); at += cn }
}
/// An element out of range of the domain `0 .. d`: neither `0Nj` nor an index below `d`.
pub fn enum_bad(v: i64, d: usize) -> bool { (v != i64::MIN) & ((v < 0) | (v as u64 >= d as u64)) }
/// The first element of `ch` out of range of `0 .. d`: a whole run is tested with no early exit so the test vectorises, and only
/// the run holding the answer is searched.
pub fn first_bad(ch: &[[u8; 8]], d: usize) -> Option<usize> {
    ch.chunks(64).enumerate().find_map(|(k, r)| r.iter().fold(false, |a, c| a | enum_bad(i64::from_le_bytes(*c), d)).then(|| k * 64 + r.iter().position(|c| enum_bad(i64::from_le_bytes(*c), d)).unwrap()))
}
/// structural.rs `qlean_structural_enum_ids`: values as ids into `0 .. d` at `w` bits, `nullid` outside; answers the
/// first element that is neither an index below `d` nor `0Nj` (`n` when every one is). `out` is written whole, so it needs no zeroing.
pub fn enum_ids(n: usize, d: usize, nullid: usize, w: u32, b: &[u8], out: &mut [u8]) -> usize {
    // the payload as whole elements; one past it reads `0` (`enum_at`), which is out of range only for an empty domain
    let ch = b.as_chunks::<8>().0;
    let bad = first_bad(&ch[..ch.len().min(n)], d).unwrap_or(if d == 0 && ch.len() < n { ch.len() } else { n });
    // a payload that holds all `n` is indexed with no bound test per element
    match ch.get(..n) {
        Some(ch) => crate::ids::pack(out, w, n, |i| enum_id(i64::from_le_bytes(ch[i]), nullid)),
        None => crate::ids::pack(out, w, n, |i| enum_id(ch.get(i).map_or(0, |c| i64::from_le_bytes(*c)), nullid)),
    }
    bad
}
/// structural.rs `qlean_structural_enum_ids_for`: from an encoded column, a block at a time (a block's ids are whole
/// bytes at every width, so each packs to its own offset). Elements past the column's own count stay zero.
pub fn enum_ids_enc(n: usize, d: usize, nullid: usize, w: u32, c: &Coc, out: &mut [u8]) -> usize {
    let (cn, mut v, mut bad) = (c.meta.n, pod::Scr::<i64>::new(c.meta.blk()), n);
    if cn < n { out.fill(0) }
    for (b, lo, nb) in Blocks::from(*c).walk() {
        c.decode_blk(b, nb, &mut v);
        if bad == n && v[..nb].iter().fold(false, |a, &x| a | enum_bad(x, d)) { bad = lo + v[..nb].iter().position(|&x| enum_bad(x, d)).unwrap() }
        crate::ids::pack(&mut out[lo / 8 * w as usize..], w, nb, |i| enum_id(v[i], nullid));
    }
    bad
}
/// structural.rs `qlean_structural_bits_of_for`: a `u1` column's low bits into the zeroed bitmap `out`, a block at a time.
/// A width-1, frame-0, unpatched block is its own bitmap and is copied; any other (constant, framed, patched) is
/// decoded into one block of L1 scratch, never the column whole. Rows past the blocks stay zero.
pub fn bits_of_enc(c: &Coc, out: &mut [u8]) {
    let mut v = pod::Scr::<u8>::new(c.meta.blk());
    for (b, lo, nb) in Blocks::from(*c).walk() {
        match c.bit_blk(b) {
            Some(p) => copy_bits(out, lo, p, 0, nb),
            None => {
                c.decode_blk(b, nb, &mut v);
                for (j, &x) in v[..nb].iter().enumerate() { out[(lo + j) / 8] |= (x & 1) << ((lo + j) % 8) }
            }
        }
    }
}
/// structural.rs `ids_place`:`cn` ids at `w` bits from `pp`, each read through `tab` (`nm + 1` entries, the last `0`, so an id at or past `nm` reads `0` with no branch;
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
    let put = |dst: &mut [u8]| crate::by_width!(w, by(dst, wout, cn, pp, tab, nm));
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
pub fn remap_table(map: &[u8], wout: u32) -> alloc::vec::Vec<usize> {
    let nm = if wout == 0 { 0 } else { map.len() * 8 / wout as usize };
    let mut tab = alloc::vec![0usize; nm + 1];
    macro_rules! at { ($($w:literal)*) => { match wout { 0 => {} $($w => crate::ids::unpack::<$w, usize>(map, &mut tab[..nm], |_, e, v| *e = v),)* _ => crate::ids::unpack::<64, usize>(map, &mut tab[..nm], |_, e, v| *e = v) } } }
    at!(1 2 4 8 16 32);
    tab
}
/// structural.rs `qlean_structural_concat_ids`: each part's ids through its map (`maps[i]` the ids of the renaming at
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

/// `shiftBytes w fill k b`: element `j - k` at each `j`, `fill` where `j - k` is outside `[0, n)`. The in-range
/// middle of a slice is one copy and the two ends are fill, where the C tests every element with one unsigned compare.
pub fn shift_w<const W: usize>(run: Runner, fill: u64, k: i64, src: &[u8], n: usize, out: &mut [u8]) {
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
/// structural.rs `shift_run` and `qlean_structural_shift`.
pub fn shift(run: Runner, w: usize, fill: u64, k: i64, src: &[u8], n: usize, out: &mut [u8]) {
    check_w(w, "shift");
    match w { 1 => shift_w::<1>(run, fill, k, src, n, out), 2 => shift_w::<2>(run, fill, k, src, n, out),
              4 => shift_w::<4>(run, fill, k, src, n, out), 8 => shift_w::<8>(run, fill, k, src, n, out),
              _ => shift_w::<16>(run, fill, k, src, n, out) }
}

// ---- A40: structural.rs, the symbol dictionary's hash table ----
/// structural.rs `symview`: a dictionary being extended: the base's first `d0` symbols, then new ones in `tb`
/// at the (unboxed) starts `to`.
#[derive(Clone, Copy)]
pub struct Symview<'a> { pub base: Syms<'a>, pub d0: usize, pub tb: &'a [u8], pub to: &'a [usize] }
/// structural.rs `symtab` without its reference count (the `sd_*` cache's): `slot` is `mask + 1` ids + 1.
pub struct Symtab<'a> { pub cnt: usize, pub mask: usize, pub stale: usize, pub slot: &'a mut [u32] }
impl<'a> Symview<'a> {
    /// structural.rs `symview_at`
    pub fn at(&self, i: usize) -> &'a [u8] {
        if i < self.d0 { return self.base.at(i) }
        let (lo, hi) = (self.to[i - self.d0], self.to[i - self.d0 + 1]);
        &self.tb[lo..hi - 1]
    }
}
/// structural.rs `symtab_find`: the id of `k` among the first `d`, or `d`.
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
    /// structural.rs `symtab_put`
    pub fn put(&mut self, _v: &Symview, k: &[u8], id: usize) {
        let mut s = sym_hash(k) as usize & self.mask;
        while self.slot[s] != 0 { s = (s + 1) & self.mask }
        self.slot[s] = (id + 1) as u32;
    }
    /// structural.rs `symtab_fit`/`symtab_build` after the slots are allocated: the `cnt` entries of
    /// `v`, both areas, hashed into empty slots.
    pub fn fill(&mut self, v: &Symview) { for i in 0..self.cnt { self.put(v, v.at(i), i) } }
    /// structural.rs `symtab_fork` after the allocation: `s`'s slots copied (`scnt` entries, `sstale` stale ones), the
    /// entries at or past `d` counted stale on top of `s`'s. O(1) beyond the copy, as the C: the counts are passed in.
    pub fn fork(&mut self, s: &[u32], scnt: usize, sstale: usize, d: usize) {
        assert!(d <= scnt, "qlean structural: symtab_fork of {d} entries from a table of {scnt}");
        self.slot.copy_from_slice(s);
        (self.mask, self.cnt, self.stale) = (s.len() - 1, d, sstale + (scnt - d));
    }
}

// ---- A41a: structural.rs ----
/// structural.rs `symdict_concat`'s per-part step: the symbols of `part` from `from` interned into `t` over the
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

// ---- A41b: structural.rs, 3005-3030 ----
/// structural.rs `til_run` and its entry: `0 .. out.len()`.
pub fn til(run: Runner, out: &mut [i64]) {
    let n = out.len();
    crate::c::run_map(run, crate::pod::bytes_mut(out), n, 8, crate::QLEAN_COST_COPY, 8, &|lo, hi, o: &mut [u8]| {
        for (i, b) in (lo..hi).zip(o.chunks_exact_mut(8)) { b.copy_from_slice(&(i as i64).to_le_bytes()) }
    });
}
/// structural.rs `qlean_structural_scatter` past the unboxing: `dst[idx[i]] = src[soff + i]` (`bcast`: `src[soff]`)
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
/// structural.rs `symtab_build` past the slot allocation: the `d` entries of the plain dictionary `v` (`d0 == d`,
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





/// `f::<W, K>` for the widths and column counts that `rows_k` and `cols_k` are instantiated at; false = neither is.
#[macro_export]
macro_rules! by_wk {
    ($w:expr, $k:expr, $f:ident($($a:expr),*)) => { match ($w, $k) {
        (1, 2) => $f::<1, 2>($($a),*), (2, 2) => $f::<2, 2>($($a),*), (4, 2) => $f::<4, 2>($($a),*), (8, 2) => $f::<8, 2>($($a),*),
        (1, 3) => $f::<1, 3>($($a),*), (2, 3) => $f::<2, 3>($($a),*), (4, 3) => $f::<4, 3>($($a),*), (8, 3) => $f::<8, 3>($($a),*),
        (1, 4) => $f::<1, 4>($($a),*), (2, 4) => $f::<2, 4>($($a),*), (4, 4) => $f::<4, 4>($($a),*), (8, 4) => $f::<8, 4>($($a),*),
        _ => return false,
    } };
}

/// `qlean_structural_scatter` past the objects: `scatter` at byte widths, and below a byte the fields are `wb` bits packed low field
/// first. A source too short for what it is asked for, or an element width the kernels are not instantiated at, is the caller's bug
/// and stops with the text C printed.
pub fn scatter_packed(wb: usize, dst: &mut [u8], idx: &[i64], src: &[u8], soff: usize, bcast: bool) {
    let (m, cap, have) = (idx.len(), dst.len() * 8 / wb, src.len() * 8 / wb);
    if m != 0 && (if bcast { soff >= have } else { soff + m > have }) {
        die(format_args!("qlean scatter: {} fields from {soff} asked of a source of {have}\n", if bcast { 1 } else { m }))
    }
    if wb >= 8 {
        let w = wb / 8;
        if !matches!(w, 1 | 2 | 4 | 8 | 16) {
            die(format_args!("qlean structural: scatter got element width {w}; the kernels are instantiated at 1, 2, 4, 8 and 16 bytes\n"))
        }
        scatter(w, dst, idx, src, soff, bcast);
        return;
    }
    let (mask, per) = ((1u8 << wb) - 1, 8 / wb);
    for (k, &x) in idx.iter().enumerate() {
        let u = x as u64 as usize;
        if u >= cap { continue }
        let e = soff + if bcast { 0 } else { k };
        let v = (src[e / per] >> ((e % per) * wb)) & mask;
        let sh = (u % per) * wb;
        dst[u / per] = dst[u / per] & !(mask << sh) | v << sh;
    }
}
/// `scatterIds`' widening: the `n` ids of `ids` at `wa` bits as `wb` bits into `out`, an id past the payload reading `0`
/// (`Column.idAt`'s convention).
pub fn widen_ids(n: usize, wa: u32, wb: u32, ids: &[u8], out: &mut [u8]) {
    let have = crate::ids::ids_avail(ids.len(), wa);
    crate::ids::pack(out, wb, n, |i| if i < have { crate::ids::id_at(ids, wa, i) as u64 } else { 0 })
}
/// `qlean_structural_scatter_syms`' first pass: for each of the `n` symbols the position of the last index that writes it
/// (`usize::MAX`: none), which names the symbol of `y` it takes (`0` under `bcast`). One that `y` does not have is the caller's bug.
pub fn scatter_sources(n: usize, ny: usize, ix: &[u64], bcast: bool) -> Vec<usize> {
    let mut src = alloc::vec![usize::MAX; n];
    for (k, &v) in ix.iter().enumerate() {
        if v >= n as u64 { continue }
        let e = if bcast { 0 } else { k };
        if e >= ny { die(format_args!("qlean scatter: symbol {e} asked of a source of {ny}\n")) }
        src[v as usize] = e;
    }
    src
}
/// Symbol `i` of the answer: whether it comes from `y`, and its byte range in that column's blob.
pub fn syms_span(src: &[usize], o: &Syms, y: &Syms, i: usize) -> (bool, usize, usize) {
    let from_y = src[i] != usize::MAX;
    let (s, e) = if from_y { (y, src[i]) } else { (o, i) };
    let lo = s.off(e);
    (from_y, lo, s.off(e + 1).max(lo))
}
/// The blob bytes of the answer `scatter_sources` plans.
pub fn scatter_syms_total(src: &[usize], o: &Syms, y: &Syms) -> usize {
    (0..src.len()).map(|i| { let (_, lo, hi) = syms_span(src, o, y, i); hi - lo }).sum()
}
/// The answer: `blob` is `scatter_syms_total` bytes, `offs` the `n + 1` boxed starts.
pub fn scatter_syms_write(src: &[usize], o: &Syms, y: &Syms, blob: &mut [u8], offs: &mut [usize]) {
    let mut at = 0;
    offs[0] = 1;
    for i in 0..src.len() {
        let (from_y, lo, hi) = syms_span(src, o, y, i);
        blob[at..at + hi - lo].copy_from_slice(&(if from_y { y } else { o }).blob[lo..hi]);
        at += hi - lo;
        offs[i + 1] = at << 1 | 1;
    }
}












// ---- B28: structural.rs, the part of the Lean boundary that holds no object ----
/// What `concat_foR_append` found: the first part's last block grown in place by the parts after it. `put` writes it into
/// the first part's own metadata and pack once Lean has handed them over.
pub struct Grow {
    /// the block grown, how many of its elements are the first part's own, the first part's count, and the elements added
    b: usize, lo: usize, n: usize, m: usize,
    /// the block's residual width, where its residuals start in the pack, its base and its sum once grown
    w: u8, s: usize, base: u64, sum: i64,
    /// elements `lo ..` of the grown block are the added ones
    buf: [i64; WBLK],
}
/// structural.rs `concat_foR_append`'s decision and block: `Some` only where the writer, asked about the grown block,
/// keeps its base, maximum and width with no exception, and the first part was the writer's to begin with. `parts` are the
/// `k >= 1` parts' views, `start` their `k + 1` boundaries, `ew` the element width; `None` is `none`, and the caller re-encodes.
pub fn append_plan(parts: &[Coc], start: &[usize], ew: usize) -> Option<Grow> {
    let (h, k) = (parts.first()?, parts.len());
    let (n, lo, b, m) = (h.meta.n, h.meta.n % WBLK, h.meta.n / WBLK, start[k] - h.meta.n);
    // `h.meta.n` is the part's own count wherever `lo != 0`: only a count past the grid is clamped, to a block boundary. The
    // writer's form covers the block; a patch list rides along in the pack's tail untouched where block `b` has no exception,
    // every one then lying before the append point; `put_res` measures from the base, so a block whose frame is above it declines.
    if h.meta.lg != crate::DEFAULT_LG || lo == 0 || lo + m > WBLK || !h.std(n) || h.blk_nexc(b) != 0 || h.frame(b) != h.meta.base[b] as u64 || !trailer_ok(h, n, ew, false) {
        return None;
    }
    let mut buf = [0i64; WBLK];
    unpack_run(&mut buf[..lo], h, b, 0, false);
    cat_fill(&|i| plain(&parts[i]), start, ew, false, &mut buf[lo..lo + m], n);
    let (mut mn, mut mx, mut sum, mut w, mut fd, mut nexc) = (0i64, 0i64, 0i64, 0u8, 0u64, 0u32);
    let mut meta = EncMeta { b: 0, base: &mut mn, maxv: &mut mx, width: &mut w, bsum: &mut sum, frm: Some(&mut fd), nexc: &mut nexc,
                             exp: None, patch: (n as u64) < 1 << 32 };
    if crate::enc::blk_meta(&mut meta, &buf[..lo + m], ew) != 0 || fd != 0 || mn != h.meta.base[b] || mx != h.meta.maxv[b] || w != h.meta.width[b] {
        return None;
    }
    Some(Grow { b, lo, n, m, w, s: h.meta.off[b] as usize, base: mn as u64, sum, buf })
}
impl Grow {
    /// The first part's own metadata and pack (`33 * nblk + 24` bytes, and its pack) with the block's sum and the trailer's
    /// count brought up to the grown column and the added residuals written into the block.
    pub fn put(&self, meta: &mut [u8], pack: &mut [u8]) {
        let (nb, at) = (meta.len() / 33, 24 * (meta.len() / 33) + 8 * self.b);
        meta[at..at + 8].copy_from_slice(&self.sum.to_ne_bytes());
        meta[32 * nb + 8..32 * nb + 16].copy_from_slice(&((self.n + self.m) as u64).to_ne_bytes());
        put_res(&mut pack[self.s..self.s + WBLK * self.w as usize / 8], self.w, self.lo, &self.buf[self.lo..self.lo + self.m], self.base);
    }
}

/// structural.rs `row_at`: part `i` of `rs` read at `want` bytes -- where it lies when it is long enough, else a copy of
/// what it has followed by zeros (`Column.bitsAt`'s convention), and a part the array does not have at all is all zeros.
pub fn row_at<'a>(rs: &[&'a [u8]], i: usize, want: usize) -> alloc::borrow::Cow<'a, [u8]> {
    match rs.get(i) {
        Some(r) if r.len() >= want => alloc::borrow::Cow::Borrowed(&r[..want]),
        r => { let mut v = alloc::vec![0u8; want]; copy_row(&mut v, r.copied()); alloc::borrow::Cow::Owned(v) }
    }
}
pub fn copy_row(dst: &mut [u8], r: Option<&[u8]>) { let t = r.map_or(0, |r| r.len().min(dst.len())); if let Some(r) = r { dst[..t].copy_from_slice(&r[..t]) } }

pub fn rows_at<'a, 'b>(rs: &'b [&'a [u8]], want: usize) -> Rows<'a, 'b> {
    let pad = rs.iter().any(|r| r.len() < want).then(|| {
        let mut v = alloc::vec![0u8; rs.len() * want];
        if want != 0 { for (d, r) in v.chunks_exact_mut(want).zip(rs) { copy_row(d, Some(r)) } }
        v
    });
    Rows { rs, want, pad }
}
/// `STR_BLK`: the unit of both passes of `string`, so the prefix sum between them is over `n / STR_BLK` numbers.
pub const STR_BLK: usize = 4096;
/// structural.rs `amend_index`: `amendRounds` of the `idx` indices (`wi` bytes each) into `n` slots, and with
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
/// structural.rs `rows_at`: every row of a matrix at `want` bytes; one short row pads all of them into a single buffer.
pub struct Rows<'a, 'b> { rs: &'b [&'a [u8]], want: usize, pub pad: Option<Vec<u8>> }
impl Rows<'_, '_> {
    /// row `i`, `want` bytes
    pub fn get(&self, i: usize) -> &[u8] {
        match &self.pad { Some(p) => &p[i * self.want..(i + 1) * self.want], None => &self.rs[i][..self.want] }
    }
}
/// The three Lean arrays `amend_index` asks its caller to allocate, in this order: `Dom` (`nd` words, only when
/// compacting and no index misses), `Rank` (`m` words, likewise), `Res` (the answer).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AmOut { Dom, Rank, Res }
// ---- K22: structural.rs `amend_index` ----
/// structural.rs `AMSEG`: the indices or bitmap words of one segment of a compaction.
pub const AMSEG: usize = 4096;
pub fn seg_hi(s: usize, lim: usize) -> usize { ((s + 1) * AMSEG).min(lim) }
/// structural.rs `amx_scan`: the prefix of `sc` into `so` (`so[0] = 0`).
pub fn seg_scan(so: &mut [usize], sc: &[usize]) {
    so[0] = 0;
    for (s, c) in sc.iter().enumerate() { so[s + 1] = so[s] + c }
}
// ---- K23: structural.rs `fsc_*`, `fsx_check`: scatter into an encoded column ----
/// `scatterFoR` and `scatterALP`, one engine for both encodings, because the block is what they share: a block no index
/// lands in keeps its metadata entries, residual bytes, exponent and exceptions as they are (`move_meta`, `move_pack`); a
/// block some index lands in is decoded, written and handed to the writer's block steps for its encoding. The kept
/// entries are only kept when the block sums were taken the way the writer takes them (`coc_sumnul`, `sumn`), and a
/// Frame of Reference patch list at another element width is not copied; either one re-encodes every block instead.
pub struct Scatter<'a> {
    old: Cocf<'a>, alp: bool, w: usize, keep: bool, ix: &'a [u64], vals: &'a [u8],
    /// block `b`'s writes are `ix[at[b] .. at[b + 1]]`; written once each by the slice that holds the first index of `b`
    at: Vec<AtomicUsize>,
}
impl<'a> Scatter<'a> {
    /// structural.rs `fsc_scatter`'s views and refusals: metadata `m`, pack `pk`, the ALP part `a` for an ALP column, `n`
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
        Scatter { old, alp, w, keep, ix, vals, at }
    }
    /// A block no index lands in, whose old entries are the new ones.
    pub fn kept(&self, b: usize) -> bool { self.keep && self.span(b).is_empty() }
    fn span(&self, b: usize) -> core::ops::Range<usize> { self.at[b].load(Relaxed)..self.at[b + 1].load(Relaxed) }
    fn nb(&self, b: usize) -> usize { Blocks::from(self.old.c).span(b).1 }
    /// structural.rs `fsc_load`: block `b` decoded at `w` bytes an element into `out` (8-aligned), its writes applied.
    fn load(&self, b: usize, nb: usize, out: &mut [u8]) {
        if self.alp { Blocks::from(self.old) } else { Blocks::from(self.old.c) }.load_w(b, nb, self.w, out);
        let r = self.span(b);
        let (ix, v) = (&self.ix[r.clone()], &self.vals[r.start * self.w..r.end * self.w]);
        match self.w { 2 => put_vals::<2>(out, b, ix, v), 4 => put_vals::<4>(out, b, ix, v), _ => put_vals::<8>(out, b, ix, v) }
    }
    /// Block `b`'s writes: the positions and the floats.
    fn writes<F: Elt>(&self, b: usize) -> (&[u64], &[F]) {
        let r = self.span(b);
        (&self.ix[r.clone()], pod::cast::<F>(&self.vals[r.start * self.w..r.end * self.w]).expect("qlean scatter: the values are misaligned"))
    }
    /// structural.rs `fsc_patch`: pass 1's integers with the writes at the block's OLD exponent (`alp_patch_blk`).
    fn patch<F: Elt>(&self, b: usize, nb: usize, d: &mut [i64], ee: &mut [i8]) -> i32 {
        let (ix, v) = self.writes::<F>(b);
        crate::alp::alp_patch_blk(&self.old, b, nb, ix, v, d, ee)
    }
    /// structural.rs `fsc_meta` then `fsc_pack` for block `b`, the block decoded and patched once: its metadata into `m`, then
    /// its residuals and patches into `pack(whole)` (asked once, after `m`; `whole` when `kept(b)`, the full `WBLK * width / 8`
    /// residual bytes).
    pub fn write<'p>(&self, m: &mut EncMeta, pack: impl FnOnce(bool) -> EncPack<'p>, b: usize) {
        let nb = self.nb(b);
        if self.kept(b) { crate::enc::move_meta(m, &self.old, b); return crate::enc::move_pack(&mut pack(true), &self.old, b, self.alp, self.w) }
        let mut buf = [0u64; WBLK];
        if !self.alp {
            let bytes = pod::bytes_mut(&mut buf);
            self.load(b, nb, bytes);
            crate::enc::for_meta(m, bytes, self.w, nb);
            return crate::enc::for_pack(&mut pack(false), bytes, self.w)
        }
        if self.w == 4 { self.write_alp::<f32>(m, pack, b, nb, &mut buf) } else { self.write_alp::<f64>(m, pack, b, nb, &mut buf) }
    }
    /// An ALP block with writes: the patch at the old exponent, unless the search's exponent leaves fewer exceptions; each
    /// costs its raw bytes and a position, more than the residual bits a higher exponent adds.
    fn write_alp<'p, F: Elt>(&self, m: &mut EncMeta, pack: impl FnOnce(bool) -> EncPack<'p>, b: usize, nb: usize, buf: &mut [u64; WBLK]) {
        let (mut d, mut ee) = ([0i64; WBLK], [0i8; WBLK]);
        let alt = self.patch::<F>(b, nb, &mut d, &mut ee);
        let np = ee[..nb].iter().filter(|&&e| e < 0).count() as u32;
        if alt >= 0 {
            let bytes = pod::bytes_mut(buf);
            self.load(b, nb, bytes);
            let x = pod::cast::<F>(&bytes[..nb * self.w]).expect("qlean scatter: the block buffer is misaligned");
            if crate::alp::alp_exc_at(x, alt, np) < np {
                *m.nexc = crate::alp::alp_meta_exp(m, x, nb, alt);
                return crate::enc::alp_pack(&mut pack(false), bytes, self.w);
            }
        }
        // `alp_fin_blk` moves only the exceptions' decimals, which `alp_patch_pack` sets to the base
        *m.nexc = crate::alp::alp_fin_blk(m, self.old.exp[b] as i32, &mut d, &ee, nb);
        let (p, (ix, v)) = (&mut pack(false), self.writes::<F>(b));
        let raw = core::mem::take(&mut p.raw);
        crate::alp::alp_patch_pack(p, &self.old, ix, v, &mut d, &ee, pod::cast_mut::<F>(raw).expect("qlean scatter: misaligned patch bits"))
    }
}
// ---- A35: structural.rs, the encoder sources ----
/// structural.rs `fsx_check`: the checks and block cursors in one pass off the pool. The first offending position is the
/// least one any slice saw, which is the one a serial loop reports, and since `ix` ascends, the blocks from just past
/// `ix[k - 1]`'s up to `ix[k]`'s are exactly those whose first index is `k`, so each cursor is written once, by the slice
/// holding that `k`, and no count is taken. `Err(k)` = `ix[k]` is not ascending, distinct and below `n`.
pub fn cursors(run: Runner, ix: &[u64], n: usize, nblk: usize) -> Result<Vec<AtomicUsize>, usize> {
    let m = ix.len();
    let at: Vec<AtomicUsize> = (0..n.div_ceil(WBLK).max(nblk) + 1).map(|_| AtomicUsize::new(0)).collect();
    let bad = AtomicUsize::new(m);
    crate::c::run_map(run, &mut [], m, 0, crate::QLEAN_COST_COPY, 16, &|lo, hi, _: &mut [u8]| {
        for k in lo..hi {
            if ix[k] >= n as u64 || (k > 0 && ix[k] <= ix[k - 1]) { bad.fetch_min(k, SeqCst); return }
            for b in (if k > 0 { ix[k - 1] / WBLK as u64 + 1 } else { 0 })..=ix[k] / WBLK as u64 { at[b as usize].store(k, Relaxed) }
        }
    });
    let bad = bad.into_inner();
    if bad < m { return Err(bad) }
    for b in (if m > 0 { ix[m - 1] as usize / WBLK + 1 } else { 0 })..=nblk { at[b].store(m, Relaxed) }
    Ok(at)
}
/// Block `b`'s writes into a decoded block: `W`-byte values at the positions `ix` names.
pub fn put_vals<const W: usize>(out: &mut [u8], b: usize, ix: &[u64], vals: &[u8]) {
    let (o, v) = (out.as_chunks_mut::<W>().0, vals.as_chunks::<W>().0);
    for (&i, &x) in ix.iter().zip(v) { o[i as usize - b * WBLK] = x }
}
