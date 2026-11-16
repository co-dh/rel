#![forbid(unsafe_code)]
//! Column (a), reduce.c: whole-vector reductions of a byte payload (A12; the byte sum is `simd::u8_sum`) and the
//! segmented reductions and bit-row folds (A13).
use alloc::vec::Vec;
use alloc::vec;
use core::sync::atomic::{AtomicI64, Ordering::Relaxed};
use crate::c::{run_map, run_slices, Runner};
use crate::ids::{id_at, ids_avail};
use crate::{simd, BLK};

// ---- A12: reduce.c:261-298 ----
/// An element of the four integer classes: read in native order, widened to `i64` as C's `(int64_t)` cast does.
trait Elem: Copy + PartialOrd + Into<i64> + TryFrom<i64> {
    const W: usize;
    const ZERO: Self;
    const ONE: Self;
    const MAX: Self;
    const MIN: Self;
    fn rd(b: &[u8]) -> Self;
}
macro_rules! elem {
    ($t:ty) => {
        impl Elem for $t {
            const W: usize = size_of::<$t>();
            const ZERO: $t = 0;
            const ONE: $t = 1;
            const MAX: $t = <$t>::MAX;
            const MIN: $t = <$t>::MIN;
            fn rd(b: &[u8]) -> $t { <$t>::from_ne_bytes(b.try_into().unwrap()) }
        }
    };
}
elem!(u8);
elem!(i16);
elem!(i32);
elem!(i64);

/// reduce.c:213 `OB_LANES`: `L` accumulators of plain vector ops, a skipped element folding in the identity `id`; every
/// step is associative with `id` its identity, so the lane split cannot move the answer.
fn lanes<T: Elem, A: Copy, const L: usize>(a: &[u8], id: A, cv: impl Fn(T) -> A, sk: impl Fn(T) -> bool,
                                           step: impl Fn(A, A) -> A) -> A {
    let mut r = [id; L];
    let mut c = a[..a.len() / T::W * T::W].chunks_exact(L * T::W);
    let put = |r: A, v: T| step(r, if sk(v) { id } else { cv(v) });
    for b in c.by_ref() {
        for (j, e) in b.chunks_exact(T::W).enumerate() { r[j] = put(r[j], T::rd(e)) }
    }
    for e in c.remainder().chunks_exact(T::W) { r[0] = put(r[0], T::rd(e)) }
    r[1..].iter().fold(r[0], |t, &x| step(t, x))
}

/// reduce.c:252 `OB_VERBS`: the six verbs at element type `T`, the null compared at `T`'s width and skipped only
/// where `nul` is a value of `T`.
fn verbs<T: Elem, const LI: usize, const LT: usize>(op: u8, nul: i64, n: usize, a: &[u8], seed: i64) -> i64 {
    let tn = T::try_from(nul).ok();
    let sk = |v: T| tn == Some(v);
    let none = |_: T| false;
    let add = |a: i64, v: i64| a.wrapping_add(v);
    let mul = |a: i64, v: i64| a.wrapping_mul(v);
    let lo = |a: T, v: T| if a < v { a } else { v };
    let hi = |a: T, v: T| if v < a { a } else { v };
    let all = |a: T, v: T| if v != T::ZERO { a } else { T::ZERO };
    let any = |a: T, v: T| if v != T::ZERO { T::ONE } else { a };
    macro_rules! go {
        ($l:ident, $id:expr, $step:expr) => { if tn.is_some() { lanes::<T, _, $l>(a, $id, |v| v, sk, $step) }
                                              else { lanes::<T, _, $l>(a, $id, |v| v, none, $step) } };
        ($l:ident, $id:expr, $cv:expr, $step:expr) => { if tn.is_some() { lanes::<T, _, $l>(a, $id, $cv, sk, $step) }
                                                        else { lanes::<T, _, $l>(a, $id, $cv, none, $step) } };
    }
    // the answer of an empty vector is the seed itself, not its step with `id`
    let fin = |t: i64, step: fn(i64, i64) -> i64| if n == 0 { seed } else { step(seed, t) };
    match op {
        0 => fin(go!(LI, 0i64, |v: T| v.into(), add), |s, t| s.wrapping_add(t)),
        1 => fin(go!(LI, 1i64, |v: T| v.into(), mul), |s, t| s.wrapping_mul(t)),
        2 => fin(go!(LT, T::MAX, lo).into(), |s, t| if s < t { s } else { t }),
        3 => fin(go!(LT, T::MIN, hi).into(), |s, t| if t < s { s } else { t }),
        4 => fin(lanes::<T, _, LT>(a, T::ONE, |v| v, none, all).into(), |s, t| if t != 0 { s } else { 0 }),
        _ => fin(lanes::<T, _, LT>(a, T::ZERO, |v| v, none, any).into(), |s, t| if t != 0 { 1 } else { s }),
    }
}

/// reduce.c:277 `qlean_over_bytes` past the unboxing: `op` (sum, prd, min, max, ...) of class `cls` over `a`, nulls
/// `nul` skipped.
pub fn over_bytes(op: u8, cls: u8, nul: i64, a: &[u8]) -> i64 {
    // a skipped `0` adds what folding it adds, so only a nonzero byte null keeps the lanes
    if cls == 0 && op == 0 && (u8::try_from(nul).is_err() || nul == 0) { return crate::simd::u8_sum(a) }
    let n = a.len() / match cls { 0 => 1, 1 => 2, 2 => 4, _ => 8 };
    // `Over.denseSeed`: for a signed class `Over.seed`, !nul for `min` and nul + 1 for `max` (wrapped, as `Int64`
    // adds); the one unsigned class has no null and every value from 0 to 255 is an element
    let seed = match op { 2 => if cls == 0 { 255 } else { !nul }, 3 => if cls == 0 { 0 } else { nul.wrapping_add(1) },
                          1 | 4 => 1, _ => 0 };
    match cls {
        0 => verbs::<u8, 32, 256>(op, nul, n, a, seed),
        1 => verbs::<i16, 32, 128>(op, nul, n, a, seed),
        2 => verbs::<i32, 32, 64>(op, nul, n, a, seed),
        // 4 sum lanes, not 32: with 32 at i64 LLVM vectorizes across blocks by stride-256-byte gathers (12.9 ms, C 1.04)
        _ => verbs::<i64, 4, 32>(op, nul, n, a, seed),
    }
}

// ---- A13: reduce.c:488-619 ----
/// reduce.c:488 `seg_at`: segment `k`'s start (`o` the `n` starts; `k == n` answers the end).
pub fn seg_at(o: &[i64], n: usize, k: usize) -> usize {
    let x = o[k];
    if x < 0 { 0 } else if x as u64 > n as u64 { n } else { x as usize }
}
/// reduce.c:493 `seg_lower`: the segment holding element `i`.
pub fn seg_lower(o: &[i64], n: usize, ng: usize, i: usize) -> usize {
    let (mut a, mut b) = (0, ng);
    while a < b { let m = a + (b - a) / 2; if seg_at(o, n, m) < i { a = m + 1 } else { b = m } }
    a
}

/// `OS_LOOP` at element type `T`: segments `from .. to` of `src`, each folded by `step` from `init` (the live elements
/// only where `nul` is a value to skip), `put(r, fold, live count)` for segment `r`.
fn fold_at<T: Elem>(init: i64, nul: Option<i64>, step: impl Fn(i64, i64) -> i64, n: usize, offs: &[i64],
                    src: &[u8], from: usize, to: usize, put: &mut impl FnMut(usize, i64, i64)) {
    for r in from..to {
        let (s, e) = (seg_at(offs, n, r), seg_at(offs, n, r + 1));
        let (mut a, mut k) = (init, 0);
        for b in src[s.min(e) * T::W..e * T::W].chunks_exact(T::W) {
            let v: i64 = T::rd(b).into();
            let live = nul != Some(v);
            a = step(a, if live { v } else { init });
            k += live as i64;
        }
        put(r, a, k);
    }
}
fn fold_op<T: Elem>(op: u8, nul: i64, lo: i64, hi: i64, n: usize, offs: &[i64], src: &[u8], from: usize,
                    to: usize, put: &mut impl FnMut(usize, i64, i64)) {
    let nl = Some(nul);
    match op {
        0 => fold_at::<T>(0, nl, |a, v| a.wrapping_add(v), n, offs, src, from, to, put),
        1 => fold_at::<T>(1, nl, |a, v| a.wrapping_mul(v), n, offs, src, from, to, put),
        2 => fold_at::<T>(hi, nl, |a, v| if a < v { a } else { v }, n, offs, src, from, to, put),
        3 => fold_at::<T>(lo, nl, |a, v| if v < a { a } else { v }, n, offs, src, from, to, put),
        4 => fold_at::<T>(1, None, |a, v| if v != 0 { a } else { 0 }, n, offs, src, from, to, put),
        _ => fold_at::<T>(0, None, |a, v| if v != 0 { 1 } else { a }, n, offs, src, from, to, put),
    }
}
fn fold_cls(op: u8, cls: u8, nul: i64, lo: i64, hi: i64, n: usize, offs: &[i64], src: &[u8], from: usize,
            to: usize, put: &mut impl FnMut(usize, i64, i64)) {
    match cls {
        0 => fold_op::<u8>(op, nul, lo, hi, n, offs, src, from, to, put),
        1 => fold_op::<i16>(op, nul, lo, hi, n, offs, src, from, to, put),
        2 => fold_op::<i32>(op, nul, lo, hi, n, offs, src, from, to, put),
        _ => fold_op::<i64>(op, nul, lo, hi, n, offs, src, from, to, put),
    }
}

/// reduce.c:516 `over_segments`: elements `from .. to` of `src` (class `cls`) folded by `op` into the
/// segment results `res`, segments `lo .. hi`.
pub fn over_segments(op: u8, cls: u8, nul: i64, lo: i64, hi: i64, ng: usize, n: usize, offs: &[i64], src: &[u8],
                     from: usize, to: usize, res: &mut [i64]) {
    fold_cls(op, cls, nul, lo, hi, n, offs, src, from, to, &mut |r, a, k| { res[r] = a; res[ng + r] = k })
}
/// reduce.c:537 `qlean_over_segments` past the unboxing: one result per segment into `res` (`2 * ng` long, the folds
/// then the live counts), threaded (`over_segments_pass`).
pub fn segments(run: Runner, op: u8, cls: u8, nul: i64, offs: &[i64], src: &[u8], n: usize, res: &mut [i64]) {
    let ng = offs.len().saturating_sub(1);
    if ng == 0 { return }
    let w = size_of::<i64>() >> (3 - cls.min(3));
    let (lo, hi) = if cls == 0 { (0, 255) } else { (nul.wrapping_add(1), !nul) };
    let up = (0..ng).all(|r| seg_at(offs, n, r) <= seg_at(offs, n, r + 1));
    if !(up && n > 0) { return over_segments(op, cls, nul, lo, hi, ng, n, offs, src, 0, ng, res) }
    // a slice of rows owns the segments starting in it, which no other slice writes: the workers share one atomic
    // answer, because their segments are not a slice of `res` (folds and counts lie `ng` apart)
    let acc: Vec<AtomicI64> = (0..2 * ng).map(|_| AtomicI64::new(0)).collect();
    let f = |a: usize, b: usize, _: &mut [u8]| {
        let (from, to) = (seg_lower(offs, n, ng, a), if b >= n { ng } else { seg_lower(offs, n, ng, b) });
        fold_cls(op, cls, nul, lo, hi, n, offs, src, from, to, &mut |r, x, k| {
            acc[r].store(x, Relaxed);
            acc[ng + r].store(k, Relaxed)
        })
    };
    run_map(run, &mut [], n, 0, crate::QLEAN_COST_ARITH, w, &f);
    for (d, s) in res.iter_mut().zip(&acc) { *d = s.load(Relaxed) }
}

/// reduce.c:560 `br_load`: 64 bits of the bit matrix `m` (`nb` bytes) from bit `bit`.
pub fn br_load(m: &[u8], bit: usize) -> u64 {
    let (b, s) = (bit >> 3, bit & 7);
    let mut x = [0u8; 8];
    let t = m.get(b..).unwrap_or(&[]);
    let t = &t[..t.len().min(8)];
    x[..t.len()].copy_from_slice(t);
    let lo = u64::from_le_bytes(x);
    if s == 0 { return lo }
    let hi = if b + 8 < m.len() { m[b + 8] as u64 } else { 0 };
    (lo >> s) | (hi << (64 - s))
}
/// reduce.c:570 `br_store`: the low `nbits` of `v` at bit `bit`.
pub fn br_store(o: &mut [u8], bit: usize, v: u64, nbits: u32) {
    let (b, s) = (bit >> 3, (bit & 7) as u32);
    let x = (v as u128) << s;
    for t in 0..(s + nbits).div_ceil(8) as usize { o[b + t] |= (x >> (8 * t)) as u8 }
}
/// reduce.c:606 `qlean_bit_rows_over` past the unboxing: per row of `w` bits, the AND (`all`) or OR of the rows
/// `idx[offs[g] .. offs[g + 1]]` of `m`, into `out`; threaded (`bit_rows_pass`).
pub fn bit_rows(run: Runner, all: bool, w: usize, offs: &[i64], idx: &[i64], m: &[u8], out: &mut [u8]) {
    let ng = offs.len().saturating_sub(1);
    let bytes = (ng * w).div_ceil(8);
    if bytes == 0 { return }
    let (nw, rows, ni) = (w.div_ceil(64), m.len() * 8 / w, idx.len());
    // a block is 64 rows, so it starts on a byte and owns `8 * w` bytes; the last is padded, then cut to `bytes`
    let blocks = ng.div_ceil(64);
    let f = |lo: usize, hi: usize, o: &mut [u8]| {
        let mut acc = vec![0u64; nw];
        for g in lo * 64..(hi * 64).min(ng) {
            acc.fill(if all { !0 } else { 0 });
            for k in seg_at(offs, ni, g)..seg_at(offs, ni, g + 1) {
                let r = idx[k].max(0) as usize;
                // a row wholly past `m` reads zeros: nothing for `|`, everything cleared for `&`
                if r > rows { if all { acc.fill(0) } continue }
                for (t, a) in acc.iter_mut().enumerate() {
                    let v = br_load(m, r * w + 64 * t);
                    if all { *a &= v } else { *a |= v }
                }
            }
            for (t, &a) in acc.iter().enumerate() {
                let nbits = (w - 64 * t).min(64) as u32;
                let v = if nbits == 64 { a } else { a & ((1u64 << nbits) - 1) };
                if v != 0 { br_store(o, (g - lo * 64) * w + 64 * t, v, nbits) }
            }
        }
    };
    let mut buf = vec![0u8; blocks * 8 * w];
    run_map(run, &mut buf, blocks, 8 * w, crate::QLEAN_COST_MATH, 8 * nw * 64, &f);
    out[..bytes].copy_from_slice(&buf[..bytes]);
}

// ---- K1: reduce.c:271-386, the grouped fold ----
/// `OB_VERBS`' six verbs as `go!(identity, skips-nul, step)` calls: `lo`/`hi` are the min/max identities. `all` and
/// `any` skip nothing, so their element count is every element.
macro_rules! og_verbs {
    ($op:expr, $lo:expr, $hi:expr, $go:ident) => {
        match $op {
            0 => $go!(0, true, |a: i64, v: i64| a.wrapping_add(v)),
            1 => $go!(1, true, |a: i64, v: i64| a.wrapping_mul(v)),
            2 => $go!($hi, true, |a: i64, v: i64| if a < v { a } else { v }),
            3 => $go!($lo, true, |a: i64, v: i64| if v < a { a } else { v }),
            4 => $go!(1, false, |a: i64, v: i64| if v != 0 { a } else { 0 }),
            _ => $go!(0, false, |a: i64, v: i64| if v != 0 { 1 } else { a }),
        }
    };
}

/// A worker's block, `[fold, count]` for each group in turn (so one pair is one cache line, not two), at element type
/// `T` and id width `IW`: rows `from .. to` scattered by their id, an id at or past `ng` dropped. Both are constants
/// of the loop, as `IDS_WIDTHS` and the class switch hoist them in C.
fn og_loop<T: Elem, const IW: u32, const SK: bool>(init: i64, nul: i64, step: impl Fn(i64, i64) -> i64, ng: usize, gid: &[u8],
                                                  src: &[u8], from: usize, to: usize, acc: &mut [i64]) {
    for p in acc[..2 * ng].chunks_exact_mut(2) { p[0] = init; p[1] = 0 }
    for (i, b) in (from..to).zip(src[from * T::W..to * T::W].chunks_exact(T::W)) {
        let g = id_at(gid, IW, i);
        let v: i64 = T::rd(b).into();
        let live = !(SK && v == nul);
        if g >= ng { continue }
        acc[2 * g] = step(acc[2 * g], if live { v } else { init });
        acc[2 * g + 1] += live as i64;
    }
}

fn og_at<T: Elem, const IW: u32>(op: u8, nul: i64, lo: i64, hi: i64, ng: usize, gid: &[u8], src: &[u8], from: usize,
                                 to: usize, acc: &mut [i64]) {
    macro_rules! go { ($init:expr, $sk:tt, $step:expr) => { og_loop::<T, IW, $sk>($init, nul, $step, ng, gid, src, from, to, acc) }; }
    og_verbs!(op, lo, hi, go)
}

fn og_cls<const IW: u32>(op: u8, cls: u8, nul: i64, ng: usize, gid: &[u8], src: &[u8], from: usize, to: usize, acc: &mut [i64]) {
    let (lo, hi) = if cls == 0 { (0, 255) } else { (nul.wrapping_add(1), !nul) };
    match cls {
        0 => og_at::<u8, IW>(op, nul, lo, hi, ng, gid, src, from, to, acc),
        1 => og_at::<i16, IW>(op, nul, lo, hi, ng, gid, src, from, to, acc),
        2 => og_at::<i32, IW>(op, nul, lo, hi, ng, gid, src, from, to, acc),
        _ => og_at::<i64, IW>(op, nul, lo, hi, ng, gid, src, from, to, acc),
    }
}

/// reduce.c:306 `over_groups`: rows `from .. to`, their ids packed at `iw` bits in `gid`, into `acc` (`2 * ng` slots).
#[allow(clippy::too_many_arguments)]
pub fn over_groups_slice(op: u8, cls: u8, nul: i64, ng: usize, iw: u32, gid: &[u8], src: &[u8], from: usize, to: usize, acc: &mut [i64]) {
    match iw {
        0 => og_cls::<0>(op, cls, nul, ng, gid, src, from, to, acc),
        1 => og_cls::<1>(op, cls, nul, ng, gid, src, from, to, acc),
        2 => og_cls::<2>(op, cls, nul, ng, gid, src, from, to, acc),
        4 => og_cls::<4>(op, cls, nul, ng, gid, src, from, to, acc),
        8 => og_cls::<8>(op, cls, nul, ng, gid, src, from, to, acc),
        16 => og_cls::<16>(op, cls, nul, ng, gid, src, from, to, acc),
        32 => og_cls::<32>(op, cls, nul, ng, gid, src, from, to, acc),
        _ => og_cls::<64>(op, cls, nul, ng, gid, src, from, to, acc),
    }
}

/// reduce.c:339 `over_groups_merge`: the blocks in slice order, folds into `res[..ng]`, counts into `res[ng..]`.
fn og_merge(op: u8, lo: i64, hi: i64, ng: usize, blocks: &[(usize, Vec<i64>)], res: &mut [i64]) {
    macro_rules! go {
        ($init:expr, $sk:tt, $step:expr) => {{
            res[..ng].fill($init);
            res[ng..2 * ng].fill(0);
            for (_, b) in blocks {
                for (g, p) in b[OG_PAD..OG_PAD + 2 * ng].chunks_exact(2).enumerate() {
                    res[g] = ($step)(res[g], p[0]);
                    res[ng + g] += p[1];
                }
            }
        }};
    }
    og_verbs!(op, lo, hi, go)
}

/// A block's first slot: a worker's block sits between 64 bytes of padding on each side, so no cache line of it is
/// shared with another allocation (C's `qlean_priv_alloc` aligns each block to its own lines).
const OG_PAD: usize = 8;
/// reduce.c:355: above this many groups a worker's block (`2 * ng` slots, 128 KB at the limit) no longer sits in its
/// own cache beside the payload it reads, so the split is declined (`wide = 0`).
const OG_MAX_GROUPS: usize = 8192;

/// reduce.c:358 `qlean_over_groups` past the unboxing: `op` of class `cls` over the first `rows` elements of `src`,
/// grouped by the ids in `gid` (packed at `iw` bits), into `res` (`2 * ng` slots: the folds, then the live counts).
/// Threaded: each slice folds into a block of its own, and the blocks combine in slice order.
#[allow(clippy::too_many_arguments)]
pub fn over_groups(run: Runner, op: u8, cls: u8, nul: i64, ng: usize, iw: u32, rows: usize, gid: &[u8], src: &[u8], res: &mut [i64]) {
    if ng == 0 { return }
    let w = size_of::<i64>() >> (3 - cls.min(3));
    // an id payload holds as many ids as its bytes do; a one-entry dictionary (`iw = 0`) stores none and every id is 0
    let gn = ids_avail(gid.len(), iw);
    let n = (src.len() / w).min(rows).min(gn);
    let iw = (iw as u8) as u32; // the C pass carries the width in a `uint8_t`
    let (lo, hi) = if cls == 0 { (0, 255) } else { (nul.wrapping_add(1), !nul) };
    let wide = if ng <= OG_MAX_GROUPS { w } else { 0 };
    let (_, blocks) = run_slices(run, n, crate::QLEAN_COST_ARITH, wide, &|from, to| {
        let mut acc = vec![0i64; 2 * ng + 2 * OG_PAD];
        over_groups_slice(op, cls, nul, ng, iw, gid, src, from, to, &mut acc[OG_PAD..OG_PAD + 2 * ng]);
        acc
    });
    og_merge(op, lo, hi, ng, &blocks, res)
}

// ---- K2: reduce.c md5, `groupCells`, float payloads ----
const MD5_K: [u32; 64] = [
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
];
// `c ^ d`, `c & !d` and `!d` are two rounds old, so each of these is one operation from `b` (the other three two):
// the round's chain is five operations, against RFC 1321's own spelling of six.
fn md5_f(b: u32, c: u32, d: u32) -> u32 { d ^ (b & (c ^ d)) }
fn md5_g(b: u32, c: u32, d: u32) -> u32 { (b & d) | (c & !d) }
fn md5_h(b: u32, c: u32, d: u32) -> u32 { b ^ c ^ d }
fn md5_i(b: u32, c: u32, d: u32) -> u32 { c ^ (b | !d) }

/// reduce.c `md5_block`: one 64-byte block into `h`. A message is one serial chain, so the cost is the round's critical
/// path; `simd::keep` holds `a + w + k` as its own addend, which is what takes the sixth operation off that chain.
fn md5_block(h: &mut [u32; 4], p: &[u8; 64]) {
    let m: [u32; 16] = core::array::from_fn(|j| u32::from_le_bytes([p[4 * j], p[4 * j + 1], p[4 * j + 2], p[4 * j + 3]]));
    let [mut a, mut b, mut c, mut d] = *h;
    macro_rules! round {
        ($f:ident, $r:expr, $g:expr, $s:expr) => {
            for i in 0..16usize {
                let t = simd::keep(a.wrapping_add(m[$g(i)]).wrapping_add(MD5_K[16 * $r + i]));
                let n = b.wrapping_add(t.wrapping_add($f(b, c, d)).rotate_left($s[i & 3]));
                (a, b, c, d) = (d, n, b, c);
            }
        };
    }
    round!(md5_f, 0, |i: usize| i, [7u32, 12, 17, 22]);
    round!(md5_g, 1, |i: usize| (5 * i + 1) & 15, [5u32, 9, 14, 20]);
    round!(md5_h, 2, |i: usize| (3 * i + 5) & 15, [4u32, 11, 16, 23]);
    round!(md5_i, 3, |i: usize| (7 * i) & 15, [6u32, 10, 15, 21]);
    h[0] = h[0].wrapping_add(a);
    h[1] = h[1].wrapping_add(b);
    h[2] = h[2].wrapping_add(c);
    h[3] = h[3].wrapping_add(d);
}

/// reduce.c:114 `qlean_md5` past the unboxing: RFC 1321's digest of `msg`, read where it lies; only the last block or
/// two are copied out (128 bytes of stack, not a padded copy of the message).
pub fn md5(msg: &[u8]) -> [u8; 16] {
    let mut h = [0x67452301u32, 0xefcdab89, 0x98badcfe, 0x10325476];
    let mut whole = msg.chunks_exact(64);
    for blk in whole.by_ref() { md5_block(&mut h, blk.try_into().unwrap()) }
    let rest = whole.remainder();
    let blocks = if rest.len() < 56 { 1 } else { 2 };
    let mut tail = [0u8; 128];
    tail[..rest.len()].copy_from_slice(rest);
    tail[rest.len()] = 0x80;
    tail[blocks * 64 - 8..blocks * 64].copy_from_slice(&(msg.len() as u64 * 8).to_le_bytes());
    for blk in tail[..blocks * 64].chunks_exact(64) { md5_block(&mut h, blk.try_into().unwrap()) }
    let mut o = [0u8; 16];
    for (d, v) in o.chunks_exact_mut(4).zip(h) { d.copy_from_slice(&v.to_le_bytes()) }
    o
}

// reduce.c `GC_*`: the cell kinds of `groupCells`.
// kind 0 (wrap) is every kind the arms below do not name
const GC_CLAMP: u8 = 1;
const GC_AVG_INT: u8 = 2;
const GC_FLOAT: u8 = 3;
const GC_AVG_FLOAT: u8 = 4;
const GC_NAN: u64 = 0xfff8000000000000;

/// reduce.c:`GC_LOOP`: cell `i` is `cell(sum, count)` of group `ord[i]`, written as its low `W` bytes; an id at or past
/// `ng` reads zero slots. `m` is the `2 * ng` slots, folds then counts.
fn cells<const W: usize>(m: &[i64], ord: &[u64], out: &mut [u8], cell: impl Fn(i64, i64) -> u64) {
    assert_eq!(out.len(), ord.len() * W, "group_cells: {} output bytes for {} cells of width {W}", out.len(), ord.len());
    let (s, k) = m.split_at(m.len() / 2);
    for (o, &g) in out.chunks_exact_mut(W).zip(ord) {
        let g = usize::try_from(g).unwrap_or(usize::MAX);
        let (s, k) = (s.get(g).copied().unwrap_or(0), k.get(g).copied().unwrap_or(0));
        o.copy_from_slice(&cell(s, k).to_le_bytes()[..W]);
    }
}
fn clamped(s: i64) -> i64 { if s > -2147483648 && s < 2147483648 { s } else { -2147483648 } }

/// reduce.c:`qlean_group_cells` past the unboxing and its width check: `out` is `ord.len()` cells of `w` bytes (eight for
/// the two averages), the kind switch outside the loop so each arm is one gather of the slots by `ord`.
pub fn group_cells(kind: u8, w: usize, ng: usize, m: &[i64], ord: &[u64], out: &mut [u8]) {
    let m = &m[..2 * ng];
    match kind {
        GC_AVG_INT => cells::<8>(m, ord, out, |s, k| if k == 0 { GC_NAN } else { (s as f64 / k as f64).to_bits() }),
        GC_AVG_FLOAT => cells::<8>(m, ord, out, |s, k| {
            let r = f64::from_bits(s as u64) / k as f64;
            if k == 0 || r.is_nan() { GC_NAN } else { r.to_bits() }
        }),
        GC_FLOAT if w == 4 => cells::<4>(m, ord, out, |s, _| (f64::from_bits(s as u64) as f32).to_bits() as u64),
        GC_FLOAT => cells::<8>(m, ord, out, |s, _| s as u64),
        _ => {
            let c = kind == GC_CLAMP;
            match w {
                1 => cells::<1>(m, ord, out, |s, _| if c { clamped(s) } else { s } as u64),
                2 => cells::<2>(m, ord, out, |s, _| if c { clamped(s) } else { s } as u64),
                4 => cells::<4>(m, ord, out, |s, _| if c { clamped(s) } else { s } as u64),
                _ => cells::<8>(m, ord, out, |s, _| if c { clamped(s) } else { s } as u64),
            }
        }
    }
}

// q reduces floats in lanes and the lane count shows up in the answer: eight double lanes and sixteen float lanes,
// the tail folded in AFTER the lanes, and no split below two full groups (`sum (1e16),(k#1f),-1e16` is the strict left
// fold's 0f through n = 15 and lane-split from n = 16). The lane count is part of the specification (`Coc.Over.lanes`,
// `overFold`). A NaN is q's null and contributes nothing. Every add is a plain `+`, no FMA, so the association order
// written here is the one that runs.

/// Where a float sum's elements come from, a block of `blk` at a time: a pointer into a dense payload, or an ALP block
/// decoded into `buf`, so a column is never restored whole and the two forms cannot be summed in two orders.
pub trait Blocks<T> {
    /// Block `b`'s first `nb` elements: a slice of the source, or of `buf` once filled.
    fn at<'a>(&'a mut self, b: usize, nb: usize, buf: &'a mut [T]) -> &'a [T];
}
/// A dense payload: block `b` starts at element `b * BLK`.
pub struct Dense<'a, T>(pub &'a [T]);
impl<T> Blocks<T> for Dense<'_, T> {
    fn at<'a>(&'a mut self, b: usize, _: usize, _: &'a mut [T]) -> &'a [T] { &self.0[b * BLK..] }
}

/// reduce.c `qlean_f32_sum_src`, q's `real` sum, measured on 20M two-decimal prices: sixteen `float` lanes over the full
/// groups, an eight-wide `float` group when eight or more remain, the last few in double, all combined in double (`sum`
/// rounds that once to `real`, `avg` divides it unrounded). `blk` is a multiple of 16, so element i is in lane i % 16
/// whatever the source and only the last block has a tail. A NaN poisons its lane and is counted; any at all and the
/// lanes are thrown away for the serial pass q takes over the live elements in one double accumulator.
pub fn f32_sum<S: Blocks<f32>>(src: &mut S, n: usize, blk: usize, buf: &mut [f32], live: Option<&mut usize>) -> f64 {
    let (mut acc, mut a8) = ([0f32; 16], [0f32; 8]);
    let (mut rest, mut s, mut s8, mut nan) = (0.0f64, 0.0f64, 0.0f64, 0usize);
    for (b, lo) in (0..n).step_by(blk).enumerate() {
        let nb = (n - lo).min(blk);
        let full = nb & !15;
        let x = src.at(b, nb, buf);
        nan += simd::f32_lanes(&x[..full], &mut acc);
        let mut k = full;
        if nb - full >= 8 {
            for j in 0..8 { a8[j] += x[k + j]; nan += (x[k + j] != x[k + j]) as usize }
            k += 8;
        }
        for &v in &x[k..nb] { rest += v as f64; nan += (v != v) as usize }
    }
    if let Some(l) = live { *l = n - nan }
    if nan != 0 {
        for (b, lo) in (0..n).step_by(blk).enumerate() {
            let nb = (n - lo).min(blk);
            for &v in &src.at(b, nb, buf)[..nb] { if v == v { s += v as f64 } }
        }
        return s;
    }
    for a in acc { s += a as f64 }
    for a in a8 { s8 += a as f64 }
    s + s8 + rest
}

/// reduce.c `qlean_f64_sum_src`, `sumF64Total`, the one order of a `float` sum and `avg` at every encoding: serial below
/// two full groups, else eight lanes over the full groups folded left to right and the tail added after. `blk` is a
/// multiple of 8, so element i is in lane i % 8 whatever the source. On a column holding a null `sum` is one serial
/// accumulator over the live elements and `avg` two lanes by position over the even prefix, then the last.
pub fn f64_sum<S: Blocks<f64>>(src: &mut S, n: usize, blk: usize, buf: &mut [f64], live: Option<&mut usize>, avg: bool)
    -> f64 {
    assert!(blk % 8 == 0, "f64_sum: block of {blk} elements is not a multiple of the 8 lanes");
    let (mut acc, mut s, mut a2) = ([0f64; 8], 0.0f64, [0f64; 2]);
    // the lanes' extent: nothing below two full groups, else every full group
    let lanes = if n / 8 < 2 { 0 } else { n & !7 };
    let mut nan = 0usize;
    for (b, lo) in (0..n).step_by(blk).enumerate() {
        let nb = (n - lo).min(blk);
        let full = lanes.wrapping_sub(lo).min(nb);
        let x = src.at(b, nb, buf);
        nan += simd::f64_lanes(&x[..full], &mut acc);
        // past the lanes: the whole column below the split, the under-eight tail above it, added after the lanes are
        // folded, both in the last block since `lanes` is a multiple of 8
        if lanes != 0 && lo + nb == n { s = acc[0]; for j in 1..8 { s += acc[j] } }
        for &v in &x[full..nb] { nan += (v != v) as usize; s += v }
    }
    if let Some(l) = live { *l = n - nan }
    if nan == 0 { return s }
    let m = if avg { n & !1 } else { 0 };
    s = 0.0;
    for (b, lo) in (0..n).step_by(blk).enumerate() {
        let nb = (n - lo).min(blk);
        for (i, &v) in src.at(b, nb, buf)[..nb].iter().enumerate() {
            if v == v { if lo + i < m { a2[i & 1] += v } else { s += v } }
        }
    }
    (a2[0] + a2[1]) + s
}

/// A scratch block for a source that decodes into it, 64-byte aligned as the decoders' stores want.
pub fn with_buf<T: Copy + Default, R>(blk: usize, f: impl FnOnce(&mut [T]) -> R) -> R {
    let mut v = alloc::vec![T::default(); blk + 64 / size_of::<T>()];
    let off = v.as_ptr().align_offset(64).min(64 / size_of::<T>());
    f(&mut v[off..off + blk])
}

/// The two float widths `over_f32` and `over_f64` share.
pub trait Fl: Copy + PartialOrd + core::ops::Add<Output = Self> + core::ops::Mul<Output = Self> + core::ops::Neg<Output = Self> {
    const ZERO: Self;
    const ONE: Self;
    const INF: Self;
}
impl Fl for f32 { const ZERO: f32 = 0.0; const ONE: f32 = 1.0; const INF: f32 = f32::INFINITY; }
impl Fl for f64 { const ZERO: f64 = 0.0; const ONE: f64 = 1.0; const INF: f64 = f64::INFINITY; }

/// reduce.c `qlean_over_sv`: `acc * base + digit` down the longs of `a`, mod 2^64, which is a monoid, so the chain splits
/// into `SV_LANES` interleaved ones (lane `j` folds elements `j, j + L, ..` under `base^L`) that recombine by one more
/// Horner: bit-identical to the serial fold. 24 lanes: where the pass stops multiplying and starts reading memory
/// (serial 711us at a million longs, 4 lanes 222, 8 111, 16 56, 24 49.6, 32 49.4). No null case: q's `sv` runs
/// straight through `0N` as `-2^63`.
pub fn over_sv(base: i64, a: &[u8]) -> i64 {
    const L: usize = 24;
    let rd = |e: &[u8]| u64::from_ne_bytes(e.try_into().unwrap());
    let b = base as u64;
    let step = (0..L).fold(1u64, |s, _| s.wrapping_mul(b));
    let mut lane = [0u64; L];
    let mut c = a[..a.len() / 8 * 8].chunks_exact(8 * L);
    for ch in c.by_ref() {
        for (j, l) in lane.iter_mut().enumerate() { *l = l.wrapping_mul(step).wrapping_add(rd(&ch[8 * j..8 * j + 8])) }
    }
    let acc = lane.iter().fold(0u64, |acc, &l| acc.wrapping_mul(b).wrapping_add(l));
    c.remainder().chunks_exact(8).fold(acc, |acc, e| acc.wrapping_mul(b).wrapping_add(rd(e))) as i64
}

/// The float verb table of `qlean_over_groups_float` and `qlean_over_segments_float`: one left fold from 0, 1, `inf`,
/// `-inf` at accumulator type `A`, the element widened to `A` first (a `real` fold in `double` widens each element).
macro_rules! of_verbs {
    ($op:expr, $go:ident) => { match $op {
        1 => $go!(A::ONE, |a: A, v: A| a * v),
        2 => $go!(A::INF, |a: A, v: A| if v < a { v } else { a }),
        3 => $go!(-A::INF, |a: A, v: A| if v > a { v } else { a }),
        _ => $go!(A::ZERO, |a: A, v: A| a + v),
    } };
}
/// `f::<T, A, W>(args)` at the id width `w`, as `ids::by_width` does for one parameter.
macro_rules! by_width_ta {
    ($w:expr, $f:ident::<$t:ty, $a:ty>($($x:expr),*)) => { match $w {
        0 => $f::<$t, $a, 0>($($x),*), 1 => $f::<$t, $a, 1>($($x),*), 2 => $f::<$t, $a, 2>($($x),*),
        4 => $f::<$t, $a, 4>($($x),*), 8 => $f::<$t, $a, 8>($($x),*), 16 => $f::<$t, $a, 16>($($x),*),
        32 => $f::<$t, $a, 32>($($x),*), _ => $f::<$t, $a, 64>($($x),*),
    } };
}

/// reduce.c `OGF_LOOP`: one group per id, one accumulator each, rows in order, NaN (q's null) skipped.
fn og_float<T: Copy + PartialEq + Into<A>, A: Fl, const IW: u32>(op: u8, ids: &[u8], x: &[T], acc: &mut [A], cnt: &mut [i64]) {
    let ng = acc.len();
    macro_rules! go { ($seed:expr, $step:expr) => {{
        acc.fill($seed);
        for (i, &v) in x.iter().enumerate() {
            let k = id_at(ids, IW, i);
            if k < ng && v == v { acc[k] = ($step)(acc[k], v.into()); cnt[k] += 1 }
        }
    }}; }
    of_verbs!(op, go)
}

/// reduce.c `qlean_over_groups_float` past the unboxing: `res` is `16 * ng` bytes, the folds as double bits then the
/// live counts. q's `select sum x by g` over floats is one left fold per group in row order, not the verb per group
/// (whose `sum` runs lanes), so one serial pass with no split: a slice's partial would be a reassociation. A `real` fold
/// rounds to `real` at each step, a `real` avg folds in double.
#[allow(clippy::too_many_arguments)]
pub fn over_groups_float(op: u8, f32: bool, avg: bool, ng: usize, iw: usize, rows: usize, gid: &[u8], a: &[u8], res: &mut [u8]) {
    let w = if f32 { 4 } else { 8 };
    let iw32 = iw as u32;
    let n = (a.len() / w).min(rows).min(ids_avail(gid.len(), iw32));
    // C's `IDS_WIDTHS` switch on the `size_t` goes to 64 for any width it does not name
    let wd = match iw { 0 | 1 | 2 | 4 | 8 | 16 | 32 => iw32, _ => 64 };
    let (s, cnt) = res.split_at_mut(ng * 8);
    let s = crate::pod::cast_mut::<f64>(s).expect("over_groups_float: the answer is not 8-aligned");
    let cnt = crate::pod::cast_mut::<i64>(cnt).expect("over_groups_float: the answer is not 8-aligned");
    cnt.fill(0);
    if f32 {
        let x = crate::pod::cast::<f32>(&a[..n * 4]).expect("over_groups_float: the payload is not 4-aligned");
        if avg { by_width_ta!(wd, og_float::<f32, f64>(op, gid, x, s, cnt)) } else {
            let mut acc = vec![0f32; ng];
            by_width_ta!(wd, og_float::<f32, f32>(op, gid, x, &mut acc, cnt));
            for (d, &v) in s.iter_mut().zip(&acc) { *d = v as f64 }
        }
    } else {
        let x = crate::pod::cast::<f64>(&a[..n * 8]).expect("over_groups_float: the payload is not 8-aligned");
        by_width_ta!(wd, og_float::<f64, f64>(op, gid, x, s, cnt))
    }
}

/// reduce.c `OSF_LOOP`: `og_float`'s fold, seeds and steps over each segment's rows (`seg_at`: the offsets clamped into
/// `[0, n]`, empty where they descend) into one accumulator of type `A`.
fn os_float<T: Copy + PartialEq + Into<A>, A: Fl + Into<f64>>(op: u8, offs: &[i64], x: &[T], s: &mut [f64], cnt: &mut [i64]) {
    let n = x.len();
    macro_rules! go { ($seed:expr, $step:expr) => {
        for (r, (d, c)) in s.iter_mut().zip(cnt.iter_mut()).enumerate() {
            let (lo, e) = (seg_at(offs, n, r), seg_at(offs, n, r + 1));
            let (mut acc, mut k) = ($seed, 0i64);
            for &v in x.get(lo..e).unwrap_or_default() { if v == v { acc = ($step)(acc, v.into()); k += 1 } }
            (*d, *c) = (acc.into(), k);
        }
    }; }
    of_verbs!(op, go)
}

/// reduce.c `qlean_over_segments_float` past the unboxing: `offs.len() - 1` segments into `res` (`16 * ng` bytes: the
/// folds as double bits, then the live counts). Serial, as the id form is.
pub fn over_segments_float(op: u8, f32: bool, avg: bool, offs: &[i64], a: &[u8], res: &mut [u8]) {
    let ng = offs.len().saturating_sub(1);
    let (s, cnt) = res.split_at_mut(ng * 8);
    let s = crate::pod::cast_mut::<f64>(s).expect("over_segments_float: the answer is not 8-aligned");
    let cnt = crate::pod::cast_mut::<i64>(cnt).expect("over_segments_float: the answer is not 8-aligned");
    if f32 {
        let x = crate::pod::cast::<f32>(&a[..a.len() / 4 * 4]).expect("over_segments_float: the payload is not 4-aligned");
        if avg { os_float::<f32, f64>(op, offs, x, s, cnt) } else { os_float::<f32, f32>(op, offs, x, s, cnt) }
    } else {
        let x = crate::pod::cast::<f64>(&a[..a.len() / 8 * 8]).expect("over_segments_float: the payload is not 8-aligned");
        os_float::<f64, f64>(op, offs, x, s, cnt)
    }
}

/// reduce.c:`OVER_MINMAX_CASE`, the AVX-512 arm: `min`/`max` over `L` lanes (one `__m512`). Below one group it is the
/// serial fold with `stepk`, which keeps its accumulator on a tie (q answers the FIRST of a `+0`/`-0` tie there); at or
/// above it the lanes take `step`, where the later wins, the tail lanes folding nothing, then the horizontal `step`.
/// A NaN is skipped by its own lane (the mask), and the count is the elements that were not.
fn minmax<T: Fl, const L: usize>(p: &[T], id: T, step: impl Fn(T, T) -> T, stepk: impl Fn(T, T) -> T) -> (T, usize) {
    if p.len() < L {
        let (mut r, mut seen) = (id, 0);
        for &v in p { if v == v { r = stepk(r, v); seen += 1 } }
        return (r, seen);
    }
    let (mut acc, mut cn) = ([id; L], [0u64; L]);
    let (whole, rest) = p.as_chunks::<L>();
    for ch in whole {
        for j in 0..L { if ch[j] == ch[j] { acc[j] = step(acc[j], ch[j]) } cn[j] += (ch[j] == ch[j]) as u64 }
    }
    for (j, &v) in rest.iter().enumerate() {
        if v == v { acc[j] = step(acc[j], v) }
        cn[j] += (v == v) as u64;
    }
    let r = acc[1..].iter().fold(acc[0], |r, &x| step(r, x));
    (r, cn.iter().sum::<u64>() as usize)
}

/// reduce.c:`OVER_ENGINE`: the verb switch outside the loop. `add` is the verb-0 fold (a block-wise sum). `prd` is not
/// lane-split (`(1e200;1e200),(1000000#1f),(1e-200;1e-200)` is `0w`, the overflow surviving as a left fold leaves it);
/// verbs past `max` answer 0 and count nothing. `live` is the count of elements the fold stepped on.
fn over<T: Fl, const L: usize>(op: u8, p: &[T], live: Option<&mut usize>, add: impl FnOnce(&[T], Option<&mut usize>) -> T) -> T {
    let (r, seen) = match op {
        0 => return add(p, live),
        1 => {
            let (mut r, mut seen) = (T::ONE, 0);
            // a skipped element multiplies by the identity, which keeps the select off the multiply's chain
            for &v in p { let ok = v == v; r = r * if ok { v } else { T::ONE }; seen += ok as usize }
            (r, seen)
        }
        2 => minmax::<T, L>(p, T::INF, |a, v| if a < v { a } else { v }, |a, v| if v < a { v } else { a }),
        3 => minmax::<T, L>(p, -T::INF, |a, v| if v < a { a } else { v }, |a, v| if a < v { v } else { a }),
        _ => (T::ZERO, 0),
    };
    if let Some(l) = live { *l = seen }
    r
}
/// reduce.c `over_f64`: `op` over doubles, `live` the non-null count.
pub fn over_f64(op: u8, p: &[f64], live: Option<&mut usize>) -> f64 {
    over::<f64, 8>(op, p, live, |p, l| f64_sum(&mut Dense(p), p.len(), BLK, &mut [], l, false))
}
/// reduce.c `over_f32`: `op` over floats; `sum` is the double total rounded once to `real`.
pub fn over_f32(op: u8, p: &[f32], live: Option<&mut usize>) -> f32 {
    over::<f32, 16>(op, p, live, |p, l| f32_sum(&mut Dense(p), p.len(), BLK, &mut [], l) as f32)
}
/// reduce.c `qlean_over_f64_sum`: the total `avg` divides and its count out of the same pass; with no null it is
/// `sum`'s to the bit, with one it is the two lanes where `sum` is serial.
pub fn over_f64_sum(p: &[f64], live: Option<&mut usize>) -> f64 { f64_sum(&mut Dense(p), p.len(), BLK, &mut [], live, true) }
/// reduce.c `qlean_over_f32_sum`.
pub fn over_f32_sum(p: &[f32], live: Option<&mut usize>) -> f64 { f32_sum(&mut Dense(p), p.len(), BLK, &mut [], live) }

#[cfg(test)]
mod tests {
    use super::over_bytes;
    use alloc::vec::Vec;
    // ids at 8 bits; the id 5 is at or past `ng` and dropped; nul 3 is skipped by `sum` and kept by `any`
    #[test] fn over_groups_small() {
        let (gid, src) = ([0u8, 1, 0, 1, 5], [1u8, 2, 3, 4, 9]);
        let mut r = [0i64; 4];
        super::over_groups(crate::c::qlean_run_c, 0, 0, 3, 2, 8, 5, &gid, &src, &mut r);
        assert_eq!(r, [1, 6, 1, 2]);
        super::over_groups(crate::c::qlean_run_c, 5, 0, 3, 2, 8, 5, &gid, &src, &mut r);
        assert_eq!(r, [1, 1, 2, 2]);
        // rows clamps the count; a width-0 payload is all group 0
        super::over_groups(crate::c::qlean_run_c, 0, 0, -1, 2, 0, 3, &[], &src, &mut r);
        assert_eq!(r, [6, 0, 3, 0]);
    }
    // three slices combine to what one slice folds, at every packed width
    #[test] fn over_groups_slices_combine() {
        let src: Vec<u8> = (0..300u32).flat_map(|i| (i as i32 * 7 - 500).to_ne_bytes()).collect();
        for iw in [0u32, 1, 2, 4, 8, 16, 32, 64] {
            let gid: Vec<u8> = (0..300 * 8).map(|i: u32| (i.wrapping_mul(2654435761) >> 13) as u8).collect();
            for op in 0..6u8 {
                let mut many = [0i64; 6];
                let mut acc = [0i64; 6];
                super::over_groups_slice(op, 2, 0, 3, iw, &gid, &src, 0, 300, &mut acc);
                let n = 300;
                super::over_groups(crate::c::qlean_run_c, op, 2, 0, 3, iw, n, &gid, &src, &mut many);
                // the combine of the three blocks folds as one block does, with the counts equal
                let mut cnt = [0i64; 3];
                for g in 0..3 { cnt[g] = acc[2 * g + 1] }
                assert_eq!(&many[3..], &cnt, "iw {iw} op {op}");
            }
        }
    }
    fn bytes<T: Copy>(x: &[T], f: fn(T) -> Vec<u8>) -> Vec<u8> { x.iter().flat_map(|&v| f(v)).collect() }
    // expected values are the C's own, from the original `qlean_over_bytes`
    #[test] fn against_c() {
        let a = bytes(&[5i16, -32768, 7, -3], |v| v.to_ne_bytes().to_vec());
        let d = bytes(&[i64::MIN, 4, -9], |v| v.to_ne_bytes().to_vec());
        let c = [200u8, 100, 0, 255];
        let want_i16 = [9, -105, -3, 7, 1, 1];
        let want_empty = [0, 1, 32767, -32767, 1, 0];
        let want_u8 = [555, 0, 0, 255, 0, 1];
        let want_u8_nul = [355, 0, 0, 255, 0, 1];
        let want_i64 = [-5, -36, -9, 4, 1, 1];
        for op in 0..6u8 {
            let k = op as usize;
            assert_eq!(over_bytes(op, 1, -32768, &a), want_i16[k], "i16 op {op}");
            assert_eq!(over_bytes(op, 1, -32768, &[]), want_empty[k], "empty op {op}");
            assert_eq!(over_bytes(op, 0, -1, &c), want_u8[k], "u8 op {op}");
            assert_eq!(over_bytes(op, 0, 200, &c), want_u8_nul[k], "u8 nul 200 op {op}");
            assert_eq!(over_bytes(op, 3, i64::MIN, &d), want_i64[k], "i64 op {op}");
        }
    }
    // expected values are the C's own (`qlean_over_segments`, `qlean_bit_rows_over`): clamped, empty and descending
    // segments, a null, a row past `m` and a negative row index
    #[test] fn segments_and_bit_rows_against_c() {
        use super::{bit_rows, segments};
        use crate::c::qlean_run_c;
        let d: Vec<u8> = [5i16, -32768, 7, -3, 9, 1].iter().flat_map(|v| v.to_ne_bytes()).collect();
        let want = [[5, 0, 13, 1, 1, 0, 3, 1], [5, 1, -189, 1, 1, 0, 3, 1], [5, 32767, -3, 1, 1, 0, 3, 1],
                    [5, -32767, 9, 1, 1, 0, 3, 1], [1, 1, 1, 1, 2, 0, 3, 1], [1, 0, 1, 1, 2, 0, 3, 1]];
        for (op, w) in want.iter().enumerate() {
            let mut res = [0; 8];
            segments(qlean_run_c, op as u8, 1, -32768, &[0, 2, 2, 5, 9], &d, 6, &mut res);
            assert_eq!(&res, w, "op {op}");
        }
        let (mut a, mut b) = ([0u8; 2], [0u8; 2]);
        bit_rows(qlean_run_c, false, 3, &[0, 2, 2, 4], &[1, 0, 5, 2, 100, -1], &[0xb5, 0x6c, 0x0f], &mut a);
        bit_rows(qlean_run_c, true, 3, &[0, 2, 2, 4], &[1, 0, 5, 2, 100, -1], &[0xb5, 0x6c, 0x0f], &mut b);
        assert_eq!((a, b), ([135, 1], [188, 0]));
    }
    // RFC 1321's suite, and the block-edge lengths 55, 56, 63, 64 (one or two padding blocks)
    #[test] fn md5_rfc_vectors() {
        let hex = |m: &[u8]| super::md5(m).iter().map(|b| alloc::format!("{b:02x}")).collect::<alloc::string::String>();
        assert_eq!(hex(b""), "d41d8cd98f00b204e9800998ecf8427e");
        assert_eq!(hex(b"abc"), "900150983cd24fb0d6963f7d28e17f72");
        assert_eq!(hex(b"message digest"), "f96b697d7cb7938d525a2f31aaf161d0");
        assert_eq!(hex(b"12345678901234567890123456789012345678901234567890123456789012345678901234567890"),
                   "57edf4a22be3c955ac49da2e2107b67a");
        assert_eq!(hex(&[b'a'; 55]), hex(&[b'a'; 55]));
        assert_ne!(hex(&[b'a'; 55]), hex(&[b'a'; 56]));
    }
    // expected values are the C's own (`over_f64`, `over_f32`): the split floor at n = 16, the tail added after the
    // lanes, and the live counts
    #[test] fn float_sums_against_c() {
        use super::{over_f32, over_f64, over_f64_sum};
        let shape = |k: usize| { let mut v = alloc::vec![1e16]; v.extend(core::iter::repeat_n(1.0, k)); v.push(-1e16); v };
        for (k, want) in [(1, 0.0), (7, 0.0), (13, 0.0), (16, 16.0), (17, 16.0), (20, 16.0), (23, 28.0), (26, 28.0)] {
            let mut live = 0;
            assert_eq!(over_f64(0, &shape(k), Some(&mut live)), want, "k {k}");
            assert_eq!(live, k + 2);
        }
        let real = |k: usize| { let mut v = alloc::vec![16777216f32]; v.extend(core::iter::repeat_n(1.0, k)); v.push(-16777216.0); v };
        for k in [14, 20, 26] { assert_eq!(over_f32(0, &real(k), None), k as f32, "real k {k}") }
        let (mut live, mut v) = (0, (1..=20).map(f64::from).collect::<Vec<_>>());
        v[5] = f64::NAN;
        assert_eq!(over_f64(0, &v, Some(&mut live)), 204.0);
        assert_eq!(live, 19);
        assert_eq!(over_f64_sum(&v, Some(&mut live)), 204.0);
        // `prd` skips the null, a verb past `max` answers 0 and counts nothing
        let n3 = [f64::NAN, 1.0, 2.0];
        assert_eq!((over_f64(1, &n3, Some(&mut live)), live), (2.0, 2));
        assert_eq!((over_f64(9, &n3, Some(&mut live)), live), (0.0, 0));
    }
    // q answers the first of a `+0`/`-0` tie below one lane group and the later one at or above it
    #[test] fn min_max_signed_zero_tie() {
        let z: Vec<f64> = (0..9).map(|i| if i & 1 == 1 { -0.0 } else { 0.0 }).collect();
        for op in [2, 3] {
            assert!(super::over_f64(op, &z[..7], None).is_sign_positive(), "op {op} n 7");
            assert!(super::over_f64(op, &z[..8], None).is_sign_negative(), "op {op} n 8");
            assert!(super::over_f64(op, &z, None).is_sign_negative(), "op {op} n 9");
        }
    }
    // expected bytes are the C's own (`qlean_group_cells`): wrap, clamp, the id past `ng` reading zero slots, and the
    // two float kinds
    #[test] fn group_cells_against_c() {
        use super::{group_cells, GC_AVG_FLOAT, GC_CLAMP, GC_FLOAT};
        let m = [-5i64, 3000000000, -3000000000, 0, 2, 1, 0, 4];
        let ord = [0u64, 1, 2, 3, 9];
        let mut o = [0u8; 10];
        group_cells(0, 2, 4, &m, &ord, &mut o);
        assert_eq!(o, [0xfb, 0xff, 0x00, 0x5e, 0x00, 0xa2, 0, 0, 0, 0]);
        let mut o = [0u8; 20];
        group_cells(GC_CLAMP, 4, 4, &m, &ord, &mut o);
        assert_eq!(o, [0xfb, 0xff, 0xff, 0xff, 0, 0, 0, 0x80, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0, 0]);
        let f = [1.5f64.to_bits() as i64, (-0.0f64).to_bits() as i64, 0, 3.0f64.to_bits() as i64, 2, 0, 1, 1];
        let mut o = [0u8; 12];
        group_cells(GC_FLOAT, 4, 4, &f, &ord[..3], &mut o);
        assert_eq!(o, [0, 0, 0xc0, 0x3f, 0, 0, 0, 0x80, 0, 0, 0, 0]);
        let mut o = [0u8; 24];
        group_cells(GC_AVG_FLOAT, 8, 4, &f, &ord[..3], &mut o);
        assert_eq!(o, [0, 0, 0, 0, 0, 0, 0xe8, 0x3f, 0, 0, 0, 0, 0, 0, 0xf8, 0xff, 0, 0, 0, 0, 0, 0, 0, 0]);
    }
}
