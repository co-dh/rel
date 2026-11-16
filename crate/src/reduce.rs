#![forbid(unsafe_code)]
//! Column (a), reduce.c: whole-vector reductions of a byte payload (A12; the byte sum is `simd::u8_sum`) and the
//! segmented reductions and bit-row folds (A13).
use alloc::vec::Vec;
use alloc::vec;
use core::sync::atomic::{AtomicI64, Ordering::Relaxed};
use crate::c::{run_map, run_slices, Runner};
use crate::ids::id_at;

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
    let gn = if iw == 0 { usize::MAX } else { gid.len() * 8 / iw as usize };
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
}
