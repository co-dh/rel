#![forbid(unsafe_code)]
//! Column (a), reduce.rs: whole-vector reductions of a byte payload (A12; the byte sum is `simd::u8_sum`) and the
//! segmented reductions and bit-row folds (A13).
use alloc::vec::Vec;
use alloc::vec;
use crate::c::{run_map, run_slices, Runner};
use crate::ids::{id_at, ids_avail};

// ---- A12: reduce.rs ----
/// An element of the four integer classes: read in native order, widened to `i64` as C's `(int64_t)` cast does.
pub trait Elem: Copy + PartialOrd + Into<i64> + TryFrom<i64> {
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

/// reduce.rs `OB_LANES`: `L` accumulators of plain vector ops, a skipped element folding in the identity `id`; every
/// step is associative with `id` its identity, so the lane split cannot move the answer.
pub fn lanes<T: Elem, A: Copy, const L: usize>(a: &[u8], id: A, cv: impl Fn(T) -> A, sk: impl Fn(T) -> bool,
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

/// reduce.rs `OB_VERBS`: the six verbs at element type `T`, the null compared at `T`'s width and skipped only
/// where `nul` is a value of `T`.
pub fn verbs<T: Elem, const LI: usize, const LT: usize>(op: u8, nul: i64, n: usize, a: &[u8], seed: i64) -> i64 {
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

/// reduce.rs `qlean_over_bytes` past the unboxing: `op` (sum, prd, min, max, ...) of class `cls` over `a`, nulls
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

// ---- A13: reduce.rs ----
/// reduce.rs `seg_at`: segment `k`'s start (`o` the `n` starts; `k == n` answers the end).
pub fn seg_at(o: &[i64], n: usize, k: usize) -> usize {
    let x = o[k];
    if x < 0 { 0 } else if x as u64 > n as u64 { n } else { x as usize }
}



/// reduce.rs `br_load`: 64 bits of the bit matrix `m` (`nb` bytes) from bit `bit`.
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
/// reduce.rs `br_store`: the low `nbits` of `v` at bit `bit`.
pub fn br_store(o: &mut [u8], bit: usize, v: u64, nbits: u32) {
    let (b, s) = (bit >> 3, (bit & 7) as u32);
    let x = (v as u128) << s;
    for t in 0..(s + nbits).div_ceil(8) as usize { o[b + t] |= (x >> (8 * t)) as u8 }
}
/// reduce.rs `qlean_bit_rows_over` past the unboxing: per row of `w` bits, the AND (`all`) or OR of the rows
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

// ---- K1: reduce.rs, the grouped fold ----
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
pub fn og_loop<T: Elem, const IW: u32, const SK: bool>(init: i64, nul: i64, step: impl Fn(i64, i64) -> i64, ng: usize, gid: &[u8],
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

pub fn og_at<T: Elem, const IW: u32>(op: u8, nul: i64, lo: i64, hi: i64, ng: usize, gid: &[u8], src: &[u8], from: usize,
                                 to: usize, acc: &mut [i64]) {
    macro_rules! go { ($init:expr, $sk:tt, $step:expr) => { og_loop::<T, IW, $sk>($init, nul, $step, ng, gid, src, from, to, acc) }; }
    og_verbs!(op, lo, hi, go)
}

pub fn og_cls<const IW: u32>(op: u8, cls: u8, nul: i64, ng: usize, gid: &[u8], src: &[u8], from: usize, to: usize, acc: &mut [i64]) {
    let (lo, hi) = if cls == 0 { (0, 255) } else { (nul.wrapping_add(1), !nul) };
    match cls {
        0 => og_at::<u8, IW>(op, nul, lo, hi, ng, gid, src, from, to, acc),
        1 => og_at::<i16, IW>(op, nul, lo, hi, ng, gid, src, from, to, acc),
        2 => og_at::<i32, IW>(op, nul, lo, hi, ng, gid, src, from, to, acc),
        _ => og_at::<i64, IW>(op, nul, lo, hi, ng, gid, src, from, to, acc),
    }
}

/// reduce.rs `over_groups`: rows `from .. to`, their ids packed at `iw` bits in `gid`, into `acc` (`2 * ng` slots).
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

/// reduce.rs `over_groups_merge`: the blocks in slice order, folds into `res[..ng]`, counts into `res[ng..]`.
pub fn og_merge(op: u8, lo: i64, hi: i64, ng: usize, blocks: &[(usize, Vec<i64>)], res: &mut [i64]) {
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
pub const OG_PAD: usize = 8;
/// reduce.rs: above this many groups a worker's block (`2 * ng` slots, 128 KB at the limit) no longer sits in its
/// own cache beside the payload it reads, so the split is declined (`wide = 0`).
pub const OG_MAX_GROUPS: usize = 8192;

/// reduce.rs `qlean_over_groups` past the unboxing: `op` of class `cls` over the first `rows` elements of `src`,
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




// reduce.rs `GC_*`: the cell kinds of `groupCells`.
// kind 0 (wrap) is every kind the arms below do not name
pub const GC_CLAMP: u8 = 1;
pub const GC_AVG_INT: u8 = 2;
pub const GC_FLOAT: u8 = 3;
pub const GC_AVG_FLOAT: u8 = 4;
pub const GC_NAN: u64 = 0xfff8000000000000;

/// reduce.rs:`GC_LOOP`: cell `i` is `cell(sum, count)` of group `ord[i]`, written as its low `W` bytes; an id at or past
/// `ng` reads zero slots. `m` is the `2 * ng` slots, folds then counts.
pub fn cells<const W: usize>(m: &[i64], ord: &[u64], out: &mut [u8], cell: impl Fn(i64, i64) -> u64) {
    assert_eq!(out.len(), ord.len() * W, "group_cells: {} output bytes for {} cells of width {W}", out.len(), ord.len());
    let (s, k) = m.split_at(m.len() / 2);
    for (o, &g) in out.chunks_exact_mut(W).zip(ord) {
        let g = usize::try_from(g).unwrap_or(usize::MAX);
        let (s, k) = (s.get(g).copied().unwrap_or(0), k.get(g).copied().unwrap_or(0));
        o.copy_from_slice(&cell(s, k).to_le_bytes()[..W]);
    }
}
pub fn clamped(s: i64) -> i64 { if s > -2147483648 && s < 2147483648 { s } else { -2147483648 } }

/// reduce.rs:`qlean_group_cells` past the unboxing and its width check: `out` is `ord.len()` cells of `w` bytes (eight for
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







/// The float verb table of `qlean_over_groups_float` and `qlean_over_segments_float`: one left fold from 0, 1, `inf`,
/// `-inf` at accumulator type `A`, the element widened to `A` first (a `real` fold in `double` widens each element).
#[macro_export]
macro_rules! of_verbs {
    ($op:expr, $go:ident) => { match $op {
        1 => $go!(A::ONE, |a: A, v: A| a * v),
        2 => $go!(A::INF, |a: A, v: A| if v < a { v } else { a }),
        3 => $go!(-A::INF, |a: A, v: A| if v > a { v } else { a }),
        _ => $go!(A::ZERO, |a: A, v: A| a + v),
    } };
}
/// `f::<T, A, W>(args)` at the id width `w`, as `ids::by_width` does for one parameter.
#[macro_export]
macro_rules! by_width_ta {
    ($w:expr, $f:ident::<$t:ty, $a:ty>($($x:expr),*)) => { match $w {
        0 => $f::<$t, $a, 0>($($x),*), 1 => $f::<$t, $a, 1>($($x),*), 2 => $f::<$t, $a, 2>($($x),*),
        4 => $f::<$t, $a, 4>($($x),*), 8 => $f::<$t, $a, 8>($($x),*), 16 => $f::<$t, $a, 16>($($x),*),
        32 => $f::<$t, $a, 32>($($x),*), _ => $f::<$t, $a, 64>($($x),*),
    } };
}







/// The two float widths `over_f32` and `over_f64` share.
pub trait Fl: Copy + PartialOrd + core::ops::Add<Output = Self> + core::ops::Mul<Output = Self> + core::ops::Neg<Output = Self> {
    const ZERO: Self;
    const ONE: Self;
    const INF: Self;
}
impl Fl for f32 { const ZERO: f32 = 0.0; const ONE: f32 = 1.0; const INF: f32 = f32::INFINITY; }
impl Fl for f64 { const ZERO: f64 = 0.0; const ONE: f64 = 1.0; const INF: f64 = f64::INFINITY; }
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
