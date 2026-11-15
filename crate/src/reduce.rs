#![forbid(unsafe_code)]
#![allow(unused_variables)] // A13 fills the rest of this module and removes it
//! Column (a), reduce.c: whole-vector reductions of a byte payload (A12; the byte sum is `simd::u8_sum`) and the
//! segmented reductions and bit-row folds (A13).
use crate::c::Runner;

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
        _ => verbs::<i64, 32, 32>(op, nul, n, a, seed),
    }
}

// ---- A13: reduce.c:488-619 ----
/// reduce.c:488 `seg_at`: segment `k`'s start (`o` the `n` starts; `k == n` answers the end).
pub fn seg_at(o: &[i64], n: usize, k: usize) -> usize { unimplemented!("A13: seg_at") }
/// reduce.c:493 `seg_lower`: the segment holding element `i`.
pub fn seg_lower(o: &[i64], n: usize, ng: usize, i: usize) -> usize { unimplemented!("A13: seg_lower") }
/// reduce.c:516 `over_segments`: elements `from .. to` of `src` (class `cls`) folded by `op` into the
/// segment results `res`, segments `lo .. hi`.
pub fn over_segments(op: u8, cls: u8, nul: i64, lo: i64, hi: i64, ng: usize, n: usize, offs: &[i64], src: &[u8],
                     from: usize, to: usize, res: &mut [i64]) {
    unimplemented!("A13: over_segments")
}
/// reduce.c:537 `qlean_over_segments` past the unboxing: one result per segment into `res` (`ng` long), threaded
/// (`over_segments_pass`).
pub fn segments(run: Runner, op: u8, cls: u8, nul: i64, offs: &[i64], src: &[u8], n: usize, res: &mut [i64]) {
    unimplemented!("A13: qlean_over_segments")
}
/// reduce.c:560 `br_load`: 64 bits of the bit matrix `m` (`nb` bytes) from bit `bit`.
pub fn br_load(m: &[u8], bit: usize) -> u64 { unimplemented!("A13: br_load") }
/// reduce.c:570 `br_store`: the low `nbits` of `v` at bit `bit`.
pub fn br_store(o: &mut [u8], bit: usize, v: u64, nbits: u32) { unimplemented!("A13: br_store") }
/// reduce.c:606 `qlean_bit_rows_over` past the unboxing: per row of `w` bits, the AND (`all`) or OR of the rows
/// `idx[offs[g] .. offs[g + 1]]` of `m`, into `out`; threaded (`bit_rows_pass`).
pub fn bit_rows(run: Runner, all: bool, w: usize, offs: &[i64], idx: &[i64], m: &[u8], out: &mut [u8]) {
    unimplemented!("A13: qlean_bit_rows_over")
}

#[cfg(test)]
mod tests {
    use super::over_bytes;
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
}
