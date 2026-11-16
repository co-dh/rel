#![forbid(unsafe_code)]
//! Column (a), scan.c:309-505 (A14): the running scans (sums, prds, mins, maxs, fills) over a dense payload and
//! the block skips over an encoded one. `scan_fill` and `scan_any_null` are AVX-512 in C: their vector bodies are in
//! `simd.rs`, which this module calls and finishes (the groups that hold a null, the tail).
use crate::alp::{Cocf, POW10};
use crate::coc::Coc;
use crate::key::{SK_BIT, SK_C8, SK_F32, SK_F64, SK_I16, SK_I32, SK_I64, SK_KINDS_N, SK_U8};
use crate::{simd, BLK};

// the verb, as QLean/Kernel/Scan.lean's `Verb` in constructor order
const SC_SUMS: i32 = 0;
const SC_PRDS: i32 = 1;
const SC_MINS: i32 = 2;
const SC_MAXS: i32 = 3;
const SC_FILLS: i32 = 4;
const SC_VERBS_N: i32 = 5;
/// q's `0n` and `0Ne`: a result NaN is written as these patterns, whatever the FPU left behind
const SC_NAN64: u64 = 0xfff8_0000_0000_0000;
const SC_NAN32: u32 = 0xffc0_0000;
/// scan.c `SCAN_CHUNK`: elements whose "did any beat the accumulator" test is one or-reduction
const SCAN_CHUNK: usize = 64;

/// The accumulator of a scan, held in the 8-byte `carry` between pieces. Integers accumulate at 64 bits and wrap, as q
/// does (`sums 9223372036854775807 1 1` is `0W 0N -0W`); no step is a fused multiply-add.
trait Acc: Copy + PartialOrd {
    const ZERO: Self;
    const ONE: Self;
    fn add(self, v: Self) -> Self;
    fn mul(self, v: Self) -> Self;
    fn get(c: &[u8]) -> Self;
    fn put(self, c: &mut [u8]);
}
macro_rules! acc { ($t:ty, $z:expr, $o:expr, |$a:ident, $v:ident| $add:expr, |$a2:ident, $v2:ident| $mul:expr) => {
    impl Acc for $t {
        const ZERO: Self = $z;
        const ONE: Self = $o;
        fn add(self, $v: Self) -> Self { let $a = self; $add }
        fn mul(self, $v2: Self) -> Self { let $a2 = self; $mul }
        fn get(c: &[u8]) -> Self { Self::from_ne_bytes(c[..size_of::<Self>()].try_into().unwrap()) }
        fn put(self, c: &mut [u8]) { c[..size_of::<Self>()].copy_from_slice(&self.to_ne_bytes()) }
    }
} }
acc!(i64, 0, 1, |a, v| a.wrapping_add(v), |a, v| a.wrapping_mul(v));
acc!(f32, 0.0, 1.0, |a, v| a + v, |a, v| a * v);
acc!(f64, 0.0, 1.0, |a, v| a + v, |a, v| a * v);

// ---- readers: the signed widths sign-extend and `byte` zero-extends; a boolean is one bit, LSB first ----
fn rd_bit(p: &[u8], i: usize) -> i64 { ((p[i >> 3] >> (i & 7)) & 1) as i64 }
fn rd_u8(p: &[u8], i: usize) -> i64 { p[i] as i64 }
fn rd_i16(p: &[u8], i: usize) -> i64 { i16::from_ne_bytes(p[2 * i..2 * i + 2].try_into().unwrap()) as i64 }
fn rd_i32(p: &[u8], i: usize) -> i64 { i32::from_ne_bytes(p[4 * i..4 * i + 4].try_into().unwrap()) as i64 }
fn rd_i64(p: &[u8], i: usize) -> i64 { i64::from_ne_bytes(p[8 * i..8 * i + 8].try_into().unwrap()) }
fn rd_f32(p: &[u8], i: usize) -> f32 { f32::from_ne_bytes(p[4 * i..4 * i + 4].try_into().unwrap()) }
fn rd_f64(p: &[u8], i: usize) -> f64 { f64::from_ne_bytes(p[8 * i..8 * i + 8].try_into().unwrap()) }

// ---- null tests: `0N` is the minimum of each signed width, byte and boolean have none, `char`'s is the blank ----
fn nul_no(_: i64) -> bool { false }
fn nul_chr(v: i64) -> bool { v == 0x20 }
fn nul_i16(v: i64) -> bool { v == i16::MIN as i64 }
fn nul_i32(v: i64) -> bool { v == i32::MIN as i64 }
fn nul_i64(v: i64) -> bool { v == i64::MIN }
fn nul_f32(v: f32) -> bool { v != v }
fn nul_f64(v: f64) -> bool { v != v }

// ---- writers: an element's bytes. Truncating (the wrap of rules 3 and 4); `ws_i32` the narrowing `sums` answering
// `0N` on overflow ----
fn wr_i8(a: i64) -> [u8; 1] { (a as u8).to_ne_bytes() }
fn wr_i16(a: i64) -> [u8; 2] { (a as i16).to_ne_bytes() }
fn wr_i32(a: i64) -> [u8; 4] { (a as i32).to_ne_bytes() }
fn wr_i64(a: i64) -> [u8; 8] { a.to_ne_bytes() }
fn ws_i32(a: i64) -> [u8; 4] { wr_i32(if a == a as i32 as i64 { a } else { i32::MIN as i64 }) }
/// a NaN accumulator is written as q's own null pattern; `sums 0w -0w` is `0w 0n`, so the case is reachable
fn wr_f32(a: f32) -> [u8; 4] { (if a != a { SC_NAN32 } else { a.to_bits() }).to_ne_bytes() }
fn wr_f64(a: f64) -> [u8; 8] { (if a != a { SC_NAN64 } else { a.to_bits() }).to_ne_bytes() }

/// The first `n` elements of `p` at `R` bytes each, decoded by `f`. A chunk iterator rather than an index, so the loop
/// has no bounds check; slicing to `n * R` panics on a payload that holds fewer.
#[inline(always)]
fn elts<'a, const R: usize, A>(p: &'a [u8], n: usize, f: impl Fn([u8; R]) -> A + Copy + 'a) -> impl Iterator<Item = A> + Clone + 'a {
    p[..n * R].chunks_exact(R).map(move |c| f(c.try_into().unwrap()))
}
/// The first `n` answer slots of `out` at `W` bytes each.
#[inline(always)]
fn slots<const W: usize>(out: &mut [u8], n: usize) -> core::slice::ChunksExactMut<'_, u8> {
    assert!(out.len() >= n * W, "scan: an answer of {} bytes holds fewer than {n} elements of {W} bytes", out.len());
    out[..n * W].chunks_exact_mut(W)
}

/// `SCAN_LOOP`: read, fold the step in where the element is not null, emit the accumulator. `carry` is the accumulator
/// a caller scanning in pieces keeps between them (empty = none), `resume` says whether this piece continues one.
#[inline(always)]
fn lp<A: Acc, const W: usize>(out: &mut [u8], n: usize, carry: &mut [u8], resume: bool, seed: A,
                              vals: impl Iterator<Item = A>, nul: impl Fn(A) -> bool, step: impl Fn(A, A) -> A,
                              wr: impl Fn(A) -> [u8; W]) {
    let mut acc = if resume { A::get(carry) } else { seed };
    for (v, o) in vals.zip(slots::<W>(out, n)) {
        if !nul(v) { acc = step(acc, v) }
        o.copy_from_slice(&wr(acc));
    }
    if !carry.is_empty() { acc.put(carry) }
}

/// `SCAN_MONO`: `mins` and `maxs` have an idempotent step, so a chunk of 64 elements none of which moves the
/// accumulator is the accumulator repeated, and the test is an or of 64 compares with no serial dependence. A chunk
/// that moves it goes through `lp`'s body unchanged, so the answer is the same fold either way.
#[inline(always)]
fn mono<A: Acc, const W: usize>(out: &mut [u8], n: usize, carry: &mut [u8], resume: bool, seed: A,
                                mut vals: impl Iterator<Item = A> + Clone, nul: impl Fn(A) -> bool,
                                step: impl Fn(A, A) -> A, wr: impl Fn(A) -> [u8; W]) {
    let mut acc = if resume { A::get(carry) } else { seed };
    let mut os = slots::<W>(out, n);
    for _ in 0..n / SCAN_CHUNK {
        // 64 values at once: the or-test over them has no serial dependence and vectorises
        let vc: [A; SCAN_CHUNK] = core::array::from_fn(|_| vals.next().unwrap());
        let beat = vc.iter().fold(0u32, |b, &v| b | (step(acc, v) != acc) as u32);
        if beat == 0 {
            let w = wr(acc);
            for o in os.by_ref().take(SCAN_CHUNK) { o.copy_from_slice(&w) }
        } else {
            for (&v, o) in vc.iter().zip(os.by_ref()) {
                if !nul(v) { acc = step(acc, v) }
                o.copy_from_slice(&wr(acc));
            }
        }
    }
    for (v, o) in vals.zip(os) {
        if !nul(v) { acc = step(acc, v) }
        o.copy_from_slice(&wr(acc));
    }
    if !carry.is_empty() { acc.put(carry) }
}

/// `SCAN_VERBS`: the four verbs that carry an accumulator at one element kind, the switch outside every loop. `we`
/// writes at the element's own width (`mins` and `maxs` answer there), `ww` at the accumulator's, `ws` is `ww`'s
/// narrowing form for `sums` alone. A tie keeps the accumulator on both extremes, so `mins 0.0 -0.0` is `0f`.
#[inline(always)]
fn verbs<A: Acc, const WE: usize, const WW: usize>(
    op: i32, out: &mut [u8], n: usize, carry: &mut [u8], resume: bool, smax: A, smin1: A,
    vals: impl Iterator<Item = A> + Clone, nul: impl Fn(A) -> bool, we: impl Fn(A) -> [u8; WE],
    ww: impl Fn(A) -> [u8; WW], ws: impl Fn(A) -> [u8; WW]) {
    match op {
        SC_SUMS => lp(out, n, carry, resume, A::ZERO, vals, nul, |a, v| a.add(v), ws),
        SC_PRDS => lp(out, n, carry, resume, A::ONE, vals, nul, |a, v| a.mul(v), ww),
        SC_MINS => mono(out, n, carry, resume, smax, vals, nul, |a, v| if v < a { v } else { a }, we),
        _ => mono(out, n, carry, resume, smin1, vals, nul, |a, v| if a < v { v } else { a }, we),
    }
}

/// scan.c:309 `sc_bad_kind`: the abort for a kind the Lean dispatch never sends.
pub fn sc_bad_kind(kind: i32) -> ! {
    // C exits 1 after this text; no_std has no exit, so the panic handler prints it and aborts
    panic!("qlean_scan: element kind {kind} is not one of the {SK_KINDS_N} in QLean/Kernel/Scan.lean")
}
/// coc.h:335 `sk_dense_width`: an element's bytes in a dense payload; the boolean has none, its payload is packed bits.
fn dense_width(kind: i32) -> usize {
    match u8::try_from(kind).unwrap_or(u8::MAX) {
        SK_U8 | SK_C8 => 1,
        SK_I16 => 2,
        SK_I32 | SK_F32 => 4,
        SK_I64 | SK_F64 => 8,
        _ => panic!("qlean: element kind {kind} has no dense width -- either it is not one of the {SK_KINDS_N} in QLean/Kernel/Scan.lean, or it is the boolean, whose payload is packed bits"),
    }
}

/// `fills` at one kind: a stretch with no null is a copy, and the accumulator is only what bridges a null. `simd`
/// copies the leading 64-byte groups that hold none; a group that holds one, and the tail, go element by element.
#[inline(always)]
fn fill<A: Acc, const W: usize>(kind: i32, p: &[u8], out: &mut [u8], n: usize, carry: &mut [u8], resume: bool, seed: A,
                rd: impl Fn(&[u8], usize) -> A, nul: impl Fn(A) -> bool, wr: impl Fn(A) -> [u8; W]) {
    let w = W;
    let mut acc = if resume { A::get(carry) } else { seed };
    let lanes = 64 / w;
    let mut i = 0;
    while i < n {
        let c = simd::scan_fill(kind, &p[i * w..n * w], &mut out[i * w..n * w], n - i);
        if c > 0 {
            i += c;
            acc = rd(p, i - 1);
            continue;
        }
        let e = if n - i >= lanes { i + lanes } else { n };
        for j in i..e {
            let v = rd(p, j);
            if !nul(v) { acc = v }
            out[w * j..w * j + w].copy_from_slice(&wr(acc));
        }
        i = e;
    }
    if !carry.is_empty() { acc.put(carry) }
}

/// scan.c:322 `scan_fill`: `fills` over `n` elements of `p` into `out`; `carry` (one element) is the last non-null
/// seen, read when `resume`. `fills` seeds with the null, and at the two kinds that have none the seed is unreachable.
pub fn scan_fill(kind: i32, p: &[u8], out: &mut [u8], n: usize, carry: &mut [u8], resume: bool) {
    match u8::try_from(kind).unwrap_or(u8::MAX) {
        // the one kind that stays on the loop: a bit read, a byte written, so a group is not a group of its bytes
        SK_BIT => lp(out, n, carry, resume, 0i64, (0..n).map(|i| rd_bit(p, i)), nul_no, |_, v| v, wr_i8),
        SK_U8 => fill(kind, p, out, n, carry, resume, 0i64, rd_u8, nul_no, wr_i8),
        SK_I16 => fill(kind, p, out, n, carry, resume, i16::MIN as i64, rd_i16, nul_i16, wr_i16),
        SK_I32 => fill(kind, p, out, n, carry, resume, i32::MIN as i64, rd_i32, nul_i32, wr_i32),
        SK_I64 => fill(kind, p, out, n, carry, resume, i64::MIN, rd_i64, nul_i64, wr_i64),
        SK_F32 => fill(kind, p, out, n, carry, resume, f32::NAN, rd_f32, nul_f32, wr_f32),
        SK_F64 => fill(kind, p, out, n, carry, resume, f64::NAN, rd_f64, nul_f64, wr_f64),
        // the blank is `char`'s null and so is `fills`'s seed: `fills " ab"` is `" ab"`, `fills "a b"` is `"aab"`
        SK_C8 => fill(kind, p, out, n, carry, resume, 0x20i64, rd_u8, nul_chr, wr_i8),
        _ => sc_bad_kind(kind),
    }
}

/// scan.c:346 `scan_any_null`: whether the payload holds a null in its first `n` elements. `fills` over one that does
/// not is the identity, so the answer can be the argument itself.
pub fn scan_any_null(kind: i32, p: &[u8], n: usize) -> bool {
    let k = u8::try_from(kind).unwrap_or(u8::MAX);
    if matches!(k, SK_BIT | SK_U8) { return false } // neither layout has a null
    if !matches!(k, SK_I16 | SK_I32 | SK_I64 | SK_F32 | SK_F64 | SK_C8) { sc_bad_kind(kind) }
    let (hit, i) = simd::any_null(kind, p, n);
    hit || (i..n).any(|j| match k {
        SK_I16 => nul_i16(rd_i16(p, j)),
        SK_I32 => nul_i32(rd_i32(p, j)),
        SK_I64 => nul_i64(rd_i64(p, j)),
        SK_F32 => nul_f32(rd_f32(p, j)),
        SK_F64 => nul_f64(rd_f64(p, j)),
        _ => nul_chr(rd_u8(p, j)),
    })
}

/// scan.c:366 `scan_run`: scan `op` over `n` elements, `carry` the running accumulator.
pub fn scan_run(op: i32, kind: i32, p: &[u8], out: &mut [u8], n: usize, carry: &mut [u8], resume: bool) {
    if op >= SC_VERBS_N { panic!("qlean_scan: verb {op} is not one of the {SC_VERBS_N} in QLean/Kernel/Scan.lean") }
    if op == SC_FILLS { return scan_fill(kind, p, out, n, carry, resume) }
    match u8::try_from(kind).unwrap_or(u8::MAX) {
        SK_BIT => verbs(op, out, n, carry, resume, 1i64, 0, (0..n).map(|i| rd_bit(p, i)), nul_no, wr_i8, wr_i32, ws_i32),
        SK_U8 => verbs(op, out, n, carry, resume, 0xffi64, 0, elts(p, n, |b: [u8; 1]| b[0] as i64), nul_no, wr_i8, wr_i32, ws_i32),
        SK_I16 => verbs(op, out, n, carry, resume, i16::MAX as i64, -(i16::MAX as i64), elts(p, n, |b| i16::from_ne_bytes(b) as i64), nul_i16,
                        wr_i16, wr_i32, ws_i32),
        SK_I32 => verbs(op, out, n, carry, resume, i32::MAX as i64, -(i32::MAX as i64), elts(p, n, |b| i32::from_ne_bytes(b) as i64), nul_i32,
                        wr_i32, wr_i32, ws_i32),
        SK_I64 => verbs(op, out, n, carry, resume, i64::MAX, -i64::MAX, elts(p, n, i64::from_ne_bytes), nul_i64, wr_i64, wr_i64,
                        wr_i64),
        SK_F32 => verbs(op, out, n, carry, resume, f32::INFINITY, f32::NEG_INFINITY, elts(p, n, f32::from_ne_bytes), nul_f32,
                        wr_f32, wr_f32, wr_f32),
        SK_F64 => verbs(op, out, n, carry, resume, f64::INFINITY, f64::NEG_INFINITY, elts(p, n, f64::from_ne_bytes), nul_f64,
                        wr_f64, wr_f64, wr_f64),
        // the same byte `SK_U8` reads with the same seeds, the blank skipped
        SK_C8 => verbs(op, out, n, carry, resume, 0xffi64, 0, elts(p, n, |b: [u8; 1]| b[0] as i64), nul_chr, wr_i8, wr_i32, ws_i32),
        _ => sc_bad_kind(kind),
    }
}

/// scan.c:411 `sc_out_width`: `sums` and `prds` answer at the aggregate's accumulator type (everything below `int`
/// widens to `int`), the other three at the element's own width; a boolean answers one byte per element.
pub fn sc_out_width(op: i32, kind: i32) -> usize {
    if op == SC_SUMS || op == SC_PRDS { return if kind == SK_I64 as i32 || kind == SK_F64 as i32 { 8 } else { 4 } }
    if kind == SK_BIT as i32 { 1 } else { dense_width(kind) }
}

/// scan.c:420 `sc_fill_c`: `cnt` copies of `acc` at `w` bytes: what a `mins` or `maxs` writes over a run that never
/// moves its accumulator.
pub fn sc_fill_c(out: &mut [u8], cnt: usize, w: usize, acc: i64) {
    let (out, b) = (&mut out[..cnt * w], acc.to_le_bytes());
    match w {
        1 => out.fill(b[0]),
        2 => out.chunks_exact_mut(2).for_each(|c| c.copy_from_slice(&b[..2])),
        4 => out.chunks_exact_mut(4).for_each(|c| c.copy_from_slice(&b[..4])),
        _ => out.chunks_exact_mut(8).for_each(|c| c.copy_from_slice(&b)),
    }
}

/// scan.c:435 `sc_blk_skip`: block `b` of `c` leaves the accumulator `acc` unchanged under `op`, so its residuals need
/// not be unpacked. `0N` is the minimum of the type, so a block holding one has `base` there and `mins` declines.
pub fn sc_blk_skip(op: i32, kind: i32, c: &Coc, b: usize, cnt: usize, acc: i64) -> bool {
    if cnt != BLK || kind < SK_U8 as i32 || kind > SK_I64 as i32 || c.blk_nexc(b) != 0 { return false }
    match op {
        SC_MINS => c.meta.base[b] >= acc,
        SC_MAXS => c.meta.maxv[b] <= acc,
        _ => false,
    }
}

/// scan.c:453 `sc_alp_skip`: the ALP twin. A block with an exception is decoded, and only the eight-byte width takes
/// it: at `real` the quotient is rounded to `float` and the rounding can cross the comparison.
pub fn sc_alp_skip(op: i32, f: &Cocf, b: usize, cnt: usize, acc: f64) -> bool {
    if cnt != BLK || f.f32 || f.exc_off[b] != f.exc_off[b + 1] { return false }
    let p10 = POW10[f.exp[b] as usize];
    match op {
        SC_MINS => f.c.meta.base[b] as f64 / p10 >= acc,
        SC_MAXS => f.c.meta.maxv[b] as f64 / p10 <= acc,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    fn run(op: i32, kind: i32, p: &[u8], n: usize) -> Vec<u8> {
        let mut o = alloc::vec![0u8; n * sc_out_width(op, kind)];
        scan_run(op, kind, p, &mut o, n, &mut [], false);
        o
    }
    fn i64s(v: &[i64]) -> Vec<u8> { v.iter().flat_map(|x| x.to_ne_bytes()).collect() }
    fn i32s(o: &[u8]) -> Vec<i32> { o.chunks(4).map(|c| i32::from_ne_bytes(c.try_into().unwrap())).collect() }
    fn i64o(o: &[u8]) -> Vec<i64> { o.chunks(8).map(|c| i64::from_ne_bytes(c.try_into().unwrap())).collect() }
    const N: i64 = i64::MIN;
    const I64: i32 = SK_I64 as i32;

    #[test]
    fn nulls_are_skipped_and_seeds_are_the_verbs_identity() {
        let p = i64s(&[N, 1, 2]);
        assert_eq!(i64o(&run(SC_SUMS, I64, &p, 3)), [0, 1, 3]);
        assert_eq!(i64o(&run(SC_MINS, I64, &p, 3)), [i64::MAX, 1, 1]);
        assert_eq!(i64o(&run(SC_MAXS, I64, &p, 3)), [-i64::MAX, 1, 2]);
        assert_eq!(i64o(&run(SC_PRDS, I64, &p, 3)), [1, 1, 2]);
        assert_eq!(i64o(&run(SC_FILLS, I64, &p, 3)), [N, 1, 2]);
    }
    #[test]
    fn long_sums_wrap_and_int_sums_narrow_to_null() {
        assert_eq!(i64o(&run(SC_SUMS, I64, &i64s(&[i64::MAX, 1, 1]), 3)), [i64::MAX, N, N + 1]);
        let p: Vec<u8> = [1_000_000_000i32; 4].iter().flat_map(|x| x.to_ne_bytes()).collect();
        assert_eq!(i32s(&run(SC_SUMS, SK_I32 as i32, &p, 4)), [1_000_000_000, 2_000_000_000, i32::MIN, i32::MIN]);
    }
    #[test]
    fn prds_wraps_at_32_bits() {
        let p: Vec<u8> = [100000i32, 100000].iter().flat_map(|x| x.to_ne_bytes()).collect();
        assert_eq!(i32s(&run(SC_PRDS, SK_I32 as i32, &p, 2)), [100000, 1410065408]);
    }
    #[test]
    fn a_tie_keeps_the_accumulator_so_mins_of_zero_and_negative_zero_is_zero() {
        let p: Vec<u8> = [0.0f64, -0.0].iter().flat_map(|x| x.to_ne_bytes()).collect();
        assert_eq!(i64o(&run(SC_MINS, SK_F64 as i32, &p, 2)), [0, 0]);
    }
    #[test]
    fn a_nan_accumulator_is_written_as_the_q_null() {
        let p: Vec<u8> = [f64::INFINITY, f64::NEG_INFINITY].iter().flat_map(|x| x.to_ne_bytes()).collect();
        assert_eq!(i64o(&run(SC_SUMS, SK_F64 as i32, &p, 2))[1] as u64, SC_NAN64);
    }
    #[test]
    fn fills_leading_blank_stays_and_a_blank_between_is_replaced() {
        assert_eq!(run(SC_FILLS, SK_C8 as i32, b" ab", 3), b" ab");
        assert_eq!(run(SC_FILLS, SK_C8 as i32, b"a b", 3), b"aab");
    }
    #[test]
    fn fills_across_vector_groups_and_pieces() {
        // 200 elements, nulls at 70 and 130..140: the groups of eight holding one go element by element
        let nul = |i: i64| i == 70 || (130..140).contains(&i);
        let v: Vec<i64> = (0..200).map(|i| if nul(i) { N } else { i }).collect();
        let want: Vec<i64> = (0..200).map(|i| if nul(i) { (0..i).rev().find(|&j| !nul(j)).unwrap() } else { i }).collect();
        let p = i64s(&v);
        assert_eq!(i64o(&run(SC_FILLS, I64, &p, 200)), want);
        let (mut o, mut c) = (alloc::vec![0u8; 1592], [0u8; 8]);
        for (k, s) in [0usize, 64, 130, 199].windows(2).enumerate() {
            let (a, b) = (s[0], s[1]);
            scan_run(SC_FILLS, I64, &p[8 * a..], &mut o[8 * a..8 * b], b - a, &mut c, k != 0);
        }
        assert_eq!(i64o(&o), want[..199]);
    }
    #[test]
    fn any_null_sees_a_null_in_a_group_and_in_the_tail() {
        let mut v = [1i64; 19];
        assert!(!scan_any_null(I64, &i64s(&v), 19));
        v[18] = N;
        assert!(scan_any_null(I64, &i64s(&v), 19) && !scan_any_null(I64, &i64s(&v), 18));
        v[18] = 1;
        v[9] = N;
        assert!(scan_any_null(I64, &i64s(&v), 19));
        assert!(!scan_any_null(SK_BIT as i32, &[0xff; 4], 32));
    }
    #[test]
    fn out_width() {
        for o in [SC_SUMS, SC_PRDS] {
            assert_eq!([SK_BIT, SK_U8, SK_I16, SK_I32, SK_F32, SK_I64, SK_F64].map(|k| sc_out_width(o, k as i32)), [4, 4, 4, 4, 4, 8, 8]);
        }
        assert_eq!([SK_BIT, SK_U8, SK_I16, SK_I32, SK_I64, SK_F32, SK_F64, SK_C8].map(|k| sc_out_width(SC_MINS, k as i32)),
                   [1, 1, 2, 4, 8, 4, 8, 1]);
    }
    #[test]
    fn fill_c_writes_the_low_w_bytes() {
        let mut o = [0xEEu8; 8];
        sc_fill_c(&mut o, 3, 2, 0x1_0203);
        assert_eq!(o, [3, 2, 3, 2, 3, 2, 0xEE, 0xEE]);
    }
}
