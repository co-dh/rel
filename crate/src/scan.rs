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

// ---- K3 (scan.c `sc_bits_run`, `ema_*`, `mw_sent`, `mw_seed`, `mw_open`, `mw_close`) ----

/// One word of `sc_bits_run`: once a set bit is seen every later bit is set, so the answer of a word is its bits from the
/// lowest set bit upward, `-(w & -w)`; `carry` is "a set bit was seen before this word".
#[inline(always)]
fn bits_word(carry: &mut bool, w: u64, inv: u64) -> u64 {
    let w = w ^ inv;
    let o = if *carry { !0 } else {
        let m = w & (!w).wrapping_add(1);
        *carry = w != 0;
        if m != 0 { 0u64.wrapping_sub(m) } else { 0 }
    };
    o ^ inv
}
/// scan.c `sc_bits_run`: the prefix fold at the bit layout over `out.len()` bytes of `p`, a word at a time; `inv` is
/// all ones for `mins` (prefix AND is prefix OR on the complement) and zero for `maxs` and `fills`. The bytes of the
/// last word past `out` are read as zero and not written, so the bits above `n` are the caller's to clear.
pub fn bits_run(out: &mut [u8], p: &[u8], inv: u64) {
    let p = &p[..out.len()];
    let mut carry = false;
    let mut ow = out.chunks_exact_mut(8);
    let mut pw = p.chunks_exact(8);
    for (o, c) in ow.by_ref().zip(pw.by_ref()) {
        o.copy_from_slice(&bits_word(&mut carry, u64::from_ne_bytes(c.try_into().unwrap()), inv).to_ne_bytes());
    }
    let (o, c) = (ow.into_remainder(), pw.remainder());
    if !o.is_empty() {
        let mut b = [0u8; 8];
        b[..c.len()].copy_from_slice(c);
        o.copy_from_slice(&bits_word(&mut carry, u64::from_ne_bytes(b), inv).to_ne_bytes()[..o.len()]);
    }
}

/// q takes the first NaN of a pair, spelled out and not left to the order the compiler emits: `0n*(1f-0n)` is `0xfff8..`
/// and `(1f-0n)*0n` is `0x7ff8..`, the left operand's NaN either way.
#[inline(always)]
fn ema_mul(x: f64, y: f64) -> f64 { if x != x { x } else if y != y { y } else { x * y } }
#[inline(always)]
fn ema_add(x: f64, y: f64) -> f64 { if x != x { x } else if y != y { y } else { x + y } }
/// The doubles of a payload, as `n = len / 8` elements.
#[inline(always)]
fn f64s(p: &[u8]) -> impl Iterator<Item = f64> + Clone + '_ { elts::<8, f64>(p, p.len() / 8, f64::from_ne_bytes) }
/// scan.c `qlean_scan_ema`'s loop: `out[i] = (1-a)*out[i-1] + a*y[i]`, `1-a` as q forms it (a NaN `a` keeps its sign bit
/// cleared, by negating the bits), and the first element is `(1-a)*y[0] + a*y[0]` and not `y[0]`, so `0n ema 1 2 3f` is
/// `0n` there too. Serial, and no step a fused multiply-add. `out` is `y.len() / 8` doubles.
pub fn ema(abits: u64, y: &[u8], out: &mut [u8]) {
    let a = f64::from_bits(abits);
    let oma = if a != a { f64::from_bits(abits ^ (1 << 63)) } else { 1.0 - a };
    // the element before the first is `y[0]` itself, so `prev` is `acc` throughout
    let mut acc = f64s(y).next().unwrap_or(0.0);
    for (v, o) in f64s(y).zip(slots::<8>(out, y.len() / 8)) {
        acc = ema_add(ema_mul(oma, acc), ema_mul(a, v));
        o.copy_from_slice(&acc.to_ne_bytes());
    }
}
/// scan.c `qlean_scan_ema_v`'s loop: `out[i] = co[i]*out[i-1] + xy[i]` seeded at `out[-1] = seed`; the product is handed
/// in already formed, so this is not `ema` with a branch.
pub fn ema_v(xy: &[u8], co: &[u8], seedbits: u64, out: &mut [u8]) {
    let mut acc = f64::from_bits(seedbits);
    for ((v, c), o) in f64s(xy).zip(f64s(co)).zip(slots::<8>(out, xy.len() / 8)) {
        acc = ema_add(ema_mul(c, acc), v);
        o.copy_from_slice(&acc.to_ne_bytes());
    }
}

// the moving-window verbs, as `QLean/Kernel/Scan.lean`'s `MOp` in constructor order (rs.h hands them to scan.c)
pub const MW_MSUM: i32 = 0;
pub const MW_MCOUNT: i32 = 1;
pub const MW_MAVG: i32 = 2;
pub const MW_MDEV: i32 = 3;
pub const MW_MMIN: i32 = 4;
pub const MW_MMAX: i32 = 5;
pub const MW_OPS_N: i32 = 6;
/// The shortest chunk the two loops of every reducing verb run in, and the tile `qlean_mwin_bits` writes a byte an
/// element into.
pub const MW_TILE: usize = 1024;

/// scan.c `mw_out_width`, `MOp.width`: bytes one element of the answer occupies. `msum` answers at `sums`'s width,
/// `mavg` and `mdev` eight, `mcount` four, the extremes at the operand's own width.
pub fn mw_out_width(op: i32, kind: i32) -> usize {
    match op {
        MW_MSUM => sc_out_width(SC_SUMS, kind),
        MW_MCOUNT => 4,
        MW_MMIN | MW_MMAX => sc_out_width(SC_MINS, kind),
        _ => 8,
    }
}
/// scan.c `mw_sent`: the extreme of no elements, as bits at the element's own width. `mmax` at a float takes q's `0n`
/// and not `-0w` (`|` ignores a null, so the null is its identity); at the signed widths `0N` already is the extreme.
fn mw_sent(op: i32, kind: i32) -> u64 {
    let mn = op == MW_MMIN;
    match u8::try_from(kind).unwrap_or(u8::MAX) {
        SK_BIT => mn as u64,
        SK_U8 | SK_C8 => if mn { 0xff } else { 0 },
        SK_I16 => if mn { i16::MAX as u64 } else { i16::MIN as u16 as u64 },
        SK_I32 => if mn { i32::MAX as u64 } else { i32::MIN as u32 as u64 },
        SK_I64 => if mn { i64::MAX as u64 } else { i64::MIN as u64 },
        SK_F32 => if mn { 0x7f80_0000 } else { SC_NAN32 as u64 },
        _ => if mn { 0x7ff0_0000_0000_0000 } else { SC_NAN64 },
    }
}
/// scan.c `mw_seed`, `MOp.seed`: the identity q's each-prior `&':` and `|':` start from, which each of the first `w - 1`
/// windows also holds. `3 mmax 0N 0N 0N 1` is `-0W -0W 0N 1`. The seed of `mmin` is the type's top.
fn mw_seed(op: i32, kind: i32) -> u64 {
    let mn = op == MW_MMIN;
    match u8::try_from(kind).unwrap_or(u8::MAX) {
        SK_I16 => if mn { i16::MAX as u64 } else { (-i16::MAX) as u16 as u64 },
        SK_I32 => if mn { i32::MAX as u64 } else { (-i32::MAX) as u32 as u64 },
        SK_I64 => if mn { i64::MAX as u64 } else { (-i64::MAX) as u64 },
        SK_F32 => if mn { 0x7f80_0000 } else { 0xff80_0000 },
        SK_F64 => if mn { 0x7ff0_0000_0000_0000 } else { 0xfff0_0000_0000_0000 },
        _ => mw_sent(op, kind),
    }
}

/// What `mw_open` sizes: the window clamped to `n + 1` (past that no lookback lands in the column), the history's chunk
/// `tl` and capacity `cap = w + tl`, and `ew`, the answer's width, which is also the width of an extreme's phase.
pub struct MwDims { pub w: usize, pub tl: usize, pub cap: usize, pub ew: usize }
pub fn mw_dims(op: i32, kind: i32, w: usize, n: usize) -> MwDims {
    let w = if w < 1 { 1 } else if w > n { n + 1 } else { w };
    let tl = w.max(MW_TILE);
    MwDims { w, tl, cap: w + tl, ew: mw_out_width(op, kind) }
}
/// The extremes' suffix table `sufx` (`w + 1` slots of `ew` bytes): the first phase has no previous one, so its suffix
/// is what a truncated window adds, q's each-prior seed in the `w` leading slots and the identity in the last, which
/// the first full window reads and no phase close overwrites. Returns the opening extreme `extbits`.
pub fn mw_prime(sufx: &mut [u8], op: i32, kind: i32, ew: usize) -> u64 {
    let (sb, sd) = (mw_sent(op, kind), mw_seed(op, kind));
    let (seed, last) = sufx.split_at_mut(sufx.len() - ew);
    #[inline(always)]
    fn fill<const E: usize>(s: &mut [u8], v: u64) { s.chunks_exact_mut(E).for_each(|c| c.copy_from_slice(&v.to_ne_bytes()[..E])) }
    match ew { 1 => fill::<1>(seed, sd), 2 => fill::<2>(seed, sd), 4 => fill::<4>(seed, sd), _ => fill::<8>(seed, sd) }
    last.copy_from_slice(&sb.to_ne_bytes()[..ew]);
    sb
}


// ---- the moving-window engine: scan.c `mw_run` and its window macros (K4) ----

/// The engine state of scan.c's `mwin` (rs.h `CMwin`), as safe slices: `qrs_mw_run` builds it from the C struct, runs
/// one piece and writes the scalars back, so a column resumes across tiles and blocks. A ring an op does not read is
/// empty.
pub struct Mw<'a> {
    pub w: usize, pub cu: usize, pub cap: usize, pub tl: usize, pub t: usize,
    pub isum: u64, pub fsum: f64, pub fsq: f64, pub cnt: i64, pub extbits: u64, pub sent: u64,
    pub ri: &'a mut [u64], pub rf: &'a mut [f64], pub rq: &'a mut [f64], pub rc: &'a mut [i64],
    pub phase: &'a mut [u8], pub sufx: &'a mut [u8],
}

/// An element stored at its own width, as the `B` bytes it occupies. `lt`/`gt` are `MW_LT`/`MW_GT`, and at a float
/// `MW_LT_F`/`MW_GT_F`: q's `&` and `|`, where the null is the smallest thing for `&` and ignored by `|`
/// (`3 mmin 1 0n 3 2 5 4f` is `1 0n 0n 0n 2 2`). `|` and not `||`: the second test is one instruction and the first is
/// a coin toss on real data.
trait Elt: Copy {
    type B: Copy;
    fn from_b(b: Self::B) -> Self;
    fn to_b(self) -> Self::B;
    fn bits(self) -> u64;
    fn from_bits(b: u64) -> Self;
    fn lt(a: Self, b: Self) -> bool;
    fn gt(a: Self, b: Self) -> bool;
}
macro_rules! elt_int { ($($t:ty, $u:ty);*) => { $(impl Elt for $t {
    type B = [u8; size_of::<$t>()];
    #[inline(always)] fn from_b(b: Self::B) -> Self { Self::from_ne_bytes(b) }
    #[inline(always)] fn to_b(self) -> Self::B { self.to_ne_bytes() }
    #[inline(always)] fn bits(self) -> u64 { self as $u as u64 }
    #[inline(always)] fn from_bits(b: u64) -> Self { b as Self }
    #[inline(always)] fn lt(a: Self, b: Self) -> bool { a < b }
    #[inline(always)] fn gt(a: Self, b: Self) -> bool { a > b }
})* } }
elt_int!(u8, u8; i16, u16; i32, u32; i64, u64);
macro_rules! elt_flt { ($t:ty, $u:ty) => { impl Elt for $t {
    type B = [u8; size_of::<$t>()];
    #[inline(always)] fn from_b(b: Self::B) -> Self { Self::from_ne_bytes(b) }
    #[inline(always)] fn to_b(self) -> Self::B { self.to_ne_bytes() }
    #[inline(always)] fn bits(self) -> u64 { self.to_bits() as u64 }
    #[inline(always)] fn from_bits(b: u64) -> Self { Self::from_bits(b as $u) }
    #[inline(always)] fn lt(a: Self, b: Self) -> bool { (a < b) | (a != a) }
    #[inline(always)] fn gt(a: Self, b: Self) -> bool { (a > b) | (b != b) }
} } }
elt_flt!(f32, u32);
elt_flt!(f64, u64);

/// The float layouts a `msum` accumulates and subtracts at: a `real` at 32 bits (measured `last 3 msum
/// "e"$1000#0.1 0.2 0.3` is `0.6000061e`), the history holding it exactly as a `double`.
trait Flt: Elt + core::ops::Add<Output = Self> + core::ops::Sub<Output = Self> + Into<f64> {
    fn of(x: f64) -> Self;
}
impl Flt for f32 { fn of(x: f64) -> Self { x as f32 } }
impl Flt for f64 { fn of(x: f64) -> Self { x } }

/// The integral width `msum` answers at, `sums`'s: `0N` where the 64-bit total does not narrow into it.
trait IntOut {
    type B: Copy;
    const NL: i64;
    fn sx(s: i64) -> i64;
    fn to_b(a: u64) -> Self::B;
}
impl IntOut for i32 {
    type B = [u8; 4];
    const NL: i64 = i32::MIN as i64;
    #[inline(always)] fn sx(s: i64) -> i64 { s as i32 as i64 }
    #[inline(always)] fn to_b(a: u64) -> [u8; 4] { (a as i32).to_ne_bytes() }
}
impl IntOut for i64 {
    type B = [u8; 8];
    const NL: i64 = i64::MIN;
    #[inline(always)] fn sx(s: i64) -> i64 { s }
    #[inline(always)] fn to_b(a: u64) -> [u8; 8] { a.to_ne_bytes() }
}

/// One element kind: the reader (`RD_*`, as the `k` elements from `i`), the null test (`NUL_*`) and the conversion to
/// the double the means accumulate. `msum` is the kind's own method because an integral kind sums at 64 bits and a float
/// at its own width.
trait Kd {
    type E: Elt;
    fn run(p: &[u8], i: usize, k: usize) -> impl Iterator<Item = Self::E> + '_;
    fn nul(e: Self::E) -> bool;
    fn dbl(e: Self::E) -> f64;
    fn msum(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize);
}
/// The integral kinds, whose accumulator is the wrapping 64-bit `+\y`.
trait KInt: Kd { fn int(e: Self::E) -> i64; }
/// A kind stored `$w` bytes an element; `$sum` is its `msum` instance.
macro_rules! kd { ($k:ident, $e:ty, $w:literal, $nul:expr, $dbl:expr, $sum:ident $(, $x:tt)*) => {
    struct $k;
    impl Kd for $k {
        type E = $e;
        #[inline(always)] fn run(p: &[u8], i: usize, k: usize) -> impl Iterator<Item = $e> + '_ {
            p[i * $w..(i + k) * $w].as_chunks::<$w>().0.iter().map(|&b| <$e as Elt>::from_b(b))
        }
        #[inline(always)] fn nul(e: $e) -> bool { let f: fn($e) -> bool = $nul; f(e) }
        #[inline(always)] fn dbl(e: $e) -> f64 { let f: fn($e) -> f64 = $dbl; f(e) }
        fn msum(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) { $sum::<$k $(, $x)*>(st, p, o, n) }
    }
} }
kd!(KU8, u8, 1, |_| false, |e| e as f64, sum_int, i32, 4);
kd!(KC8, u8, 1, |e| e == 0x20, |e| e as f64, sum_int, i32, 4);
kd!(KI16, i16, 2, |e| e == i16::MIN, |e| e as f64, sum_int, i32, 4);
kd!(KI32, i32, 4, |e| e == i32::MIN, |e| e as f64, sum_int, i32, 4);
kd!(KI64, i64, 8, |e| e == i64::MIN, |e| e as f64, sum_int, i64, 8);
kd!(KF32, f32, 4, |e| e != e, |e| e as f64, sum_flt, 4);
kd!(KF64, f64, 8, |e| e != e, |e| e, sum_flt, 8);
/// A boolean is one bit an element, LSB first, so its reader is not a width: it takes the bit at each index.
struct KBit;
impl Kd for KBit {
    type E = u8;
    #[inline(always)] fn run(p: &[u8], i: usize, k: usize) -> impl Iterator<Item = u8> + '_ { (i..i + k).map(|j| (p[j >> 3] >> (j & 7)) & 1) }
    #[inline(always)] fn nul(_: u8) -> bool { false }
    #[inline(always)] fn dbl(e: u8) -> f64 { e as f64 }
    fn msum(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) { sum_int::<KBit, i32, 4>(st, p, o, n) }
}
macro_rules! kints { ($($k:ident),*) => { $(impl KInt for $k { #[inline(always)] fn int(e: Self::E) -> i64 { e as i64 } })* } }
kints!(KBit, KU8, KC8, KI16, KI32, KI64);

/// `MW_HEAD` and `MW_NEXT`: the chunks the two loops of every reducing verb run in. A chunk is the longest run from the
/// cursor `cu` for which the slot the accumulator is written to and the slot `w` back (`rp`) are both contiguous; it
/// is never split and no element is copied. `body(i, k, cu, rp)` runs the accumulator loop then the subtraction loop.
#[inline(always)]
fn chunks(st: &mut Mw, n: usize, mut body: impl FnMut(usize, usize, usize, usize, &mut Mw)) {
    let (w, cap, tl) = (st.w, st.cap, st.tl);
    let mut i = 0;
    while i < n {
        let cu = st.cu;
        let lim = if cu >= w { cap - cu } else { w - cu };
        let k = (n - i).min(lim);
        let rp = if cu >= w { cu - w } else { cu + tl };
        body(i, k, cu, rp, st);
        i += k;
        st.cu = if cu + k == cap { 0 } else { cu + k };
    }
}
/// The first `k` answer slots of `o` from element `i`, `W` bytes each.
#[inline(always)]
fn out<const W: usize>(o: &mut [u8], i: usize, k: usize) -> &mut [[u8; W]] { o[i * W..(i + k) * W].as_chunks_mut::<W>().0 }

/// `+\y` at an integral layout minus the same total `w` back, answered at `O`, `sums`'s type. The total stays exact at
/// 64 bits and each prefix is narrowed as `sums` narrows it; q's `-` then carries a null and wraps at `O`, so the two
/// ends are tested rather than the elements (`2 msum 2147483647 0N 1i` is `0W 0W 0Ni`).
#[inline(always)]
fn sum_int<K: KInt, O: IntOut<B = [u8; OW]>, const OW: usize>(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) {
    let mut acc = st.isum;
    chunks(st, n, |i, k, cu, rp, st| {
        for (h, e) in st.ri[cu..cu + k].iter_mut().zip(K::run(p, i, k)) {
            if !K::nul(e) { acc = acc.wrapping_add(K::int(e) as u64) }
            let s = acc as i64;
            *h = (if s == O::sx(s) { s } else { O::NL }) as u64;
        }
        let (hd, bk) = (&st.ri[cu..cu + k], &st.ri[rp..rp + k]);
        for ((c, &a), &b) in out::<OW>(o, i, k).iter_mut().zip(hd).zip(bk) {
            *c = O::to_b(if a == O::NL as u64 || b == O::NL as u64 { O::NL as u64 } else { a.wrapping_sub(b) });
        }
    });
    st.isum = acc;
}

/// The same at a float layout, where `+\` skips the null rather than wrapping and the subtraction is the plain one,
/// cancellation included.
#[inline(always)]
fn sum_flt<K: Kd, const EW: usize>(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) where K::E: Flt + Elt<B = [u8; EW]> {
    let mut acc = <K::E as Flt>::of(st.fsum);
    chunks(st, n, |i, k, cu, rp, st| {
        for (h, e) in st.rf[cu..cu + k].iter_mut().zip(K::run(p, i, k)) {
            // `acc` is never -0.0 (it starts at +0.0 and a sum is -0.0 only of two -0.0), so adding +0.0 at a null leaves it
            // unchanged and the chain is the add alone, not a compare and a blend on it
            acc = acc + if K::nul(e) { <K::E as Flt>::of(0.0) } else { e };
            *h = acc.into();
        }
        let (hd, bk) = (&st.rf[cu..cu + k], &st.rf[rp..rp + k]);
        for ((c, &a), &b) in out::<EW>(o, i, k).iter_mut().zip(hd).zip(bk) { *c = (<K::E as Flt>::of(a) - <K::E as Flt>::of(b)).to_b() }
    });
    st.fsum = acc.into();
}

/// `mcount:{msum[x;~^y]}` -- the window's non-nulls, at `int`.
#[inline(always)]
fn cnt<K: Kd>(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) {
    let mut acc = st.cnt;
    chunks(st, n, |i, k, cu, rp, st| {
        for (h, e) in st.rc[cu..cu + k].iter_mut().zip(K::run(p, i, k)) {
            acc += !K::nul(e) as i64;
            *h = acc;
        }
        let (hd, bk) = (&st.rc[cu..cu + k], &st.rc[rp..rp + k]);
        for ((c, &a), &b) in out::<4>(o, i, k).iter_mut().zip(hd).zip(bk) { *c = ((a - b) as i32).to_ne_bytes() }
    });
    st.cnt = acc;
}

/// `mavg:{msum[x;0.0^y]%mcount[x;y]}` -- two accumulators over one pass. The null adds `0.0` rather than being skipped
/// (the `0.0^`, which makes a `-0f` total end at `0f`) and is left out of the count (the `~^`).
#[inline(always)]
fn avg<K: Kd>(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) {
    let (mut s, mut c) = (st.fsum, st.cnt);
    chunks(st, n, |i, k, cu, rp, st| {
        for ((hs, hc), e) in st.rf[cu..cu + k].iter_mut().zip(st.rc[cu..cu + k].iter_mut()).zip(K::run(p, i, k)) {
            let live = !K::nul(e);
            s += if live { K::dbl(e) } else { 0.0 };
            c += live as i64;
            (*hs, *hc) = (s, c);
        }
        let (hs, bs, hc, bc) = (&st.rf[cu..cu + k], &st.rf[rp..rp + k], &st.rc[cu..cu + k], &st.rc[rp..rp + k]);
        for (((r, (&a, &b)), &x), &y) in out::<8>(o, i, k).iter_mut().zip(hs.iter().zip(bs)).zip(hc).zip(bc) {
            *r = ((a - b) / (x - y) as f64).to_ne_bytes();
        }
    });
    (st.fsum, st.cnt) = (s, c);
}

/// `mdev:{sqrt mavg[x;y*y]-m*m:mavg[x;y:"f"$y]}` -- the third accumulator joins the other two. The square is taken of
/// the *filled* value. A negative variance and an empty window both reach `sqrt` as q's `0n`. No step is a fused
/// multiply-add: Rust never contracts, which is scan.c's `-ffp-contract=off`.
#[inline(always)]
fn dev<K: Kd>(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) {
    let (mut s, mut q, mut c) = (st.fsum, st.fsq, st.cnt);
    chunks(st, n, |i, k, cu, rp, st| {
        for (((hs, hq), hc), e) in st.rf[cu..cu + k].iter_mut().zip(st.rq[cu..cu + k].iter_mut()).zip(st.rc[cu..cu + k].iter_mut()).zip(K::run(p, i, k)) {
            let live = !K::nul(e);
            let x = if live { K::dbl(e) } else { 0.0 };
            s += x; q += x * x; c += live as i64;
            (*hs, *hq, *hc) = (s, q, c);
        }
        let (hs, bs, hq, bq) = (&st.rf[cu..cu + k], &st.rf[rp..rp + k], &st.rq[cu..cu + k], &st.rq[rp..rp + k]);
        let (hc, bc) = (&st.rc[cu..cu + k], &st.rc[rp..rp + k]);
        for (g, r) in out::<8>(o, i, k).iter_mut().enumerate() {
            let dc = (hc[g] - bc[g]) as f64;
            let m = (hs[g] - bs[g]) / dc;
            let v = simd::sqrt64((hq[g] - bq[g]) / dc - m * m);
            *r = (if v != v { SC_NAN64 } else { v.to_bits() }).to_ne_bytes();
        }
    });
    (st.fsum, st.fsq, st.cnt) = (s, q, c);
}

/// van Herk's two-level pass: inside a phase of `w` keep the running extreme `ex` of its prefix, between phases keep
/// `sufx`, the previous phase's suffix extremes; the window ending at offset `t` is `min(sufx[t+1], ex)`, two loads,
/// two compares and a store an element with no branch on the data. The inner loop runs to the end of the phase or the
/// piece; the suffix pass that closes a phase touches `w` elements once every `w`.
#[inline(always)]
fn ext<K: Kd, const MIN: bool, const EW: usize>(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) where K::E: Elt<B = [u8; EW]> {
    let better = |a: K::E, b: K::E| if MIN { <K::E as Elt>::lt(a, b) } else { <K::E as Elt>::gt(a, b) };
    let w = st.w;
    let (sent, mut ex, mut t) = (<K::E as Elt>::from_bits(st.sent), <K::E as Elt>::from_bits(st.extbits), st.t);
    let (ph, sf) = (&mut *st.phase, &mut *st.sufx);
    let mut i = 0;
    while i < n {
        let k = (w - t).min(n - i);
        let it = out::<EW>(ph, t, k).iter_mut().zip(sf[(t + 1) * EW..(t + 1 + k) * EW].as_chunks::<EW>().0).zip(out::<EW>(o, i, k)).zip(K::run(p, i, k));
        for (((pc, sc), oc), v) in it {
            let r = <K::E as Elt>::from_b(*sc);
            ex = if better(v, ex) { v } else { ex };
            *pc = v.to_b();
            *oc = (if better(ex, r) { ex } else { r }).to_b();
        }
        t += k; i += k;
        if t == w {
            let mut a = sent;
            for (pc, sc) in ph.as_chunks_mut::<EW>().0.iter().zip(sf.as_chunks_mut::<EW>().0.iter_mut()).rev() {
                let b = <K::E as Elt>::from_b(*pc);
                a = if better(a, b) { a } else { b };
                *sc = a.to_b();
            }
            t = 0; ex = sent;
        }
    }
    st.t = t;
    st.extbits = ex.bits();
}

/// `MW_OPS`: one expansion per element layout with the op switch outside the loop; `EW` is the element's width.
#[inline(always)]
fn ops<K: Kd, const EW: usize>(st: &mut Mw, op: i32, p: &[u8], o: &mut [u8], n: usize) where K::E: Elt<B = [u8; EW]> {
    match op {
        MW_MSUM => K::msum(st, p, o, n),
        MW_MCOUNT => cnt::<K>(st, p, o, n),
        MW_MAVG => avg::<K>(st, p, o, n),
        MW_MDEV => dev::<K>(st, p, o, n),
        MW_MMIN => ext::<K, true, EW>(st, p, o, n),
        _ => ext::<K, false, EW>(st, p, o, n),
    }
}

/// scan.c `mw_run`: the window verb `op` over `n` elements of `p` at `kind`, resuming where `st` stopped. A boolean
/// reads one bit an element, so `p` must be the whole bitmap from element 0 of the piece.
pub fn mw_run(st: &mut Mw, op: i32, kind: i32, p: &[u8], o: &mut [u8], n: usize) {
    if op >= MW_OPS_N {
        // C exits 1 after this text; no_std has no exit, so the panic handler prints it and aborts
        panic!("qlean_mwin: verb {op} is not one of the {MW_OPS_N} in QLean/Kernel/Scan.lean")
    }
    match u8::try_from(kind).unwrap_or(u8::MAX) {
        SK_BIT => ops::<KBit, 1>(st, op, p, o, n),
        SK_U8 => ops::<KU8, 1>(st, op, p, o, n),
        SK_C8 => ops::<KC8, 1>(st, op, p, o, n),
        SK_I16 => ops::<KI16, 2>(st, op, p, o, n),
        SK_I32 => ops::<KI32, 4>(st, op, p, o, n),
        SK_I64 => ops::<KI64, 8>(st, op, p, o, n),
        SK_F32 => ops::<KF32, 4>(st, op, p, o, n),
        SK_F64 => ops::<KF64, 8>(st, op, p, o, n),
        _ => sc_bad_kind(kind),
    }
}
/// The bytes of `p` that hold `n` elements at `kind`: packed bits for the boolean, `dense_width` each otherwise.
pub fn mw_in_bytes(kind: i32, n: usize) -> usize {
    if kind == SK_BIT as i32 { n.div_ceil(8) } else { n * dense_width(kind) }
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
    #[test]
    fn bits_run_is_the_bitwise_prefix_or_and_and() {
        // set bit 13 and 70: maxs is zero below 13, one from 13; mins (inv = !0) is one until the first clear bit
        let nb = 11;
        let mut p = [0u8; 11];
        p[1] |= 1 << 5;
        p[8] |= 1 << 6;
        let (mut o, mut want) = ([0xAAu8; 11], [0u8; 11]);
        bits_run(&mut o, &p, 0);
        (13..nb * 8).for_each(|i| want[i / 8] |= 1 << (i % 8));
        assert_eq!(o, want);
        let q = p.map(|b| !b);
        bits_run(&mut o, &q, !0);
        want = [0xff; 11];
        (13..nb * 8).for_each(|i| want[i / 8] &= !(1 << (i % 8)));
        assert_eq!(o, want);
        bits_run(&mut [], &[], 0);
    }
    #[test]
    fn ema_nan_coefficient_gives_the_positive_nan_at_every_element() {
        let y: Vec<u8> = [1.0f64, 2.0, 3.0].iter().flat_map(|x| x.to_ne_bytes()).collect();
        let mut o = [0u8; 24];
        ema(f64::NAN.to_bits() | 1 << 63, &y, &mut o);
        assert!(o.chunks(8).all(|c| u64::from_ne_bytes(c.try_into().unwrap()) >> 63 == 0 && c[7] == 0x7f));
        ema(0.5f64.to_bits(), &y, &mut o);
        assert_eq!(f64s(&o).collect::<Vec<_>>(), [1.0, 1.5, 2.25]);
        ema_v(&y, &y, 2.0f64.to_bits(), &mut o);
        assert_eq!(f64s(&o).collect::<Vec<_>>(), [3.0, 8.0, 27.0]);
    }
    #[test]
    fn window_seeds_and_sentinels() {
        assert_eq!(mw_seed(MW_MMAX, SK_I64 as i32), (-i64::MAX) as u64);
        assert_eq!(mw_sent(MW_MMAX, SK_I64 as i32), i64::MIN as u64);
        assert_eq!(mw_sent(MW_MMAX, SK_F64 as i32), SC_NAN64);
        assert_eq!(mw_seed(MW_MMIN, SK_F32 as i32), 0x7f80_0000);
        assert_eq!(mw_sent(MW_MMIN, SK_BIT as i32), 1);
        let d = mw_dims(MW_MMIN, SK_I16 as i32, 5000, 10);
        assert_eq!((d.w, d.tl, d.cap, d.ew), (11, MW_TILE, 11 + MW_TILE, 2));
        let mut sufx = [0u8; 8];
        assert_eq!(mw_prime(&mut sufx, MW_MMAX, SK_I16 as i32, 2), i16::MIN as u16 as u64);
        assert_eq!(sufx, [1, 0x80, 1, 0x80, 1, 0x80, 0x00, 0x80]);
    }

    /// the window engine over one piece, rings and phases sized as `qrs_mw_open` sizes them
    fn mw(op: i32, kind: i32, w: usize, p: &[u8], n: usize) -> Vec<u8> {
        let d = mw_dims(op, kind, w, n);
        let (mut ri, mut rf, mut rq, mut rc) = (alloc::vec![0u64; d.cap], alloc::vec![0f64; d.cap], alloc::vec![0f64; d.cap], alloc::vec![0i64; d.cap]);
        let (mut phase, mut sufx) = (alloc::vec![0u8; d.w * d.ew], alloc::vec![0u8; (d.w + 1) * d.ew]);
        let sent = mw_prime(&mut sufx, op, kind, d.ew);
        let mut st = Mw { w: d.w, cu: 0, cap: d.cap, tl: d.tl, t: 0, isum: 0, fsum: 0.0, fsq: 0.0, cnt: 0, extbits: sent, sent,
                          ri: &mut ri, rf: &mut rf, rq: &mut rq, rc: &mut rc, phase: &mut phase, sufx: &mut sufx };
        let mut o = alloc::vec![0u8; n * mw_out_width(op, kind)];
        mw_run(&mut st, op, kind, p, &mut o, n);
        o
    }
    fn f64b(v: &[f64]) -> Vec<u8> { v.iter().flat_map(|x| x.to_ne_bytes()).collect() }
    fn f64o(o: &[u8]) -> Vec<f64> { o.chunks(8).map(|c| f64::from_ne_bytes(c.try_into().unwrap())).collect() }
    fn i32b(v: &[i32]) -> Vec<u8> { v.iter().flat_map(|x| x.to_ne_bytes()).collect() }
    const FN: f64 = f64::NAN;
    #[test]
    fn mmin_and_mmax_of_a_float_null_follow_qs_and_and_or() {
        let p = f64b(&[1.0, FN, 3.0, 2.0, 5.0, 4.0]);
        let mn = f64o(&mw(MW_MMIN, SK_F64 as i32, 3, &p, 6));
        assert_eq!([mn[0], mn[4], mn[5]], [1.0, 2.0, 2.0]);
        assert!(mn[1].is_nan() && mn[2].is_nan() && mn[3].is_nan());
        assert_eq!(f64o(&mw(MW_MMAX, SK_F64 as i32, 3, &p, 6)), [1.0, 1.0, 3.0, 3.0, 5.0, 5.0]);
    }
    #[test]
    fn msum_of_an_int_column_narrows_to_null_and_a_null_end_stays_null() {
        let o = mw(MW_MSUM, SK_I32 as i32, 3, &i32b(&[2_000_000_000, 2_000_000_000, -2_000_000_000]), 3);
        assert_eq!(i32s(&o), [2_000_000_000, i32::MIN, 2_000_000_000]);
        assert_eq!(i32s(&mw(MW_MSUM, SK_I32 as i32, 2, &i32b(&[i32::MAX, i32::MIN, 1]), 3)), [i32::MAX, i32::MAX, i32::MIN]);
    }
    #[test]
    fn mavg_and_mcount_skip_nulls_and_a_window_wider_than_the_column_is_short() {
        let p = f64b(&[1.0, FN, 3.0]);
        assert_eq!(f64o(&mw(MW_MAVG, SK_F64 as i32, 9, &p, 3)), [1.0, 1.0, 2.0]);
        assert_eq!(i32s(&mw(MW_MCOUNT, SK_F64 as i32, 2, &p, 3)), [1, 1, 1]);
        assert_eq!(f64o(&mw(MW_MDEV, SK_F64 as i32, 9, &f64b(&[1.0, 3.0]), 2)), [0.0, 1.0]);
    }
    #[test]
    #[should_panic(expected = "verb 6")]
    fn a_verb_past_the_last_is_refused() { mw(6, SK_I64 as i32, 1, &[], 0); }
}
