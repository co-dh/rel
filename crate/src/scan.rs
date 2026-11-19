#![forbid(unsafe_code)]
//! Column (a), scan.rs (A14): the running scans (sums, prds, mins, maxs, fills) over a dense payload and
//! the block skips over an encoded one. `scan_fill` and `scan_any_null` are AVX-512 in C: their vector bodies are in
//! `simd.rs`, which this module calls and finishes (the groups that hold a null, the tail).
use crate::key::{SK_BIT, SK_C8, SK_I8, SK_F32, SK_F64, SK_I16, SK_I32, SK_I64, SK_KINDS_N, SK_U8};
use crate::simd;
use crate::pod::{self, Elt};
use crate::blocks::{Blocks, Grid, Src};
use crate::coc::Coc;
use crate::ffi::{Form, Sink};
use crate::ids;
use crate::lean::{B, O};
use alloc::{format, string::String, vec::Vec};

// the verb, as QLean/Kernel/Scan.lean's `Verb` in constructor order
pub const SC_SUMS: i32 = 0;
pub const SC_PRDS: i32 = 1;
pub const SC_MINS: i32 = 2;
pub const SC_FILLS: i32 = 4;
pub const SC_VERBS_N: i32 = 5;
/// q's `0n` and `0Ne`: a result NaN is written as these patterns, whatever the FPU left behind
pub const SC_NAN64: u64 = 0xfff8_0000_0000_0000;
pub const SC_NAN32: u32 = 0xffc0_0000;
/// scan.rs `SCAN_CHUNK`: elements whose "did any beat the accumulator" test is one or-reduction
pub const SCAN_CHUNK: usize = 64;

/// The accumulator of a scan, held in the 8-byte `carry` between pieces. Integers accumulate at 64 bits and wrap, as q
/// does (`sums 9223372036854775807 1 1` is `0W 0N -0W`); no step is a fused multiply-add.
pub trait Acc: Copy + PartialOrd {
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
pub fn rd_bit(p: &[u8], i: usize) -> i64 { ((p[i >> 3] >> (i & 7)) & 1) as i64 }
pub fn rd_u8(p: &[u8], i: usize) -> i64 { p[i] as i64 }
pub fn rd_i8(p: &[u8], i: usize) -> i64 { p[i] as i8 as i64 }
pub fn rd_i16(p: &[u8], i: usize) -> i64 { i16::from_ne_bytes(p[2 * i..2 * i + 2].try_into().unwrap()) as i64 }
pub fn rd_i32(p: &[u8], i: usize) -> i64 { i32::from_ne_bytes(p[4 * i..4 * i + 4].try_into().unwrap()) as i64 }
pub fn rd_i64(p: &[u8], i: usize) -> i64 { i64::from_ne_bytes(p[8 * i..8 * i + 8].try_into().unwrap()) }
pub fn rd_f32(p: &[u8], i: usize) -> f32 { f32::from_ne_bytes(p[4 * i..4 * i + 4].try_into().unwrap()) }
pub fn rd_f64(p: &[u8], i: usize) -> f64 { f64::from_ne_bytes(p[8 * i..8 * i + 8].try_into().unwrap()) }

// ---- null tests: `0N` is the minimum of each signed width, byte and boolean have none, `char`'s is the blank ----
pub fn nul_no(_: i64) -> bool { false }
pub fn nul_chr(v: i64) -> bool { v == 0x20 }
pub fn nul_i8(v: i64) -> bool { v == i8::MIN as i64 }
pub fn nul_i16(v: i64) -> bool { v == i16::MIN as i64 }
pub fn nul_i32(v: i64) -> bool { v == i32::MIN as i64 }
pub fn nul_i64(v: i64) -> bool { v == i64::MIN }
pub fn nul_f32(v: f32) -> bool { v != v }
pub fn nul_f64(v: f64) -> bool { v != v }

// ---- writers: an element's bytes. Truncating (the wrap of rules 3 and 4); `ws_i32` the narrowing `sums` answering
// `0N` on overflow ----
pub fn wr_i8(a: i64) -> [u8; 1] { (a as u8).to_ne_bytes() }
pub fn wr_i16(a: i64) -> [u8; 2] { (a as i16).to_ne_bytes() }
pub fn wr_i32(a: i64) -> [u8; 4] { (a as i32).to_ne_bytes() }
pub fn wr_i64(a: i64) -> [u8; 8] { a.to_ne_bytes() }
pub fn ws_i32(a: i64) -> [u8; 4] { wr_i32(if a == a as i32 as i64 { a } else { i32::MIN as i64 }) }
/// a NaN accumulator is written as q's own null pattern; `sums 0w -0w` is `0w 0n`, so the case is reachable
pub fn wr_f32(a: f32) -> [u8; 4] { (if a != a { SC_NAN32 } else { a.to_bits() }).to_ne_bytes() }
pub fn wr_f64(a: f64) -> [u8; 8] { (if a != a { SC_NAN64 } else { a.to_bits() }).to_ne_bytes() }

/// The first `n` elements of `p` at `R` bytes each, decoded by `f`. A chunk iterator rather than an index, so the loop
/// has no bounds check; slicing to `n * R` panics on a payload that holds fewer.
#[inline(always)]
pub fn elts<'a, const R: usize, A>(p: &'a [u8], n: usize, f: impl Fn([u8; R]) -> A + Copy + 'a) -> impl Iterator<Item = A> + Clone + 'a {
    p[..n * R].chunks_exact(R).map(move |c| f(c.try_into().unwrap()))
}
/// The first `n` answer slots of `out` at `W` bytes each.
#[inline(always)]
pub fn slots<const W: usize>(out: &mut [u8], n: usize) -> core::slice::ChunksExactMut<'_, u8> {
    assert!(out.len() >= n * W, "scan: an answer of {} bytes holds fewer than {n} elements of {W} bytes", out.len());
    out[..n * W].chunks_exact_mut(W)
}

/// `SCAN_LOOP`: read, fold the step in where the element is not null, emit the accumulator. `carry` is the accumulator
/// a caller scanning in pieces keeps between them (empty = none), `resume` says whether this piece continues one.
#[inline(always)]
pub fn lp<A: Acc, const W: usize>(out: &mut [u8], n: usize, carry: &mut [u8], resume: bool, seed: A,
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
pub fn mono<A: Acc, const W: usize>(out: &mut [u8], n: usize, carry: &mut [u8], resume: bool, seed: A,
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
pub fn verbs<A: Acc, const WE: usize, const WW: usize>(
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

/// scan.rs `sc_bad_kind`: the abort for a kind the Lean dispatch never sends.
pub fn sc_bad_kind(kind: i32) -> ! {
    // C exits 1 after this text; no_std has no exit, so the panic handler prints it and aborts
    panic!("qlean_scan: element kind {kind} is not one of the {SK_KINDS_N} in QLean/Kernel/Scan.lean")
}
/// coc.rs `sk_dense_width`: an element's bytes in a dense payload; the boolean has none, its payload is packed bits.
pub fn dense_width(kind: i32) -> usize {
    match u8::try_from(kind).unwrap_or(u8::MAX) {
        SK_U8 | SK_C8 | SK_I8 => 1,
        SK_I16 => 2,
        SK_I32 | SK_F32 => 4,
        SK_I64 | SK_F64 => 8,
        _ => panic!("qlean: element kind {kind} has no dense width -- either it is not one of the {SK_KINDS_N} in QLean/Kernel/Scan.lean, or it is the boolean, whose payload is packed bits"),
    }
}

/// `fills` at one kind: a stretch with no null is a copy, and the accumulator is only what bridges a null. `simd`
/// copies the leading 64-byte groups that hold none; a group that holds one, and the tail, go element by element.
#[inline(always)]
pub fn fill<A: Acc, const W: usize>(kind: i32, p: &[u8], out: &mut [u8], n: usize, carry: &mut [u8], resume: bool, seed: A,
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

/// scan.rs `scan_fill`: `fills` over `n` elements of `p` into `out`; `carry` (one element) is the last non-null
/// seen, read when `resume`. `fills` seeds with the null, and at the two kinds that have none the seed is unreachable.
pub fn scan_fill(kind: i32, p: &[u8], out: &mut [u8], n: usize, carry: &mut [u8], resume: bool) {
    match u8::try_from(kind).unwrap_or(u8::MAX) {
        // the one kind that stays on the loop: a bit read, a byte written, so a group is not a group of its bytes
        SK_BIT => lp(out, n, carry, resume, 0i64, (0..n).map(|i| rd_bit(p, i)), nul_no, |_, v| v, wr_i8),
        SK_U8 => fill(kind, p, out, n, carry, resume, 0i64, rd_u8, nul_no, wr_i8),
        SK_I8 => fill(kind, p, out, n, carry, resume, i8::MIN as i64, rd_i8, nul_i8, wr_i8),
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

/// scan.rs `scan_any_null`: whether the payload holds a null in its first `n` elements. `fills` over one that does
/// not is the identity, so the answer can be the argument itself.
pub fn scan_any_null(kind: i32, p: &[u8], n: usize) -> bool {
    let k = u8::try_from(kind).unwrap_or(u8::MAX);
    if matches!(k, SK_BIT | SK_U8) { return false } // neither layout has a null
    if !matches!(k, SK_I8 | SK_I16 | SK_I32 | SK_I64 | SK_F32 | SK_F64 | SK_C8) { sc_bad_kind(kind) }
    let (hit, i) = simd::any_null(kind, p, n);
    hit || (i..n).any(|j| match k {
        SK_I8 => nul_i8(rd_i8(p, j)),
        SK_I16 => nul_i16(rd_i16(p, j)),
        SK_I32 => nul_i32(rd_i32(p, j)),
        SK_I64 => nul_i64(rd_i64(p, j)),
        SK_F32 => nul_f32(rd_f32(p, j)),
        SK_F64 => nul_f64(rd_f64(p, j)),
        _ => nul_chr(rd_u8(p, j)),
    })
}

/// scan.rs `scan_run`: scan `op` over `n` elements, `carry` the running accumulator.
pub fn scan_run(op: i32, kind: i32, p: &[u8], out: &mut [u8], n: usize, carry: &mut [u8], resume: bool) {
    if op >= SC_VERBS_N { panic!("qlean_scan: verb {op} is not one of the {SC_VERBS_N} in QLean/Kernel/Scan.lean") }
    if op == SC_FILLS { return scan_fill(kind, p, out, n, carry, resume) }
    match u8::try_from(kind).unwrap_or(u8::MAX) {
        SK_BIT => verbs(op, out, n, carry, resume, 1i64, 0, (0..n).map(|i| rd_bit(p, i)), nul_no, wr_i8, wr_i32, ws_i32),
        SK_U8 => verbs(op, out, n, carry, resume, 0xffi64, 0, elts(p, n, |b: [u8; 1]| b[0] as i64), nul_no, wr_i8, wr_i32, ws_i32),
        SK_I8 => verbs(op, out, n, carry, resume, i8::MAX as i64, -(i8::MAX as i64), elts(p, n, |b: [u8; 1]| b[0] as i8 as i64), nul_i8,
                       wr_i8, wr_i32, ws_i32),
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

/// scan.rs `sc_out_width`: `sums` and `prds` answer at the aggregate's accumulator type (everything below `int`
/// widens to `int`), the other three at the element's own width; a boolean answers one byte per element.
pub fn sc_out_width(op: i32, kind: i32) -> usize {
    if op == SC_SUMS || op == SC_PRDS { return if kind == SK_I64 as i32 || kind == SK_F64 as i32 { 8 } else { 4 } }
    if kind == SK_BIT as i32 { 1 } else { dense_width(kind) }
}




// ---- K3 (scan.rs `sc_bits_run`, `ema_*`, `mw_sent`, `mw_seed`, `mw_open`, `mw_close`) ----







// ---- the moving-window engine: scan.rs `mw_run` and its window macros (K4) ----


macro_rules! elt_int { ($($t:ty, $u:ty, $reg:ident, $lane:ident, $stv:ident, $mn:ident, $mx:ident);*) => { $(impl Reg for $t {
    type Acc = simd::VReg;
    #[inline(always)] fn reg(self) -> simd::VReg { simd::$reg(self) }
    #[inline(always)] fn lane(a: simd::VReg) -> Self { simd::$lane(a) }
    #[inline(always)] fn stv(a: simd::VReg, d: &mut Self::B) { simd::$stv(a, d) }
    #[inline(always)] fn best<const MIN: bool, const BR: bool>(v: simd::VReg, ex: simd::VReg) -> simd::VReg { if MIN { simd::$mn(v, ex) } else { simd::$mx(v, ex) } }
    type B = [u8; size_of::<$t>()];
    #[inline(always)] fn from_b(b: Self::B) -> Self { Self::from_ne_bytes(b) }
    #[inline(always)] fn to_b(self) -> Self::B { self.to_ne_bytes() }
})* } }
elt_int!(u8, u8, reg_u8, lane_u8, st_u8, min_u8, max_u8; i16, u16, reg_i16, lane_i16, st_i16, min_i16, max_i16;
         i32, u32, reg_i32, lane_i32, st_i32, min_i32, max_i32; i64, u64, reg_i64, lane_i64, st_i64, min_i64, max_i64);
macro_rules! elt_flt { ($t:ty, $u:ty, $mn:ident, $mx:ident) => { impl Reg for $t {
    type Acc = $t;
    #[inline(always)] fn reg(self) -> $t { self }
    #[inline(always)] fn lane(a: $t) -> Self { a }
    #[inline(always)] fn stv(a: $t, d: &mut Self::B) { *d = a.to_ne_bytes() }
    #[inline(always)] fn best<const MIN: bool, const BR: bool>(v: $t, ex: $t) -> $t {
        match (MIN, BR) {
            (true, true) => simd::$mn(v, ex),
            (false, true) => simd::$mx(v, ex),
            (true, false) => if (v < ex) | (v != v) { v } else { ex },
            (false, false) => if (v > ex) | (ex != ex) { v } else { ex },
        }
    }
    type B = [u8; size_of::<$t>()];
    #[inline(always)] fn from_b(b: Self::B) -> Self { Self::from_ne_bytes(b) }
    #[inline(always)] fn to_b(self) -> Self::B { self.to_ne_bytes() }
} } }
elt_flt!(f32, u32, min_f32, max_f32);
elt_flt!(f64, u64, min_f64, max_f64);



/// A kind stored `$w` bytes an element; `$sum` is its `msum` instance.
macro_rules! kd { ($k:ident, $e:ty, $w:literal, $nul:expr, $dbl:expr, $nn:literal, $nv:expr, $raw:expr, $sum:ident $(, $x:tt)*) => {
    pub struct $k;
    impl Kd for $k {
        type E = $e;
        #[inline(always)] fn run(p: &[u8], i: usize, k: usize) -> impl Iterator<Item = $e> + '_ {
            p[i * $w..(i + k) * $w].as_chunks::<$w>().0.iter().map(|&b| <$e as Reg>::from_b(b))
        }
        #[inline(always)] fn nul(e: $e) -> bool { let f: fn($e) -> bool = $nul; f(e) }
        #[inline(always)] fn dbl(e: $e) -> f64 { let f: fn($e) -> f64 = $dbl; f(e) }
        const NAN_NULL: bool = $nn;
        const NULV: i64 = $nv;
        #[inline(always)] fn raw(e: $e) -> i64 { let f: fn($e) -> i64 = $raw; f(e) }
        fn msum(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) { $sum::<$k $(, $x)*>(st, p, o, n) }
    }
} }
kd!(KU8, u8, 1, |_| false, |e| e as f64, false, -1, |e| e as i64, sum_int, i32, 4);
kd!(KC8, u8, 1, |e| e == 0x20, |e| e as f64, false, 0x20, |e| e as i64, sum_int, i32, 4);
kd!(KI16, i16, 2, |e| e == i16::MIN, |e| e as f64, false, i16::MIN as i64, |e| e as i64, sum_int, i32, 4);
kd!(KI32, i32, 4, |e| e == i32::MIN, |e| e as f64, false, i32::MIN as i64, |e| e as i64, sum_int, i32, 4);
kd!(KI64, i64, 8, |e| e == i64::MIN, |e| e as f64, false, i64::MIN, |e| e, sum_int, i64, 8);
kd!(KF32, f32, 4, |e| e != e, |e| e as f64, true, 0, |_| 0, sum_flt, 4);
kd!(KF64, f64, 8, |e| e != e, |e| e, true, 0, |_| 0, sum_flt, 8);
macro_rules! kints { ($($k:ident),*) => { $(impl KInt for $k { #[inline(always)] fn int(e: Self::E) -> i64 { e as i64 } })* } }
kints!(KBit, KU8, KC8, KI16, KI32, KI64);










// ---- B7/B8: the column entry points of scan.rs's twelve Lean exports (ffi/scan.rs), over the payloads' bytes ----

/// coc.rs `sk_avail`: how many elements `bytes` hold (the boolean's payload is packed bits).
pub fn avail(kind: i32, bytes: usize) -> usize { if kind == SK_BIT as i32 { bytes * 8 } else { bytes / dense_width(kind) } }
/// `n` clamped to what a payload of `bytes` holds: getting `n` wrong would otherwise read past it.
pub fn clamp(kind: i32, n: usize, bytes: usize) -> usize { n.min(avail(kind, bytes)) }

/// `qlean_scan`: the bytes of the answer, `n` (clamped) elements at `sc_out_width`.
pub fn col_len(op: u8, kind: u8, n: usize, bytes: usize) -> usize { clamp(kind as i32, n, bytes) * sc_out_width(op as i32, kind as i32) }
/// `qlean_scan`: `fills` over a payload with no null in its first `n` elements is the argument itself, where the answer's
/// bytes are the argument's -- not at `bit`, whose `fills` writes a byte an element, and not where `n` was clamped.
pub fn col_same(op: u8, kind: u8, n: usize, a: &[u8]) -> bool {
    op as i32 == SC_FILLS && kind != SK_BIT && col_len(op, kind, n, a.len()) == a.len()
        && !scan_any_null(kind as i32, a, clamp(kind as i32, n, a.len()))
}
/// `qlean_scan`: the scan into `out` (`col_len` bytes).
pub fn col(op: u8, kind: u8, n: usize, a: &[u8], out: &mut [u8]) {
    scan_run(op as i32, kind as i32, a, out, clamp(kind as i32, n, a.len()), &mut [], false)
}








/// An element stored at its own width, as the `B` bytes it occupies. `lt`/`gt` are `MW_LT`/`MW_GT`, and at a float
/// `MW_LT_F`/`MW_GT_F`: q's `&` and `|`, where the null is the smallest thing for `&` and ignored by `|`
/// (`3 mmin 1 0n 3 2 5 4f` is `1 0n 0n 0n 2 2`). `|` and not `||`: the second test is one instruction and the first is
/// a coin toss on real data.
pub trait Reg: Elt {
    type B: Copy;
    fn from_b(b: Self::B) -> Self;
    fn to_b(self) -> Self::B;
    /// The register the carried extreme lives in, and `better(v, ex) ? v : ex`, the carried select of `MW_EXT`, on it.
    type Acc: Copy;
    fn reg(self) -> Self::Acc;
    fn lane(a: Self::Acc) -> Self;
    fn stv(a: Self::Acc, d: &mut Self::B);
    /// `BR` picks a float's branch over its select, the choice of `ext`; an integral kind has the one form.
    fn best<const MIN: bool, const BR: bool>(v: Self::Acc, ex: Self::Acc) -> Self::Acc;
}
/// A boolean is one bit an element, LSB first, so its reader is not a width: it takes the bit at each index.
pub struct KBit;
impl Kd for KBit {
    type E = u8;
    #[inline(always)] fn run(p: &[u8], i: usize, k: usize) -> impl Iterator<Item = u8> + '_ { (i..i + k).map(|j| (p[j >> 3] >> (j & 7)) & 1) }
    #[inline(always)] fn nul(_: u8) -> bool { false }
    #[inline(always)] fn dbl(e: u8) -> f64 { e as f64 }
    const NAN_NULL: bool = false;
    const NULV: i64 = -1;
    #[inline(always)] fn raw(e: u8) -> i64 { e as i64 }
    fn msum(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) { sum_int::<KBit, i32, 4>(st, p, o, n) }
}
/// One element kind: the reader (`RD_*`, as the `k` elements from `i`), the null test (`NUL_*`) and the conversion to
/// the double the means accumulate. `msum` is the kind's own method because an integral kind sums at 64 bits and a float
/// at its own width.
pub trait Kd {
    type E: Reg;
    fn run(p: &[u8], i: usize, k: usize) -> impl Iterator<Item = Self::E> + '_;
    fn nul(e: Self::E) -> bool;
    fn dbl(e: Self::E) -> f64;
    /// The null as `fill` tests it: a NaN (`NULV` is then unused), or the element sign-extended equal to `NULV`.
    const NAN_NULL: bool;
    const NULV: i64;
    fn raw(e: Self::E) -> i64;
    /// `(live ? dbl : 0.0, live as i64)`: the filled value the means add and the count they keep, each a branch on the
    /// null (`simd::fill_*`).
    #[inline(always)] fn fill(e: Self::E) -> (f64, i64) {
        if Self::NAN_NULL { simd::fill_nan(Self::dbl(e)) } else { simd::fill_int(Self::raw(e), Self::NULV) }
    }
    fn msum(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize);
}
/// The integral kinds, whose accumulator is the wrapping 64-bit `+\y`.
pub trait KInt: Kd { fn int(e: Self::E) -> i64; }
/// The engine state of scan.rs's `mwin` (rs.h `CMwin`), as safe slices: `qrs_mw_run` builds it from the C struct, runs
/// one piece and writes the scalars back, so a column resumes across tiles and blocks. A ring an op does not read is
/// empty.
pub struct Mw<'a> {
    pub w: usize, pub cu: usize, pub cap: usize, pub tl: usize, pub t: usize,
    pub isum: u64, pub fsum: f64, pub fsq: f64, pub cnt: i64, pub extbits: u64, pub sent: u64,
    pub ri: &'a mut [u64], pub rf: &'a mut [f64], pub rq: &'a mut [f64], pub rc: &'a mut [i64],
    pub phase: &'a mut [u8], pub sufx: &'a mut [u8],
}
/// The same at a float layout, where `+\` skips the null rather than wrapping and the subtraction is the plain one,
/// cancellation included.
#[inline(always)]
pub fn sum_flt<K: Kd, const EW: usize>(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) where K::E: Reg<B = [u8; EW]> + core::ops::Add<Output = K::E> + core::ops::Sub<Output = K::E> {
    let mut acc = <K::E as Elt>::of_f(st.fsum);
    chunks(st, n, |i, k, cu, rp, st| {
        for (h, e) in st.rf[cu..cu + k].iter_mut().zip(K::run(p, i, k)) {
            // `acc` is never -0.0 (it starts at +0.0 and a sum is -0.0 only of two -0.0), so adding +0.0 at a null leaves it
            // unchanged and the chain is the add alone, not a compare and a blend on it
            acc = acc + if K::nul(e) { <K::E as Elt>::of_f(0.0) } else { e };
            *h = acc.f();
        }
        let (hd, bk) = (&st.rf[cu..cu + k], &st.rf[rp..rp + k]);
        for ((c, &a), &b) in out::<EW>(o, i, k).iter_mut().zip(hd).zip(bk) { *c = (<K::E as Elt>::of_f(a) - <K::E as Elt>::of_f(b)).to_b() }
    });
    st.fsum = acc.f();
}
/// `+\y` at an integral layout minus the same total `w` back, answered at `O`, `sums`'s type. The total stays exact at
/// 64 bits and each prefix is narrowed as `sums` narrows it; q's `-` then carries a null and wraps at `O`, so the two
/// ends are tested rather than the elements (`2 msum 2147483647 0N 1i` is `0W 0W 0Ni`).
#[inline(always)]
pub fn sum_int<K: KInt, O: Reg<B = [u8; OW]>, const OW: usize>(st: &mut Mw, p: &[u8], o: &mut [u8], n: usize) {
    // a history slot holds the prefix sign-extended (`i`), so its null is too: `O::LO.bits()` is zero-extended and
    // equals it only at 64 bits
    let (mut acc, nul) = (st.isum, O::LO.i() as u64);
    chunks(st, n, |i, k, cu, rp, st| {
        for (h, e) in st.ri[cu..cu + k].iter_mut().zip(K::run(p, i, k)) {
            if !K::nul(e) { acc = acc.wrapping_add(K::int(e) as u64) }
            let s = acc as i64;
            *h = if s == O::wrap(s as u64).i() { s as u64 } else { nul };
        }
        let (hd, bk) = (&st.ri[cu..cu + k], &st.ri[rp..rp + k]);
        for ((c, &a), &b) in out::<OW>(o, i, k).iter_mut().zip(hd).zip(bk) {
            *c = O::wrap(if a == nul || b == nul { nul } else { a.wrapping_sub(b) }).to_b();
        }
    });
    st.isum = acc;
}
/// `MW_HEAD` and `MW_NEXT`: the chunks the two loops of every reducing verb run in. A chunk is the longest run from the
/// cursor `cu` for which the slot the accumulator is written to and the slot `w` back (`rp`) are both contiguous; it
/// is never split and no element is copied. `body(i, k, cu, rp)` runs the accumulator loop then the subtraction loop.
#[inline(always)]
pub fn chunks(st: &mut Mw, n: usize, mut body: impl FnMut(usize, usize, usize, usize, &mut Mw)) {
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
pub fn out<const W: usize>(o: &mut [u8], i: usize, k: usize) -> &mut [[u8; W]] { o[i * W..(i + k) * W].as_chunks_mut::<W>().0 }

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{vec, vec::Vec};

    /// `w msum x` through `sum` over a fresh ring of `2w` zeroed slots (the prefix before the start is 0), in chunks
    /// that wrap it, answered at `O`.
    fn msum<E: Reg, O: Reg<B = [u8; OW]>, const OW: usize>(w: usize, x: &[E], sum: fn(&mut Mw, &[u8], &mut [u8], usize)) -> Vec<O> {
        let p: Vec<u8> = x.iter().flat_map(|e| e.bits().to_ne_bytes()[..E::W].to_vec()).collect();
        let (mut ri, mut o) = (vec![0u64; 2 * w], vec![0u8; x.len() * OW]);
        let mut st = Mw { w, cu: 0, cap: 2 * w, tl: w, t: 0, isum: 0, fsum: 0.0, fsq: 0.0, cnt: 0, extbits: 0, sent: 0,
            ri: &mut ri, rf: &mut [], rq: &mut [], rc: &mut [], phase: &mut [], sufx: &mut [] };
        sum(&mut st, &p, &mut o, x.len());
        o.chunks_exact(OW).map(O::rd).collect()
    }

    // `2 msum 0W 0N 1 5 7`: the prefix past `O`'s range is null and stays null at both ends of the window; at 64 bits
    // the prefix wraps instead, onto the null and then past it
    #[test] fn msum_int_null_ends() {
        assert_eq!(msum::<i32, i32, 4>(2, &[i32::MAX, i32::MIN, 1, 5, 7], KI32::msum), [i32::MAX, i32::MAX, i32::MIN, i32::MIN, i32::MIN]);
        assert_eq!(msum::<i16, i16, 2>(2, &[i16::MAX, i16::MIN, 1, 5, 7], sum_int::<KI16, i16, 2>), [i16::MAX, i16::MAX, i16::MIN, i16::MIN, i16::MIN]);
        assert_eq!(msum::<i64, i64, 8>(2, &[i64::MAX, i64::MIN, 1, 5, 7], KI64::msum), [i64::MAX, i64::MAX, i64::MIN, 6, i64::MIN]);
    }
}

// ---------------------------------------------------------------- `kscan` (Rel/Kernel/Scan.lean, design §4)

/// `QAtomicType`'s constructor indices `kscan` tells apart (Rel/Kernel/Value.lean's order).
pub const QT_BOOLEAN: u8 = 0;
pub const QT_SYMBOL: u8 = 9;
/// `QAtomicType.width` at the constructor index `t`: `None` at `sym` (9) and `general` (12).
pub fn qtype_width(t: u8) -> Option<usize> {
    match t { 0 | 1 | 7 | 8 => Some(1), 2 => Some(2), 3 | 5 | 10 => Some(4), 4 | 6 | 11 => Some(8), _ => None }
}

/// `Int.fdiv` and `Int.fmod` cut to 64 bits (`Int64.ofInt`): floored, so `i64::MIN / -1` wraps to `i64::MIN`; `y != 0`.
fn fdivmod(x: i64, y: i64) -> (u64, u64) {
    let (x, y) = (x as i128, y as i128);
    let q = x / y - if x % y != 0 && (x < 0) != (y < 0) { 1 } else { 0 };
    (q as i64 as u64, (x - y * q) as i64 as u64)
}
/// `Op.widen32`: an `f32` word widened, a NaN keeping its sign as the quiet `f64` NaN.
fn widen32(x: u64) -> u64 {
    let b = x as u32;
    let v = f32::from_bits(b);
    if v.is_nan() { ((b >> 31) as u64) << 63 | 0x7ff8_0000_0000_0000 } else { (v as f64).to_bits() }
}

/// `Op.eval` (Rel/Kernel/Op.lean) at the constructor index `op`, one scan step on raw words: the integer ops on `i64`
/// wrapping, the `f` ops on `f64` bits, a boolean the word 0 or 1. `Err` is the Lean `.error` text, word for word.
pub fn op_eval(op: u8, a: u64, x: u64) -> Result<u64, &'static str> {
    match (op, x) { (3, 0) => Err("Op.div: integer division by 0"), (4, 0) => Err("Op.mod: integer remainder by 0"), _ => Ok(op_word(op, a, x)) }
}
/// `op_eval` where it has an answer: `div` and `mod` by 0, its two errors, are excluded by the caller (`kscan`'s `zero`
/// test runs before any row), so the loop over a block's rows carries no `Result`.
#[inline(always)]
pub fn op_word(op: u8, a: u64, x: u64) -> u64 {
    use crate::c as m;
    let (i, f, w, fw) = (|v: u64| v as i64, f64::from_bits, |b: bool| b as u64, f64::to_bits);
    // a NaN is the least value (`Op.fle'`), so `fmin`/`fmax` choose under a total order
    let fle = |a: u64, x: u64| f(a).is_nan() || (!f(x).is_nan() && f(a) <= f(x));
    // which NaN operand `+ - * /` return is unspecified (LLVM commutes `fadd`/`fmul` freely, so release and debug
    // differ): fixed here as IEEE 754's recommendation and x86's scalar rule, the first NaN operand quieted
    let ar = |r: f64| if !r.is_nan() { fw(r) } else if f(a).is_nan() { a | 1 << 51 } else if f(x).is_nan() { x | 1 << 51 } else { fw(r) };
    match op {
        0 => a.wrapping_add(x), 1 => a.wrapping_sub(x), 2 => a.wrapping_mul(x),
        3 => fdivmod(i(a), i(x) | (x == 0) as i64).0,
        4 => fdivmod(i(a), i(x) | (x == 0) as i64).1,
        5 => if i(x) < i(a) { x } else { a }, 6 => if i(a) < i(x) { x } else { a },
        7 => x.wrapping_neg(), 8 => if i(x) < 0 { x.wrapping_neg() } else { x },
        9 => w(a == x), 10 => w(a != x), 11 => w(i(a) < i(x)), 12 => w(i(a) <= i(x)), 13 => w(i(x) < i(a)), 14 => w(i(x) <= i(a)),
        15 => a & x, 16 => a | x, 17 => x ^ 1, 18 => a, 19 => x,
        20 => ar(f(a) + f(x)), 21 => ar(f(a) - f(x)), 22 => ar(f(a) * f(x)), 23 => ar(f(a) / f(x)), 24 => fw(m::pow(f(a), f(x))),
        25 => if fle(a, x) { a } else { x }, 26 => if fle(a, x) { x } else { a },
        27 => x ^ 0x8000_0000_0000_0000, 28 => x & 0x7fff_ffff_ffff_ffff,
        29 => fw(m::sqrt(f(x))), 30 => fw(m::exp(f(x))), 31 => fw(m::log(f(x))), 32 => fw(m::sin(f(x))), 33 => fw(m::cos(f(x))),
        34 => fw(m::tan(f(x))), 35 => fw(m::asin(f(x))), 36 => fw(m::acos(f(x))), 37 => fw(m::atan(f(x))),
        38 => fw(crate::ew::floor64(f(x))),
        39 => w(f(a) == f(x)), 40 => w(f(a) != f(x)), 41 => w(f(a) < f(x)), 42 => w(f(a) <= f(x)), 43 => w(f(x) < f(a)), 44 => w(f(x) <= f(a)),
        // 45, `f32to64`: the last constructor, and Lean passes no other index
        _ => widen32(x),
    }
}

/// `body` with the const `$k` bound to the op `op` (0 ..= 45), so a loop over rows is compiled once per op and its
/// `op_word` folds to that op's arm: the `match` on the op runs once per block, not once per row.
macro_rules! by_op { ($op:expr, $k:ident => $body:expr) => { by_op!(@ $op, $k, $body; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17
    18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44) };
    (@ $op:expr, $k:ident, $body:expr; $($n:literal)*) => { match $op { $($n => { const $k: u8 = $n; $body })* _ => { const $k: u8 = 45; $body } } } }

/// The writer's block size, `kscan`'s answer grid: a block of rows is computed whole in one scratch of this many words.
const BLK: usize = 1 << crate::DEFAULT_LG;
/// A block's `seg` bits as words.
type Seg = [u64; BLK / 64];

/// One column of `kscan` as `Enc.raw s n` reads it, a block of rows at a time: a dense payload of `w`-byte elements,
/// a bit payload, or a block source of `w`-byte elements cut by the mask `m` (`!0`, or `1` for a boolean `foR`, which
/// `raw` reads at its one bit). Each form reads 0 past what it holds, as `raw` does.
#[derive(Clone, Copy)]
enum Col<'a> { Dense(&'a [u8], usize), Bits(&'a [u8]), Blk(Blocks<'a>, usize, u64) }

impl<'a> Col<'a> {
    /// `Enc.raw s n e`'s arms; `None` where `raw` is `#[]`.
    fn of(s: u8, n: usize, e: B<'a>) -> Option<Col<'a>> {
        let (w, boolean) = (qtype_width(s), s == QT_BOOLEAN);
        match (e.tag(), w) {
            (0, Some(w)) if !boolean => Some(Col::Dense(e.field(0).bytes(), w)),
            (1, _) if boolean => Some(Col::Bits(e.field(0).bytes())),
            (3, Some(w)) if boolean => Some(Col::Blk(Blocks::of(e, w, n, "qlean_k_scan"), w, 1)),
            (3 | 4, Some(w)) if !boolean => Some(Col::Blk(Blocks::of(e, w, n, "qlean_k_scan"), w, !0)),
            // `pos` (tag 7) is `raw`'s at `i64` (type 4) only: the loop index
            (7, _) if s == 4 => Some(Col::Blk(Blocks::pos(n), 8, !0)),
            // ids of no bits (a dictionary of one entry) read 0 at every row
            (5, _) if s == QT_SYMBOL => Some(match ids::id_width(e.field(1).words().len().saturating_sub(1)) {
                0 => Col::Dense(&[], 8), lw => Col::Blk(Blocks::ids(e.field(2).bytes(), n, lw), 8, !0) }),
            _ => None,
        }
    }
    /// Rows `lo .. lo + out.len()` as words into `out`, each zero-extended from its width. `tmp` holds a block at 8
    /// bytes a row; a source on the writer's grid is decoded one block straight into it (or into `out` at 8 bytes).
    fn load(&self, lo: usize, out: &mut [u64], tmp: &mut [u8]) {
        match *self {
            Col::Dense(p, w) => widen(p.get(lo * w..).unwrap_or(&[]), w, out),
            Col::Bits(p) => for (k, o) in out.iter_mut().enumerate() { *o = bit(p, lo + k) as u64 },
            Col::Blk(bl, w, m) => {
                let got = (lo + out.len()).min(bl.n).saturating_sub(lo);
                let on_grid = bl.lg() == crate::DEFAULT_LG;
                if on_grid && w == 8 {
                    bl.load_w(lo >> bl.lg(), got, 8, pod::bytes_mut(&mut out[..got]));
                    return out[got..].fill(0)
                }
                let x = if got == 0 { &[][..] } else if on_grid { bl.load_w(lo >> bl.lg(), got, w, tmp) } else { bl.range(lo, got, w, tmp) };
                widen(x, w, out);
                if m != !0 { for o in out.iter_mut() { *o &= m } }
            }
        }
    }
    /// The FoR column behind block `b` of the writer's grid where its metadata are its rows' words read as `i64`: 8
    /// bytes, or a block whose minimum is at least 0, where zero- and sign-extension agree. `[base, maxv]` bounds
    /// every element of the block, patches included (`Coc.blockOf`); under a mask, only where `maxv` is within it.
    fn coc(&self, b: usize) -> Option<Coc<'a>> {
        match *self {
            Col::Blk(Blocks { src: Src::For(c), g }, w, m) if g.lg == crate::DEFAULT_LG && (w == 8 || c.meta.base[b] >= 0)
                && c.meta.maxv[b] as u64 <= m => Some(c),
            _ => None,
        }
    }
    /// Block `b`'s one word where its metadata say every row holds it.
    fn konst(&self, b: usize) -> Option<u64> { self.coc(b).filter(|c| c.meta.base[b] == c.meta.maxv[b]).map(|c| c.meta.base[b] as u64) }
}
/// `p`'s bit `i`, LSB first, 0 past its end (`bitAt`).
fn bit(p: &[u8], i: usize) -> bool { p.get(i >> 3).is_some_and(|b| b >> (i & 7) & 1 == 1) }
/// The `w`-byte elements of `x` zero-extended into `out`, 0 past `x`; an element `x` cuts short reads its low bytes, as
/// `raw`'s `rd` does.
fn widen(x: &[u8], w: usize, out: &mut [u64]) {
    fn at<const W: usize>(x: &[u8], out: &mut [u64]) {
        for (o, c) in out.iter_mut().zip(x.as_chunks::<W>().0) { let mut a = [0u8; 8]; a[..W].copy_from_slice(c); *o = u64::from_le_bytes(a) }
    }
    let k = (x.len() / w).min(out.len());
    match w { 1 => at::<1>(x, &mut out[..k]), 2 => at::<2>(x, &mut out[..k]), 4 => at::<4>(x, &mut out[..k]), _ => at::<8>(x, &mut out[..k]) }
    out[k..].fill(0);
    if let Some(o) = out.get_mut(k) { for (j, &b) in x[k * w..].iter().take(w).enumerate() { *o |= (b as u64) << (8 * j) } }
}

/// `for $p in $it $body`, walking `$it` from its end where `$rev`: a block's rows in the order `kscan` folds them.
macro_rules! rows { ($rev:expr, $it:expr, $p:pat => $body:block) => { if $rev { for $p in $it.rev() $body } else { for $p in $it $body } } }

/// `kscan`'s columns, read a block of rows at a time, and the carry into each block (`carry[b]`, the answer of the row
/// the fold reaches the block from: `lo - 1`, or `lo + nb` under `rev`).
struct Scan<'a> { op: u8, rev: bool, n: usize, seg: Col<'a>, seed: Col<'a>, xs: &'a [Col<'a>], carry: Vec<u64> }

impl Scan<'_> {
    /// The `seg` bits of the `nb` rows from `lo` (a block of the writer's grid), the first row the fold reaches always a
    /// segment start (`kscanRow`'s `0 < i`): row 0, or row `n - 1` under `rev`.
    fn seg(&self, lo: usize, nb: usize) -> Seg {
        let mut g = [0u64; BLK / 64];
        match self.seg {
            Col::Bits(p) => {
                let src = p.get(lo / 8..).unwrap_or(&[]);
                for (k, o) in g.iter_mut().enumerate().take(nb.div_ceil(64)) {
                    let mut a = [0u8; 8];
                    let s = src.get(8 * k..).unwrap_or(&[]);
                    a[..s.len().min(8)].copy_from_slice(&s[..s.len().min(8)]);
                    *o = u64::from_le_bytes(a);
                }
            }
            // a `foR` boolean: the block decoded into the L1 scratch, each row's bit packed
            c => {
                let (mut v, mut tmp) = (pod::Scr::<u64>::new(nb), pod::Scr::<u64>::new(BLK));
                c.load(lo, &mut v, pod::bytes_mut(&mut tmp));
                for (k, &x) in v.iter().enumerate() { g[k >> 6] |= (x & 1) << (k & 63) }
            }
        }
        if nb & 63 != 0 { g[nb >> 6] &= !0 >> (64 - (nb & 63)) }
        if self.rev { if lo + nb == self.n { g[(nb - 1) >> 6] |= 1 << ((nb - 1) & 63) } } else if lo == 0 { g[0] |= 1 }
        g
    }
    /// Row `i`'s `seg` bit, `i` being no row the fold starts at.
    fn seg_at(&self, i: usize) -> bool {
        let lo = i / BLK * BLK;
        self.seg(lo, (self.n - lo).min(BLK))[(i - lo) >> 6] >> ((i - lo) & 63) & 1 == 1
    }
    /// Rows `lo .. lo + out.len()` into `out`, from `c`, row `lo - 1`'s answer.
    fn block(&self, lo: usize, c: u64, out: &mut [u64]) { let g = self.seg(lo, out.len()); by_op!(self.op, OP => self.fold::<OP>(&g, lo, c, out)) }
    /// `kscanRow` over one block at the op `OP`: the shapes that need no per-row `seg` test (every row a segment, or
    /// none) and one folded column are loops of their own, so the map shape vectorises.
    #[inline(always)]
    fn fold<const OP: u8>(&self, g: &Seg, lo: usize, mut c: u64, out: &mut [u64]) {
        let (nb, f) = (out.len(), |a, x| op_word(OP, a, x));
        let at = |i: usize| g[i >> 6] >> (i & 63) & 1 == 1;
        let none = g.iter().all(|&w| w == 0);
        let all = (0..nb.div_ceil(64)).all(|k| g[k] == if 64 * (k + 1) <= nb { !0 } else { !0 >> (64 - (nb & 63)) });
        let mut tmp = pod::Scr::<u64>::new(nb);
        // the seed is read only at a segment start
        let mut sd = pod::Scr::<u64>::new(if none { 0 } else { nb });
        if !none { self.seed.load(lo, &mut sd, pod::bytes_mut(&mut tmp)) }
        let Some((x0, rest)) = self.xs.split_first() else {
            rows!(self.rev, out.iter_mut().enumerate(), (i, o) => { if at(i) { c = sd[i] } *o = c });
            return
        };
        x0.load(lo, out, pod::bytes_mut(&mut tmp));
        if rest.is_empty() {
            if all { for (o, &a) in out.iter_mut().zip(sd.iter()) { *o = f(a, *o) } }
            else if none { rows!(self.rev, out.iter_mut(), o => { c = f(c, *o); *o = c }) }
            else { rows!(self.rev, out.iter_mut().enumerate(), (i, o) => { c = f(if at(i) { sd[i] } else { c }, *o); *o = c }) }
            return
        }
        let xr: Vec<pod::Scr<u64>> = rest.iter().map(|x| { let mut v = pod::Scr::<u64>::new(nb); x.load(lo, &mut v, pod::bytes_mut(&mut tmp)); v }).collect();
        rows!(self.rev, out.iter_mut().enumerate(), (i, o) => {
            let mut a = f(if at(i) { sd[i] } else { c }, *o);
            for x in &xr { a = f(a, x[i]) }
            (*o, c) = (a, a);
        });
    }
    /// Block `b`'s last row from `c` where no row of it starts a segment and the folded columns' metadata give it: `+`
    /// and `-` move the carry by the blocks' sums (`bsum`, which skips only the null, and a block holding the null
    /// has it as its minimum), `min` and `max` by their extremes, `first` and an empty fold leave it.
    fn summary(&self, b: usize, c: u64) -> Option<u64> {
        let m = |f: &dyn Fn(u64, Coc) -> Option<u64>| self.xs.iter().try_fold(c, |a, x| f(a, x.coc(b)?));
        match self.op {
            _ if self.xs.is_empty() => Some(c),
            0 | 1 => m(&|a, k| (k.meta.base[b] != i64::MIN).then(|| op_word(self.op, a, k.meta.bsum[b] as u64))),
            5 => m(&|a, k| Some(op_word(5, a, k.meta.base[b] as u64))),
            6 => m(&|a, k| Some(op_word(6, a, k.meta.maxv[b] as u64))),
            18 => Some(c),
            _ => None,
        }
    }
    /// Each block's carry in, serially in the fold's order (the blocks walked backwards under `rev`): a block's last row
    /// in that order is computed only where the next block's row continues it, from the metadata where `summary`
    /// answers, else by folding the block.
    fn carries(&mut self) {
        let g = Grid { n: self.n, lg: crate::DEFAULT_LG };
        let mut bs: Vec<(usize, usize, usize)> = g.walk().collect();
        if self.rev { bs.reverse() }
        let (mut cs, mut c, mut tmp) = (alloc::vec![0u64; bs.len()], 0u64, pod::Scr::<u64>::new(BLK));
        for (b, lo, nb) in bs {
            cs[b] = c;
            // the row the fold reaches next, which continues this block unless `seg` starts a segment there
            let next = if self.rev { lo.checked_sub(1) } else { Some(lo + nb).filter(|&i| i < self.n) };
            if next.is_none_or(|i| self.seg_at(i)) { continue }
            let quiet = self.seg(lo, nb).iter().all(|&w| w == 0);
            c = match self.summary(b, c).filter(|_| quiet) {
                Some(v) => v,
                None => { self.block(lo, c, &mut tmp[..nb]); tmp[if self.rev { 0 } else { nb - 1 }] }
            };
        }
        self.carry = cs;
    }
    /// Whether some row of a folded column reads 0: `div` and `mod` then fail, and every row folds every column.
    fn zero(&self) -> bool {
        let g = Grid { n: self.n, lg: crate::DEFAULT_LG };
        let (mut v, mut tmp) = (pod::Scr::<u64>::new(BLK), pod::Scr::<u64>::new(BLK));
        self.xs.iter().any(|x| g.walk().any(|(b, lo, nb)| match x.coc(b) {
            Some(c) if c.meta.base[b] > 0 || c.meta.maxv[b] < 0 => false,
            _ => { x.load(lo, &mut v[..nb], pod::bytes_mut(&mut tmp)); v[..nb].contains(&0) }
        }))
    }
    /// Block `b` of a boolean answer straight from the compare kernel where it is a map of one column against a
    /// block the metadata make constant: `codec::mask_blk`, which settles the block from `[base, maxv]` when it can and
    /// tests the residuals in place when not. `false` where the block is not of that shape.
    fn cmp_blk(&self, b: usize, lo: usize, nb: usize, w64: &mut [u64], scratch: &mut [u8]) -> bool {
        use crate::cocops::{EQ, GE, GT, LE, LT, NE};
        let ([x], 9..=14) = (self.xs, self.op) else { return false };
        let g = self.seg(lo, nb);
        if !(0..nb.div_ceil(64)).all(|k| g[k] == if 64 * (k + 1) <= nb { !0 } else { !0 >> (64 - (nb & 63)) }) { return false }
        // the row is `seed op x`: against a constant seed the column is `x`, the order turned round
        let (on_x, on_seed) = ([EQ, NE, GT, GE, LT, LE], [EQ, NE, LT, LE, GT, GE]);
        let k = (self.op - 9) as usize;
        let (c, op, v) = match (x.coc(b), self.seed.konst(b), self.seed.coc(b), x.konst(b)) {
            (Some(c), Some(v), _, _) => (c, on_x[k], v),
            (_, _, Some(c), Some(v)) => (c, on_seed[k], v),
            _ => return false,
        };
        crate::codec::mask_blk(&c, b, nb, op, v as i64, w64, scratch);
        true
    }
}

/// `Kernel.kscan op s t n seg es` (Rel/Kernel/Scan.lean) on the columns' blocks, in its order of failure: `seg`, each of
/// `es` left to right, the rows (`div`/`mod` by 0), the width. The answer is the `Enc` the model's `Except` holds.
///
/// Owner approval S (PLAN 6.10): one block decoded into an L1 scratch (`BLK` words, 8 KiB) counts as computing on the
/// block, so each column is read here a block at a time through `Col::load`, never as a whole decoded column. A compare
/// against a constant block goes to `codec::mask_blk` on the residuals; the carry between blocks comes from block
/// metadata where `Scan::summary` gives it. The answer is written by the encoder's block step (`Sink`), a block at
/// a time, so its bytes are `Coc.encode 8` of the rows (at a boolean `t` each cut to its low bit, a `foR` of `u1`).
/// Under `rev` the blocks are walked backwards and each block's rows from its end: no column is reversed in memory.
pub fn kscan<'a>(op: u8, rev: bool, s: u8, t: u8, n: usize, seg: B<'a>, es: &[B<'a>]) -> Result<O, String> {
    // `None` is `raw`'s `#[]`, of size 0: at `n = 0` that is every row
    let all = |t: u8, e: B<'a>| match Col::of(t, n, e) {
        Some(c) => Ok(c),
        None if n == 0 => Ok(Col::Dense(&[], 8)),
        None => Err(format!("kscan: a column holds 0 raw elements, not {n}")),
    };
    let g = all(QT_BOOLEAN, seg)?;
    let cols = es.iter().map(|&e| all(s, e)).collect::<Result<Vec<_>, _>>()?;
    let Some((&seed, xs)) = cols.split_first() else { return Err("kscan: es is empty; its first column is the seed".into()) };
    let mut r = Scan { op, rev, n, seg: g, seed, xs, carry: Vec::new() };
    if let Err(m) = op_eval(op, 0, 0) && r.zero() { return Err(m.into()) }
    qtype_width(t).ok_or("kscan: the answer type has no fixed width")?;
    r.carries();
    let (r, low) = (&r, if t == QT_BOOLEAN { 1 } else { !0u64 });
    Ok(Sink::new(n, 8, Form::For).enc().answer(&|buf: &mut [i64], lo: usize| {
        let o = pod::cast_mut::<u64>(pod::bytes_mut(buf)).expect("kscan: an i64 block is a u64 block");
        let (b, nb, mut w64) = (lo >> crate::DEFAULT_LG, o.len(), [0u64; BLK / 64]);
        // a compare against a constant block: the compare kernel's bits, each a row's word
        if (9..=14).contains(&r.op) && r.cmp_blk(b, lo, nb, &mut w64, pod::bytes_mut(&mut pod::Scr::<u64>::new(BLK))) {
            for (k, v) in o.iter_mut().enumerate() { *v = w64[k >> 6] >> (k & 63) & 1 }
        } else {
            r.block(lo, r.carry[b], o);
            if low != !0 { for v in o.iter_mut() { *v &= low } }
        }
    }))
}

#[cfg(test)]
mod kscan_tests {
    use super::*;
    use crate::lean::{self, SArr};
    use alloc::{vec, vec::Vec};
    /// `kscanRow` folded over the rows on words, the first error stopping it: the model the kernel answers.
    fn rows(op: u8, rev: bool, seg: &[u64], seed: &[u64], xs: &[Vec<u64>]) -> Result<Vec<u64>, &'static str> {
        if rev {
            let r = |v: &[u64]| v.iter().rev().copied().collect::<Vec<u64>>();
            return rows(op, false, &r(seg), &r(seed), &xs.iter().map(|x| r(x)).collect::<Vec<_>>()).map(|o| r(&o))
        }
        let mut out: Vec<u64> = Vec::with_capacity(seed.len());
        for i in 0..seed.len() {
            let mut a = if i > 0 && seg[i] == 0 { out[i - 1] } else { seed[i] };
            for x in xs { a = op_eval(op, a, x[i])? }
            out.push(a);
        }
        Ok(out)
    }
    fn bytes(v: &[u64], w: usize) -> Vec<u8> { v.iter().flat_map(|e| e.to_le_bytes()[..w].to_vec()).collect() }
    fn enc_for(v: &[u64], w: usize) -> O { Sink::new(v.len(), w, Form::For).enc().answer(&Blocks::dense(&bytes(v, w), w)) }
    fn enc_dense(p: &[u8]) -> O { let mut a = SArr::new(1, p.len()); a.bytes_mut().copy_from_slice(p); lean::ctor(0, [a.into()], &[]) }
    fn enc_bits(v: &[u64]) -> O { Sink::new(v.len(), 1, Form::Ids(1)).enc().answer(&Blocks::dense(&bytes(v, 1).iter().map(|b| b & 1).collect::<Vec<_>>(), 1)) }
    fn parts(o: &O) -> Vec<Vec<u8>> { let b = o.borrow(); (0..if b.tag() == 1 { 1 } else { 2 }).map(|i| b.field(i).bytes().to_vec()).collect() }
    /// A column of `n` words: a smooth run, an outlier every 97th row (a patch), negatives, a null every 301st, `0n`
    /// every 211th.
    fn column(n: usize, k: u64) -> Vec<u64> {
        (0..n as u64).map(|i| match i % 301 { 7 => i64::MIN as u64, _ if i % 211 == 11 => 0xfff8_0000_0000_0000, _ if i % 97 == 5 => i.wrapping_mul(1_000_003 * k), _ => (1000 + (i * 7919 * k) % 8000).wrapping_sub(3000) }).collect()
    }
    /// Both directions, `seg` as bits and as a boolean `foR` (`kscan`'s own boolean answer, at 8 bytes).
    fn check(op: u8, s: u8, t: u8, n: usize, seg: &[u64], es: &[(O, Vec<u64>)]) {
        for rev in [false, true] { for g in [enc_bits(seg), enc_for(seg, 8)] { check1(op, rev, s, t, n, seg, &g, es) } }
    }
    fn check1(op: u8, rev: bool, s: u8, t: u8, n: usize, seg: &[u64], g: &O, es: &[(O, Vec<u64>)]) {
        let xs: Vec<Vec<u64>> = es.iter().skip(1).map(|e| e.1.clone()).collect();
        let want = match es.first() {
            None => Err("kscan: es is empty; its first column is the seed".into()),
            Some(sd) => rows(op, rev, seg, &sd.1, &xs).map_err(String::from).and_then(|r| match qtype_width(t) {
                None => Err("kscan: the answer type has no fixed width".into()),
                Some(_) => Ok(parts(&enc_for(&r.iter().map(|v| if t == QT_BOOLEAN { v & 1 } else { *v }).collect::<Vec<_>>(), 8))),
            }),
        };
        let bs: Vec<B> = es.iter().map(|e| e.0.borrow()).collect();
        assert_eq!(kscan(op, rev, s, t, n, g.borrow(), &bs).map(|o| parts(&o)), want, "op {op} rev {rev} s {s} t {t} n {n}");
    }
    // every shape (map, scan, segmented, fill) and op against the row model, over FoR columns with patches and nulls at
    // each width, a dense column cut short, and a constant seed (the compare kernel's path) beside a varying one
    #[test] fn kscan_agrees_with_its_rows() {
        for n in [0usize, 1, 1000, 2500] {
            let segs = [vec![1u64; n], vec![0; n], (0..n as u64).map(|i| (i % 1000 == 0 || i % 37 == 3) as u64).collect()];
            for (s, w) in [(6u8, 8usize), (5, 4), (2, 2)] {
                let m = |v: Vec<u64>| -> Vec<u64> { v.into_iter().map(|x| if w == 8 { x } else { x & ((1 << (8 * w)) - 1) }).collect() };
                let (x, y, c) = (m(column(n, 3)), m(column(n, 5)), m(vec![column(n.max(3), 3)[2]; n]));
                let col = |v: &Vec<u64>| (enc_for(v, w), v.clone());
                // a dense payload three bytes short reads its last element's low bytes and 0 past them
                let p = bytes(&y, w);
                let cut = p[..p.len().saturating_sub(3)].to_vec();
                let sv: Vec<u64> = (0..n).map(|i| (0..w).fold(0u64, |a, k| a | (cut.get(i * w + k).copied().unwrap_or(0) as u64) << (8 * k))).collect();
                for op in [0u8, 1, 2, 3, 5, 6, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 25, 39, 41, 45] {
                    for g in &segs {
                        for t in [QT_BOOLEAN, 6] {
                            check(op, s, t, n, g, &[col(&c), col(&x)]);
                            check(op, s, t, n, g, &[col(&x), col(&c)]);
                        }
                        check(op, s, 6, n, g, &[col(&y), col(&x)]);
                        check(op, s, 6, n, g, &[col(&c), col(&x), (enc_dense(&p), y.clone())]);
                        check(op, s, 6, n, g, &[(enc_dense(&cut), sv.clone()), col(&x)]);
                        check(op, s, 6, n, g, &[col(&x)]);
                    }
                }
                check(0, s, 6, n, &segs[0], &[]);
                check(0, s, 12, n, &segs[0], &[col(&x)]);
            }
            // `div` by a 0 anywhere fails; a dense column read as booleans holds no raw elements
            let z: Vec<u64> = (0..n as u64).map(|i| (i != n as u64 / 2) as u64 * 7).collect();
            check(3, 6, 6, n, &segs[0], &[(enc_for(&z, 8), z.clone()), (enc_for(&z, 8), z.clone())]);
            if n > 0 {
                let e = enc_dense(&bytes(&z, 1));
                assert_eq!(kscan(0, false, QT_BOOLEAN, 6, n, enc_bits(&segs[0]).borrow(), &[e.borrow()]).map(|o| parts(&o)),
                           Err(format!("kscan: a column holds 0 raw elements, not {n}")));
            }
            let (a, b): (Vec<u64>, Vec<u64>) = ((0..n as u64).map(|i| i % 3 & 1).collect(), (0..n as u64).map(|i| i % 5 & 1).collect());
            // a boolean column as bits, as a `foR` of `u1`, and as a `foR` holding 0..3, which reads its low bit
            let q: Vec<u64> = (0..n as u64).map(|i| i % 4).collect();
            let ql: Vec<u64> = q.iter().map(|v| v & 1).collect();
            for op in [15u8, 16, 0, 9, 11] {
                check(op, QT_BOOLEAN, QT_BOOLEAN, n, &segs[2], &[(enc_bits(&a), a.clone()), (enc_bits(&b), b.clone())]);
                check(op, QT_BOOLEAN, QT_BOOLEAN, n, &segs[2], &[(enc_for(&a, 8), a.clone()), (enc_for(&q, 8), ql.clone())]);
                check(op, QT_BOOLEAN, 6, n, &segs[1], &[(enc_for(&q, 1), ql.clone()), (enc_bits(&b), b.clone())]);
            }
        }
    }
    #[test] fn op_eval_floors_and_types_its_errors() {
        assert_eq!(op_eval(3, -1i64 as u64, 2), Ok(-1i64 as u64));
        assert_eq!(op_eval(4, -7i64 as u64, 3), Ok(2));
        assert_eq!(op_eval(4, 7, -3i64 as u64), Ok(-2i64 as u64));
        assert_eq!(op_eval(3, i64::MIN as u64, -1i64 as u64), Ok(i64::MIN as u64));
        assert_eq!(op_eval(3, 7, 0), Err("Op.div: integer division by 0"));
        assert_eq!(op_eval(4, 7, 0), Err("Op.mod: integer remainder by 0"));
        assert_eq!(op_eval(45, 0, 0x3fc0_0000), Ok(0x3ff8_0000_0000_0000));
        assert_eq!(op_eval(25, f64::NAN.to_bits(), 1f64.to_bits()), Ok(f64::NAN.to_bits()));
        assert_eq!(op_eval(38, 0, 2.5f64.to_bits()), Ok(2f64.to_bits()));
    }
}

