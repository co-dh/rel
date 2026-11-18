#![forbid(unsafe_code)]
//! Column (a), scan.rs (A14): the running scans (sums, prds, mins, maxs, fills) over a dense payload and
//! the block skips over an encoded one. `scan_fill` and `scan_any_null` are AVX-512 in C: their vector bodies are in
//! `simd.rs`, which this module calls and finishes (the groups that hold a null, the tail).
use crate::key::{SK_BIT, SK_C8, SK_F32, SK_F64, SK_I16, SK_I32, SK_I64, SK_KINDS_N, SK_U8};
use crate::simd;
use crate::pod::Elt;

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
pub fn rd_i16(p: &[u8], i: usize) -> i64 { i16::from_ne_bytes(p[2 * i..2 * i + 2].try_into().unwrap()) as i64 }
pub fn rd_i32(p: &[u8], i: usize) -> i64 { i32::from_ne_bytes(p[4 * i..4 * i + 4].try_into().unwrap()) as i64 }
pub fn rd_i64(p: &[u8], i: usize) -> i64 { i64::from_ne_bytes(p[8 * i..8 * i + 8].try_into().unwrap()) }
pub fn rd_f32(p: &[u8], i: usize) -> f32 { f32::from_ne_bytes(p[4 * i..4 * i + 4].try_into().unwrap()) }
pub fn rd_f64(p: &[u8], i: usize) -> f64 { f64::from_ne_bytes(p[8 * i..8 * i + 8].try_into().unwrap()) }

// ---- null tests: `0N` is the minimum of each signed width, byte and boolean have none, `char`'s is the blank ----
pub fn nul_no(_: i64) -> bool { false }
pub fn nul_chr(v: i64) -> bool { v == 0x20 }
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

/// scan.rs `scan_run`: scan `op` over `n` elements, `carry` the running accumulator.
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
pub const QT_BOOLEAN: u8 = 1;
pub const QT_SYMBOL: u8 = 9;
/// `QAtomicType.width` at the constructor index `t`: `None` at `general` (0) and `symbol` (9).
pub fn qtype_width(t: u8) -> Option<usize> {
    match t { 1 | 2 | 8 => Some(1), 3 => Some(2), 4 | 6 | 11 | 12 | 15 | 16 | 17 => Some(4), 5 | 7 | 10 | 13 | 14 => Some(8), _ => None }
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
    use crate::c as m;
    let (i, f, w, fw) = (|v: u64| v as i64, f64::from_bits, |b: bool| b as u64, f64::to_bits);
    // a NaN is the least value (`Op.fle'`), so `fmin`/`fmax` choose under a total order
    let fle = |a: u64, x: u64| f(a).is_nan() || (!f(x).is_nan() && f(a) <= f(x));
    Ok(match op {
        0 => a.wrapping_add(x), 1 => a.wrapping_sub(x), 2 => a.wrapping_mul(x),
        3 => if x == 0 { return Err("Op.div: integer division by 0") } else { fdivmod(i(a), i(x)).0 },
        4 => if x == 0 { return Err("Op.mod: integer remainder by 0") } else { fdivmod(i(a), i(x)).1 },
        5 => if i(x) < i(a) { x } else { a }, 6 => if i(a) < i(x) { x } else { a },
        7 => x.wrapping_neg(), 8 => if i(x) < 0 { x.wrapping_neg() } else { x },
        9 => w(a == x), 10 => w(a != x), 11 => w(i(a) < i(x)), 12 => w(i(a) <= i(x)), 13 => w(i(x) < i(a)), 14 => w(i(x) <= i(a)),
        15 => a & x, 16 => a | x, 17 => x ^ 1, 18 => a, 19 => x,
        20 => fw(f(a) + f(x)), 21 => fw(f(a) - f(x)), 22 => fw(f(a) * f(x)), 23 => fw(f(a) / f(x)), 24 => fw(m::pow(f(a), f(x))),
        25 => if fle(a, x) { a } else { x }, 26 => if fle(a, x) { x } else { a },
        27 => x ^ 0x8000_0000_0000_0000, 28 => x & 0x7fff_ffff_ffff_ffff,
        29 => fw(m::sqrt(f(x))), 30 => fw(m::exp(f(x))), 31 => fw(m::log(f(x))), 32 => fw(m::sin(f(x))), 33 => fw(m::cos(f(x))),
        34 => fw(m::tan(f(x))), 35 => fw(m::asin(f(x))), 36 => fw(m::acos(f(x))), 37 => fw(m::atan(f(x))),
        38 => fw(crate::ew::floor64(f(x))),
        39 => w(f(a) == f(x)), 40 => w(f(a) != f(x)), 41 => w(f(a) < f(x)), 42 => w(f(a) <= f(x)), 43 => w(f(x) < f(a)), 44 => w(f(x) <= f(a)),
        // 45, `f32to64`: the last constructor, and Lean passes no other index
        _ => widen32(x),
    })
}

/// `kscan`'s rows (`kscanRow` folded over `0 .. n`): row `i` starts from `seed[i]` where `i == 0` or `seg[i] != 0`, else
/// from row `i - 1`'s answer, and folds each column of `xs` at row `i` into it through `op`; the first error stops it.
/// Every slice holds `seed.len()` words.
pub fn kscan_rows(op: u8, seg: &[u64], seed: &[u64], xs: &[alloc::vec::Vec<u64>]) -> Result<alloc::vec::Vec<u64>, &'static str> {
    let mut out = alloc::vec::Vec::with_capacity(seed.len());
    for i in 0..seed.len() {
        let mut a = if i > 0 && seg[i] == 0 { out[i - 1] } else { seed[i] };
        for x in xs { a = op_eval(op, a, x[i])? }
        out.push(a);
    }
    Ok(out)
}

/// `kscan`'s answer payload, `Column.packIds W n (v % 2^W)`: at `W = 1` one bit a word, LSB first and the tail bits 0;
/// else `W / 8` little-endian bytes a word.
pub fn kscan_pack(wb: usize, out: &[u64]) -> alloc::vec::Vec<u8> {
    if wb == 1 {
        let mut b = alloc::vec![0u8; out.len().div_ceil(8)];
        for (i, v) in out.iter().enumerate() { b[i >> 3] |= ((v & 1) as u8) << (i & 7) }
        b
    } else {
        let mut b = alloc::vec::Vec::with_capacity(out.len() * wb / 8);
        for v in out { b.extend_from_slice(&v.to_le_bytes()[..wb / 8]) }
        b
    }
}

#[cfg(test)]
mod kscan_tests {
    use super::*;
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
    #[test] fn kscan_rows_restart_at_segments_and_stop_at_an_error() {
        let (seg, seed) = ([1, 0, 1, 0], [100, 100, 100, 100]);
        assert_eq!(kscan_rows(0, &seg, &seed, &[alloc::vec![1, 2, 3, 4]]), Ok(alloc::vec![101, 103, 103, 107]));
        // `es = [e]` fills `e` forward from the marked rows
        assert_eq!(kscan_rows(0, &[0, 0, 1, 0], &[5, 6, 7, 8], &[]), Ok(alloc::vec![5, 5, 7, 7]));
        assert_eq!(kscan_rows(3, &seg, &seed, &[alloc::vec![1, 0, 1, 1]]), Err("Op.div: integer division by 0"));
        assert_eq!(kscan_pack(1, &[1, 0, 3, 2, 1]), [0b10101]);
        assert_eq!(kscan_pack(16, &[0x1_0203, 4]), [3, 2, 4, 0]);
    }
}
