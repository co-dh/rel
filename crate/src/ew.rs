#![forbid(unsafe_code)]
//! Column (a), elementwise.c: scalar helpers (A42), the two-operand verbs and comparisons (A43; `ew_val_avx` and
//! `ew_cmp_avx` are `simd::ew_val`/`simd::ew_cmp`), bit verbs and the monadic ones (A44), casts and time (A45),
//! widening (A46a), the fused chain's stage table (A46b; its runner is `c::run_chain`). `op`, `cls`, `shape` are
//! elementwise.c:86-100's `EW_*`. The `qlean_ew_*` entries unbox and allocate and stay C (§1).
use crate::c::Runner;
use crate::coc::Coc;
use crate::sym::Syms;

// ---- A42: elementwise.c:140-299 (per element: C keeps these bodies while a C caller remains) ----
/// elementwise.c:140 `ew_unsupported`: the abort naming the engine, `op` and `cls`.
pub fn ew_unsupported(engine: &str, op: u32, cls: u32) -> ! {
    // C exits 1 after this text; no_std has no exit, so the panic handler prints it and aborts
    panic!("{engine}: no case for verb {op} at storage class {cls}. The dispatch in QLean/Kernel/Elementwise.lean is the only caller and must not claim this pair; answering anything here would be a wrong column rather than a fallback.")
}
/// elementwise.c:149 `ew_width`: an element's bytes in class `cls`.
pub fn ew_width(cls: u32) -> usize {
    match cls {
        0 => 1,
        1 => 2,
        2 | 4 => 4,
        3 | 5 => 8,
        _ => panic!("qlean_ew: storage class {cls} has no dense element width"),
    }
}
// q's order on floats as two predicates: a null (a NaN) below everything, two nulls equal (elementwise.c:177)
fn lt64(x: u64, y: u64) -> bool { if f64::from_bits(x).is_nan() { !f64::from_bits(y).is_nan() } else { f64::from_bits(x) < f64::from_bits(y) } }
fn lt32(x: u32, y: u32) -> bool { if f32::from_bits(x).is_nan() { !f32::from_bits(y).is_nan() } else { f32::from_bits(x) < f32::from_bits(y) } }
/// elementwise.c:195 `ew_tol`: q's tolerant float equality.
pub fn ew_tol(x: f64, y: f64) -> bool {
    let (ax, ay) = (x.abs(), y.abs());
    (x - y).abs() < 1.0 / (1u64 << 43) as f64 * if ax < ay { ax } else { ay }
}
/// elementwise.c:203 `ew_ord64`: a double's bits as an order-preserving key.
pub fn ew_ord64(x: u64, y: u64) -> i32 { if lt64(x, y) { -1 } else if lt64(y, x) { 1 } else { 0 } }
/// elementwise.c:207 `ew_ord32`
pub fn ew_ord32(x: u32, y: u32) -> i32 { if lt32(x, y) { -1 } else if lt32(y, x) { 1 } else { 0 } }
/// elementwise.c:240 `ew_outside_long`: `f` has no long.
pub fn ew_outside_long(f: f64) -> bool { f <= -9223372036854775808.0 || f >= 9223372036854775808.0 }
/// elementwise.c:250 `ew_fdiv`: floor division, q's nulls.
pub fn ew_fdiv(x: i64, y: i64) -> i64 {
    // the caller excluded y = 0 and the null x, the one dividend whose quotient by -1 overflows
    let (q, r) = (x.wrapping_div(y), x.wrapping_rem(y));
    q - ((r ^ y) < 0 && r != 0) as i64
}
/// elementwise.c:263 `ew_magic`: a divisor's multiply-shift form.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Magic { pub m: i64, pub d: i64, pub sh: u32, pub add: bool }
/// elementwise.c:265 `ew_magic_of`; `None` where C answers 0.
pub fn magic_of(d: i64) -> Option<Magic> {
    const TWO63: u64 = 1 << 63;
    let ad = d.unsigned_abs();
    if ad < 2 { return None; }
    let t = TWO63 + ((d as u64) >> 63);
    let anc = t - 1 - t % ad;
    let (mut q1, mut r1) = (TWO63 / anc, TWO63 - TWO63 / anc * anc);
    let (mut q2, mut r2) = (TWO63 / ad, TWO63 - TWO63 / ad * ad);
    let mut p = 63u32;
    loop {
        p += 1;
        q1 = q1.wrapping_mul(2); r1 = r1.wrapping_mul(2);
        if r1 >= anc { q1 = q1.wrapping_add(1); r1 = r1.wrapping_sub(anc); }
        q2 = q2.wrapping_mul(2); r2 = r2.wrapping_mul(2);
        if r2 >= ad { q2 = q2.wrapping_add(1); r2 = r2.wrapping_sub(ad); }
        let delta = ad - r2;
        if !(q1 < delta || (q1 == delta && r1 == 0)) { break; }
    }
    let m = q2.wrapping_add(1) as i64;
    let m = if d < 0 { m.wrapping_neg() } else { m };
    // C's `add` is 1, -1 or 0; the -1 only arises for d < 0, so `fdiv_magic` reads its sign from d
    Some(Magic { m, d, sh: p - 64, add: (d > 0 && m < 0) || (d < 0 && m > 0) })
}
/// elementwise.c:293 `ew_fdiv_magic`: `ew_fdiv(x, g.d)` by the magic.
pub fn fdiv_magic(g: &Magic, x: i64) -> i64 {
    let add = if !g.add { 0 } else if g.d > 0 { x } else { x.wrapping_neg() };
    let mut q = (((g.m as i128 * x as i128) >> 64) as i64).wrapping_add(add) >> g.sh;
    q += ((q as u64) >> 63) as i64;
    let rem = x.wrapping_sub(q.wrapping_mul(g.d));
    q - ((rem ^ g.d) < 0 && rem != 0) as i64
}

// ---- A43: elementwise.c:482-1092 ----
use crate::c::run_map;
use crate::ids::{id_at, ids_bytes, pack, unpack};
use crate::pod::{self, bytes_mut, Lane, Pod};
use crate::sym::sym_msort;
use crate::{BLK, QLEAN_COST_ARITH, QLEAN_COST_COPY, QLEAN_COST_MATH};
use alloc::vec;
use alloc::vec::Vec;

/// `EW_*` codes of elementwise.c:86-100 that this section reads; the two lists cannot change apart.
mod k {
    pub(super) const F32: u8 = 4; pub(super) const BITS: u8 = 6; pub(super) const ABS: u8 = 1;
    pub(super) const ADD: u8 = 0; pub(super) const SUB: u8 = 1; pub(super) const MUL: u8 = 2; pub(super) const DIV: u8 = 3; pub(super) const FILL: u8 = 4;
    pub(super) const LESSER: u8 = 5; pub(super) const GREATER: u8 = 6; pub(super) const IDIV: u8 = 7; pub(super) const IMOD: u8 = 8; pub(super) const POW: u8 = 9;
    pub(super) const EQ: u8 = 0; pub(super) const NE: u8 = 1; pub(super) const LT: u8 = 2; pub(super) const LE: u8 = 3; pub(super) const GT: u8 = 4; pub(super) const GE: u8 = 5;
    pub(super) const VV: u8 = 0; pub(super) const VA: u8 = 1; pub(super) const AV: u8 = 2;
}
/// elementwise.c:436's `#if`: the mask paths exist only where the build enables the instructions they use.
const VEC: bool = cfg!(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw"));
const NAN64: u64 = 0xfff8000000000000;
const PNAN64: u64 = 0x7ff8000000000000;
const NAN32: u32 = 0xffc00000;
const PNAN32: u32 = 0x7fc00000;

/// An integral storage class: `i` is the element as q reads it (zero-extended at `u8`), `wrap` the truncating write.
trait Elt: Lane + Ord { fn i(self) -> i64; }
impl Elt for u8 { fn i(self) -> i64 { self as i64 } }
impl Elt for i16 { fn i(self) -> i64 { self as i64 } }
impl Elt for i32 { fn i(self) -> i64 { self as i64 } }
impl Elt for i64 { fn i(self) -> i64 { self } }

fn ro<T: Pod>(b: &[u8]) -> &[T] {
    pod::cast(b).unwrap_or_else(|| panic!("qlean_ew: a {}-byte payload is not a whole, aligned array of {}-byte elements", b.len(), size_of::<T>()))
}
fn rw<T: Pod>(b: &mut [u8]) -> &mut [T] {
    let n = b.len();
    pod::cast_mut(b).unwrap_or_else(|| panic!("qlean_ew: a {n}-byte output is not a whole, aligned array of {}-byte elements", size_of::<T>()))
}
/// elements `[lo, hi)` of the `w`-byte payload `x`, or its first element when `atom`; the C reads past the end instead.
fn side<'a>(x: &'a [u8], atom: bool, lo: usize, hi: usize, w: usize) -> &'a [u8] {
    let (s, e) = if atom { (0, w) } else { (lo * w, hi * w) };
    x.get(s..e).unwrap_or_else(|| panic!("qlean_ew: elements {}..{} of a {}-byte payload of {w}-byte elements", s / w, e / w, x.len()))
}
/// elementwise.c:1269 `ew_decode_run` (`coc_load_blk_at`): block `b`'s first `cnt` elements, `w` bytes each, into `o`.
pub fn decode_stage(c: &Coc, b: usize, cnt: usize, w: usize, o: &mut [u8]) {
    match w {
        1 => c.decode_blk::<u8>(b, cnt, rw(o)),
        2 => c.decode_blk::<i16>(b, cnt, rw(o)),
        4 => c.decode_blk::<i32>(b, cnt, rw(o)),
        _ => c.decode_blk::<i64>(b, cnt, rw(o)),
    }
}
/// The bytes of `buf` as a block's elements.
fn block<'a>(c: &Coc, b: usize, cnt: usize, w: usize, buf: &'a mut [u64; BLK]) -> &'a [u8] {
    let o = bytes_mut(buf);
    decode_stage(c, b, cnt, w, o);
    o
}

/// elementwise.c:226 `EW_SHAPED`: `o[i] = f(a[ia], b[ib])` with `(ia, ib)` the shape's index pair, an atom a one-element slice.
#[inline(always)]
fn zip2<T: Copy, U: Copy>(shape: u8, a: &[T], b: &[T], o: &mut [U], f: impl Fn(T, T) -> U) {
    if o.is_empty() { return }
    match shape {
        k::VV => for ((o, &x), &y) in o.iter_mut().zip(a).zip(b) { *o = f(x, y) },
        k::VA => { let y = b[0]; for (o, &x) in o.iter_mut().zip(a) { *o = f(x, y) } }
        _ => { let x = a[0]; for (o, &y) in o.iter_mut().zip(b) { *o = f(x, y) } }
    }
}
/// elementwise.c:626 `EW_CMP_SHAPED`: the `m` bits LSB-first, the bits of the last byte above `m` zero.
#[inline(always)]
fn pack_bits(o: &mut [u8], m: usize, ev: impl Fn(usize) -> bool) {
    for (k, byte) in o.iter_mut().enumerate() {
        let (lo, hi) = (k * 8, (k * 8 + 8).min(m));
        *byte = (lo..hi).fold(0u8, |v, i| v | (ev(i) as u8) << (i - lo));
    }
}
/// `pack_bits` of `p(a[ia], b[ib])`, `(ia, ib)` the shape's index pair.
#[inline(always)]
fn pack2<T: Copy>(shape: u8, a: &[T], b: &[T], o: &mut [u8], m: usize, p: impl Fn(T, T) -> bool) {
    if m == 0 { return }
    match shape {
        k::VV => pack_bits(o, m, |i| p(a[i], b[i])),
        k::VA => { let y = b[0]; pack_bits(o, m, |i| p(a[i], y)) }
        _ => { let x = a[0]; pack_bits(o, m, |i| p(x, b[i])) }
    }
}

/// elementwise.c:305 `EW_VAL_INT`: the wrap is the truncation the write does; `&` and `|` need no null test, q's
/// null being the least value of the type.
fn val_int<T: Elt>(op: u8, cls: u8, nul: i64, shape: u8, a: &[T], b: &[T], o: &mut [T]) {
    let nulv = T::wrap(nul as u64);
    let isn = |x: T| x.i() == nul;
    let wrap = |x: T, y: T, f: fn(u64, u64) -> u64| if isn(x) || isn(y) { nulv } else { T::wrap(f(x.i() as u64, y.i() as u64)) };
    match op {
        k::ADD => zip2(shape, a, b, o, |x, y| wrap(x, y, u64::wrapping_add)),
        k::SUB => zip2(shape, a, b, o, |x, y| wrap(x, y, u64::wrapping_sub)),
        k::MUL => zip2(shape, a, b, o, |x, y| wrap(x, y, u64::wrapping_mul)),
        k::FILL => zip2(shape, a, b, o, |x, y| if isn(y) { x } else { y }),
        k::LESSER => zip2(shape, a, b, o, |x, y| if x < y { x } else { y }),
        k::GREATER => zip2(shape, a, b, o, |x, y| if y < x { x } else { y }),
        k::IDIV | k::IMOD => {
            // a constant divisor (elementwise.c:253) takes the multiply-shift form instead of a 64-bit divide
            let g = if shape == k::VA && !o.is_empty() && !isn(b[0]) { magic_of(b[0].i()) } else { None };
            let md = op == k::IMOD;
            let q = |x: i64, y: i64| if md { (x as u64).wrapping_sub((y as u64).wrapping_mul(ew_fdiv(x, y) as u64)) } else { ew_fdiv(x, y) as u64 };
            match g {
                Some(g) => for (o, &x) in o.iter_mut().zip(a) {
                    let x = x.i();
                    *o = if x == nul { nulv } else if md { T::wrap((x as u64).wrapping_sub((g.d as u64).wrapping_mul(fdiv_magic(&g, x) as u64))) } else { T::wrap(fdiv_magic(&g, x) as u64) };
                },
                None => zip2(shape, a, b, o, |x, y| { let (x, y) = (x.i(), y.i()); if x == nul || y == nul || y == 0 { nulv } else { T::wrap(q(x, y)) } }),
            }
        }
        _ => ew_unsupported("qlean_ew_val", op as u32, cls as u32),
    }
}

/// `floor` at double width; `core` has none. A NaN, an infinity, a magnitude from 2^52 and a zero are their own floor.
fn floor64(x: f64) -> f64 {
    if !(x.abs() < 4503599627370496.0) || x == 0.0 { return x }
    let t = x as i64 as f64;
    if t > x { t - 1.0 } else { t }
}
fn floor32(x: f32) -> f32 {
    if !(x.abs() < 8388608.0) || x == 0.0 { return x }
    let t = x as i32 as f32;
    if t > x { t - 1.0 } else { t }
}
fn le64(x: u64, y: u64) -> bool { if f64::from_bits(x).is_nan() { true } else { f64::from_bits(x) <= f64::from_bits(y) } }
fn le32(x: u32, y: u32) -> bool { if f32::from_bits(x).is_nan() { true } else { f32::from_bits(x) <= f32::from_bits(y) } }
fn eq64(x: u64, y: u64) -> bool { if f64::from_bits(x).is_nan() { f64::from_bits(y).is_nan() } else { f64::from_bits(x) == f64::from_bits(y) } }
fn eq32(x: u32, y: u32) -> bool { if f32::from_bits(x).is_nan() { f32::from_bits(y).is_nan() } else { f32::from_bits(x) == f32::from_bits(y) } }
fn tol64(x: u64, y: u64) -> bool { ew_tol(f64::from_bits(x), f64::from_bits(y)) }
fn tol32(_: u32, _: u32) -> bool { false }

/// elementwise.c:366 `EW_VAL_FLT`: a NaN operand is answered before any conversion and comes back as it is, the left
/// one first; the right one of `-` comes back with its sign flipped (q subtracts by negating and adding).
macro_rules! val_flt { ($name:ident, $B:ty, $F:ty, $nanq:expr, $nanp:expr, $ord:ident, $floor:ident, $fnma:ident, $pow:expr) => {
    fn $name(op: u8, cls: u8, shape: u8, a: &[$B], b: &[$B], o: &mut [$B]) {
        let isn = |x: $B| <$F>::from_bits(x).is_nan();
        let (tof, tob) = (<$F>::from_bits, |v: $F| if v.is_nan() { $nanq } else { v.to_bits() });
        match op {
            k::ADD => zip2(shape, a, b, o, |x, y| if isn(x) { x } else if isn(y) { y } else { tob(tof(x) + tof(y)) }),
            k::SUB => zip2(shape, a, b, o, |x, y| if isn(x) { x } else if isn(y) { y ^ ($nanq ^ $nanp) } else { tob(tof(x) - tof(y)) }),
            k::MUL => zip2(shape, a, b, o, |x, y| if isn(x) { x } else if isn(y) { y } else { tob(tof(x) * tof(y)) }),
            k::DIV => zip2(shape, a, b, o, |x, y| if isn(x) { x } else if isn(y) { y } else { tob(tof(x) / tof(y)) }),
            k::FILL => zip2(shape, a, b, o, |x, y| if isn(y) { x } else { y }),
            k::LESSER => zip2(shape, a, b, o, |x, y| if $ord(x, y) > 0 { y } else { x }),
            k::GREATER => zip2(shape, a, b, o, |x, y| if $ord(x, y) < 0 { y } else { x }),
            k::IDIV => zip2(shape, a, b, o, |x, y| {
                let f = $floor(tof(x) / tof(y));
                if isn(x) || isn(y) || ew_outside_long(f as f64) { $nanq } else { tob(f) }
            }),
            k::IMOD => zip2(shape, a, b, o, |x, y| {
                let f = $floor(tof(x) / tof(y));
                if isn(x) || isn(y) { $nanq } else if ew_outside_long(f as f64) { $nanp } else { tob($fnma(tof(x), tof(y), f)) }
            }),
            // elementwise.c `EW_POW`: a NaN operand is `0n`; the power is libm's, at double width (the float class narrows it)
            k::POW => zip2(shape, a, b, o, |x, y| if isn(x) || isn(y) { $nanq } else { tob($pow(tof(x), tof(y))) }),
            _ => ew_unsupported("qlean_ew_val", op as u32, cls as u32),
        }
    }
} }
val_flt!(val_f64, u64, f64, NAN64, PNAN64, ew_ord64, floor64, fnma64, |x: f64, y: f64| crate::c::pow(x, y));
val_flt!(val_f32, u32, f32, NAN32, PNAN32, ew_ord32, floor32, fnma32, |x: f32, y: f32| crate::c::pow(x as f64, y as f64) as f32);
fn fnma64(x: f64, y: f64, f: f64) -> f64 { crate::simd::fnma64(x, y, f) }
fn fnma32(x: f32, y: f32, f: f32) -> f32 { crate::simd::fnma32(x, y, f) }

/// elementwise.c:501 `ew_val_run` over the elements `[lo, hi)` of `a`, `b` (an atom is one element): into `o`.
fn val_slice(op: u8, cls: u8, shape: u8, nul: i64, a: &[u8], b: &[u8], lo: usize, hi: usize, o: &mut [u8]) {
    let w = ew_width(cls as u32);
    let (a, b) = (side(a, shape == k::AV, lo, hi, w), side(b, shape == k::VA, lo, hi, w));
    // the mask path answers the four arithmetic verbs at a float width; every other pair is the loop below
    if VEC && cls >= k::F32 && op <= k::DIV { return crate::simd::ew_val(op, cls, a, b, hi - lo, o) }
    match cls {
        0 => val_int::<u8>(op, cls, nul, shape, ro(a), ro(b), rw(o)),
        1 => val_int::<i16>(op, cls, nul, shape, ro(a), ro(b), rw(o)),
        2 => val_int::<i32>(op, cls, nul, shape, ro(a), ro(b), rw(o)),
        3 => val_int::<i64>(op, cls, nul, shape, ro(a), ro(b), rw(o)),
        4 => val_f32(op, cls, shape, ro(a), ro(b), rw(o)),
        5 => val_f64(op, cls, shape, ro(a), ro(b), rw(o)),
        _ => ew_unsupported("qlean_ew_val", op as u32, cls as u32),
    }
}

/// elementwise.c:501 `ew_val_run` and its entry: `a op b` of class `cls` (`shape` vector/atom) into `out`, `n` long.
pub fn val(run: Runner, op: u8, cls: u8, shape: u8, nul: i64, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    let w = ew_width(cls as u32);
    run_map(run, out, n, w, QLEAN_COST_ARITH, w, &|lo, hi, o| val_slice(op, cls, shape, nul, a, b, lo, hi, o));
}
/// elementwise.c:539 `ew_val_foR_run`: two encoded columns, the answer dense.
pub fn val_enc(run: Runner, op: u8, cls: u8, nul: i64, a: &Coc, b: &Coc, out: &mut [u8]) {
    let (w, n) = (ew_width(cls as u32), a.meta.n);
    run_map(run, out, n, w, QLEAN_COST_ARITH, w, &|lo, hi, o| {
        let (mut xa, mut xb) = ([0u64; BLK], [0u64; BLK]);
        let mut at = lo;
        while at < hi {
            // a slice may start inside a block, so the block is decoded from its own start and entered at `at - blo`
            let (blk, end) = (at / BLK, (at / BLK * BLK + BLK).min(hi));
            let (blo, cnt) = (blk * BLK, end - blk * BLK);
            let (pa, pb) = (block(a, blk, cnt, w, &mut xa), block(b, blk, cnt, w, &mut xb));
            val_slice(op, cls, k::VV, nul, pa, pb, at - blo, cnt, &mut o[(at - lo) * w..(end - lo) * w]);
            at = end;
        }
    });
}
/// elementwise.c:562 `ew_val_foR_atom_run`: an encoded column and an atom.
pub fn val_enc_atom(run: Runner, op: u8, cls: u8, shape: u8, nul: i64, c: &Coc, atom: &[u8], out: &mut [u8]) {
    let (w, n) = (ew_width(cls as u32), c.meta.n);
    run_map(run, out, n, w, QLEAN_COST_ARITH, w, &|lo, hi, o| {
        let mut xv = [0u64; BLK];
        let mut at = lo;
        while at < hi {
            let (blk, end) = (at / BLK, (at / BLK * BLK + BLK).min(hi));
            let (blo, cnt) = (blk * BLK, end - blk * BLK);
            let x = block(c, blk, cnt, w, &mut xv);
            let o = &mut o[(at - lo) * w..(end - lo) * w];
            if shape == k::VA { val_slice(op, cls, shape, nul, x, atom, at - blo, cnt, o) } else { val_slice(op, cls, shape, nul, atom, x, at - blo, cnt, o) }
            at = end;
        }
    });
}

/// elementwise.c:648 `EW_CMP_INT`: no null case, q's null being the least value of the type (a byte and a char compare
/// by their byte).
fn cmp_int<T: Elt>(op: u8, cls: u8, shape: u8, a: &[T], b: &[T], o: &mut [u8], m: usize) {
    match op {
        k::EQ => pack2(shape, a, b, o, m, |x, y| x == y),
        k::NE => pack2(shape, a, b, o, m, |x, y| x != y),
        k::LT => pack2(shape, a, b, o, m, |x, y| x < y),
        k::LE => pack2(shape, a, b, o, m, |x, y| x <= y),
        k::GT => pack2(shape, a, b, o, m, |x, y| x > y),
        k::GE => pack2(shape, a, b, o, m, |x, y| x >= y),
        _ => ew_unsupported("qlean_ew_cmp", op as u32, cls as u32),
    }
}
/// elementwise.c:661 `EW_CMP_FLT`: q's order (a null below everything) with its tolerance, which `<` excludes.
macro_rules! cmp_flt { ($name:ident, $B:ty, $lt:ident, $le:ident, $eq:ident, $tol:ident) => {
    fn $name(op: u8, cls: u8, shape: u8, a: &[$B], b: &[$B], o: &mut [u8], m: usize) {
        match op {
            k::EQ => pack2(shape, a, b, o, m, |x, y| $eq(x, y) || $tol(x, y)),
            k::NE => pack2(shape, a, b, o, m, |x, y| !($eq(x, y) || $tol(x, y))),
            k::LT => pack2(shape, a, b, o, m, |x, y| $lt(x, y) && !$tol(x, y)),
            k::LE => pack2(shape, a, b, o, m, |x, y| $le(x, y) || $tol(x, y)),
            k::GT => pack2(shape, a, b, o, m, |x, y| !($le(x, y) || $tol(x, y))),
            k::GE => pack2(shape, a, b, o, m, |x, y| !($lt(x, y) && !$tol(x, y))),
            _ => ew_unsupported("qlean_ew_cmp", op as u32, cls as u32),
        }
    }
} }
cmp_flt!(cmp_f64, u64, lt64, le64, eq64, tol64);
cmp_flt!(cmp_f32, u32, lt32, le32, eq32, tol32);

/// elementwise.c:820 `ew_cmp_run` over the output bytes `[lo, hi)`: the elements `8 lo ..` of `a`, `b`, `n` in all.
fn cmp_slice(op: u8, cls: u8, shape: u8, a: &[u8], b: &[u8], n: usize, lo: usize, hi: usize, o: &mut [u8]) {
    let w = ew_width(cls as u32);
    let (e0, e1) = (lo * 8, (hi * 8).min(n));
    let (a, b) = (side(a, shape == k::AV, e0, e1, w), side(b, shape == k::VA, e0, e1, w));
    let m = e1 - e0;
    if VEC && op <= k::GE { return crate::simd::ew_cmp(op, cls, a, b, m, o) }
    match cls {
        0 => cmp_int::<u8>(op, cls, shape, ro(a), ro(b), o, m),
        1 => cmp_int::<i16>(op, cls, shape, ro(a), ro(b), o, m),
        2 => cmp_int::<i32>(op, cls, shape, ro(a), ro(b), o, m),
        3 => cmp_int::<i64>(op, cls, shape, ro(a), ro(b), o, m),
        4 => cmp_f32(op, cls, shape, ro(a), ro(b), o, m),
        5 => cmp_f64(op, cls, shape, ro(a), ro(b), o, m),
        _ => ew_unsupported("qlean_ew_cmp", op as u32, cls as u32),
    }
}
/// elementwise.c:820 `ew_cmp_run` and its entry: a byte per comparison.
pub fn cmp(run: Runner, op: u8, cls: u8, shape: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    let nb = n.div_ceil(8);
    // sliced by output byte, so eight elements move together and no two threads share one
    run_map(run, out, nb, 1, QLEAN_COST_ARITH, 8 * ew_width(cls as u32), &|lo, hi, o| cmp_slice(op, cls, shape, a, b, n, lo, hi, o));
}
/// elementwise.c:867 `ew_low_zero_run`: bit `i` is `(a[i] & b[0]) = 0`.
pub fn low_zero(run: Runner, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    let (a, b) = (side(a, false, 0, n, 8), side(b, true, 0, 1, 8));
    run_map(run, out, n.div_ceil(8), 1, QLEAN_COST_ARITH, 64, &|lo, hi, o| {
        let (e0, e1) = (lo * 8, (hi * 8).min(n));
        pack2(k::VA, ro::<u64>(&a[e0 * 8..e1 * 8]), ro::<u64>(b), o, e1 - e0, |x, y| x & y == 0)
    });
}
/// elementwise.c:888 `ew_low_zero_foR_run`: a block with `base = maxv` is one value and is answered from its metadata,
/// any other is restored into a buffer; sliced by output byte, a block's bytes may be split between two slices.
pub fn low_zero_enc(run: Runner, c: &Coc, atom: &[u8], out: &mut [u8]) {
    let (n, m) = (c.meta.n, ro::<u64>(side(atom, true, 0, 1, 8))[0]);
    run_map(run, out, n.div_ceil(8), 1, QLEAN_COST_ARITH, BLK * 8, &|lo, hi, o| {
        let mut xv = [0u64; BLK];
        let mut at = lo;
        while at < hi {
            let (blk, end) = (at / (BLK / 8), ((at / (BLK / 8) + 1) * (BLK / 8)).min(hi));
            let (blo, cnt) = (blk * BLK, (n - blk * BLK).min(BLK));
            let (e0, e1) = (at * 8, (end * 8).min(blo + cnt));
            let o = &mut o[at - lo..end - lo];
            if c.meta.base[blk] == c.meta.maxv[blk] {
                let all = c.meta.base[blk] as u64 & m == 0;
                pack_bits(o, e1 - e0, |_| all);
            } else {
                let x = ro::<u64>(block(c, blk, cnt, 8, &mut xv));
                pack2(k::VA, &x[e0 - blo..e1 - blo], &[m], o, e1 - e0, |x, y| x & y == 0);
            }
            at = end;
        }
    });
}
/// elementwise.c:927 `ew_bitw_run`: `op` is band 0, bor 1, bandnot 2; any other reads as band.
pub fn bitw(run: Runner, op: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    let (a, b) = (ro::<u64>(side(a, false, 0, n, 8)), ro::<u64>(side(b, false, 0, n, 8)));
    run_map(run, out, n, 8, QLEAN_COST_ARITH, 8, &|lo, hi, o| {
        let o = rw::<u64>(o);
        let (a, b) = (&a[lo..hi], &b[lo..hi]);
        match op {
            1 => zip2(k::VV, a, b, o, |x, y| x | y),
            2 => zip2(k::VV, a, b, o, |x, y| x & !y),
            _ => zip2(k::VV, a, b, o, |x, y| x & y),
        }
    });
}
/// elementwise.c:970 `qlean_ew_rank_pair` past the unboxing: each symbol's rank in the merged order of `da`, `db`.
pub fn rank_pair(da: &Syms, db: &Syms, ra: &mut [i32], rb: &mut [i32]) {
    let (na, n) = (da.count(), da.count() + db.count());
    if n == 0 { return }
    let mut v = da.slices(na);
    v.extend(db.slices(db.count()));
    let (mut ord, mut tmp) = ((0..n).collect::<Vec<_>>(), vec![0usize; n]);
    sym_msort(&v, &mut ord, &mut tmp);
    // identical entries land in one group and both sides get the same rank
    let mut r = 0;
    for t in 0..n {
        if t > 0 && v[ord[t - 1]] != v[ord[t]] { r += 1 }
        if ord[t] < na { ra[ord[t]] = r } else { rb[ord[t] - na] = r }
    }
}
/// elementwise.c:1040-1079 `ew_cmp_ids_run`, `ew_eq_ids_run` and their entry: ids at `w` compared through the
/// rank tables `ra`, `rb`; a byte each. Both tables empty is `ew_eq_ids_run`: the ids themselves, only `=` and `<>`.
pub fn eq_ids(run: Runner, op: u8, shape: u8, ia: &[u8], ib: &[u8], w: u32, n: usize, ra: &[i32], rb: &[i32], out: &mut [u8]) {
    let ranked = !(ra.is_empty() && rb.is_empty());
    let (cost, wide) = if ranked { (QLEAN_COST_ARITH, 32) } else { (QLEAN_COST_COPY, 2 * w as usize) };
    run_map(run, out, n.div_ceil(8), 1, cost, wide, &|lo, hi, o| {
        let (e0, m) = (lo * 8, (hi * 8).min(n) - lo * 8);
        let at = |i: usize, atom: bool, p: &[u8]| id_at(p, w, if atom { 0 } else { e0 + i });
        let rank = |t: &[i32], u: usize| t.get(u).copied().unwrap_or(0);
        if !ranked {
            let ne = op == k::NE;
            return pack_bits(o, m, |i| (at(i, shape == k::AV, ia) == at(i, shape == k::VA, ib)) != ne);
        }
        let (x, y) = (|i| rank(ra, at(i, shape == k::AV, ia)), |i| rank(rb, at(i, shape == k::VA, ib)));
        match op {
            k::EQ => pack_bits(o, m, |i| x(i) == y(i)),
            k::NE => pack_bits(o, m, |i| x(i) != y(i)),
            k::LT => pack_bits(o, m, |i| x(i) < y(i)),
            k::LE => pack_bits(o, m, |i| x(i) <= y(i)),
            k::GT => pack_bits(o, m, |i| x(i) > y(i)),
            _ => pack_bits(o, m, |i| x(i) >= y(i)),
        }
    });
}

// ---- A44: elementwise.c:1569-1813 ----
/// `EW_*` codes of elementwise.c:86-100 this section reads (the verbs `k` does not hold).
mod k44 {
    pub(super) const BITS: u32 = 6; pub(super) const F32: u8 = 4; pub(super) const F64: u8 = 5;
    pub(super) const NEG: u8 = 0; pub(super) const ABS: u8 = 1; pub(super) const SQRT: u8 = 2; pub(super) const ATAN: u8 = 10;
    // `EW_BCMP + EW_EQ ..= EW_GE`
    pub(super) const BEQ: u8 = 16; pub(super) const BNE: u8 = 17; pub(super) const BLT: u8 = 18;
    pub(super) const BLE: u8 = 19; pub(super) const BGT: u8 = 20; pub(super) const BGE: u8 = 21;
}
/// elementwise.c:1569 `ew_bit_run` and its entry: bitmap verbs. `out` is the `⌈n / 8⌉` bytes, the bits above `n` zero;
/// an atom operand is one bit, widened to a byte before the loop.
pub fn bit(run: Runner, op: u8, shape: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    let nb = n.div_ceil(8);
    if nb == 0 { return }
    // chosen before the pool starts: a panic inside a worker cannot unwind through the C pool
    let f: fn(u8, u8) -> u8 = match op {
        k::LESSER => |x, y| x & y,
        k::GREATER => |x, y| x | y,
        k::FILL => |_, y| y,
        k44::BEQ => |x, y| !(x ^ y),
        k44::BNE => |x, y| x ^ y,
        k44::BLT => |x, y| !x & y,
        k44::BLE => |x, y| !x | y,
        k44::BGT => |x, y| x & !y,
        k44::BGE => |x, y| x | !y,
        _ => ew_unsupported("qlean_ew_bit", op as u32, k44::BITS),
    };
    assert!(shape == k::AV || a.len() >= nb, "qlean_ew_bit: a {}-byte operand for {n} bits", a.len());
    assert!(shape == k::VA || b.len() >= nb, "qlean_ew_bit: a {}-byte operand for {n} bits", b.len());
    let wide = |x: &[u8]| if x.first().is_some_and(|v| v & 1 == 1) { 0xffu8 } else { 0 };
    let (ac, bc) = (wide(a), wide(b));
    run_map(run, out, nb, 1, QLEAN_COST_COPY, 1, &|lo, hi, o| {
        for (k, ob) in (lo..hi).zip(o) {
            *ob = f(if shape == k::AV { ac } else { a[k] }, if shape == k::VA { bc } else { b[k] });
        }
    });
    // the tail byte belongs to whoever wrote the last slice, so it is cleared here and not in a worker
    if n & 7 != 0 { out[nb - 1] &= ((1u16 << (n & 7)) - 1) as u8 }
}

/// `neg` and `abs` over the class's elements: a null stays itself (q's null is the least value, so `abs` needs no case
/// of its own but shares the loop's shape); `neg` at a float flips the sign bit, `abs` clears it.
fn mon_int<T: Elt>(op: u8, nul: i64, x: &[T], o: &mut [T]) {
    let nulv = T::wrap(nul as u64);
    for (o, &v) in o.iter_mut().zip(x) {
        *o = if v.i() == nul { nulv } else if op == k44::NEG || v.i() < 0 { T::wrap(0u64.wrapping_sub(v.i() as u64)) } else { v };
    }
}
/// elementwise.c:1665 `ew_mon_run` over `x`'s elements into `o` (the same count): the pair was checked by `mon_chk`.
fn mon_slice(op: u8, cls: u8, nul: i64, x: &[u8], o: &mut [u8]) {
    match cls {
        0 => mon_int::<u8>(op, nul, ro(x), rw(o)),
        1 => mon_int::<i16>(op, nul, ro(x), rw(o)),
        2 => mon_int::<i32>(op, nul, ro(x), rw(o)),
        3 => mon_int::<i64>(op, nul, ro(x), rw(o)),
        k44::F32 => for (o, &v) in rw::<u32>(o).iter_mut().zip(ro::<u32>(x)) { *o = if op == k44::NEG { v ^ 0x8000_0000 } else { v & 0x7fff_ffff } },
        _ => for (o, &v) in rw::<u64>(o).iter_mut().zip(ro::<u64>(x)) { *o = if op == k44::NEG { v ^ (1 << 63) } else { v & !(1 << 63) } },
    }
}
/// The nine float maps' answer at `f64`, elementwise.c `EW_MON_MAP`: a NaN operand answers `0n` before libm sees it, and
/// a NaN result is `nanout` (`0n`, except the two arc functions' positive one: measured, `asin 2` and `acos -0w`).
#[inline(always)]
fn mon_map(x: &[u64], o: &mut [u64], nanout: u64, f: impl Fn(f64) -> f64) {
    for (o, &b) in o.iter_mut().zip(x) {
        *o = if f64::from_bits(b).is_nan() { NAN64 } else {
            let y = f(f64::from_bits(b)).to_bits();
            if f64::from_bits(y).is_nan() { nanout } else { y }
        };
    }
}
/// elementwise.c:1039 `ew_mon_run`'s switch, outside the loop: one straight libm loop per map.
fn mon_libm(op: u8, x: &[u8], o: &mut [u8]) {
    use crate::c as m;
    let (x, o) = (ro::<u64>(x), rw::<u64>(o));
    match op {
        2 => mon_map(x, o, NAN64, m::sqrt), 3 => mon_map(x, o, NAN64, m::exp), 4 => mon_map(x, o, NAN64, m::log),
        5 => mon_map(x, o, NAN64, m::sin), 6 => mon_map(x, o, NAN64, m::cos), 7 => mon_map(x, o, NAN64, m::tan),
        8 => mon_map(x, o, PNAN64, m::asin), 9 => mon_map(x, o, PNAN64, m::acos), _ => mon_map(x, o, NAN64, m::atan),
    }
}
/// The pairs `neg`/`abs` answer (the encoded entries read nothing else): the six classes at the two verbs.
fn mon_chk(op: u8, cls: u8) {
    if op > k44::ABS || cls > k44::F64 { ew_unsupported("qlean_ew_mon", op as u32, cls as u32) }
}
/// The nine float maps are `SQRT ..= ATAN` at `f64` alone (q answers a float whatever the argument's type, so the
/// dispatch widens first); any other pair of them is unsupported, as `ew_mon_run`'s `default`.
fn is_libm(op: u8, cls: u8) -> bool { (k44::SQRT..=k44::ATAN).contains(&op) && cls == k44::F64 }
/// elementwise.c:1039 `ew_mon_run` and its entry: the monadic verbs, `neg` and `abs` and the nine libm maps.
pub fn mon(run: Runner, op: u8, cls: u8, nul: i64, x: &[u8], n: usize, out: &mut [u8]) {
    if n == 0 { return }
    let lib = is_libm(op, cls);
    if !lib { mon_chk(op, cls) }
    let w = ew_width(cls as u32);
    // chosen before the pool starts: the cost is the verb's, and a libm call an element is `QLEAN_COST_MATH`
    let cost = if lib { QLEAN_COST_MATH } else { QLEAN_COST_ARITH };
    run_map(run, out, n, w, cost, w, &|lo, hi, o| {
        let x = side(x, false, lo, hi, w);
        if lib { mon_libm(op, x, o) } else { mon_slice(op, cls, nul, x, o) }
    });
}
/// elementwise.c:1708-1765 `ew_mon_foR_run`, `ew_mon_foR_blk`: over an encoded column, the answer dense.
pub fn mon_enc(run: Runner, op: u8, cls: u8, nul: i64, c: &Coc, out: &mut [u8]) {
    let n = c.meta.n;
    if n == 0 { return }
    mon_chk(op, cls);
    let w = ew_width(cls as u32);
    run_map(run, out, n, w, QLEAN_COST_ARITH, w, &|lo, hi, o| {
        let mut xv = [0u64; BLK];
        let mut at = lo;
        while at < hi {
            // a slice may start inside a block, so the block is decoded from its own start and entered at `at - blo`
            let (blk, end) = (at / BLK, (at / BLK * BLK + BLK).min(hi));
            let (blo, cnt) = (blk * BLK, end - blk * BLK);
            let x = block(c, blk, cnt, w, &mut xv);
            mon_slice(op, cls, nul, &x[(at - blo) * w..cnt * w], &mut o[(at - lo) * w..(end - lo) * w]);
            at = end;
        }
    });
}
/// elementwise.c:1743 `ew_mon_fill`: the encoder source of `qlean_coc_ew_mon_enc`. `buf` is the `buf.len()` elements of
/// block `i0 / BLK`, mapped at the class's width and widened back to `i64` (`coc_widen`, which reads any width but 2
/// and 4 as eight bytes).
pub fn mon_fill(op: u8, cls: u8, nul: i64, c: &Coc, buf: &mut [i64], i0: usize) {
    let (nb, w) = (buf.len(), ew_width(cls as u32));
    if nb == 0 { return }
    mon_chk(op, cls);
    let mut xv = [0u64; BLK];
    let x = block(c, i0 / BLK, nb, w, &mut xv);
    if w == 8 { return mon_slice(op, cls, nul, &x[..nb * 8], bytes_mut(buf)) }
    let mut yv = [0u64; BLK];
    let y = bytes_mut(&mut yv);
    mon_slice(op, cls, nul, &x[..nb * w], &mut y[..nb * w]);
    match w {
        2 => for (d, &s) in buf.iter_mut().zip(ro::<i16>(&y[..nb * 2])) { *d = s as i64 },
        4 => for (d, &s) in buf.iter_mut().zip(ro::<i32>(&y[..nb * 4])) { *d = s as i64 },
        _ => for (d, &s) in buf.iter_mut().zip(ro::<u64>(&y[..nb * 8])) { *d = s as i64 },
    }
}
/// elementwise.c:1789 `ew_floor_run`: `floor` at a float class, always a `long`; out of range or a NaN answers `0N`.
pub fn floor(run: Runner, cls: u8, x: &[u8], n: usize, out: &mut [u8]) {
    if n == 0 { return }
    if cls != k44::F32 && cls != k44::F64 { ew_unsupported("qlean_ew_floor", 0, cls as u32) }
    let w = ew_width(cls as u32);
    // the bound is tested on the floored value, exactly as QLean/Eval/Mon.lean's `floorFloats` does
    let long = |v: f64| if v.is_nan() { i64::MIN } else { let f = floor64(v); if ew_outside_long(f) { i64::MIN } else { f as i64 } };
    run_map(run, out, n, 8, QLEAN_COST_ARITH, 8, &|lo, hi, o| {
        let (x, o) = (side(x, false, lo, hi, w), rw::<i64>(o));
        if cls == k44::F32 { for (o, &v) in o.iter_mut().zip(ro::<u32>(x)) { *o = long(f32::from_bits(v) as f64) } }
        else { for (o, &v) in o.iter_mut().zip(ro::<u64>(x)) { *o = long(f64::from_bits(v)) } }
    });
}

// ---- A45: elementwise.c:1469-1610 ----
/// elementwise.c:1469 `ew_cast_clamp`
pub fn cast_clamp(v: i64, lo: i64, hi: i64) -> i64 { if v < lo { lo } else if v > hi { hi } else { v } }
/// elementwise.c:1476 `ew_cast_round`: q's round half away from zero; a value `long` cannot hold saturates (to `-0W`
/// below), and a NaN is the caller's to test first. `core` has no `round`, which would be a libm call anyway.
pub fn cast_round(x: f64) -> i64 {
    // from 2^52 on every double is its own round; below, `a - trunc(a)` is exact, so the half test is too
    let t = if !(x.abs() < 4503599627370496.0) { x } else {
        let a = x.abs();
        let f = a as i64 as f64;
        let r = if a - f >= 0.5 { f + 1.0 } else { f };
        if x < 0.0 { -r } else { r }
    };
    if t <= -9223372036854775808.0 { i64::MIN + 1 } else if t >= 9223372036854775808.0 { i64::MAX } else { t as i64 }
}
/// elementwise.c:1508 `ew_cast_run` and its entry `qlean_ew_cast`: class `src` to class `dst`, every element
/// `Ew.castStep` (the target's clamp or wrap, its null, a float source rounding).
pub fn cast(run: Runner, src: u8, dst: u8, nul_in: i64, x: &[u8], n: usize, out: &mut [u8]) {
    if n == 0 { return }
    if src > k44::F64 || dst > k44::F64 { ew_unsupported("qlean_ew_cast", src as u32, dst as u32) }
    let (sw, dw) = (ew_width(src as u32), ew_width(dst as u32));
    // `Ew.castBounds` and `Ew.castNul`: U8 keeps the whole range and writes 0, its truncating store being the narrowing
    let (lo, hi, nul_out) = match dst {
        1 => (-32767, 32767, i16::MIN as i64),
        2 => (-2147483647, 2147483647, i32::MIN as i64),
        3 => (i64::MIN + 1, i64::MAX, i64::MIN),
        _ => (i64::MIN + 1, i64::MAX, 0),
    };
    // one straight-line pass per (source, target): `ld` reads an element three ways, `em` writes the target's one line
    fn go<S: Pod, D: Pod>(x: &[u8], l: usize, h: usize, o: &mut [u8], ld: impl Fn(S) -> (i64, f64, bool), em: impl Fn(i64, f64, bool) -> D) {
        for (o, &v) in rw::<D>(o).iter_mut().zip(ro::<S>(side(x, false, l, h, size_of::<S>()))) { let (i, d, m) = ld(v); *o = em(i, d, m) }
    }
    fn src_of<D: Pod>(src: u8, nul: i64, x: &[u8], l: usize, h: usize, o: &mut [u8], em: impl Fn(i64, f64, bool) -> D) {
        match src {
            0 => go::<u8, D>(x, l, h, o, |v| (v as i64, v as f64, v as i64 == nul), em),
            1 => go::<i16, D>(x, l, h, o, |v| (v as i64, v as f64, v as i64 == nul), em),
            2 => go::<i32, D>(x, l, h, o, |v| (v as i64, v as f64, v as i64 == nul), em),
            3 => go::<i64, D>(x, l, h, o, |v| (v, v as f64, v == nul), em),
            4 => go::<u32, D>(x, l, h, o, |v| { let f = f32::from_bits(v) as f64; (cast_round(f), f, f.is_nan()) }, em),
            _ => go::<u64, D>(x, l, h, o, |v| { let f = f64::from_bits(v); (cast_round(f), f, f.is_nan()) }, em),
        }
    }
    crate::c::run_map(run, out, n, dw, crate::QLEAN_COST_CAST, sw.max(dw), &|l, h, o: &mut [u8]| match dst {
        5 => src_of::<u64>(src, nul_in, x, l, h, o, |_, d, m| if m { NAN64 } else { d.to_bits() }),
        4 => src_of::<u32>(src, nul_in, x, l, h, o, |_, d, m| if m { NAN32 } else { (d as f32).to_bits() }),
        0 => src_of::<u8>(src, nul_in, x, l, h, o, |i, _, m| (if m { nul_out } else { cast_clamp(i, lo, hi) }) as u8),
        1 => src_of::<i16>(src, nul_in, x, l, h, o, |i, _, m| (if m { nul_out } else { cast_clamp(i, lo, hi) }) as i16),
        2 => src_of::<i32>(src, nul_in, x, l, h, o, |i, _, m| (if m { nul_out } else { cast_clamp(i, lo, hi) }) as i32),
        _ => src_of::<i64>(src, nul_in, x, l, h, o, |i, _, m| if m { nul_out } else { cast_clamp(i, lo, hi) }),
    });
}
/// elementwise.c:1547 `ew_fdiv64`: floor division by a positive divisor.
pub fn fdiv64(a: i64, b: i64) -> i64 { a / b - (a % b < 0) as i64 }
/// `fdiv64` by one of the tick units `U`, each divisor a constant.
#[inline(always)]
fn fdiv_unit(a: i64, u: i64) -> i64 {
    match u { 1000000 => fdiv64(a, 1000000), 1000000000 => fdiv64(a, 1000000000), 60000000000 => fdiv64(a, 60000000000), _ => fdiv64(a, 86400000000000) }
}
/// elementwise.c:1551 `ew_days_of_first`: days from 2000.01.01 to the first of month `m`. Wrapping, as the C is at
/// the extremes of `long`.
pub fn days_of_first(m: i64) -> i64 {
    let (y, mo) = (2000i64.wrapping_add(fdiv64(m, 12)), 1 + m.wrapping_sub(12i64.wrapping_mul(fdiv64(m, 12))));
    let y = if mo <= 2 { y.wrapping_sub(1) } else { y };
    let era = fdiv64(if y >= 0 { y } else { y.wrapping_sub(399) }, 400);
    let yoe = y.wrapping_sub(era.wrapping_mul(400));
    let doy = fdiv64(153 * ((mo + 9) % 12) + 2, 5);
    era.wrapping_mul(146097).wrapping_add(yoe * 365 + fdiv64(yoe, 4) - fdiv64(yoe, 100) + doy).wrapping_sub(730425)
}
/// elementwise.c:1561 `ew_month_of_days`: the month from 2000.01 holding day `d` from 2000.01.01.
pub fn month_of_days(d: i64) -> i64 {
    let z = d.wrapping_add(730425);
    let era = fdiv64(if z >= 0 { z } else { z.wrapping_sub(146096) }, 146097);
    let doe = z.wrapping_sub(era.wrapping_mul(146097));
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let mp = (5 * (doe - (365 * yoe + yoe / 4 - yoe / 100)) + 2) / 153;
    let m = mp + if mp < 10 { 3 } else { -9 };
    era.wrapping_mul(400).wrapping_add(yoe).wrapping_add((m <= 2) as i64).wrapping_mul(12).wrapping_sub(24000).wrapping_add(m - 1)
}
/// elementwise.c:1577 `ew_tick_run`: a temporal operand re-counted in its result's unit (`op` is the source unit's
/// code times 16 plus the target's; `nul_in` the source null, `nul_out` the target's). The nanosecond count is 128 bits
/// and the wrap to the target's width is the store. A source is `i32`, `f64` (days) or else `i64`; a target `f64`,
/// `i32` or else `i64`.
pub fn tick(run: Runner, op: u8, src: u8, dst: u8, nul_in: i64, nul_out: i64, x: &[u8], n: usize, out: &mut [u8]) {
    const U: [i64; 5] = [1, 1000000, 1000000000, 60000000000, 86400000000000];
    let (su, du) = ((op >> 4) as usize, (op & 15) as usize);
    let u = U[if du < 5 { du } else { 4 }];
    let (sw, dw) = (if src == 2 { 4 } else { 8 }, if dst == 2 { 4 } else { 8 });
    let one = |k: usize, x: &[u8]| -> (bool, i128) {
        if src == k44::F64 {
            let f = f64::from_bits(u64::from_le_bytes(x[k * 8..k * 8 + 8].try_into().unwrap()));
            if f.is_nan() { (true, 0) } else { (false, cast_round(f * 86400000000000.0) as i128) }
        } else {
            let v = if src == 2 { i32::from_le_bytes(x[k * 4..k * 4 + 4].try_into().unwrap()) as i64 } else { i64::from_le_bytes(x[k * 8..k * 8 + 8].try_into().unwrap()) };
            let a = if su == 5 { days_of_first(v) as i128 * U[4] as i128 } else { v as i128 * U[if su < 5 { su } else { 4 }] as i128 };
            (v == nul_in, a)
        }
    };
    crate::c::run_map(run, out, n, dw, crate::QLEAN_COST_CAST, sw.max(dw), &|l, h, o: &mut [u8]| {
        let x = side(x, false, l, h, sw);
        for k in 0..h - l {
            let (miss, ns) = one(k, x);
            if dst == k44::F64 {
                rw::<u64>(o)[k] = if miss { nul_out as u64 } else { (ns as f64 / u as f64).to_bits() };
                continue;
            }
            // `u` is one of five constants; a constant divisor is a multiply, where the runtime one is an `idiv` per element
            let mut q = if u == 1 { ns as i64 } else if ns >= i64::MIN as i128 && ns <= i64::MAX as i128 { fdiv_unit(ns as i64, u) } else { (ns / u as i128 - (ns % (u as i128) < 0) as i128) as i64 };
            // a month target: `u` is a day, and the calendar takes the day count the rest of the way
            if du == 5 { q = month_of_days(q) }
            if miss { q = nul_out }
            if dst == 2 { rw::<i32>(o)[k] = q as i32 } else { rw::<i64>(o)[k] = q }
        }
    });
}

#[cfg(test)]
mod a45 {
    use super::*;
    // expected values are the C's comments (elementwise.c "Eval.castAtom ... measured against q 4.1") and its helpers
    #[test] fn round_is_half_away_and_saturates() {
        assert_eq!((cast_round(2.5), cast_round(-2.5), cast_round(0.49999999999999994)), (3, -3, 0));
        assert_eq!((cast_round(1e19), cast_round(-1e19), cast_round(f64::INFINITY)), (i64::MAX, i64::MIN + 1, i64::MAX));
    }
    #[test] fn casts_clamp_at_a_null_target_and_wrap_without() {
        let x: Vec<u8> = [70000.0f64, -32768.0, 300.0, f64::NAN].iter().flat_map(|v| v.to_bits().to_le_bytes()).collect();
        let mut o = [0u8; 8];
        cast(crate::c::qlean_run_c, 5, 1, 0, &x, 4, &mut o);
        assert_eq!([i16::from_le_bytes([o[0], o[1]]), i16::from_le_bytes([o[2], o[3]]), i16::from_le_bytes([o[4], o[5]]), i16::from_le_bytes([o[6], o[7]])],
                   [32767, -32767, 300, i16::MIN]);
        let mut o = [0u8; 4];
        cast(crate::c::qlean_run_c, 5, 0, 0, &x, 4, &mut o);
        assert_eq!(o, [0x70, 0, 0x2c, 0]);
    }
    #[test] fn calendar_round_trips() {
        assert_eq!((fdiv64(-7, 2), days_of_first(0), month_of_days(0), days_of_first(1), days_of_first(-1)), (-4, 0, 0, 31, -31));
        for m in -20000..30000 { assert_eq!(month_of_days(days_of_first(m)), m); assert_eq!(month_of_days(days_of_first(m + 1) - 1), m) }
    }
    #[test] fn tick_counts_a_month_in_days() {
        // su 5 (month) to du 4 (day): months 0, 1, 2 from 2000.01 are 0, 31, 60 days; the null stays the target's
        let x: Vec<u8> = [0i32, 1, 2, i32::MIN].iter().flat_map(|v| v.to_le_bytes()).collect();
        let mut o = [0u8; 32];
        tick(crate::c::qlean_run_c, 5 * 16 + 4, 2, 3, i32::MIN as i64, i64::MIN, &x, 4, &mut o);
        let v: Vec<i64> = o.chunks(8).map(|c| i64::from_le_bytes(c.try_into().unwrap())).collect();
        assert_eq!(v, [0, 31, 60, i64::MIN]);
    }
}

// ---- A46a: elementwise.c:2007-2150 ----
/// elementwise.c:2007 `ew_widen_run`'s refusal: widening goes up to `int`, `long`, `real` or `float`, and a float only to `float`.
fn widen_chk(src: u8, dst: u8) {
    if !matches!(dst, 2..=5) || (dst != 5 && matches!(src, 4 | 5)) { ew_unsupported("qlean_ew_widen", src as u32, dst as u32) }
}
/// elementwise.c:2007 `ew_widen_run` over elements `[lo, hi)` of the whole source `x` (a bit source indexed from its own
/// bit 0, so a slice may start inside a byte) into `o`, the `hi - lo` answers. The pair was checked by `widen_chk`.
fn widen_slice(src: u8, dst: u8, nul_in: i64, nul_out: i64, x: &[u8], lo: usize, hi: usize, o: &mut [u8]) {
    const PNAN64: u64 = 0x7ff8000000000000;
    // the source class is chosen outside the loop, so each pair is its own straight-line pass (elementwise.c:2023)
    fn pass<const W: usize>(src: u8, lo: usize, hi: usize, x: &[u8], o: &mut [u8], f: impl Fn(i64) -> [u8; W]) {
        let os = o.chunks_exact_mut(W);
        match src {
            6 => for (k, c) in os.enumerate() { let i = lo + k; c.copy_from_slice(&f(((x[i >> 3] >> (i & 7)) & 1) as i64)) },
            0 => for (c, &b) in os.zip(&x[lo..hi]) { c.copy_from_slice(&f(b as i64)) },
            1 => for (c, b) in os.zip(x[lo * 2..hi * 2].chunks_exact(2)) { c.copy_from_slice(&f(i16::from_le_bytes([b[0], b[1]]) as i64)) },
            2 => for (c, b) in os.zip(x[lo * 4..hi * 4].chunks_exact(4)) { c.copy_from_slice(&f(i32::from_le_bytes([b[0], b[1], b[2], b[3]]) as i64)) },
            _ => for (c, b) in os.zip(x[lo * 8..hi * 8].chunks_exact(8)) { c.copy_from_slice(&f(i64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]))) },
        }
    }
    match dst {
        2 => pass(src, lo, hi, x, o, |v| (if v == nul_in { nul_out } else { v } as i32).to_le_bytes()),
        3 => pass(src, lo, hi, x, o, |v| (if v == nul_in { nul_out } else { v }).to_le_bytes()),
        4 => pass(src, lo, hi, x, o, |v| (if v == nul_in { nul_out as u32 } else { (v as f32).to_bits() }).to_le_bytes()),
        _ if src == 4 => for (c, b) in o.chunks_exact_mut(8).zip(x[lo * 4..hi * 4].chunks_exact(4)) {
            let f = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
            // a real null is q's `0n` at double width, the sign kept (elementwise.c:2070)
            let r = if f32::from_bits(f).is_nan() { ((f >> 31) as u64) << 63 | PNAN64 } else { (f32::from_bits(f) as f64).to_bits() };
            c.copy_from_slice(&r.to_le_bytes())
        },
        _ if src == 5 => o.copy_from_slice(&x[lo * 8..hi * 8]),
        _ => pass(src, lo, hi, x, o, |v| (if v == nul_in { nul_out as u64 } else { (v as f64).to_bits() }).to_le_bytes()),
    }
}
/// elementwise.c:2007 `ew_widen_run` and its entry: class `src` widened to `dst`, nulls mapped.
pub fn widen(run: Runner, src: u8, dst: u8, nul_in: i64, nul_out: i64, x: &[u8], n: usize, out: &mut [u8]) {
    if n > 0 { widen_chk(src, dst) }
    let w = if matches!(dst, 2..=5) { ew_width(dst as u32) } else { 1 };
    crate::c::run_map(run, out, n, w, crate::QLEAN_COST_COPY, w, &|lo, hi, o: &mut [u8]| widen_slice(src, dst, nul_in, nul_out, x, lo, hi, o));
}
/// elementwise.c:1214 `ew_widen_stage`: elements `[lo, hi)` of a chain tile (or of a column of one stage) of `n`
/// elements, on the calling thread. A bit source may be cut inside a byte; `widen_slice` indexes bits from the tile's own.
pub fn widen_stage(src: u8, dst: u8, nul_in: i64, nul_out: i64, x: &[u8], lo: usize, hi: usize, out: &mut [u8]) {
    if lo == hi { return }
    widen_chk(src, dst);
    widen_slice(src, dst, nul_in, nul_out, x, lo, hi, &mut out[lo * ew_width(dst as u32)..hi * ew_width(dst as u32)])
}

#[cfg(test)]
mod a46a {
    use super::*;
    #[test] fn widen_nulls_and_floats() {
        let x: Vec<u8> = [i16::MIN, 5, -7].iter().flat_map(|v| v.to_le_bytes()).collect();
        let mut o = [0u8; 24];
        widen(crate::c::qlean_run_c, 1, 3, i16::MIN as i64, i64::MIN, &x, 3, &mut o);
        assert_eq!(&o[..8], &i64::MIN.to_le_bytes());
        assert_eq!(&o[8..16], &5i64.to_le_bytes());
        let f: Vec<u8> = [0xffc00000u32, 0x3f800000].iter().flat_map(|v| v.to_le_bytes()).collect();
        let mut o = [0u8; 16];
        widen(crate::c::qlean_run_c, 4, 5, 0, 0, &f, 2, &mut o);
        assert_eq!(u64::from_le_bytes(o[..8].try_into().unwrap()), 0xfff8000000000000);
        assert_eq!(u64::from_le_bytes(o[8..].try_into().unwrap()), 1f64.to_bits());
    }
}

// ---- A46b: elementwise.c:2150-2310 (the stage workers stay C until `c::run_chain` calls Rust ones) ----
/// elementwise.c:2242 `ew_stage_bits`: a stage's bits per element of `a`, `b`, `o`; answers the cost.
pub fn stage_bits(engine: u32, op: u32, cls: u32, shape: u32) -> (u32, u16, u16, u16) {
    use crate::{QLEAN_COST_ARITH as ARITH, QLEAN_COST_CAST as CAST, QLEAN_COST_COPY as COPY, QLEAN_COST_MATH as MATH};
    let bits = |c: u32| (8 * ew_width(c)) as u16;
    match engine {
        eng::VAL => (if op == k::POW as u32 { MATH } else { ARITH }, bits(cls), bits(cls), bits(cls)),
        eng::CMP => (ARITH, bits(cls), bits(cls), 1),
        eng::MON => (if op > k::ABS as u32 { MATH } else { ARITH }, bits(cls), 0, bits(cls)),
        eng::WIDEN => (COPY, if cls == k::BITS as u32 { 1 } else { bits(cls) }, 0, bits(shape)),
        eng::BIT => (COPY, 1, 1, 1),
        eng::FLOOR => (ARITH, bits(cls), 0, 64),
        eng::CAST | eng::TICK => (CAST, bits(cls), 0, bits(shape)),
        eng::IDS => (COPY, shape as u16, 0, bits(cls)),
        eng::PACK => (COPY, bits(cls), 0, shape as u16),
        // an ALP block costs a division an element on top of the unpack, which a Frame-of-Reference block does not
        eng::ALP => (ARITH, 0, 0, bits(cls)),
        // both encoder stages read the tile and answer no payload: what they write is the `coc` at `p.o`
        eng::ENCMETA | eng::ENCPACK => (ARITH, bits(cls), 0, 0),
        _ => (COPY, 0, 0, bits(cls)),
    }
}
/// elementwise.c:2294 `ew_stage_fixed`: operand `left` of the stage is not re-based per tile.
pub fn stage_fixed(engine: u32, shape: u32, left: bool) -> bool {
    if engine == eng::DECODE || engine == eng::ALP { return true }
    if !matches!(engine, eng::VAL | eng::CMP | eng::BIT) { return !left }
    if left { shape == k::AV as u32 } else { shape == k::VA as u32 }
}
/// elementwise.c:2150's engine codes, the `Ew.Engine` constants of QLean/Kernel/Elementwise.lean.
mod eng {
    pub(super) const VAL: u32 = 0; pub(super) const CMP: u32 = 1; pub(super) const MON: u32 = 2; pub(super) const WIDEN: u32 = 3;
    pub(super) const BIT: u32 = 4; pub(super) const FLOOR: u32 = 5; pub(super) const CAST: u32 = 6; pub(super) const DECODE: u32 = 7;
    pub(super) const ALP: u32 = 8; pub(super) const ENCMETA: u32 = 9; pub(super) const ENCPACK: u32 = 10; pub(super) const TICK: u32 = 11;
    pub(super) const IDS: u32 = 12; pub(super) const PACK: u32 = 13;
}

// ---- K9: the chain's tile workers over a packed id column (elementwise.c:1288 `ew_ids_run`, :1315 `ew_pack_run`) ----
/// Bytes of `n` ids at `w` bits as the two stages see them: a width the table does not list is the 64-bit lane, as in
/// `IDS_WIDTHS`' `default`.
pub fn ids_len(n: usize, w: u32) -> usize {
    match w { 0 => 0, 1 | 2 | 4 => ids_bytes(n, w), 8 => n, 16 => 2 * n, 32 => 4 * n, _ => 8 * n }
}
/// elementwise.c:1288 `ew_ids_run`: ids `[lo, hi)` of the packed payload `x` (`w` bits each) written into `o` at class
/// `cls`'s width. A sub-byte slice may start inside a word, so its ragged head goes id by id and the rest is `ids::unpack`.
pub fn ids_stage(cls: u8, w: u32, x: &[u8], lo: usize, hi: usize, o: &mut [u8]) {
    #[inline(always)]
    fn go<const W: u32, T: Lane>(x: &[u8], lo: usize, hi: usize, o: &mut [T]) {
        let mut i = lo;
        if W != 0 && W < 8 { while i < hi && i % (64 / W as usize) != 0 { o[i] = T::wrap(id_at(x, W, i) as u64); i += 1 } }
        // `i` is a whole word in (or the lane width makes it a whole id), so the byte it starts at is exact
        let at = i * W as usize / 8;
        unpack::<W, T>(&x[at..], &mut o[i..hi], |_, e, v| *e = T::wrap(v as u64));
    }
    #[inline(always)]
    fn by_w<T: Lane>(w: u32, x: &[u8], lo: usize, hi: usize, o: &mut [T]) {
        match w {
            0 => go::<0, T>(x, lo, hi, o), 1 => go::<1, T>(x, lo, hi, o), 2 => go::<2, T>(x, lo, hi, o),
            4 => go::<4, T>(x, lo, hi, o), 8 => go::<8, T>(x, lo, hi, o), 16 => go::<16, T>(x, lo, hi, o),
            32 => go::<32, T>(x, lo, hi, o), _ => go::<64, T>(x, lo, hi, o),
        }
    }
    match ew_width(cls as u32) {
        1 => by_w::<u8>(w, x, lo, hi, rw(o)),
        2 => by_w::<i16>(w, x, lo, hi, rw(o)),
        4 => by_w::<i32>(w, x, lo, hi, rw(o)),
        _ => by_w::<i64>(w, x, lo, hi, rw(o)),
    }
}
/// elementwise.c:1315 `ew_pack_run`: the `n` elements of `x` (class `cls`, zero-extended) written as `w`-bit ids. Below a
/// byte `[lo, hi)` are output bytes, each built in a register, so no two slices share a byte and the last byte's fields
/// past `n` stay zero; at a byte and up they are elements. `o` is `ids_len(n, w)` bytes.
pub fn pack_stage(cls: u8, w: u32, x: &[u8], n: usize, lo: usize, hi: usize, o: &mut [u8]) {
    fn go<T: Pod + Into<u64>>(w: u32, x: &[u8], n: usize, lo: usize, hi: usize, o: &mut [u8]) {
        let x = ro::<T>(x);
        if matches!(w, 1 | 2 | 4) {
            let per = 8 / w as usize;
            pack(&mut o[lo..hi], w, n.saturating_sub(lo * per).min((hi - lo) * per), |i| x[lo * per + i].into())
        } else {
            let k = match w { 0 => 0, 8 => 1, 16 => 2, 32 => 4, _ => 8 };
            pack(&mut o[lo * k..hi * k], k as u32 * 8, hi - lo, |i| x[lo + i].into())
        }
    }
    match ew_width(cls as u32) {
        1 => go::<u8>(w, x, n, lo, hi, o),
        2 => go::<u16>(w, x, n, lo, hi, o),
        4 => go::<u32>(w, x, n, lo, hi, o),
        _ => go::<u64>(w, x, n, lo, hi, o),
    }
}

#[cfg(test)]
mod a46b {
    use super::*;
    // expected values are elementwise.c's `ew_stage_bits` / `ew_stage_fixed` read off the C switch
    #[test] fn stage_costs_and_widths() {
        use crate::{QLEAN_COST_ARITH as A, QLEAN_COST_COPY as C, QLEAN_COST_MATH as M};
        assert_eq!(stage_bits(eng::VAL, k::POW as u32, 5, 0), (M, 64, 64, 64));
        assert_eq!(stage_bits(eng::VAL, k::ADD as u32, 0, 0), (A, 8, 8, 8));
        assert_eq!(stage_bits(eng::CMP, 0, 3, 0), (A, 64, 64, 1));
        assert_eq!(stage_bits(eng::WIDEN, 0, 6, 3), (C, 1, 0, 64));
        assert_eq!(stage_bits(eng::WIDEN, 0, 1, 2), (C, 16, 0, 32));
        assert_eq!(stage_bits(eng::BIT, 0, 0, 0), (C, 1, 1, 1));
        assert_eq!(stage_bits(eng::PACK, 0, 3, 2), (C, 64, 0, 2));
        assert_eq!(stage_bits(eng::ENCMETA, 0, 2, 0), (A, 32, 0, 0));
        assert_eq!(stage_bits(eng::DECODE, 0, 2, 0), (C, 0, 0, 32));
    }
    #[test] fn atoms_and_encoded_views_are_not_rebased() {
        assert!(stage_fixed(eng::VAL, k::AV as u32, true) && !stage_fixed(eng::VAL, k::AV as u32, false));
        assert!(stage_fixed(eng::CMP, k::VA as u32, false) && !stage_fixed(eng::CMP, k::VV as u32, true));
        assert!(stage_fixed(eng::DECODE, 0, true) && stage_fixed(eng::ALP, 0, false));
        // a monadic engine has no left atom, and its right side is always fixed
        assert!(!stage_fixed(eng::MON, 0, true) && stage_fixed(eng::MON, 0, false));
    }
}

#[cfg(test)]
mod a42 {
    use super::*;
    fn h(s: &str) -> u64 { u64::from_str_radix(s, 16).unwrap() }
    /// Replays vectors dumped by elementwise.c's own bodies (testdata/ew_a42.vec); `EW_A42_VEC` names a bigger dump.
    fn replay(text: &str) -> usize {
        let mut gm: Option<Magic> = None;
        let mut n = 0;
        for l in text.lines() {
            let f: Vec<&str> = l.split(' ').collect();
            match f[0] {
                "w" => assert_eq!(ew_width(f[1].parse().unwrap()), f[2].parse::<usize>().unwrap(), "{l}"),
                "tol" => assert_eq!(ew_tol(f64::from_bits(h(f[1])), f64::from_bits(h(f[2]))), f[3] == "1", "{l}"),
                "ord64" => assert_eq!(ew_ord64(h(f[1]), h(f[2])), f[3].parse::<i32>().unwrap(), "{l}"),
                "ord32" => assert_eq!(ew_ord32(h(f[1]) as u32, h(f[2]) as u32), f[3].parse::<i32>().unwrap(), "{l}"),
                "out" => assert_eq!(ew_outside_long(f64::from_bits(h(f[1]))), f[2] == "1", "{l}"),
                "fdiv" => assert_eq!(ew_fdiv(h(f[1]) as i64, h(f[2]) as i64), h(f[3]) as i64, "{l}"),
                "magic" => {
                    let d = h(f[1]) as i64;
                    gm = magic_of(d);
                    // C's add is 1, -1 or 0: nonzero is `add`, its sign follows d
                    let want = (f[2] == "1").then(|| Magic { m: h(f[3]) as i64, d, sh: f[4].parse().unwrap(), add: f[5] != "0" });
                    assert_eq!(gm, want, "{l}");
                    if let (Some(g), Some(_)) = (gm, want) { assert_eq!(g.add, f[5] != "0"); assert!(f[5] != "-1" || d < 0); }
                }
                "fm" => assert_eq!(fdiv_magic(&gm.unwrap(), h(f[2]) as i64), h(f[3]) as i64, "{l}"),
                k => panic!("unknown vector {k}"),
            }
            n += 1;
        }
        n
    }
    #[test] fn vectors() { assert!(replay(include_str!("../testdata/ew_a42.vec")) > 1000); }
    #[test] fn big() { if let Ok(p) = std::env::var("EW_A42_VEC") { println!("{} vectors", replay(&std::fs::read_to_string(p).unwrap())); } }
    #[test] #[should_panic(expected = "storage class 6 has no dense element width")] fn width_bits() { ew_width(6); }
    #[test] #[should_panic(expected = "qlean_ew_val: no case for verb 9 at storage class 0. The dispatch")] fn unsupported() { ew_unsupported("qlean_ew_val", 9, 0); }
    #[test] fn named() {
        assert_eq!((ew_fdiv(-7, 2), ew_fdiv(7, -2), ew_fdiv(-7, -2), ew_fdiv(i64::MIN, -1)), (-4, -4, 3, i64::MIN));
        assert_eq!(magic_of(1), None); assert_eq!(magic_of(-1), None); assert_eq!(magic_of(0), None);
        assert!(ew_outside_long(9.3e18) && !ew_outside_long(9.2e18) && ew_outside_long(-9223372036854775808.0));
    }
}

#[cfg(test)]
mod tests43 {
    use super::*;
    use crate::c::qlean_run_c;
    use crate::coc::Meta;
    use crate::pod::bytes_mut;
    use std::vec::Vec;

    fn by<T: Pod>(v: &mut [T]) -> &[u8] { bytes_mut(v) }
    fn run_val<T: Pod>(op: u8, cls: u8, shape: u8, nul: i64, a: &mut [T], b: &mut [T], n: usize) -> Vec<u64> {
        let mut o = vec![0u64; n];
        val(qlean_run_c, op, cls, shape, nul, by(a), by(b), n, bytes_mut(&mut o[..]));
        o
    }
    // expected values below are the C worker's (`ew_val_run`, `ew_cmp_run` of a43be95) answers on the same inputs
    #[test] fn floored_division_and_remainder() {
        let mut a = [-7i64, 7, 0, i64::MIN, i64::MAX];
        let n = i64::MIN;
        assert_eq!(run_val(7, 3, k::VA, n, &mut a, &mut [2i64], 5), [0xfffffffffffffffc, 3, 0, 1 << 63, 0x3fffffffffffffff]);
        assert_eq!(run_val(7, 3, k::VA, n, &mut a, &mut [-2i64], 5), [3, 0xfffffffffffffffc, 0, 1 << 63, 0xc000000000000000]);
        assert_eq!(run_val(8, 3, k::VA, n, &mut a, &mut [7i64], 5), [0, 0, 0, 1 << 63, 0]);
        assert_eq!(run_val(7, 3, k::VA, n, &mut a, &mut [0i64], 5), [1 << 63; 5]);
    }
    #[test] fn byte_wraps_and_never_meets_its_null() {
        let mut a = [250u8, 3, 255, 100];
        let mut o = [0u8; 4];
        val(qlean_run_c, k::ADD, 0, k::VA, 256, by(&mut a), &[10], 4, &mut o);
        assert_eq!(o, [4, 0xd, 9, 0x6e]);
        val(qlean_run_c, k::MUL, 0, k::VA, 256, by(&mut a), &[10], 4, &mut o);
        assert_eq!(o, [0xc4, 0x1e, 0xf6, 0xe8]);
    }
    #[test] fn float_nulls_come_back_as_they_are_and_the_right_one_of_minus_flips() {
        let mut f = [0xfff8000000000000u64, 0x3ff0000000000000, 0x43f0000000000000, 0x4015800000000000, 0xc015800000000000, 0x7e37e43c8800759c];
        let (mut one, mut two) = ([0x3ff0000000000000u64], [0x4000000000000000u64]);
        assert_eq!(run_val(k::SUB, 5, k::AV, 0, &mut one, &mut f, 6),
                   [0x7ff8000000000000, 0, 0xc3f0000000000000, 0xc011800000000000, 0x4019800000000000, 0xfe37e43c8800759c]);
        assert_eq!(run_val(k::ADD, 5, k::VA, 0, &mut f, &mut one, 6),
                   [0xfff8000000000000, 0x4000000000000000, 0x43f0000000000000, 0x4019800000000000, 0xc011800000000000, 0x7e37e43c8800759c]);
        // a quotient outside q's long is a null, and `mod` of it the other one
        assert_eq!(run_val(k::IDIV, 5, k::VA, 0, &mut f, &mut one, 6),
                   [0xfff8000000000000, 0x3ff0000000000000, 0xfff8000000000000, 0x4014000000000000, 0xc018000000000000, 0xfff8000000000000]);
        assert_eq!(run_val(k::IMOD, 5, k::VA, 0, &mut f, &mut two, 6),
                   [0xfff8000000000000, 0x3ff0000000000000, 0x7ff8000000000000, 0x3ff6000000000000, 0x3fe4000000000000, 0x7ff8000000000000]);
    }
    // `pow` (libm) at both float widths, the f32 one computed at double width and narrowed; a NaN operand is `0n`
    #[test] fn pow_through_libm() {
        let (mut x, mut y) = ([2.0f64.to_bits(), f64::NAN.to_bits(), 4.0f64.to_bits()], [10.0f64.to_bits(), 1.0f64.to_bits(), 0.5f64.to_bits()]);
        assert_eq!(run_val(k::POW, 5, k::VV, 0, &mut x, &mut y, 3), [0x4090000000000000, 0xfff8000000000000, 0x4000000000000000]);
        let (mut x, mut y) = ([2.0f32.to_bits(), f32::NAN.to_bits()], [10.0f32.to_bits(), 1.0f32.to_bits()]);
        let mut o = [0u32; 2];
        val(qlean_run_c, k::POW, 4, k::VV, 0, by(&mut x), by(&mut y), 2, bytes_mut(&mut o[..]));
        assert_eq!(o, [1024.0f32.to_bits(), 0xffc00000]);
    }
    fn run_cmp<T: Pod>(op: u8, cls: u8, shape: u8, a: &mut [T], b: &mut [T], n: usize) -> Vec<u8> {
        let mut o = vec![0xABu8; n.div_ceil(8)];
        cmp(qlean_run_c, op, cls, shape, by(a), by(b), n, &mut o);
        o
    }
    #[test] fn comparisons_pack_lsb_first_with_zero_tail() {
        let mut t = [0x3ff0000000000000u64, 0x3ff0000000000001, 0x3ff00000000fffff, 0xfff8000000000000];
        assert_eq!(run_cmp(k::EQ, 5, k::VA, &mut t, &mut [0x3ff0000000000000u64], 4), [0x03]);
        assert_eq!(run_cmp(k::LT, 5, k::VA, &mut t, &mut [0x3ff0000000000000u64], 4), [0x08]);
        let mut u = t;
        assert_eq!(run_cmp(k::LE, 5, k::VV, &mut t, &mut u, 4), [0x0f]);
        let mut i: [i32; 11] = core::array::from_fn(|k| k as i32 + 1);
        assert_eq!(run_cmp(k::LT, 2, k::VA, &mut i, &mut [3i32], 11), [0x03, 0x00]);
        assert_eq!(run_cmp(k::GE, 2, k::AV, &mut [3i32], &mut i, 11), [0x07, 0x00]);
        // the tail past `n` stays zero whatever the verb answers there
        assert_eq!(run_cmp(k::NE, 0, k::VA, &mut [1u8; 9], &mut [0u8], 9), [0xff, 0x01]);
    }
    #[test] fn bitwise_and_low_zero() {
        let (mut a, mut b) = ([0b1100u64, !0, 5, 0, 9], [0b1010u64; 5]);
        let mut o = [0u64; 5];
        for (op, want) in [(0u8, [0b1000u64, 0b1010, 0, 0, 8]), (1, [0b1110, !0, 0b1111, 0b1010, 0b1011]), (2, [0b0100, !0b1010, 5, 0, 1]), (7, [0b1000, 0b1010, 0, 0, 8])] {
            bitw(qlean_run_c, op, by(&mut a), by(&mut b), 5, bytes_mut(&mut o));
            assert_eq!(o, want, "op {op}");
        }
        let mut z = vec![0xABu8; 1];
        low_zero(qlean_run_c, by(&mut a), by(&mut [0b0001u64]), 5, &mut z);
        assert_eq!(z, [0b01001]);
    }
    /// three blocks of 1024 longs and a tail of 452: block 0 and 2 at 8-bit residuals, block 1 constant
    fn coc_data() -> (Vec<u8>, Vec<i64>, Vec<u64>, Vec<u64>, Vec<i64>) {
        let (mut s, mut pack) = (0x9e3779b97f4a7c15u64, vec![]);
        let mut next = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        for _ in 0..2048 { pack.push(next() as u8) }
        (pack, vec![-1000, 77, 1 << 40], vec![0, 1024, 1024], vec![0; 3], vec![0, 0, 0])
    }
    #[test] fn encoded_operands_equal_their_decodes() {
        let n = 2 * BLK + 452;
        let (pack, base, off, _, bsum) = coc_data();
        let (maxv, width) = (vec![base[0] + 255, 77, base[2] + 255], [8u8, 0, 8]);
        let meta = Meta { base: &base, maxv: &maxv, off: &off, bsum: &bsum, width: &width, sumnul: 0, sumn: 0, n, nblk: 3, mblk: 3 };
        let c = Coc { meta, pack: &pack, exc: None, fdelta: None };
        let mut dense = vec![0i64; 3 * BLK];
        for b in 0..3 { c.decode_blk::<i64>(b, if b < 2 { BLK } else { 452 }, &mut dense[b * BLK..]) }
        let mut other: Vec<i64> = (0..n as i64).map(|i| i * 3 - 2000).collect();
        let mut ds = dense[..n].to_vec();
        let mut o = vec![0u64; n];
        val_enc(qlean_run_c, k::ADD, 3, i64::MIN, &c, &c, bytes_mut(&mut o));
        assert_eq!(o, run_val(k::ADD, 3, k::VV, i64::MIN, &mut ds, &mut dense[..n].to_vec(), n));
        for (shape, op) in [(k::VA, k::SUB), (k::AV, k::MUL), (k::VA, k::IDIV)] {
            let mut atom = [7i64];
            let want = if shape == k::VA { run_val(op, 3, shape, i64::MIN, &mut ds, &mut atom, n) } else { run_val(op, 3, shape, i64::MIN, &mut atom, &mut ds, n) };
            val_enc_atom(qlean_run_c, op, 3, shape, i64::MIN, &c, by(&mut atom), bytes_mut(&mut o));
            assert_eq!(o, want, "shape {shape} op {op}");
        }
        for m in [0u64, 0xff, 1 << 40, 77, 1] {
            let mut want = vec![0u8; n.div_ceil(8)];
            let mut got = vec![0xABu8; n.div_ceil(8)];
            let mut me = [m];
            let _ = &mut other;
            low_zero(qlean_run_c, by(&mut ds), by(&mut me), n, &mut want);
            low_zero_enc(qlean_run_c, &c, by(&mut me), &mut got);
            assert_eq!(got, want, "mask {m:#x}");
        }
    }
    fn syms(ss: &[&[u8]]) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (vec![], vec![1]);
        for s in ss { b.extend_from_slice(s); b.push(0); o.push(b.len() << 1 | 1) }
        (b, o)
    }
    #[test] fn ranks_in_the_merged_distinct_order_and_ids_through_them() {
        let ((ba, oa), (bb, ob)) = (syms(&[b"b", b"a", b"b"]), syms(&[b"c", b"a", b"", b"b"]));
        let (da, db) = (Syms { blob: &ba, offs: &oa }, Syms { blob: &bb, offs: &ob });
        let (mut ra, mut rb) = (vec![9; 3], vec![9; 4]);
        rank_pair(&da, &db, &mut ra, &mut rb);
        assert_eq!((ra.as_slice(), rb.as_slice()), (&[2, 1, 2][..], &[3, 1, 0, 2][..]));
        // ids at 2 bits, four to a byte: 0 1 2 3 0 | 3 2 1 0 3
        let (ia, ib) = ([0b11100100u8, 0b00000000], [0b00011011u8, 0b00000011]);
        let mut o = [0xABu8; 1];
        eq_ids(qlean_run_c, k::EQ, k::VV, &ia, &ib, 2, 5, &[], &[], &mut o);
        assert_eq!(o, [0b00000000]);
        eq_ids(qlean_run_c, k::NE, k::VV, &ia, &ib, 2, 5, &[], &[], &mut o);
        assert_eq!(o, [0b11111]);
        // ranks: ra = [2, 1, 2] for ids 0..2, past the table reads 0; rb = [3, 1, 0, 2]
        eq_ids(qlean_run_c, k::LT, k::VV, &ia, &ib, 2, 5, &ra, &rb, &mut o);
        assert_eq!(o, [0b01000]);
        eq_ids(qlean_run_c, k::GE, k::VV, &ia, &ib, 2, 5, &ra, &rb, &mut o);
        assert_eq!(o, [0b10111]);
        eq_ids(qlean_run_c, k::EQ, k::VA, &ia, &[0b10], 2, 5, &[], &[], &mut o);
        assert_eq!(o, [0b00100]);
    }
}

#[cfg(test)]
mod tests44 {
    use super::*;
    use crate::c::qlean_run_c;
    use crate::coc::Meta;
    use std::vec::Vec;

    fn hex(s: &str) -> Vec<u8> { (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect() }
    fn mon_of(op: u8, cls: u8, nul: i64, x: &[u8], n: usize) -> Vec<u8> {
        let mut o = vec![0u8; n * ew_width(cls as u32)];
        mon(qlean_run_c, op, cls, nul, x, n, &mut o);
        o
    }
    #[test] fn neg_abs_edges() {
        // null stays null; the wrapping minimum of the class is its own negation
        assert_eq!(mon_of(0, 3, i64::MIN, &i64::MIN.to_ne_bytes(), 1), i64::MIN.to_ne_bytes());
        assert_eq!(mon_of(1, 3, i64::MIN, &(i64::MIN + 1).to_ne_bytes(), 1), i64::MAX.to_ne_bytes());
        assert_eq!(mon_of(0, 1, -32768, &(-32768i16).to_ne_bytes(), 1), (-32768i16).to_ne_bytes());
        assert_eq!(mon_of(0, 0, 256, &[0, 1, 255], 3), [0, 255, 1]);
        assert_eq!(mon_of(0, 5, 0, &0f64.to_bits().to_ne_bytes(), 1), (-0f64).to_bits().to_ne_bytes());
        assert_eq!(mon_of(1, 5, 0, &(-0f64).to_bits().to_ne_bytes(), 1), 0f64.to_bits().to_ne_bytes());
        assert_eq!(mon_of(0, 4, 0, &1.5f32.to_bits().to_ne_bytes(), 1), (-1.5f32).to_bits().to_ne_bytes());
    }
    #[test] fn floor_bounds() {
        let x: Vec<u8> = [9.3e18f64, f64::INFINITY, f64::NAN, -2.5, 9.2e18, -9.3e18].iter().flat_map(|v| v.to_bits().to_ne_bytes()).collect();
        let mut o = vec![0u8; 48];
        floor(qlean_run_c, 5, &x, 6, &mut o);
        let r: Vec<i64> = o.chunks(8).map(|c| i64::from_ne_bytes(c.try_into().unwrap())).collect();
        assert_eq!(r, [i64::MIN, i64::MIN, i64::MIN, -3, 9_200_000_000_000_000_000, i64::MIN]);
    }
    #[test] fn bit_tail_is_masked() {
        let mut o = [0xabu8; 2];
        bit(qlean_run_c, 16 + 5, 1, &[0, 0], &[0], 11, &mut o); // not-zero by `>=` against a zero atom: all ones
        assert_eq!(o, [0xff, 0x07]);
    }
    /// the vectors `/data/tmp/qrs/A44/drv` dumps from the C of 78a5c06; run with EW_A44_VEC=<file> --ignored
    #[test] #[ignore] fn diff44() {
        let path = std::env::var("EW_A44_VEC").expect("EW_A44_VEC: the file `drv N file` wrote");
        let (mut cnt, mut bad) = (0, 0);
        for l in std::fs::read_to_string(path).unwrap().lines() {
            let f: Vec<&str> = l.split(' ').collect();
            let num = |i: usize| f[i].parse::<i64>().unwrap();
            match f[0] {
                "mon" => {
                    let (op, cls, nul, n) = (num(1) as u8, num(2) as u8, num(3), num(4) as usize);
                    if mon_of(op, cls, nul, &hex(f[5]), n) != hex(f[6]) { bad += 1 }
                }
                "floor" => {
                    let (cls, n) = (num(2) as u8, num(4) as usize);
                    let mut o = vec![0u8; n * 8];
                    floor(qlean_run_c, cls, &hex(f[5]), n, &mut o);
                    if o != hex(f[6]) { bad += 1 }
                }
                _ => {
                    let (op, shape, n) = (num(1) as u8, num(2) as u8, num(3) as usize);
                    let mut o = vec![0u8; n.div_ceil(8)];
                    bit(qlean_run_c, op, shape, &hex(f[4]), &hex(f[5]), n, &mut o);
                    if o != hex(f[6]) { bad += 1 }
                }
            }
            cnt += 1;
        }
        eprintln!("diff44: {cnt} vectors, {bad} mismatches");
        assert_eq!(bad, 0);
    }
    /// `foRMon = mon (decode ..)`: three blocks at widths 8, 16, 0 bits, the last one short
    #[test] fn enc_and_fill_equal_mon_of_the_decode() {
        let (n, nblk) = (2500usize, 3usize);
        let (base, maxv, bsum) = ([-5i64, 100, 7], [0i64; 3], [0i64; 3]);
        let width = [8u8, 16, 0];
        let mut off = [0u64; 3];
        let mut pack: Vec<u8> = vec![];
        for b in 0..nblk { off[b] = pack.len() as u64; pack.extend((0..crate::BLK * width[b] as usize / 8).map(|i| (i * 37 + b * 11) as u8)) }
        let meta = Meta { base: &base, maxv: &maxv, off: &off, bsum: &bsum, width: &width, sumnul: 0, sumn: 0, n, nblk, mblk: nblk };
        let c = Coc { meta, pack: &pack, exc: None, fdelta: None };
        for (cls, w) in [(1u8, 2usize), (2, 4), (3, 8)] {
            for op in 0..2u8 {
                let mut dense = vec![0u8; n * w];
                for b in 0..nblk {
                    let (cnt, mut xv) = ((n - b * crate::BLK).min(crate::BLK), [0u64; crate::BLK]);
                    let x = block(&c, b, cnt, w, &mut xv);
                    dense[b * crate::BLK * w..(b * crate::BLK + cnt) * w].copy_from_slice(&x[..cnt * w]);
                }
                let want = mon_of(op, cls, i64::MIN, &dense, n);
                let mut got = vec![0u8; n * w];
                mon_enc(qlean_run_c, op, cls, i64::MIN, &c, &mut got);
                assert_eq!(got, want, "mon_enc cls {cls} op {op}");
                for b in 0..nblk {
                    let cnt = (n - b * crate::BLK).min(crate::BLK);
                    let mut buf = vec![0i64; cnt];
                    mon_fill(op, cls, i64::MIN, &c, &mut buf, b * crate::BLK);
                    let ex: Vec<i64> = want[b * crate::BLK * w..(b * crate::BLK + cnt) * w].chunks(w).map(|e| match w {
                        2 => i16::from_ne_bytes(e.try_into().unwrap()) as i64, 4 => i32::from_ne_bytes(e.try_into().unwrap()) as i64,
                        _ => i64::from_ne_bytes(e.try_into().unwrap()) }).collect();
                    assert_eq!(buf, ex, "mon_fill cls {cls} op {op} blk {b}");
                }
            }
        }
    }
}

#[cfg(test)]
mod k9 {
    use super::*;
    use crate::c::qlean_run_c;
    fn mon_f64(op: u8, x: &[u64]) -> Vec<u64> {
        let mut o = vec![0u64; x.len()];
        mon(qlean_run_c, op, k44::F64, 0, bytes_mut(&mut x.to_vec()[..]), x.len(), bytes_mut(&mut o[..]));
        o
    }
    // expected bits are the C's own answers: `sqrt -1`, `log -1`, `tan 0w` are 0n; `asin 2`, `acos -0w` are the positive NaN
    #[test] fn libm_maps_answer_q_nulls() {
        let (inf, ninf) = (f64::INFINITY.to_bits(), f64::NEG_INFINITY.to_bits());
        assert_eq!(mon_f64(2, &[(-1f64).to_bits(), 4f64.to_bits(), 0x7ff8000000000001]), [NAN64, 2f64.to_bits(), NAN64]);
        assert_eq!(mon_f64(4, &[(-1f64).to_bits(), 0, 1f64.to_bits()]), [NAN64, ninf, 0]);
        assert_eq!(mon_f64(7, &[inf]), [NAN64]);
        assert_eq!(mon_f64(8, &[2f64.to_bits()]), [PNAN64]);
        assert_eq!(mon_f64(9, &[ninf]), [PNAN64]);
        assert_eq!(mon_f64(10, &[0f64.to_bits(), inf]), [0, (core::f64::consts::FRAC_PI_2).to_bits()]);
    }
    #[test] #[should_panic(expected = "qlean_ew_mon: no case for verb 11 at storage class 5")]
    fn a_verb_past_atan_is_refused() { mon_f64(11, &[0]); }
    #[test] #[should_panic(expected = "qlean_ew_mon: no case for verb 2 at storage class 3")]
    fn a_libm_map_at_long_is_refused() { mon(qlean_run_c, 2, 3, 0, &[0; 8], 1, &mut [0; 8]); }
    // `pack_stage` then `ids_stage` returns every id, whole or cut in two at a point inside a word
    #[test] fn ids_round_trip_cut_anywhere() {
        for w in [0u32, 1, 2, 4, 8, 16, 32, 64] {
            for n in [0usize, 1, 7, 64, 65, 200] {
                let x: Vec<u64> = (0..n as u64).map(|i| if w == 0 { 0 } else { i.wrapping_mul(0x9e3779b97f4a7c15) & (if w == 64 { !0 } else { (1 << w) - 1 }) }).collect();
                let mut p = vec![0u8; ids_len(n, w)];
                let nb = if matches!(w, 1 | 2 | 4) { p.len() } else { n };
                pack_stage(3, w, bytes_mut(&mut x.clone()[..]), n, 0, nb, &mut p);
                for cut in [0, n / 3, n / 2, n] {
                    let mut o = vec![0u64; n];
                    for (lo, hi) in [(0, cut), (cut, n)] { ids_stage(3, w, &p, lo, hi, bytes_mut(&mut o[..])) }
                    assert_eq!(o, x, "w {w} n {n} cut {cut}");
                }
            }
        }
    }
    #[test] fn widen_stage_cuts_a_bit_source_inside_a_byte() {
        let x = [0b1010_0110u8, 0b0000_0101];
        let mut whole = [0u8; 10 * 4];
        widen(qlean_run_c, 6, 2, 7, 9, &x, 10, &mut whole);
        let mut o = [0xAAu8; 10 * 4];
        widen_stage(6, 2, 7, 9, &x, 0, 3, &mut o);
        widen_stage(6, 2, 7, 9, &x, 3, 10, &mut o);
        assert_eq!(o, whole);
    }
}
