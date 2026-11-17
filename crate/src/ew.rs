#![forbid(unsafe_code)]
//! Column (a), ew.rs: scalar helpers (A42), the two-operand verbs and comparisons (A43; `ew_val_avx` and
//! `ew_cmp_avx` are `simd::ew_val`/`simd::ew_cmp`), bit verbs and the monadic ones (A44), casts and time (A45),
//! widening (A46a), the fused chain's stage table (A46b; its runner is `c::run_chain`). `op`, `cls`, `shape` are
//! ew.rs's `EW_*`. The `qlean_ew_*` entries unbox and allocate and stay C (§1).
use crate::c::Runner;
use crate::blocks::Blocks;
use crate::coc::Coc;
use crate::sym::{sym_eq, sym_msort, Syms};
use alloc::vec;
use alloc::vec::Vec;

// ---- A42: ew.rs (per element: C keeps these bodies while a C caller remains) ----
/// ew.rs `ew_unsupported`: the abort naming the engine, `op` and `cls`.
pub fn ew_unsupported(engine: &str, op: u32, cls: u32) -> ! {
    // C exits 1 after this text; no_std has no exit, so the panic handler prints it and aborts
    panic!("{engine}: no case for verb {op} at storage class {cls}. The dispatch in QLean/Kernel/Elementwise.lean is the only caller and must not claim this pair; answering anything here would be a wrong column rather than a fallback.")
}
/// ew.rs `ew_width`: an element's bytes in class `cls`.
pub fn ew_width(cls: u32) -> usize {
    match cls {
        0 => 1,
        1 => 2,
        2 | 4 => 4,
        3 | 5 => 8,
        _ => panic!("qlean_ew: storage class {cls} has no dense element width"),
    }
}
// q's order on floats as two predicates: a null (a NaN) below everything, two nulls equal (ew.rs)
pub fn lt64(x: u64, y: u64) -> bool { if f64::from_bits(x).is_nan() { !f64::from_bits(y).is_nan() } else { f64::from_bits(x) < f64::from_bits(y) } }
pub fn lt32(x: u32, y: u32) -> bool { if f32::from_bits(x).is_nan() { !f32::from_bits(y).is_nan() } else { f32::from_bits(x) < f32::from_bits(y) } }
/// ew.rs `ew_tol`: q's tolerant float equality.
pub fn ew_tol(x: f64, y: f64) -> bool {
    let (ax, ay) = (x.abs(), y.abs());
    (x - y).abs() < 1.0 / (1u64 << 43) as f64 * if ax < ay { ax } else { ay }
}
/// ew.rs `ew_ord64`: a double's bits as an order-preserving key.
pub fn ew_ord64(x: u64, y: u64) -> i32 { if lt64(x, y) { -1 } else if lt64(y, x) { 1 } else { 0 } }
/// ew.rs `ew_ord32`
pub fn ew_ord32(x: u32, y: u32) -> i32 { if lt32(x, y) { -1 } else if lt32(y, x) { 1 } else { 0 } }
/// ew.rs `ew_outside_long`: `f` has no long.
pub fn ew_outside_long(f: f64) -> bool { f <= -9223372036854775808.0 || f >= 9223372036854775808.0 }
/// ew.rs `ew_fdiv`: floor division, q's nulls.
pub fn ew_fdiv(x: i64, y: i64) -> i64 {
    // the caller excluded y = 0 and the null x, the one dividend whose quotient by -1 overflows
    let (q, r) = (x.wrapping_div(y), x.wrapping_rem(y));
    q - ((r ^ y) < 0 && r != 0) as i64
}
/// ew.rs `ew_magic`: a divisor's multiply-shift form.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Magic { pub m: i64, pub d: i64, pub sh: u32, pub add: bool }
/// ew.rs `ew_magic_of`; `None` where C answers 0.
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
/// ew.rs `ew_fdiv_magic`: `ew_fdiv(x, g.d)` by the magic.
pub fn fdiv_magic(g: &Magic, x: i64) -> i64 {
    let add = if !g.add { 0 } else if g.d > 0 { x } else { x.wrapping_neg() };
    let mut q = (((g.m as i128 * x as i128) >> 64) as i64).wrapping_add(add) >> g.sh;
    q += ((q as u64) >> 63) as i64;
    let rem = x.wrapping_sub(q.wrapping_mul(g.d));
    q - ((rem ^ g.d) < 0 && rem != 0) as i64
}

// ---- A43: ew.rs ----
use crate::c::run_map;
use crate::ids::{self, id_at, ids_avail, ids_bytes, pack, unpack};
use crate::pod::{self, bytes_mut, Elt, Pod};
use crate::{QLEAN_COST_ARITH, QLEAN_COST_COPY, QLEAN_COST_MATH};

/// `EW_*` codes of ew.rs that this section reads; the two lists cannot change apart.
pub mod k {
    pub const I16: u8 = 1; pub const I32: u8 = 2; pub const I64: u8 = 3;
    pub const F32: u8 = 4; pub const BITS: u8 = 6; pub const ABS: u8 = 1;
    pub const ADD: u8 = 0; pub const SUB: u8 = 1; pub const MUL: u8 = 2; pub const DIV: u8 = 3; pub const FILL: u8 = 4;
    pub const LESSER: u8 = 5; pub const GREATER: u8 = 6; pub const IDIV: u8 = 7; pub const IMOD: u8 = 8; pub const POW: u8 = 9;
    pub const EQ: u8 = 0; pub const NE: u8 = 1; pub const LT: u8 = 2; pub const LE: u8 = 3; pub const GT: u8 = 4; pub const GE: u8 = 5;
    pub const VV: u8 = 0; pub const VA: u8 = 1; pub const AV: u8 = 2;
}
/// ew.rs's `#if`: the mask paths exist only where the build enables the instructions they use.
pub const VEC: bool = cfg!(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw"));
pub const NAN64: u64 = 0xfff8000000000000;
pub const PNAN64: u64 = 0x7ff8000000000000;
pub const NAN32: u32 = 0xffc00000;
pub const PNAN32: u32 = 0x7fc00000;


pub fn ro<T: Pod>(b: &[u8]) -> &[T] {
    pod::cast(b).unwrap_or_else(|| panic!("qlean_ew: a {}-byte payload is not a whole, aligned array of {}-byte elements", b.len(), size_of::<T>()))
}
pub fn rw<T: Pod>(b: &mut [u8]) -> &mut [T] {
    let n = b.len();
    pod::cast_mut(b).unwrap_or_else(|| panic!("qlean_ew: a {n}-byte output is not a whole, aligned array of {}-byte elements", size_of::<T>()))
}
/// elements `[lo, hi)` of the `w`-byte payload `x`, or its first element when `atom`; the C reads past the end instead.
pub fn side<'a>(x: &'a [u8], atom: bool, lo: usize, hi: usize, w: usize) -> &'a [u8] {
    let (s, e) = if atom { (0, w) } else { (lo * w, hi * w) };
    x.get(s..e).unwrap_or_else(|| panic!("qlean_ew: elements {}..{} of a {}-byte payload of {w}-byte elements", s / w, e / w, x.len()))
}
/// A block-sized scratch for `c`.
pub fn pod_scr(c: &Coc) -> crate::pod::Scr<u64> { crate::pod::Scr::<u64>::new(c.meta.blk()) }

/// ew.rs `EW_SHAPED`: `o[i] = f(a[ia], b[ib])` with `(ia, ib)` the shape's index pair, an atom a one-element slice.
#[inline(always)]
pub fn zip2<T: Copy, U: Copy>(shape: u8, a: &[T], b: &[T], o: &mut [U], f: impl Fn(T, T) -> U) {
    if o.is_empty() { return }
    match shape {
        k::VV => for ((o, &x), &y) in o.iter_mut().zip(a).zip(b) { *o = f(x, y) },
        k::VA => { let y = b[0]; for (o, &x) in o.iter_mut().zip(a) { *o = f(x, y) } }
        _ => { let x = a[0]; for (o, &y) in o.iter_mut().zip(b) { *o = f(x, y) } }
    }
}
/// ew.rs `EW_CMP_SHAPED`: the `m` bits LSB-first, the bits of the last byte above `m` zero.
#[inline(always)]
pub fn pack_bits(o: &mut [u8], m: usize, ev: impl Fn(usize) -> bool) {
    for (k, byte) in o.iter_mut().enumerate() {
        let (lo, hi) = (k * 8, (k * 8 + 8).min(m));
        *byte = (lo..hi).fold(0u8, |v, i| v | (ev(i) as u8) << (i - lo));
    }
}
/// `pack_bits` of `p(a[ia], b[ib])`, `(ia, ib)` the shape's index pair.
#[inline(always)]
pub fn pack2<T: Copy>(shape: u8, a: &[T], b: &[T], o: &mut [u8], m: usize, p: impl Fn(T, T) -> bool) {
    if m == 0 { return }
    match shape {
        k::VV => pack_bits(o, m, |i| p(a[i], b[i])),
        k::VA => { let y = b[0]; pack_bits(o, m, |i| p(a[i], y)) }
        _ => { let x = a[0]; pack_bits(o, m, |i| p(x, b[i])) }
    }
}

/// ew.rs `EW_VAL_INT`: the wrap is the truncation the write does; `&` and `|` need no null test, q's
/// null being the least value of the type.
pub fn val_int<T: Elt>(op: u8, cls: u8, nul: i64, shape: u8, a: &[T], b: &[T], o: &mut [T]) {
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
            // a constant divisor (ew.rs) takes the multiply-shift form instead of a 64-bit divide
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
pub fn floor64(x: f64) -> f64 {
    if !(x.abs() < 4503599627370496.0) || x == 0.0 { return x }
    let t = x as i64 as f64;
    if t > x { t - 1.0 } else { t }
}
pub fn floor32(x: f32) -> f32 {
    if !(x.abs() < 8388608.0) || x == 0.0 { return x }
    let t = x as i32 as f32;
    if t > x { t - 1.0 } else { t }
}
pub fn le64(x: u64, y: u64) -> bool { if f64::from_bits(x).is_nan() { true } else { f64::from_bits(x) <= f64::from_bits(y) } }
pub fn le32(x: u32, y: u32) -> bool { if f32::from_bits(x).is_nan() { true } else { f32::from_bits(x) <= f32::from_bits(y) } }
pub fn eq64(x: u64, y: u64) -> bool { if f64::from_bits(x).is_nan() { f64::from_bits(y).is_nan() } else { f64::from_bits(x) == f64::from_bits(y) } }
pub fn eq32(x: u32, y: u32) -> bool { if f32::from_bits(x).is_nan() { f32::from_bits(y).is_nan() } else { f32::from_bits(x) == f32::from_bits(y) } }
pub fn tol64(x: u64, y: u64) -> bool { ew_tol(f64::from_bits(x), f64::from_bits(y)) }
pub fn tol32(_: u32, _: u32) -> bool { false }

/// ew.rs `EW_VAL_FLT`: a NaN operand is answered before any conversion and comes back as it is, the left
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
            // ew.rs `EW_POW`: a NaN operand is `0n`; the power is libm's, at double width (the float class narrows it)
            k::POW => zip2(shape, a, b, o, |x, y| if isn(x) || isn(y) { $nanq } else { tob($pow(tof(x), tof(y))) }),
            _ => ew_unsupported("qlean_ew_val", op as u32, cls as u32),
        }
    }
} }
val_flt!(val_f64, u64, f64, NAN64, PNAN64, ew_ord64, floor64, fnma64, |x: f64, y: f64| crate::c::pow(x, y));
val_flt!(val_f32, u32, f32, NAN32, PNAN32, ew_ord32, floor32, fnma32, |x: f32, y: f32| crate::c::pow(x as f64, y as f64) as f32);
pub fn fnma64(x: f64, y: f64, f: f64) -> f64 { crate::simd::fnma64(x, y, f) }
pub fn fnma32(x: f32, y: f32, f: f32) -> f32 { crate::simd::fnma32(x, y, f) }

/// ew.rs `ew_val_run` over the elements `[lo, hi)` of `a`, `b` (an atom is one element): into `o`.
pub fn val_slice(op: u8, cls: u8, shape: u8, nul: i64, a: &[u8], b: &[u8], lo: usize, hi: usize, o: &mut [u8]) {
    let w = ew_width(cls as u32);
    let (a, b) = (side(a, shape == k::AV, lo, hi, w), side(b, shape == k::VA, lo, hi, w));
    // the mask path answers the four arithmetic verbs at a float width; every other pair is the loop below
    if VEC && cls >= k::F32 && op <= k::DIV { return crate::simd::ew_val(op, cls, a, b, hi - lo, o) }
    match cls {
        0..=3 => crate::by_width!(int w, val_int(op, cls, nul, shape, ro(a), ro(b), rw(o))),
        4 => val_f32(op, cls, shape, ro(a), ro(b), rw(o)),
        5 => val_f64(op, cls, shape, ro(a), ro(b), rw(o)),
        _ => ew_unsupported("qlean_ew_val", op as u32, cls as u32),
    }
}

/// ew.rs `ew_val_run` and its entry: `a op b` of class `cls` (`shape` vector/atom) into `out`, `n` long.
pub fn val(run: Runner, op: u8, cls: u8, shape: u8, nul: i64, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    let w = ew_width(cls as u32);
    run_map(run, out, n, w, QLEAN_COST_ARITH, w, &|lo, hi, o| val_slice(op, cls, shape, nul, a, b, lo, hi, o));
}
/// ew.rs `ew_val_foR_run`: two encoded columns, the answer dense.
pub fn val_enc(run: Runner, op: u8, cls: u8, nul: i64, a: &Coc, b: &Coc, out: &mut [u8]) {
    let (w, n, lg, s) = (ew_width(cls as u32), a.meta.n, a.meta.lg, Blocks::from(*a));
    assert_eq!(lg, b.meta.lg, "qlean ew: two encoded columns at block sizes 1 << {} and 1 << {}; the caller decodes one", lg, b.meta.lg);
    run_map(run, out, n, w, QLEAN_COST_ARITH, w, &|lo, hi, o| {
        let (mut xa, mut xb) = (pod_scr(a), pod_scr(a));
        for (blk, blo, at, end) in s.tiles(lo, hi) {
            // a slice may start inside a block, so the block is decoded from its own start and entered at `at - blo`
            let cnt = end - blo;
            let (pa, pb) = (s.load_w(blk, cnt, w, bytes_mut(&mut xa)), Blocks::from(*b).load_w(blk, cnt, w, bytes_mut(&mut xb)));
            val_slice(op, cls, k::VV, nul, pa, pb, at - blo, cnt, &mut o[(at - lo) * w..(end - lo) * w]);
        }
    });
}
/// ew.rs `ew_val_foR_atom_run`: an encoded column and an atom.
pub fn val_enc_atom(run: Runner, op: u8, cls: u8, shape: u8, nul: i64, c: &Coc, atom: &[u8], out: &mut [u8]) {
    let (w, s) = (ew_width(cls as u32), Blocks::from(*c));
    run_map(run, out, s.n, w, QLEAN_COST_ARITH, w, &|lo, hi, o| {
        let mut xv = pod_scr(c);
        for (blk, blo, at, end) in s.tiles(lo, hi) {
            let cnt = end - blo;
            let x = s.load_w(blk, cnt, w, bytes_mut(&mut xv));
            let o = &mut o[(at - lo) * w..(end - lo) * w];
            if shape == k::VA { val_slice(op, cls, shape, nul, x, atom, at - blo, cnt, o) } else { val_slice(op, cls, shape, nul, atom, x, at - blo, cnt, o) }
        }
    });
}

/// ew.rs `EW_CMP_INT`: no null case, q's null being the least value of the type (a byte and a char compare
/// by their byte).
pub fn cmp_int<T: Elt>(op: u8, cls: u8, shape: u8, a: &[T], b: &[T], o: &mut [u8], m: usize) {
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
/// ew.rs `EW_CMP_FLT`: q's order (a null below everything) with its tolerance, which `<` excludes.
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

/// ew.rs `ew_cmp_run` over the output bytes `[lo, hi)`: the elements `8 lo ..` of `a`, `b`, `n` in all.
pub fn cmp_slice(op: u8, cls: u8, shape: u8, a: &[u8], b: &[u8], n: usize, lo: usize, hi: usize, o: &mut [u8]) {
    let w = ew_width(cls as u32);
    let (e0, e1) = (lo * 8, (hi * 8).min(n));
    let (a, b) = (side(a, shape == k::AV, e0, e1, w), side(b, shape == k::VA, e0, e1, w));
    let m = e1 - e0;
    if VEC && op <= k::GE { return crate::simd::ew_cmp(op, cls, a, b, m, o) }
    match cls {
        0..=3 => crate::by_width!(int ew_width(cls as u32), cmp_int(op, cls, shape, ro(a), ro(b), o, m)),
        4 => cmp_f32(op, cls, shape, ro(a), ro(b), o, m),
        5 => cmp_f64(op, cls, shape, ro(a), ro(b), o, m),
        _ => ew_unsupported("qlean_ew_cmp", op as u32, cls as u32),
    }
}
/// ew.rs `ew_cmp_run` and its entry: a byte per comparison.
pub fn cmp(run: Runner, op: u8, cls: u8, shape: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    let nb = n.div_ceil(8);
    // sliced by output byte, so eight elements move together and no two threads share one
    run_map(run, out, nb, 1, QLEAN_COST_ARITH, 8 * ew_width(cls as u32), &|lo, hi, o| cmp_slice(op, cls, shape, a, b, n, lo, hi, o));
}
/// Elements per block of the id kernels: 64 are eight whole output bytes and a whole number of bytes at every id width.
pub const IDB: usize = 64;
/// `Column.idWidth`'s lane widths; any other width reads as 64, as `id_at` and the C `IDS_WIDTHS` default do.
pub fn lane(w: u32) -> u32 { if matches!(w, 0 | 1 | 2 | 4 | 8 | 16 | 32) { w } else { 64 } }
/// The ids of `p` into `out` at the lane width `w`, matched once per block.
pub fn unpack_w(p: &[u8], w: u32, out: &mut [i64]) {
    macro_rules! at { ($W:literal) => { ids::unpack::<$W, i64>(p, out, |_, e, v| *e = v as i64) } }
    match w { 0 => at!(0), 1 => at!(1), 2 => at!(2), 4 => at!(4), 8 => at!(8), 16 => at!(16), 32 => at!(32), _ => at!(64) }
}
/// Bits `[0, c)` of one block, `p(x[i], y[i])` at bit `i`; the verb matched once per block.
#[inline(always)]
pub fn verb_bits(op: u8, x: &[i64], y: &[i64], c: usize) -> u64 {
    let f = |p: fn(i64, i64) -> bool| (0..c).fold(0u64, |m, i| m | (p(x[i], y[i]) as u64) << i);
    match op {
        k::EQ => f(|x, y| x == y), k::NE => f(|x, y| x != y), k::LT => f(|x, y| x < y),
        k::LE => f(|x, y| x <= y), k::GT => f(|x, y| x > y), _ => f(|x, y| x >= y),
    }
}
/// ew.rs `EW_CMP_IDS`: the `m` bits for elements `[e0, e0 + m)` of the shape's two id streams, a block of
/// `IDB` at a time. `get(a, p, out)` unpacks side `a`'s (`true` = left) ids from `p`; `map(a, id)` is the key compared
/// (the id's rank, or the id). An atom side is its element 0, mapped once. `e0` is a multiple of 8, so a slice starts
/// on a byte at every width.
#[inline(always)]
pub fn ids_bits(op: u8, shape: u8, ia: &[u8], wa: u32, ib: &[u8], wb: u32, e0: usize, m: usize, o: &mut [u8],
            get: impl Fn(bool, &[u8], &mut [i64]), map: impl Fn(bool, i64) -> i64) {
    if m == 0 { return }
    let (mut x, mut y) = ([0i64; IDB], [0i64; IDB]);
    if shape == k::AV { x = [map(true, id_at(ia, wa, 0) as i64); IDB] }
    if shape == k::VA { y = [map(false, id_at(ib, wb, 0) as i64); IDB] }
    let off = |w: u32, s: usize| (e0 + s) * w as usize / 8;
    for (j, ob) in o.chunks_mut(IDB / 8).enumerate() {
        let (s, c) = (j * IDB, (m - j * IDB).min(IDB));
        if shape != k::AV {
            get(true, &ia[off(wa, s)..], &mut x[..c]);
            x[..c].iter_mut().for_each(|v| *v = map(true, *v));
        }
        if shape != k::VA {
            get(false, &ib[off(wb, s)..], &mut y[..c]);
            y[..c].iter_mut().for_each(|v| *v = map(false, *v));
        }
        ob.copy_from_slice(&verb_bits(op, &x, &y, c).to_le_bytes()[..ob.len()]);
    }
}
/// `ids_bits` over the whole bitmap: one width switch outside the loops where the two sides agree (every pair a column
/// meets its own kind in), the general `unpack_w` where they differ. `ranks` is `ew_cmp_ids_run`'s two tables; none is
/// `ew_eq_ids_run`: the ids themselves, only `=` and `<>`.
pub fn ids_pair(run: Runner, cost: u32, wide: usize, op: u8, shape: u8, ia: &[u8], wa: u32, ib: &[u8], wb: u32, n: usize,
            ranks: Option<(&[i32], &[i32])>, out: &mut [u8]) {
    let (wa, wb) = (lane(wa), lane(wb));
    let op = if ranks.is_none() && op != k::NE { k::EQ } else { op };
    run_map(run, out, n.div_ceil(8), 1, cost, wide, &|lo, hi, o| {
        let (e0, m) = (lo * 8, (hi * 8).min(n).saturating_sub(lo * 8));
        // an id past its table reads rank 0, the convention `Column.idAt` sets
        let map = |a: bool, u: i64| match ranks {
            None => u,
            Some((ra, rb)) => (if a { ra } else { rb }).get(u as usize).copied().unwrap_or(0) as i64,
        };
        macro_rules! same { ($W:literal) => {
            ids_bits(op, shape, ia, wa, ib, wb, e0, m, o, |_, p, out| ids::unpack::<$W, i64>(p, out, |_, e, v| *e = v as i64), map)
        } }
        if wa == wb {
            match wa { 0 => same!(0), 1 => same!(1), 2 => same!(2), 4 => same!(4), 8 => same!(8), 16 => same!(16), 32 => same!(32), _ => same!(64) }
        } else {
            ids_bits(op, shape, ia, wa, ib, wb, e0, m, o, |a, p, out| unpack_w(p, if a { wa } else { wb }, out), map)
        }
    });
}
/// ew.rs `ew_eq_ids_run` and its entry: bit `i` is whether the two ids the shape indexes, both read at `w`,
/// are equal (`op` = `=`) or differ (`<>`).
pub fn eq_ids(run: Runner, op: u8, shape: u8, ia: &[u8], ib: &[u8], w: u32, n: usize, out: &mut [u8]) {
    ids_pair(run, QLEAN_COST_COPY, 2 * w as usize, op, shape, ia, w, ib, w, n, None, out)
}

/// ew.rs `qlean_ew_eq_ids` / `qlean_ew_cmp_ids`: `n` clamped to what the vector sides hold (an atom side is read at
/// index 0 only, so an empty one leaves nothing to compare); `ba`, `bb` are the id payloads' byte counts.
pub fn ids_n(shape: u8, n: usize, ba: usize, wa: u32, bb: usize, wb: u32) -> usize {
    let (aa, ab) = (ids_avail(ba, wa), ids_avail(bb, wb));
    if (shape == k::AV && aa == 0) || (shape == k::VA && ab == 0) { return 0 }
    let n = if shape != k::AV { n.min(aa) } else { n };
    if shape != k::VA { n.min(ab) } else { n }
}
// ---- A44: ew.rs ----
/// `EW_*` codes of ew.rs this section reads (the verbs `k` does not hold).
mod k44 {
    pub(super) const BITS: u32 = 6; pub(super) const F32: u8 = 4; pub(super) const F64: u8 = 5;
    pub(super) const NEG: u8 = 0; pub(super) const ABS: u8 = 1; pub(super) const SQRT: u8 = 2; pub(super) const ATAN: u8 = 10;
    // `EW_BCMP + EW_EQ ..= EW_GE`
    pub(super) const BEQ: u8 = 16; pub(super) const BNE: u8 = 17; pub(super) const BLT: u8 = 18;
    pub(super) const BLE: u8 = 19; pub(super) const BGT: u8 = 20; pub(super) const BGE: u8 = 21;
}
/// ew.rs `ew_bit_run` and its entry: bitmap verbs. `out` is the `⌈n / 8⌉` bytes, the bits above `n` zero;
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
pub fn mon_int<T: Elt>(op: u8, nul: i64, x: &[T], o: &mut [T]) {
    let nulv = T::wrap(nul as u64);
    for (o, &v) in o.iter_mut().zip(x) {
        *o = if v.i() == nul { nulv } else if op == k44::NEG || v.i() < 0 { T::wrap(0u64.wrapping_sub(v.i() as u64)) } else { v };
    }
}
/// ew.rs `ew_mon_run` over `x`'s elements into `o` (the same count): the pair was checked by `mon_chk`.
pub fn mon_slice(op: u8, cls: u8, nul: i64, x: &[u8], o: &mut [u8]) {
    match cls {
        0..=3 => crate::by_width!(int ew_width(cls as u32), mon_int(op, nul, ro(x), rw(o))),
        k44::F32 => for (o, &v) in rw::<u32>(o).iter_mut().zip(ro::<u32>(x)) { *o = if op == k44::NEG { v ^ 0x8000_0000 } else { v & 0x7fff_ffff } },
        _ => for (o, &v) in rw::<u64>(o).iter_mut().zip(ro::<u64>(x)) { *o = if op == k44::NEG { v ^ (1 << 63) } else { v & !(1 << 63) } },
    }
}
/// The nine float maps' answer at `f64`, ew.rs `EW_MON_MAP`: a NaN operand answers `0n` before libm sees it, and
/// a NaN result is `nanout` (`0n`, except the two arc functions' positive one: measured, `asin 2` and `acos -0w`).
#[inline(always)]
pub fn mon_map(x: &[u64], o: &mut [u64], nanout: u64, f: impl Fn(f64) -> f64) {
    for (o, &b) in o.iter_mut().zip(x) {
        *o = if f64::from_bits(b).is_nan() { NAN64 } else {
            let y = f(f64::from_bits(b)).to_bits();
            if f64::from_bits(y).is_nan() { nanout } else { y }
        };
    }
}
/// ew.rs `ew_mon_run`'s switch, outside the loop: one straight libm loop per map.
pub fn mon_libm(op: u8, x: &[u8], o: &mut [u8]) {
    use crate::c as m;
    let (x, o) = (ro::<u64>(x), rw::<u64>(o));
    match op {
        2 => mon_map(x, o, NAN64, m::sqrt), 3 => mon_map(x, o, NAN64, m::exp), 4 => mon_map(x, o, NAN64, m::log),
        5 => mon_map(x, o, NAN64, m::sin), 6 => mon_map(x, o, NAN64, m::cos), 7 => mon_map(x, o, NAN64, m::tan),
        8 => mon_map(x, o, PNAN64, m::asin), 9 => mon_map(x, o, PNAN64, m::acos), _ => mon_map(x, o, NAN64, m::atan),
    }
}
/// The pairs `neg`/`abs` answer (the encoded entries read nothing else): the six classes at the two verbs.
pub fn mon_chk(op: u8, cls: u8) {
    if op > k44::ABS || cls > k44::F64 { ew_unsupported("qlean_ew_mon", op as u32, cls as u32) }
}
/// The nine float maps are `SQRT ..= ATAN` at `f64` alone (q answers a float whatever the argument's type, so the
/// dispatch widens first); any other pair of them is unsupported, as `ew_mon_run`'s `default`.
pub fn is_libm(op: u8, cls: u8) -> bool { (k44::SQRT..=k44::ATAN).contains(&op) && cls == k44::F64 }
/// `Ew.monStep` over a block, `x` and `o` the same count at `cls`'s width: the monadic verbs, `neg` and `abs` and the
/// nine libm maps; the one body of `mon`, which `Map` runs over a column and the chain's stage over a tile.
pub fn mon_lane(op: u8, cls: u8, nul: i64, x: &[u8], o: &mut [u8]) {
    if is_libm(op, cls) { mon_libm(op, x, o) } else { mon_chk(op, cls); mon_slice(op, cls, nul, x, o) }
}
/// The `map` driver's producer (coc plan §3): the source's block read at `wi` bytes an element, through `lane` into the
/// writer's elements. A `Sink` or `ffi::of_raw` writes it.
pub struct Map<'a, F> { pub src: Blocks<'a>, pub wi: usize, pub lane: F }
impl<F: Fn(&[u8], &mut [u8]) + Sync> crate::enc::Producer for Map<'_, F> {
    fn block<'s>(&'s self, b: usize, lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8] {
        let (x, o) = buf.split_at_mut(8 * nb);
        (self.lane)(self.src.block(b, lo, nb, self.wi, x), &mut o[..nb * w]);
        &o[..nb * w]
    }
    fn block_into(&self, b: usize, lo: usize, nb: usize, _: usize, buf: &mut [u8], out: &mut [u8]) { (self.lane)(self.src.block(b, lo, nb, self.wi, buf), out) }
}
/// The encoding an answer at class `cls` takes: `Column.alpEncodes` holds of every type of a float class and
/// `Column.encodes` of every type of the classes `i16 ..= i64`; a byte class has none.
pub fn form_of(cls: u8) -> Option<crate::ffi::Form> {
    use crate::ffi::Form;
    match cls { k44::F32 | k44::F64 => Some(Form::Alp), 1..=3 => Some(Form::For), _ => None }
}
/// The cost of `mon` an element: a libm call is `QLEAN_COST_MATH`.
pub fn mon_cost(op: u8, cls: u8) -> u32 { if is_libm(op, cls) { QLEAN_COST_MATH } else { QLEAN_COST_ARITH } }
/// ew.rs `ew_floor_run`: `floor` at a float class, always a `long`; out of range or a NaN answers `0N`.
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

// ---- A45: ew.rs ----
/// ew.rs `ew_cast_clamp`
pub fn cast_clamp(v: i64, lo: i64, hi: i64) -> i64 { if v < lo { lo } else if v > hi { hi } else { v } }
/// ew.rs `ew_cast_round`: q's round half away from zero; a value `long` cannot hold saturates (to `-0W`
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
/// ew.rs `ew_cast_run` and its entry `qlean_ew_cast`: class `src` to class `dst`, every element
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
/// ew.rs `ew_fdiv64`: floor division by a positive divisor.
pub fn fdiv64(a: i64, b: i64) -> i64 { a / b - (a % b < 0) as i64 }
/// `fdiv64` by one of the tick units `U`, each divisor a constant.
#[inline(always)]
pub fn fdiv_unit(a: i64, u: i64) -> i64 {
    match u { 1000000 => fdiv64(a, 1000000), 1000000000 => fdiv64(a, 1000000000), 60000000000 => fdiv64(a, 60000000000), _ => fdiv64(a, 86400000000000) }
}
/// ew.rs `ew_days_of_first`: days from 2000.01.01 to the first of month `m`. Wrapping, as the C is at
/// the extremes of `long`.
pub fn days_of_first(m: i64) -> i64 {
    let (y, mo) = (2000i64.wrapping_add(fdiv64(m, 12)), 1 + m.wrapping_sub(12i64.wrapping_mul(fdiv64(m, 12))));
    let y = if mo <= 2 { y.wrapping_sub(1) } else { y };
    let era = fdiv64(if y >= 0 { y } else { y.wrapping_sub(399) }, 400);
    let yoe = y.wrapping_sub(era.wrapping_mul(400));
    let doy = fdiv64(153 * ((mo + 9) % 12) + 2, 5);
    era.wrapping_mul(146097).wrapping_add(yoe * 365 + fdiv64(yoe, 4) - fdiv64(yoe, 100) + doy).wrapping_sub(730425)
}
/// ew.rs `ew_month_of_days`: the month from 2000.01 holding day `d` from 2000.01.01.
pub fn month_of_days(d: i64) -> i64 {
    let z = d.wrapping_add(730425);
    let era = fdiv64(if z >= 0 { z } else { z.wrapping_sub(146096) }, 146097);
    let doe = z.wrapping_sub(era.wrapping_mul(146097));
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let mp = (5 * (doe - (365 * yoe + yoe / 4 - yoe / 100)) + 2) / 153;
    let m = mp + if mp < 10 { 3 } else { -9 };
    era.wrapping_mul(400).wrapping_add(yoe).wrapping_add((m <= 2) as i64).wrapping_mul(12).wrapping_sub(24000).wrapping_add(m - 1)
}
/// ew.rs `ew_tick_run`: a temporal operand re-counted in its result's unit (`op` is the source unit's
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


// ---- A46a: ew.rs ----
/// ew.rs `ew_widen_run`'s refusal: widening goes up to `int`, `long`, `real` or `float`, and a float only to `float`.
pub fn widen_chk(src: u8, dst: u8) {
    if !matches!(dst, 2..=5) || (dst != 5 && matches!(src, 4 | 5)) { ew_unsupported("qlean_ew_widen", src as u32, dst as u32) }
}
/// ew.rs `ew_widen_run` over elements `[lo, hi)` of the whole source `x` (a bit source indexed from its own
/// bit 0, so a slice may start inside a byte) into `o`, the `hi - lo` answers. The pair was checked by `widen_chk`.
pub fn widen_slice(src: u8, dst: u8, nul_in: i64, nul_out: i64, x: &[u8], lo: usize, hi: usize, o: &mut [u8]) {
    const PNAN64: u64 = 0x7ff8000000000000;
    // the source class is chosen outside the loop, so each pair is its own straight-line pass (ew.rs)
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
            // a real null is q's `0n` at double width, the sign kept (ew.rs)
            let r = if f32::from_bits(f).is_nan() { ((f >> 31) as u64) << 63 | PNAN64 } else { (f32::from_bits(f) as f64).to_bits() };
            c.copy_from_slice(&r.to_le_bytes())
        },
        _ if src == 5 => o.copy_from_slice(&x[lo * 8..hi * 8]),
        _ => pass(src, lo, hi, x, o, |v| (if v == nul_in { nul_out as u64 } else { (v as f64).to_bits() }).to_le_bytes()),
    }
}
/// ew.rs `ew_widen_run` and its entry: class `src` widened to `dst`, nulls mapped.
pub fn widen(run: Runner, src: u8, dst: u8, nul_in: i64, nul_out: i64, x: &[u8], n: usize, out: &mut [u8]) {
    if n > 0 { widen_chk(src, dst) }
    let w = if matches!(dst, 2..=5) { ew_width(dst as u32) } else { 1 };
    crate::c::run_map(run, out, n, w, crate::QLEAN_COST_COPY, w, &|lo, hi, o: &mut [u8]| widen_slice(src, dst, nul_in, nul_out, x, lo, hi, o));
}
/// ew.rs `ew_widen_stage`: elements `[lo, hi)` of a chain tile (or of a column of one stage) of `n`
/// elements, on the calling thread. A bit source may be cut inside a byte; `widen_slice` indexes bits from the tile's own.
pub fn widen_stage(src: u8, dst: u8, nul_in: i64, nul_out: i64, x: &[u8], lo: usize, hi: usize, out: &mut [u8]) {
    if lo == hi { return }
    widen_chk(src, dst);
    widen_slice(src, dst, nul_in, nul_out, x, lo, hi, &mut out[lo * ew_width(dst as u32)..hi * ew_width(dst as u32)])
}







// ---- A46b: ew.rs (the stage workers stay C until `c::run_chain` calls Rust ones) ----
/// ew.rs `ew_stage_bits`: a stage's bits per element of `a`, `b`, `o`; answers the cost.
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
/// ew.rs `ew_stage_fixed`: operand `left` of the stage is not re-based per tile.
pub fn stage_fixed(engine: u32, shape: u32, left: bool) -> bool {
    if engine == eng::DECODE || engine == eng::ALP { return true }
    if !matches!(engine, eng::VAL | eng::CMP | eng::BIT) { return !left }
    if left { shape == k::AV as u32 } else { shape == k::VA as u32 }
}
/// ew.rs's engine codes, the `Ew.Engine` constants of QLean/Kernel/Elementwise.lean.
pub mod eng {
    pub const VAL: u32 = 0; pub const CMP: u32 = 1; pub const MON: u32 = 2; pub const WIDEN: u32 = 3;
    pub const BIT: u32 = 4; pub const FLOOR: u32 = 5; pub const CAST: u32 = 6; pub const DECODE: u32 = 7;
    pub const ALP: u32 = 8; pub const ENCMETA: u32 = 9; pub const ENCPACK: u32 = 10; pub const TICK: u32 = 11;
    pub const IDS: u32 = 12; pub const PACK: u32 = 13;
}

// ---- K9: the chain's tile workers over a packed id column (ew.rs `ew_ids_run`, :1315 `ew_pack_run`) ----
/// Bytes of `n` ids at `w` bits as the two stages see them: a width the table does not list is the 64-bit lane, as in
/// `IDS_WIDTHS`' `default`.
pub fn ids_len(n: usize, w: u32) -> usize {
    match w { 0 => 0, 1 | 2 | 4 => ids_bytes(n, w), 8 => n, 16 => 2 * n, 32 => 4 * n, _ => 8 * n }
}
/// ew.rs `ew_ids_run`: ids `[lo, hi)` of the packed payload `x` (`w` bits each) written into `o` at class
/// `cls`'s width. A sub-byte slice may start inside a word, so its ragged head goes id by id and the rest is `ids::unpack`.
pub fn ids_stage(cls: u8, w: u32, x: &[u8], lo: usize, hi: usize, o: &mut [u8]) {
    #[inline(always)]
    fn go<const W: u32, T: Elt>(x: &[u8], lo: usize, hi: usize, o: &mut [T]) {
        let mut i = lo;
        if W != 0 && W < 8 { while i < hi && i % (64 / W as usize) != 0 { o[i] = T::wrap(id_at(x, W, i) as u64); i += 1 } }
        // `i` is a whole word in (or the lane width makes it a whole id), so the byte it starts at is exact
        let at = i * W as usize / 8;
        unpack::<W, T>(&x[at..], &mut o[i..hi], |_, e, v| *e = T::wrap(v as u64));
    }
    #[inline(always)]
    fn by_w<T: Elt>(w: u32, x: &[u8], lo: usize, hi: usize, o: &mut [T]) {
        match w {
            0 => go::<0, T>(x, lo, hi, o), 1 => go::<1, T>(x, lo, hi, o), 2 => go::<2, T>(x, lo, hi, o),
            4 => go::<4, T>(x, lo, hi, o), 8 => go::<8, T>(x, lo, hi, o), 16 => go::<16, T>(x, lo, hi, o),
            32 => go::<32, T>(x, lo, hi, o), _ => go::<64, T>(x, lo, hi, o),
        }
    }
    crate::by_width!(int ew_width(cls as u32), by_w(w, x, lo, hi, rw(o)))
}
/// ew.rs `ew_pack_run`: the `n` elements of `x` (class `cls`, zero-extended) written as `w`-bit ids. Below a
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
    crate::by_width!(uint ew_width(cls as u32), go(w, x, n, lo, hi, o))
}

// ---- K10: the statistics fold, a chain's last stage (ew.rs `ew_stats_run`, `ew_stats_sum`) ----
/// ew.rs's `ST_*`: the five phases, each one pass over the column.
pub mod st { pub const SUMS: u8 = 0; pub const CENTRED: u8 = 1; pub const DOTS: u8 = 2; pub const DOTS32: u8 = 3; pub const SERIAL: u8 = 4; }






// ---- E: the fused chain's program, its builder and its two folds (ew.rs `ew_chain_build`, `qlean_ew_chain*`, `qlean_stats_chain`) ----
use crate::c::{pool, run_chain};
use crate::coc::Meta;
use crate::alp::Cocf;
use crate::ffi::{stage_worker, CCoc, CCocf, CPass, CStage};
use core::ffi::c_void;

/// c.rs's `QLEAN_SLOTS`: the most stages a chain holds, and the first source code that is a column, a fixed operand or a slot.
pub const SLOTS: usize = 10;
pub const COLUMN: u8 = 254;
pub const FIXED: u8 = 255;
/// ew.rs `EW_SLOT0`: a source code from here is the answer of the stage that many places along.
pub const SLOT0: u8 = 128;
/// ew.rs `EW_STAGE_BYTES`: one record of the program `Ew.Stage.bytes` writes.
pub const STAGE_BYTES: usize = 24;

/// The number of stages of `prog`, none refused: the chain is built in QLean/Kernel/Elementwise.lean and every one holds at most `SLOTS`.
pub fn stages(prog: &[u8]) -> usize { prog.len() / STAGE_BYTES }
pub fn checked(k: usize) -> usize {
    assert!(k != 0 && k <= SLOTS, "qlean_ew_chain: {k} stages, and the driver holds {SLOTS}. The chain is built in QLean/Kernel/Elementwise.lean and every one of them is shorter than that; a longer one needs QLEAN_SLOTS in rust/src/c.rs raised with it.");
    k
}
/// One record of a program: `engine op cls shape`, the two operand codes (a third for ALP's float sections), the stage's null and the
/// target's null.
pub struct Rec { engine: u32, op: u8, cls: u8, shape: u8, code: [u8; 3], nul: i64, nul_out: i64 }
pub fn rec(prog: &[u8], i: usize) -> Rec {
    let r = &prog[i * STAGE_BYTES..(i + 1) * STAGE_BYTES];
    Rec { engine: r[0] as u32, op: r[1], cls: r[2], shape: r[3], code: [r[4], r[5], r[6]],
          nul: i64::from_ne_bytes(r[8..16].try_into().unwrap()), nul_out: i64::from_ne_bytes(r[16..24].try_into().unwrap()) }
}

/// The bytes of the answer of the `n`-element chain `prog`: its last stage's bits per element over `n`, rounded up to a byte.
pub fn chain_bytes(prog: &[u8], n: usize) -> usize {
    let r = rec(prog, checked(stages(prog)) - 1);
    (n * stage_bits(r.engine, r.op as u32, r.cls as u32, r.shape as u32).3 as usize).div_ceil(8)
}
/// A decode or ALP stage's view: metadata `m`, pack `pk`, and for ALP the float sections `a`. Where C's `coc_attach` aborts or a
/// buffer is misaligned or short, the stage names it.
pub fn stage_view(i: usize, alp: bool, m: &[u8], pk: &[u8], a: &[u8], n: usize) -> CCocf {
    let me = Meta::new(m, n).unwrap_or_else(|| panic!("qlean_ew_chain: stage {i}'s metadata is misaligned or short"));
    let cocf = alp.then(|| Cocf::meta_view(m, a, n).unwrap_or_else(|| panic!("qlean_ew_chain: stage {i}'s ALP sections are misaligned or short")));
    let c = Coc::attach(cocf.as_ref().map_or(me, |f| f.c.meta), pk).unwrap_or_else(|| {
        panic!("qlean: a Frame of Reference pack of {} bytes whose residuals end at {} holds no patch list of {} blocks after them", pk.len(), me.res_end(), me.mblk)
    });
    let cc = CCoc::of(&c, m.as_ptr().cast_mut());
    match cocf {
        Some(f) => CCocf { c: cc, exp: f.exp.as_ptr().cast_mut(), exc_off: f.exc_off.as_ptr().cast_mut(), exc_pos: f.exc_pos.as_ptr().cast_mut(),
                           exc_raw: f.exc_raw.as_ptr().cast_mut().cast(), nexc: f.exc_pos.len(), f32: f.f32 as core::ffi::c_int },
        None => CCocf { c: cc, ..CCocf::EMPTY },
    }
}
/// ew.rs `ew_chain_build`: the `st[..k]` the `k`-record program `prog` describes, every stage writing its own slot, the caller
/// re-binding the last one's output. `input(code)` is the payload a source code names; `views` is the caller's array because a decode
/// stage's `p.a` points into it (a `cocf` serves both decode engines: its first member is the integral view). Answers the whole chain's
/// cost and widest element in bytes. `st` and `views` stay in place from here until the chain has run, and every binding reaches `n` elements.
pub fn chain_build<'a>(prog: &[u8], k: usize, input: &impl Fn(u8) -> &'a [u8], n: usize, st: &mut [CStage], views: &mut [CCocf]) -> (u32, usize) {
    checked(k);
    let (mut cost, mut wide) = (0u32, 1usize);
    for i in 0..k {
        let r = rec(prog, i);
        let (engine, shape) = (r.engine, r.shape);
        let (c, ab, bb, ob) = stage_bits(engine, r.op as u32, r.cls as u32, shape as u32);
        let mut s = CStage {
            f: Some(stage_worker(engine)),
            p: CPass { c: r.nul_out as isize as *const c_void, nul: r.nul, op: r.op, cls: r.cls, shape, ..CPass::EMPTY },
            asrc: 0, bsrc: 0, osrc: i as u8, abits: ab, bbits: bb, obits: ob,
            bytewise: (engine == eng::CMP || engine == eng::BIT || (engine == eng::PACK && shape != 0 && shape < 8)) as u8,
        };
        cost += c;
        wide = wide.max(ab as usize / 8).max(ob as usize / 8);
        // an operand names either a slot, the answer of the stage that many places along (already tile-local), or one of the payloads handed in
        for side in 0..2 {
            let code = r.code[side];
            let (bind, src) = if side == 0 { (&mut s.p.a, &mut s.asrc) } else { (&mut s.p.b, &mut s.bsrc) };
            // a monadic engine has no right operand, which is where `bbits` is zero
            if side == 1 && bb == 0 && engine != eng::DECODE && engine != eng::ALP { *bind = core::ptr::null(); *src = FIXED; continue }
            if code >= SLOT0 { *src = code - SLOT0; continue }
            *bind = input(code).as_ptr().cast();
            *src = if stage_fixed(engine, shape as u32, side == 0) { FIXED } else { COLUMN };
        }
        if engine == eng::DECODE || engine == eng::ALP {
            // the metadata and the pack become one view for the run, with an ALP column's float sections read out of the third payload
            let alp = engine == eng::ALP;
            views[i] = stage_view(i, alp, input(r.code[0]), input(r.code[1]), if alp { input(r.code[2]) } else { &[] }, n);
            s.p.a = if alp { (&raw const views[i]).cast() } else { (&raw const views[i].c).cast() };
            s.p.b = core::ptr::null();
        }
        st[i] = s;
    }
    (cost, wide)
}

/// `Ew.chain prog inputs n`: stage `k` is its engine over the payloads its source codes name, at the whole count `n`; `out` is the last
/// stage's answer (`chain_bytes` of them), computed a tile at a time so every intermediate stays in L1.
pub fn chain<'a>(prog: &[u8], input: &impl Fn(u8) -> &'a [u8], n: usize, out: &mut [u8]) {
    let k = stages(prog);
    let mut st = [const { CStage::EMPTY }; SLOTS + 1];
    let mut views = [const { CCocf::EMPTY }; SLOTS];
    let (cost, wide) = chain_build(prog, k, input, n, &mut st, &mut views);
    let (bytes, obits) = (out.len(), st[k - 1].obits as usize);
    st[k - 1].p.o = out.as_mut_ptr().cast();
    st[k - 1].osrc = COLUMN;
    // an empty column is answered without entering a worker, `bit`'s own guard: a stage that broadcasts an atom reads its operand's first byte first
    if n != 0 { run_chain(pool(), &st[..k], n, cost, wide); }
    // the last byte of a `&`/`|`/`^` over two bitmaps belongs to no element past `n`, as `bit` fixes it up outside its own worker
    if st[k - 1].bytewise != 0 && bytes != 0 && (n * obits & 7) != 0 { out[bytes - 1] &= ((1u32 << (n * obits & 7)) - 1) as u8 }
}
/// `chainEnc`'s result class at `width` bytes: the encoder stage reads `width`-byte integers, and the chain's last stage must answer exactly those.
pub fn enc_cls(width: usize, obits: usize) -> u32 {
    assert!(8 * width == obits && matches!(width, 2 | 4 | 8),
            "qlean_ew_chain_enc: the result type is {width} bytes wide and the chain's last stage answers {obits} bits. `Kernel.payload` passes `QAtomicType.width`, so the two disagree only if a builder named a stage whose class is not the result type's.");
    match width { 2 => k::I16 as u32, 4 => k::I32 as u32, _ => k::I64 as u32 }
}
/// ew.rs `qlean_ew_chain_enc`'s appended stage: stage `k` is the encoder's meta step (`pack` false) or pack step over the tile stage
/// `k - 1` wrote, `enc` the `coc_enc` it writes through, at class `cls`. It answers no slot (`osrc` fixed), and its cost is added to `cost`
/// the first time.
pub fn enc_stage(st: &mut [CStage], k: usize, cls: u32, enc: *mut c_void, pack: bool, cost: &mut u32) {
    let (cs, ab, bb, ob) = stage_bits(eng::ENCMETA, 0, cls, 0);
    st[k] = CStage { f: Some(stage_worker(if pack { eng::ENCPACK } else { eng::ENCMETA })), p: CPass { o: enc, cls: cls as u8, ..CPass::EMPTY },
                     asrc: (k - 1) as u8, bsrc: FIXED, osrc: FIXED, abits: ab, bbits: bb, obits: ob, bytewise: 0 };
    if !pack { *cost += cs }
}


/// ew.rs `ew_stats`: the accumulators of one phase. `l` and `lf` are `lanes` wide, row `k` the sum `k`.
pub struct Stats {
    pub phase: u8, pub lanes: usize, nt: usize, full: usize, pub cnt: usize, pub bad: usize, pub mx: f64, pub my: f64,
    tail: [[f64; 8]; 3], l: [[f64; 8]; 3], lf: [[f32; 4]; 3],
}
impl Stats {
    pub fn new() -> Stats { Stats { phase: 0, lanes: 1, nt: 0, full: 0, cnt: 0, bad: 0, mx: 0.0, my: 0.0, tail: [[0.0; 8]; 3], l: [[0.0; 8]; 3], lf: [[0.0; 4]; 3] } }
    /// ew.rs `ew_stats_pass`'s set-up: `phase` over a column of `n`, before the chain runs.
    pub fn begin(&mut self, phase: u8, n: usize) {
        self.phase = phase;
        self.lanes = [2, 2, 8, 4, 1][phase as usize];
        self.nt = 0;
        self.cnt = 0;
        self.bad = 0;
        self.full = n - n % self.lanes;
        self.l = [[0.0; 8]; 3];
        self.lf = [[0.0; 4]; 3];
    }
    /// ew.rs `ew_stats_run`: one tile `x`, `y` at element `at` of the column, in order on the calling thread.
    /// q rounds each product before it adds it, which Rust never contracts into a fused multiply-add.
    pub fn run(&mut self, x: &[f64], y: &[f64], at: usize) {
        let n = x.len();
        let m = if self.phase == st::SERIAL || at >= self.full { 0 } else if at + n <= self.full { n } else { self.full - at };
        let (mx, my) = (self.mx, self.my);
        // a null right operand counts in a lane whatever is left of it, and past the lanes under a live one
        let (mut c, mut bad) = (0, m);
        // `var x` is `cov[x;x]`: both operands one tile, so every accumulator is the same sum, run once and copied
        let same = core::ptr::eq(x.as_ptr(), y.as_ptr());
        let (kept, ykept) = match self.phase {
            st::SUMS | st::CENTRED if same => {
                let ph = self.phase;
                let f = |x: f64| if ph == st::SUMS { (x, x) } else { let u = x - mx; (u, u * u) };
                let mut a: [f64; 2] = self.l[0][..2].try_into().unwrap();
                let mut kept = [0u32; 2];
                for xc in x[..m].chunks_exact(2) {
                    for j in 0..2 { let (u, t0) = f(xc[j]); a[j] += if u == u { t0 } else { 0.0 }; kept[j] += (u == u) as u32 }
                }
                for k in 0..2 { self.l[k][..2].copy_from_slice(&a) }
                if self.phase == st::CENTRED { self.l[2][..2].copy_from_slice(&a) }
                let k = (kept[0] + kept[1]) as usize;
                (k, k)
            }
            st::SUMS => fold::<2, 8, f64>(&mut self.l, x, y, m, |u, v| (u, v), |u, v| [u, v, 0.0]),
            st::CENTRED => fold::<2, 8, f64>(&mut self.l, x, y, m, |u, v| (u - mx, v - my), |u, v| [u * v, u * u, v * v]),
            st::DOTS => fold::<8, 8, f64>(&mut self.l, x, y, m, |u, v| (u, v), |u, v| [u * v, u, 0.0]),
            st::DOTS32 => fold::<4, 4, f32>(&mut self.lf, x, y, m, |u, v| (u as f32, v as f32), |u, v| [u * v, u, 0.0]),
            _ => (0, 0),
        };
        c += kept;
        bad -= ykept;
        // past the last full group: held back for the fold's end, or, with one lane, the fold itself
        let (mut a0, mut a1) = (self.l[0][0], self.l[1][0]);
        for i in m..n {
            let (mut u, mut v) = (x[i], y[i]);
            if self.phase == st::DOTS32 { u = u as f32 as f64; v = v as f32 as f64 }
            if self.phase == st::CENTRED { u -= mx; v -= my }
            bad += (u == u && v != v) as usize;
            if u != u || v != v { continue }
            c += 1;
            let t = match self.phase {
                st::SUMS => [u, v, 0.0],
                st::CENTRED => [u * v, u * u, v * v],
                st::DOTS32 => [(u as f32 * v as f32) as f64, u, 0.0],
                _ => [u * v, u, 0.0],
            };
            if self.phase == st::SERIAL { a0 += t[0]; a1 += t[1]; continue }
            for k in 0..3 { self.tail[k][self.nt] = t[k] }
            self.nt += 1;
        }
        if self.phase == st::SERIAL { self.l[0][0] = a0; self.l[1][0] = a1 }
        self.cnt += c;
        self.bad += bad;
    }
    /// ew.rs `ew_stats_sum`: sum `k` of the phase just run, the lanes in order and then the tail, which is q's order.
    pub fn sum(&self, k: usize) -> f64 {
        let mut r = 0.0;
        for j in 0..self.lanes { r += if self.phase == st::DOTS32 { self.lf[k][j] as f64 } else { self.l[k][j] } }
        for t in 0..self.nt { r += self.tail[k][t] }
        r
    }
}
/// ew.rs `ST_FOLD`: one tile into `L` lanes by position, `m` a multiple of `L`. A term of a dropped pair adds a
/// zero, so an accumulator is never `-0`. Answers the pairs kept and the null right operands among them.
#[inline(always)]
pub fn fold<const L: usize, const W: usize, T: Elt + core::ops::Add<Output = T>>(a: &mut [[T; W]; 3], x: &[f64], y: &[f64], m: usize,
                                              uv: impl Fn(f64, f64) -> (T, T), t: impl Fn(T, T) -> [T; 3]) -> (usize, usize) {
    let mut acc = [0, 1, 2].map(|k| -> [T; L] { a[k][..L].try_into().unwrap() });
    let (mut kept, mut ykept) = ([0u32; L], [0u32; L]);
    for (xc, yc) in x[..m].chunks_exact(L).zip(y[..m].chunks_exact(L)) {
        for j in 0..L {
            let (u, v) = uv(xc[j], yc[j]);
            let (ylive, live) = (v == v, v == v && u == u);
            let t = t(u, v);
            for k in 0..3 { acc[k][j] = acc[k][j] + if live { t[k] } else { T::ZERO } }
            kept[j] += live as u32;
            ykept[j] += ylive as u32;
        }
    }
    for k in 0..3 { a[k][..L].copy_from_slice(&acc[k]) }
    (kept.iter().map(|&c| c as usize).sum(), ykept.iter().map(|&c| c as usize).sum())
}
/// ew.rs `ew_bitw_run`: `op` is band 0, bor 1, bandnot 2; any other reads as band.
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
#[cfg(test)]
mod a45 {
    use super::*;
    // expected values are the C's comments (ew.rs "Eval.castAtom ... measured against q 4.1") and its helpers
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
#[cfg(test)]
mod tests_k8 {
    use super::*;
    use crate::c::qlean_run_c;
    /// a symbol column of `ss`: NUL-terminated blob, boxed starts
    fn col(ss: &[&[u8]]) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (Vec::new(), alloc::vec![1]);
        for s in ss { b.extend_from_slice(s); b.push(0); o.push(b.len() << 1 | 1) }
        (b, o)
    }
    fn like(pat: &[u8], ss: &[&[u8]]) -> Option<Vec<u8>> {
        let (b, o) = col(ss);
        let mut out = alloc::vec![0xAAu8; ss.len().div_ceil(8)];
        like_syms(pat, &Syms { blob: &b, offs: &o }, &mut out).then_some(out)
    }
    fn hits(atom: bool, pat: &[u8], b: &[u8]) -> Option<Vec<i64>> {
        let w = fixed_width(atom, pat);
        if w == 0 { return None }
        let mut h = alloc::vec![0i64; b.len() / w + 1];
        let k = fixed_scan(atom, pat, b, &mut h);
        h.truncate(k);
        Some(h)
    }
    #[test] fn like_language() {
        let ss: [&[u8]; 5] = [b"abc", b"", b"a-c", b"xbz", b"ab"];
        assert_eq!(like(b"a*", &ss), Some(alloc::vec![0b10101]));
        assert_eq!(like(b"?b?", &ss), Some(alloc::vec![0b01001]));
        assert_eq!(like(b"[a-b]*", &ss), Some(alloc::vec![0b10101]));
        assert_eq!(like(b"[^a]*", &ss), Some(alloc::vec![0b01000]));
        assert_eq!(like(b"", &ss), Some(alloc::vec![0b00010]));
        assert_eq!(like(b"*", &ss), Some(alloc::vec![0b11111]));
        assert_eq!(like(b"a**", &ss), None); // q's `'nyi`
        assert_eq!(like(b"[abc", &ss), None); // q's `'[`
        assert_eq!(like(b"[]]", &[b"]"]), Some(alloc::vec![1])); // a `]` first in a class is a member
        assert_eq!(like(b"[a-]", &[b"-", b"a"]), Some(alloc::vec![0b11])); // a range needs a byte after `-` that is not `]`
    }
    #[test] fn fixed_matches_do_not_overlap() {
        assert_eq!(hits(false, b"aa", b"aaaa"), Some(alloc::vec![0, 2])); // measured: `"aaaa" ss "aa"` is `0 2`
        assert_eq!(hits(true, b"?", b"abc"), Some(alloc::vec![]));
        assert_eq!(hits(false, b"?", b"abc"), Some(alloc::vec![0, 1, 2]));
        assert_eq!(hits(true, b"[", b"a[c"), Some(alloc::vec![1]));
        assert_eq!(hits(false, b"[", b"a[c"), None);
        assert_eq!(hits(false, b"", b"abc"), None);
        assert_eq!(hits(false, b"a*", b"abc"), None);
        // the vector path (64 positions at a time) and the item walk agree, hits across a 64-byte step included
        let b: Vec<u8> = (0..300).map(|i| if i % 5 == 3 || i % 7 == 0 { b'a' } else { b'b' }).collect();
        for pat in [&b"ab"[..], b"a", b"aba", b"abbab", b"b"] {
            let item: Vec<u8> = pat.iter().flat_map(|&c| [b'[', c, b']']).collect(); // the same needle as `[a][b]`: no vector path
            assert_eq!(hits(false, pat, &b), hits(false, &item, &b), "{}", core::str::from_utf8(pat).unwrap());
        }
    }
    #[test] fn ssr_replaces_the_scan() {
        let run = |pat: &[u8], t: &[u8], b: &[u8]| {
            let (w, mut h) = (fixed_width(false, pat), alloc::vec![0i64; b.len() + 1]);
            let k = fixed_scan(false, pat, b, &mut h);
            let mut o = alloc::vec![0u8; b.len() - k * w + k * t.len() + 16];
            ssr_fill(&mut o, b, &h[..k], w, t);
            o.truncate(b.len() - k * w + k * t.len());
            o
        };
        assert_eq!(run(b"aa", b"b", b"aaa"), b"ba"); // measured: `ssr["aaa";"aa";"b"]` is `"ba"`
        assert_eq!(run(b"[ab]", b"X", b"abc"), b"XXc"); // the step is the item count, not the byte count
        let long = [b'z'; 40];
        assert_eq!(run(b"a", &long, b"xay"), [&b"x"[..], &long, b"y"].concat());
    }
    #[test] fn sym_order_is_slice_order() {
        let mut s = 0x2545F4914F6CDD1Du64;
        let mut next = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        for _ in 0..20000 {
            let (la, lb) = (next() as usize % 40, next() as usize % 40);
            let mut a: Vec<u8> = (0..la).map(|_| (next() % 3) as u8 * 100).collect();
            let mut b: Vec<u8> = (0..lb).map(|_| (next() % 3) as u8 * 100).collect();
            if next() % 3 == 0 { let k = la.min(lb); b[..k].copy_from_slice(&a[..k]) }
            if next() % 7 == 0 { b = a.clone(); a.push(0) }
            assert_eq!(sym_ord(&a, &b), a.cmp(&b), "{a:?} {b:?}");
        }
    }
    #[test] fn cmp_all_shapes() {
        let (ba, oa) = col(&[b"ab", b"", b"b", "\u{e9}".as_bytes(), b"ab", b"abc", b"z", b"a", b"b", b"q"]);
        let (bb, ob) = col(&[b"ab", b"a", b"a", b"z", b"abc", b"ab", b"z", b"", b"b", b"q"]);
        let (a, b) = (Syms { blob: &ba, offs: &oa }, Syms { blob: &bb, offs: &ob });
        let n = 10;
        let go = |op, sh, a: &Syms, b: &Syms| { let mut o = alloc::vec![0xFFu8; 2]; cmp_syms(qlean_run_c, op, sh, a, b, n, &mut o); o };
        let want = |op: u8, f: &dyn Fn(usize) -> (Vec<u8>, Vec<u8>)| {
            let mut o = alloc::vec![0u8; 2];
            for i in 0..n { let (x, y) = f(i); let r = match op { 0 => x == y, 1 => x != y, 2 => x < y, 3 => x <= y, 4 => x > y, _ => x >= y }; o[i / 8] |= (r as u8) << (i % 8) }
            o
        };
        let (sa, sb) = (a.slices(10), b.slices(10));
        for op in 0..6 {
            assert_eq!(go(op, k::VV, &a, &b), want(op, &|i| (sa[i].to_vec(), sb[i].to_vec())), "VV {op}");
            assert_eq!(go(op, k::VA, &a, &b), want(op, &|i| (sa[i].to_vec(), sb[0].to_vec())), "VA {op}");
            assert_eq!(go(op, k::AV, &a, &b), want(op, &|i| (sa[0].to_vec(), sb[i].to_vec())), "AV {op}");
        }
    }
}
#[cfg(test)]
mod a46b {
    use super::*;
    // expected values are ew.rs's `ew_stage_bits` / `ew_stage_fixed` read off the C switch
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
    /// Replays vectors dumped by ew.rs's own bodies (testdata/ew_a42.vec); `EW_A42_VEC` names a bigger dump.
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
    use crate::BLK;
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
        let meta = Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &maxv, off: &off, bsum: &bsum, width: &width, sumnul: 0, sumn: 0, n, nblk: 3, mblk: 3 };
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
        eq_ids(qlean_run_c, k::EQ, k::VV, &ia, &ib, 2, 5, &mut o);
        assert_eq!(o, [0b00000000]);
        eq_ids(qlean_run_c, k::NE, k::VV, &ia, &ib, 2, 5, &mut o);
        assert_eq!(o, [0b11111]);
        // ranks: ra = [2, 1, 2] for ids 0..2, past the table reads 0; rb = [3, 1, 0, 2]
        cmp_ids(qlean_run_c, k::LT, k::VV, &ra, &ia, 2, &rb, &ib, 2, 5, &mut o);
        assert_eq!(o, [0b01000]);
        cmp_ids(qlean_run_c, k::GE, k::VV, &ra, &ia, 2, &rb, &ib, 2, 5, &mut o);
        assert_eq!(o, [0b10111]);
        eq_ids(qlean_run_c, k::EQ, k::VA, &ia, &[0b10], 2, 5, &mut o);
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
        mon_lane(op, cls, nul, &x[..n * ew_width(cls as u32)], &mut o);
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
        let meta = Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &maxv, off: &off, bsum: &bsum, width: &width, sumnul: 0, sumn: 0, n, nblk, mblk: nblk };
        let c = Coc { meta, pack: &pack, exc: None, fdelta: None };
        for (cls, w) in [(1u8, 2usize), (2, 4), (3, 8)] {
            for op in 0..2u8 {
                let mut dense = vec![0u8; n * w];
                for b in 0..nblk {
                    let (cnt, mut xv) = ((n - b * crate::BLK).min(crate::BLK), [0u64; crate::BLK]);
                    let x = Blocks::from(c).load_w(b, cnt, w, bytes_mut(&mut xv));
                    dense[b * crate::BLK * w..(b * crate::BLK + cnt) * w].copy_from_slice(&x[..cnt * w]);
                }
                let want = mon_of(op, cls, i64::MIN, &dense, n);
                let map = Map { src: Blocks::from(c), wi: w, lane: |x: &[u8], o: &mut [u8]| mon_lane(op, cls, i64::MIN, x, o) };
                // the writer's blocks, aligned and (at 100 elements, off the source's grid) cut across the source's
                for step in [crate::BLK, 100] {
                    for lo in (0..n).step_by(step) {
                        let (nb, mut buf) = (step.min(n - lo), vec![0u64; 2 * crate::BLK]);
                        let got = crate::enc::Producer::block(&map, lo / crate::BLK, lo, nb, w, bytes_mut(&mut buf));
                        assert_eq!(got, &want[lo * w..(lo + nb) * w], "map cls {cls} op {op} at {lo}");
                    }
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
        mon_lane(op, k44::F64, 0, bytes_mut(&mut x.to_vec()[..]), bytes_mut(&mut o[..]));
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
    fn a_libm_map_at_long_is_refused() { mon_lane(2, 3, 0, &[0; 8], &mut [0; 8]); }
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
/// ew.rs `ew_cmp_ids_run` and its entry: `op` between the ranks `ra[id]`, `rb[id]` of the two ids the shape
/// indexes, read at `wa`, `wb`.
pub fn cmp_ids(run: Runner, op: u8, shape: u8, ra: &[i32], ia: &[u8], wa: u32, rb: &[i32], ib: &[u8], wb: u32, n: usize,
               out: &mut [u8]) {
    ids_pair(run, QLEAN_COST_ARITH, 8 * 4, op, shape, ia, wa, ib, wb, n, Some((ra, rb)), out)
}
/// ew.rs `ew_cmp_syms_run` and its entry: bit `i` is `op` of the two symbols the shape indexes; sliced by output
/// byte, so the whole answer is written here (the C zeroed it first and or-ed).
pub fn cmp_syms(run: Runner, op: u8, shape: u8, a: &Syms, b: &Syms, n: usize, out: &mut [u8]) {
    use core::cmp::Ordering::{Greater, Less};
    run_map(run, out, n.div_ceil(8), 1, QLEAN_COST_ARITH, 8 * 4, &|lo, hi, o| {
        let (e0, m) = (lo * 8, (hi * 8).min(n) - lo * 8);
        match op {
            k::EQ => pack_syms(shape, a, b, o, e0, m, |x, y| sym_eq(x, y)),
            k::NE => pack_syms(shape, a, b, o, e0, m, |x, y| !sym_eq(x, y)),
            k::LT => pack_syms(shape, a, b, o, e0, m, |x, y| sym_ord(x, y) == Less),
            k::LE => pack_syms(shape, a, b, o, e0, m, |x, y| sym_ord(x, y) != Greater),
            k::GT => pack_syms(shape, a, b, o, e0, m, |x, y| sym_ord(x, y) == Greater),
            _ => pack_syms(shape, a, b, o, e0, m, |x, y| sym_ord(x, y) != Less), // EW_GE
        }
    });
}
/// ew.rs `fixed_scan` (`atom`, `p` as `fixed_width`'s): every non-overlapping match start, in order, into `o`
/// (`b.len() / w + 1` entries, `w` the answer of `fixed_width`); answers how many. One walk for `ss` and `ssr`, so they cannot
/// disagree. A literal needle takes 64 positions at a time where the build has avx512bw: its first and last byte give the mask
/// of positions where both sit, and only those are compared in full.
pub fn fixed_scan(atom: bool, p: &[u8], b: &[u8], o: &mut [i64]) -> usize {
    let q = Pattern::fixed(atom, p).expect("qlean_ew_fixed_scan: a pattern `fixed_width` accepted");
    let (n, w, mut at, mut i) = (b.len(), q.width(), 0, 0);
    if w == 0 || w > n { return 0 }
    let last = n - w; // the final position a match may start at
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw"))]
    {
        // an all-literal pattern's items are the raw pattern bytes one for one (`parse` reaches `Lit` only where it takes one byte)
        if last >= 63 && q.its.iter().all(|it| matches!(it, Item::Lit(_))) {
            let mut s = 0;
            while s + 63 <= last {
                let mut m = crate::simd::lit_mask64(b, s, w, p[0], p[w - 1]);
                // clearing the low bit is loop-carried, so it is one `blsr`; `k < i` is the non-overlap, the last match still covers it
                while m != 0 {
                    let k = s + m.trailing_zeros() as usize;
                    if k >= i && (w <= 2 || sym_eq(&b[k + 1..k + w - 1], &p[1..w - 1])) {
                        o[at] = k as i64;
                        at += 1;
                        i = k + w;
                    }
                    m &= m - 1;
                }
                if i < s + 64 { i = s + 64 } // every position under here is decided
                s += 64;
            }
        }
    }
    while i <= last {
        if q.its.iter().zip(&b[i..i + w]).all(|(&it, &c)| q.hit(it, c)) { o[at] = i as i64; at += 1; i += w } else { i += 1 }
    }
    at
}
/// `fixed_width` past `fixed_items`: 0 for all three refusals (`fixed_items`'s, an empty pattern, a `*`), where the caller answers `none`.
pub fn fixed_width(atom: bool, p: &[u8]) -> usize { Pattern::fixed(atom, p).map_or(0, |q| q.width()) }
/// `qlean_ew_like_syms` past the allocation: bit `i` of `out` (`⌈n / 8⌉` bytes, all written) is `patMatch` at symbol `i`;
/// false where `parsePat` refuses, `out` untouched.
pub fn like_syms(pat: &[u8], s: &Syms, out: &mut [u8]) -> bool {
    let Some(q) = Pattern::parse(pat) else { return false };
    pack_bits(out, s.count(), |i| q.matches(s.at(i)));
    true
}
/// ew.rs `ew_low_zero_run`: bit `i` is `(a[i] & b[0]) = 0`.
pub fn low_zero(run: Runner, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    let (a, b) = (side(a, false, 0, n, 8), side(b, true, 0, 1, 8));
    run_map(run, out, n.div_ceil(8), 1, QLEAN_COST_ARITH, 64, &|lo, hi, o| {
        let (e0, e1) = (lo * 8, (hi * 8).min(n));
        pack2(k::VA, ro::<u64>(&a[e0 * 8..e1 * 8]), ro::<u64>(b), o, e1 - e0, |x, y| x & y == 0)
    });
}
/// ew.rs `ew_low_zero_foR_run`: a block with `base = maxv` is one value and is answered from its metadata,
/// any other is restored into a buffer; sliced by output byte, a block's bytes may be split between two slices.
pub fn low_zero_enc(run: Runner, c: &Coc, atom: &[u8], out: &mut [u8]) {
    let (s, m) = (Blocks::from(*c), ro::<u64>(side(atom, true, 0, 1, 8))[0]);
    run_map(run, out, s.n.div_ceil(8), 1, QLEAN_COST_ARITH, c.meta.blk() * 8, &|lo, hi, o| {
        let mut xv = pod_scr(c);
        // a slice of output bytes is the elements `8 lo .. 8 hi`, cut at the column end
        for (blk, blo, e0, e1) in s.tiles(lo * 8, (hi * 8).min(s.n)) {
            let (cnt, o) = (s.span(blk).1, &mut o[e0 / 8 - lo..e1.div_ceil(8) - lo]);
            if c.meta.base[blk] == c.meta.maxv[blk] {
                let all = c.meta.base[blk] as u64 & m == 0;
                pack_bits(o, e1 - e0, |_| all);
            } else {
                let x = ro::<u64>(s.load_w(blk, cnt, 8, bytes_mut(&mut xv)));
                pack2(k::VA, &x[e0 - blo..e1 - blo], &[m], o, e1 - e0, |x, y| x & y == 0);
            }
        }
    });
}
/// ew.rs `qlean_ew_rank_pair` past the unboxing: each symbol's rank in the merged order of `da`, `db`.
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
/// `qlean_ew_ssr`'s copy loop: `o` is `b` with each of the `hits` (`fixed_scan`'s) `w` bytes replaced by `t`. `o` is the answer
/// and 16 bytes of slack, so a short run is one fixed-width move: measured, `ssr[xc;"ab";"xy"]` copies one subject byte and
/// two replacement bytes 333333 times.
pub fn ssr_fill(o: &mut [u8], b: &[u8], hits: &[i64], w: usize, t: &[u8]) {
    let (n, tn, wide) = (b.len(), t.len(), t.len() > 16);
    let mut tb = [0u8; 16];
    if !wide { tb[..tn].copy_from_slice(t) }
    let (mut i, mut at) = (0, 0);
    for &h in hits {
        let s = h as usize;
        if s - i <= 16 && i + 16 <= n { o[at..at + 16].copy_from_slice(&b[i..i + 16]) } else { copy_run(&mut o[at..at + s - i], &b[i..s]) }
        at += s - i;
        if wide { o[at..at + tn].copy_from_slice(t) } else { o[at..at + 16].copy_from_slice(&tb) }
        at += tn;
        i = s + w;
    }
    copy_run(&mut o[at..at + n - i], &b[i..]);
}
// ---- K8: ew.rs `like_*`, `fixed_*`, `ew_cmp_syms_run` (symbol patterns, fixed-width search, symbol comparisons) ----
/// `Order.symCmp` over two symbols: q's order (bytes unsigned, then length). Overlapping big-endian windows of 8, 4, 2, 1 bytes
/// (the last window ends at the shorter length), so a short symbol is a few compares and never a `memcmp` call (`[u8]::cmp` is one).
/// When the first window differs it decides; when it is equal the last one's first difference is the first of the bytes beyond it.
#[inline(always)]
pub fn sym_ord(a: &[u8], b: &[u8]) -> core::cmp::Ordering {
    macro_rules! win { ($t:ty, $s:expr, $at:expr) => { <$t>::from_be_bytes($s[$at..$at + size_of::<$t>()].try_into().unwrap()) } }
    macro_rules! two { ($t:ty, $n:expr) => { {
        let (x, y) = (win!($t, a, 0), win!($t, b, 0));
        if x != y { x.cmp(&y) } else { win!($t, a, $n - size_of::<$t>()).cmp(&win!($t, b, $n - size_of::<$t>())) }
    } } }
    let n = a.len().min(b.len());
    let c = if n >= 8 {
        let mut i = 0;
        loop {
            if i + 8 >= n { break win!(u64, a, n - 8).cmp(&win!(u64, b, n - 8)) }
            let (x, y) = (win!(u64, a, i), win!(u64, b, i));
            if x != y { break x.cmp(&y) }
            i += 8;
        }
    } else if n >= 4 { two!(u32, n) } else if n >= 2 { two!(u16, n) } else if n == 1 { a[0].cmp(&b[0]) } else { core::cmp::Ordering::Equal };
    c.then(a.len().cmp(&b.len()))
}
/// `copy_run`: `d = s` (equal lengths) by overlapping fixed-width moves up to 32 bytes, so a short run is no `memcpy` call.
#[inline(always)]
pub fn copy_run(d: &mut [u8], s: &[u8]) {
    macro_rules! mv { ($n:literal, $k:expr) => { { d[..$n].copy_from_slice(&s[..$n]); d[$k - $n..$k].copy_from_slice(&s[$k - $n..$k]) } } }
    let k = s.len();
    if k >= 32 { d.copy_from_slice(s) } else if k >= 16 { mv!(16, k) } else if k >= 8 { mv!(8, k) } else if k >= 4 { mv!(4, k) }
    else if k >= 2 { mv!(2, k) } else if k == 1 { d[0] = s[0] }
}
/// ew.rs `pat_item`: one parsed item of a `like` pattern; a set's ranges are `Pattern::rng[lo .. lo + 2 * n]`, pairs.
#[derive(Clone, Copy)]
pub enum Item { Star, Any, Lit(u8), Set { neg: bool, lo: usize, n: usize } }
/// `pack_bits` of `p(x, y)` over the symbols the shape indexes at elements `e0 ..`, `x` of `a` and `y` of `b`.
#[inline(always)]
pub fn pack_syms(shape: u8, a: &Syms, b: &Syms, o: &mut [u8], e0: usize, m: usize, p: impl Fn(&[u8], &[u8]) -> bool) {
    if m == 0 { return }
    match shape {
        k::VV => pack_bits(o, m, |i| p(a.at(e0 + i), b.at(e0 + i))),
        k::VA => { let y = b.at(0); pack_bits(o, m, |i| p(a.at(e0 + i), y)) }
        _ => { let x = a.at(0); pack_bits(o, m, |i| p(x, b.at(e0 + i))) }
    }
}
/// ew.rs `pattern`: the items and the ranges of every set, packed end to end.
pub struct Pattern { its: Vec<Item>, rng: Vec<u8> }
impl Pattern {
    /// `like_parse`, `parsePat` transcribed: `None` for two `*` in a row (q's `'nyi`) and a class that never closes (q's `'[`);
    /// a `[` never closed is refused, a range needs a byte after its `-` that is inside the pattern and is not `]`.
    pub fn parse(p: &[u8]) -> Option<Pattern> {
        let pn = p.len();
        let (mut its, mut rng) = (Vec::with_capacity(pn), Vec::with_capacity(2 * pn));
        let mut i = 0;
        while i < pn {
            let c = p[i];
            if c == b'*' {
                if matches!(its.last(), Some(Item::Star)) { return None }
                its.push(Item::Star);
                i += 1;
            } else if c == b'?' {
                its.push(Item::Any);
                i += 1;
            } else if c == b'[' {
                let mut j = i + 1;
                let neg = j < pn && p[j] == b'^';
                if neg { j += 1 }
                let lo = rng.len();
                let (mut closed, mut first) = (false, true);
                while j < pn {
                    if p[j] == b']' && !first { closed = true; j += 1; break }
                    if j + 2 < pn && p[j + 1] == b'-' && p[j + 2] != b']' { rng.push(p[j]); rng.push(p[j + 2]); j += 3 }
                    else { rng.push(p[j]); rng.push(p[j]); j += 1 }
                    first = false;
                }
                if !closed { return None }
                its.push(Item::Set { neg, lo, n: (rng.len() - lo) / 2 });
                i = j;
            } else {
                its.push(Item::Lit(c));
                i += 1;
            }
        }
        Some(Pattern { its, rng })
    }
    /// `like_hit`: byte `c` matches the non-`*` item `it`.
    #[inline(always)]
    fn hit(&self, it: Item, c: u8) -> bool {
        match it {
            Item::Any => true,
            Item::Lit(l) => c == l,
            Item::Set { neg, lo, n } => self.rng[lo..lo + 2 * n].chunks_exact(2).any(|r| r[0] <= c && c <= r[1]) != neg,
            Item::Star => false,
        }
    }
    /// `like_match`: the two-pointer wildcard walk, one `*` remembered and the position after it.
    #[inline]
    fn matches(&self, s: &[u8]) -> bool {
        let (its, n) = (&self.its[..], s.len());
        let (mut i, mut j, mut mark, mut star) = (0, 0, 0, usize::MAX);
        while i < n {
            match its.get(j) {
                Some(&it) if !matches!(it, Item::Star) && self.hit(it, s[i]) => { i += 1; j += 1 }
                Some(Item::Star) => { star = j; j += 1; mark = i }
                _ if star != usize::MAX => { j = star + 1; mark += 1; i = mark }
                _ => return false,
            }
        }
        while matches!(its.get(j), Some(Item::Star)) { j += 1 }
        j == its.len()
    }
    /// `fixed_width`: the item count, 0 where the pattern is empty or holds a `*` (q's two `'length` refusals).
    fn width(&self) -> usize { if self.its.iter().any(|it| matches!(it, Item::Star)) { 0 } else { self.its.len() } }
    /// `fixed_items`: a char atom operand is one literal byte and not a pattern, the one place `ss` and `ssr` differ from `like`.
    fn fixed(atom: bool, p: &[u8]) -> Option<Pattern> {
        if atom && p.len() == 1 { Some(Pattern { its: alloc::vec![Item::Lit(p[0])], rng: Vec::new() }) } else { Pattern::parse(p) }
    }
}
