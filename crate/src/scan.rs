#![forbid(unsafe_code)]
//! Column (a), scan.rs (A14): the running scans (sums, prds, mins, maxs, fills) over a dense payload and
//! the block skips over an encoded one. `scan_fill` and `scan_any_null` are AVX-512 in C: their vector bodies are in
//! `simd.rs`, which this module calls and finishes (the groups that hold a null, the tail).
use crate::pod::{self};
use crate::blocks::{Blocks, Grid, Src, tag};
use crate::coc::Coc;
use crate::ffi::{Form, Sink};
use crate::ids;
use crate::lean::{B, O};
use alloc::{format, string::String, vec::Vec};

// the verb, as QLean/Kernel/Scan.lean's `Verb` in constructor order


// ---- readers: the signed widths sign-extend and `byte` zero-extends; a boolean is one bit, LSB first ----

// ---- null tests: `0N` is the minimum of each signed width, byte and boolean have none, `char`'s is the blank ----

// ---- writers: an element's bytes. Truncating (the wrap of rules 3 and 4); `ws_i32` the narrowing `sums` answering
// `0N` on overflow ----














// ---- K3 (scan.rs `sc_bits_run`, `ema_*`, `mw_sent`, `mw_seed`, `mw_open`, `mw_close`) ----







// ---- the moving-window engine: scan.rs `mw_run` and its window macros (K4) ----















// ---- B7/B8: the column entry points of scan.rs's twelve Lean exports (ffi/scan.rs), over the payloads' bytes ----











#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{vec, vec::Vec};

    // `Op.fto` (Rel/Kernel/Op.lean's `#guard`s): rounding to `f32`, `-0` and an underflow to `-0` as `+0`, NaN as `2^63`
    #[test]
    fn fto() {
        let b = f64::to_bits;
        assert_eq!(op_word(FTO + 6, 0, b(2.5)), b(2.5));
        assert_eq!(op_word(FTO + 6, 0, b(-0.0)), 0);
        assert_eq!(op_word(FTO + 6, 0, b(f64::NAN)), 1 << 63);
        assert_eq!(op_word(FTO + 5, 0, b(0.1)), 0x3dcc_cccd);
        assert_eq!(op_word(FTO + 5, 0, b(-1e-50)), 0);
        assert_eq!(op_word(FTO + 5, 0, b(1e300)), 0x7f80_0000);
        assert_eq!(op_word(FTO + 4, 0, b(1.0)), 1 << 63);
    }

    // `2 msum 0W 0N 1 5 7`: the prefix past `O`'s range is null and stays null at both ends of the window; at 64 bits
    // the prefix wraps instead, onto the null and then past it
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
        45 => widen32(x),
        // `fto t`, the last constructor: its code is `FTO + t`; `cast s t`: `CAST + 13 s + t` (`op_code`)
        c if c >= FTO => fto_word(c - FTO, x),
        _ => cast_word(op, x),
    }
}

/// The code of `Op.fto t` is `FTO + t` (`t` a `QAtomicType` index), past every cast's code.
pub const FTO: u8 = CAST + 13 * 13;

/// `Op.eval (.fto t)` (Rel/Kernel/Op.lean `ftoWord`): the `f64` word `x` as the word of the float atom `t` nearest it
/// (`as f32` rounds to nearest even, as Lean's `Float.toFloat32`), a zero as `+0`; `2^63` at a NaN or a `t` holding
/// no float.
pub fn fto_word(t: u8, x: u64) -> u64 {
    const NONE: u64 = 1 << 63;
    let f = f64::from_bits(x);
    if f.is_nan() { return NONE }
    match t {
        6 => if f == 0.0 { 0 } else { x },
        5 => { let g = f as f32; if g == 0.0 { 0 } else { g.to_bits() as u64 } }
        _ => NONE,
    }
}

/// The code of `Op.cast s t` is `CAST + 13 * s + t` (`s`, `t` `QAtomicType` indices, below 13): one `u8` names every op.
pub const CAST: u8 = 46;

/// The op code of the Lean `Op` `o`: a nullary op is the scalar of its constructor index, `cast s t` (tag 46) a ctor
/// whose two `QAtomicType` fields are its scalar bytes 0 and 1, `fto t` (tag 47) one whose field is byte 0.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
pub fn op_code(o: crate::lean::B) -> u8 {
    if o.is_scalar() { o.unbox() as u8 }
    else if o.tag() == CAST as u32 { CAST + 13 * o.u8_field(0) + o.u8_field(1) }
    else { FTO + o.u8_field(0) }
}

/// `Op.eval (.cast s t)` (Rel/Kernel/Cast.lean `castWord`) at the code `CAST + 13 s + t`: the word `x` read at `s`
/// (`ofBits`), its value, and the word of `t` holding exactly that value (`QAtomicType.embed`, `word`: an integer
/// sign-extended, a float's bits, `+0` the one zero); `2^63` where there is none (a null, an infinity, a NaN, a value
/// `t` does not hold exactly, an atom holding no number). Lean's rounding-free `floatBits` is the native conversion
/// checked exact by converting back.
pub fn cast_word(code: u8, x: u64) -> u64 {
    const NONE: u64 = 1 << 63;
    #[derive(Clone, Copy)] enum V { I(i64), F(f64) }
    let (s, t) = ((code - CAST) / 13, (code - CAST) % 13);
    let int = |k: i64, nul: i64| if k == nul { None } else { Some(V::I(k)) };
    let v = match s {
        1 => Some(V::I(x as u8 as i64)),
        8 => int(x as u8 as i8 as i64, i8::MIN as i64),
        2 => int(x as u16 as i16 as i64, i16::MIN as i64),
        3 => int(x as u32 as i32 as i64, i32::MIN as i64),
        4 => int(x as i64, i64::MIN),
        5 => Some(f32::from_bits(x as u32) as f64).filter(|f| f.is_finite()).map(V::F),
        6 => Some(f64::from_bits(x)).filter(|f| f.is_finite()).map(V::F),
        _ => None,
    };
    // an integer `t` holds `k` where `k` is in its range; a float holds `k` where the conversion back is `k`
    let at = |lo: i64, hi: i64| v.and_then(|v| match v {
        V::I(k) => Some(k),
        // `f as i64` is exact below 2^63 in magnitude; converting back tests integrality without `fract` (not in `core`)
        V::F(f) => (-9223372036854775808.0 <= f && f < 9223372036854775808.0 && f as i64 as f64 == f).then_some(f as i64),
    }).filter(|k| lo <= *k && *k <= hi).map(|k| k as u64);
    let zero = |b: u64, z: bool| if z { 0 } else { b };
    let r = match t {
        1 => at(0, 255),
        8 => at(-(i8::MAX as i64), i8::MAX as i64),
        2 => at(-(i16::MAX as i64), i16::MAX as i64),
        3 => at(-(i32::MAX as i64), i32::MAX as i64),
        4 => at(-i64::MAX, i64::MAX),
        5 => v.and_then(|v| match v {
            V::I(k) => { let g = k as f32; (g as i128 == k as i128).then(|| zero(g.to_bits() as u64, g == 0.0)) }
            V::F(f) => { let g = f as f32; (g.is_finite() && g as f64 == f).then(|| zero(g.to_bits() as u64, g == 0.0)) }
        }),
        6 => v.and_then(|v| match v {
            V::I(k) => { let g = k as f64; (g as i128 == k as i128).then(|| zero(g.to_bits(), g == 0.0)) }
            V::F(f) => Some(zero(f.to_bits(), f == 0.0)),
        }),
        _ => None,
    };
    r.unwrap_or(NONE)
}

/// `body` with the const `$k` bound to the op `op` (0 ..= 45, `CAST` for every cast), so a loop over rows is compiled
/// once per op and its `op_word` folds to that op's arm: the `match` on the op runs once per block, not once per row.
macro_rules! by_op { ($op:expr, $k:ident => $body:expr) => { by_op!(@ $op, $k, $body; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17
    18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45) };
    (@ $op:expr, $k:ident, $body:expr; $($n:literal)*) => { match $op { $($n => { const $k: u8 = $n; $body })* _ => { const $k: u8 = CAST; $body } } } }

/// The writer's block size, `kscan`'s answer grid: a block of rows is computed whole in one scratch of this many words.
const BLK: usize = 1 << crate::DEFAULT_LG;
/// A block's `seg` bits as words.
type Seg = [u64; BLK / 64];

/// One column of `kscan` as `Enc.raw s n` reads it, a block of rows at a time: a dense payload of `w`-byte elements,
/// or a block source of `w`-byte elements cut by the mask `m` (`!0`, or `1` for a boolean `foR`, which `raw` reads at
/// its one bit). Each form reads 0 past what it holds, as `raw` does.
#[derive(Clone, Copy)]
pub(crate) enum Col<'a> { Dense(&'a [u8], usize), Blk(Blocks<'a>, usize, u64) }

/// `rawAll t n e` (Rel/Kernel/Scan.lean): `e` read as `Enc.raw t n`, whose every arm holds `n` words but the `#[]` ones,
/// which are the refusal unless `n = 0`. The CSV writer reads its columns through it too.
pub(crate) fn raw_all<'a>(t: u8, n: usize, e: B<'a>) -> Result<Col<'a>, String> {
    match Col::of(t, n, e) {
        Some(c) => Ok(c),
        None if n == 0 => Ok(Col::Dense(&[], 8)),
        None => Err(format!("kscan: a column holds 0 raw elements, not {n}")),
    }
}

impl<'a> Col<'a> {
    /// `Enc.raw s n e`'s arms; `None` where `raw` is `#[]`.
    fn of(s: u8, n: usize, e: B<'a>) -> Option<Col<'a>> {
        let (w, boolean) = (qtype_width(s), s == QT_BOOLEAN);
        match (e.tag(), w) {
            (tag::BYTES, Some(w)) if !boolean => Some(Col::Dense(e.field(0).bytes(), w)),
            (tag::FOR, Some(w)) if boolean => Some(Col::Blk(Blocks::of(e, w, n, "qlean_k_scan"), w, 1)),
            (tag::FOR | tag::ALP, Some(w)) if !boolean => Some(Col::Blk(Blocks::of(e, w, n, "qlean_k_scan"), w, !0)),
            // `pos` is `raw`'s at `i64` (type 4) only: the loop index
            (tag::POS, _) if s == 4 => Some(Col::Blk(Blocks::pos(n), 8, !0)),
            // ids of no bits (a dictionary of one entry) read 0 at every row
            (tag::ENUM, _) if s == QT_SYMBOL => Some(match ids::id_width(e.field(1).words().len().saturating_sub(1)) {
                0 => Col::Dense(&[], 8), lw => Col::Blk(Blocks::ids(e.field(2).bytes(), n, lw), 8, !0) }),
            _ => None,
        }
    }
    /// Rows `lo .. lo + out.len()` as words into `out`, each zero-extended from its width. `tmp` holds a block at 8
    /// bytes a row; a source on the writer's grid is decoded one block straight into it (or into `out` at 8 bytes).
    pub(crate) fn load(&self, lo: usize, out: &mut [u64], tmp: &mut [u8]) {
        match *self {
            Col::Dense(p, w) => widen(p.get(lo * w..).unwrap_or(&[]), w, out),
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
        // a `foR` boolean: the block decoded into the L1 scratch, each row's bit packed
        let (mut v, mut tmp) = (pod::Scr::<u64>::new(nb), pod::Scr::<u64>::new(nb));
        self.seg.load(lo, &mut v, pod::bytes_mut(&mut tmp));
        for (k, &x) in v.iter().enumerate() { g[k >> 6] |= (x & 1) << (k & 63) }
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
        // a cast's code carries its two atoms, so `CAST` stands for all of them and the row reads `self.op`
        let (nb, f) = (out.len(), |a, x| op_word(if OP == CAST { self.op } else { OP }, a, x));
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
        let (mut cs, mut c, mut tmp) = (alloc::vec![0u64; bs.len()], 0u64, pod::Scr::<u64>::new(self.n.min(BLK)));
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
        let (mut v, mut tmp) = (pod::Scr::<u64>::new(self.n.min(BLK)), pod::Scr::<u64>::new(self.n.min(BLK)));
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
/// The fold result is the row the fold visits last (row `n - 1`, row 0 under `rev`), taken from the block the writer
/// fills and cut to `t`'s width as `Enc.raw t` reads it back; `None` at `n = 0`, where no row is visited.
pub fn kscan<'a>(op: u8, rev: bool, s: u8, t: u8, n: usize, seg: B<'a>, es: &[B<'a>]) -> Result<(O, Option<u64>), String> {
    let g = raw_all(QT_BOOLEAN, n, seg)?;
    let cols = es.iter().map(|&e| raw_all(s, n, e)).collect::<Result<Vec<_>, _>>()?;
    let Some((&seed, xs)) = cols.split_first() else { return Err("kscan: es is empty; its first column is the seed".into()) };
    let mut r = Scan { op, rev, n, seg: g, seed, xs, carry: Vec::new() };
    if let Err(m) = op_eval(op, 0, 0) && r.zero() { return Err(m.into()) }
    let tw = qtype_width(t).ok_or("kscan: the answer type has no fixed width")?;
    r.carries();
    let (r, low) = (&r, if t == QT_BOOLEAN { 1 } else { !0u64 });
    // `raw t`'s cut: one bit at a boolean, `8 * tw` bits otherwise
    let cut = if t == QT_BOOLEAN { 1 } else if tw < 8 { (1u64 << (8 * tw)) - 1 } else { !0u64 };
    // the writer may fill blocks on several threads, so the one block holding `last` stores it atomically
    let (fin, last) = (core::sync::atomic::AtomicU64::new(0), if rev { 0 } else { n.wrapping_sub(1) });
    let e = Sink::new(n, 8, Form::For).enc().answer(&|buf: &mut [i64], lo: usize| {
        let o = pod::cast_mut::<u64>(pod::bytes_mut(buf)).expect("kscan: an i64 block is a u64 block");
        let (b, nb, mut w64) = (lo >> crate::DEFAULT_LG, o.len(), [0u64; BLK / 64]);
        // a compare against a constant block: the compare kernel's bits, each a row's word
        if (9..=14).contains(&r.op) && r.cmp_blk(b, lo, nb, &mut w64, pod::bytes_mut(&mut pod::Scr::<u64>::new(nb + 8))) {
            for (k, v) in o.iter_mut().enumerate() { *v = w64[k >> 6] >> (k & 63) & 1 }
        } else {
            r.block(lo, r.carry[b], o);
            if low != !0 { for v in o.iter_mut() { *v &= low } }
        }
        if (lo..lo + nb).contains(&last) { fin.store(o[last - lo] & cut, core::sync::atomic::Ordering::Relaxed) }
    });
    // every row is written, so at `n > 0` the block holding `last` stored it
    Ok((e, (n > 0).then(|| fin.load(core::sync::atomic::Ordering::Relaxed))))
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
    fn enc_bits(v: &[u64]) -> O { enc_for(&v.iter().map(|b| b & 1).collect::<Vec<_>>(), 1) }
    fn parts(o: &O) -> Vec<Vec<u8>> {
        let b = o.borrow();
        (0..if b.tag() == tag::BYTES { 1 } else { 2 }).map(|i| b.field(i).bytes().to_vec()).collect()
    }
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
                Some(w) => { let ws: Vec<u64> = r.iter().map(|v| if t == QT_BOOLEAN { v & 1 } else { *v }).collect(); let fin = if rev { ws.first() } else { ws.last() }; Ok((parts(&enc_for(&ws, 8)), fin.map(|v| if w < 8 { v & ((1 << (8 * w)) - 1) } else { *v }))) }
            }),
        };
        let bs: Vec<B> = es.iter().map(|e| e.0.borrow()).collect();
        assert_eq!(kscan(op, rev, s, t, n, g.borrow(), &bs).map(|(o, v)| (parts(&o), v)), want, "op {op} rev {rev} s {s} t {t} n {n}");
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
                        check(op, s, 5, n, g, &[col(&y), col(&x)]);
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
                assert_eq!(kscan(0, false, QT_BOOLEAN, 6, n, enc_bits(&segs[0]).borrow(), &[e.borrow()]).map(|(o, v)| (parts(&o), v)),
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
    // a compare against a constant at, below and above a patched block's frame, the column on either side: `Tab.comp`'s
    // `p < n` of 81 × 729 (each of `n` rows before its `m` partners, block 0 framed at 81 with 0 and 1 patched) once
    // matched every row of that block, `t - 1` wrapping at `t = 0`
    #[test] fn compare_against_a_constant_at_the_frame() {
        let (n, m) = (81u64, 729u64);
        let p: Vec<u64> = (0..n).flat_map(|g| core::iter::once(g).chain(n + m * g..n + m * (g + 1))).collect();
        let k = p.len();
        for v in [n - 1, n, n + 1] {
            for op in [9u8, 10, 11, 12, 13, 14] {
                check(op, 6, 6, k, &vec![1; k], &[(enc_for(&p, 8), p.clone()), (enc_for(&vec![v; k], 8), vec![v; k])]);
                check(op, 6, 6, k, &vec![1; k], &[(enc_for(&vec![v; k], 8), vec![v; k]), (enc_for(&p, 8), p.clone())]);
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

