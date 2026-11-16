#![forbid(unsafe_code)]
//! Column (a), coc.h: the ALP (decimal float) column. `Cocf` is the read view of coc.h:1443 `cocf` (A5: view,
//! block loads, decode, the finishing step); the encoder's per-block steps are A9.
use crate::coc::{Coc, Meta};
use crate::layout::{Tail, exc_layout};
use crate::pod;
use crate::enc::{EncMeta, EncPack};
use crate::pod::Pod;
use alloc::vec::Vec;

/// coc.h:1443 `cocf`: the integer column `c` (the FoR encoding of the decimals `d`) plus each block's exponent and
/// the float patches. `'a` as `Coc`'s. Built from C by `ffi::CCocf::view`.
#[derive(Clone, Copy)]
pub struct Cocf<'a> {
    pub c: Coc<'a>,
    /// nblk
    pub exp: &'a [i8],
    /// nblk + 1, prefix sums into `exc_pos`/`exc_raw`
    pub exc_off: &'a [u32],
    /// nexc, position inside its block
    pub exc_pos: &'a [u16],
    /// nexc elements of 4 (`f32`) or 8 bytes
    pub exc_raw: &'a [u8],
    pub f32: bool,
}

/// The element of an ALP column: `f32` (q real) or `f64` (q float). The ALP template's `COC_F`.
pub trait Flt: Pod + PartialEq {
    const F32: bool;
    fn to_f64(self) -> f64;
    fn of_f64(v: f64) -> Self;
    /// coc.h:2567 `bits_f32`/`bits_f64`, widened
    fn bits(self) -> u64;
}
impl Flt for f32 {
    const F32: bool = true;
    fn to_f64(self) -> f64 { self as f64 }
    fn of_f64(v: f64) -> Self { v as f32 }
    fn bits(self) -> u64 { self.to_bits() as u64 }
}
impl Flt for f64 {
    const F32: bool = false;
    fn to_f64(self) -> f64 { self }
    fn of_f64(v: f64) -> Self { v }
    fn bits(self) -> u64 { self.to_bits() }
}

// ---- A5: coc.h:1341-1437, 1689 ----
/// coc.h:1303 `POW10`: `10^e`, exact as doubles up to 1e18.
pub(crate) const POW10: [f64; 19] = [1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11, 1e12, 1e13, 1e14, 1e15,
                              1e16, 1e17, 1e18];
/// coc.h:1341 `alp_offsets`: per-block patch counts in `exc_off[1..=nblk]` into prefix sums; answers the total.
pub fn alp_offsets(exc_off: &mut [u32], nblk: usize) -> usize {
    exc_off[0] = 0;
    for b in 0..nblk { exc_off[b + 1] = exc_off[b + 1].wrapping_add(exc_off[b]) }
    exc_off[nblk] as usize
}
impl<'a> Cocf<'a> {
    /// coc.h:1351 `cocf_meta_view`: metadata `m` and the ALP part `a` of an `n`-element column; `None` = misaligned
    /// or short. The pack is left empty, as `Coc::attach` leaves it for a column with none: the caller sets `c.pack`.
    pub fn meta_view(m: &'a [u8], a: &'a [u8], n: usize) -> Option<Cocf<'a>> {
        let c = Coc::attach(Meta::new(m, n)?, &[])?;
        let nexc = u64::from_ne_bytes(a.get(..8)?.try_into().ok()?);
        let f32 = u64::from_ne_bytes(a.get(8..16)?.try_into().ok()?) & 1 != 0;
        let esz = if f32 { 4 } else { 8 };
        if nexc > a.len() as u64 { return None }
        let (nexc, mb) = (nexc as usize, c.meta.mblk);
        let l = exc_layout(mb, nexc, esz, Tail::Exps)?;
        if a.len() < l.size { return None }
        Some(Cocf { c, exp: pod::cast(&a[l.tail..l.tail + mb])?, exc_off: pod::cast(&a[l.off..l.off + 4 * (mb + 1)])?,
                    exc_pos: pod::cast(&a[l.pos..l.pos + 2 * nexc])?, exc_raw: &a[l.raw..l.raw + nexc * esz], f32 })
    }
    /// coc.h:1387 `cocf_load_range`: elements `i0 .. i1` of block `b` (residuals `p` at width `w`) into `out` as
    /// `f32`/`f64` bytes, at their own places (`out[i * esz]`).
    pub fn load_range(&self, b: usize, p: &[u8], w: u8, i0: usize, i1: usize, out: &mut [u8]) {
        let (base, p10, esz) = (self.c.meta.base[b] as u64, POW10[self.exp[b] as usize], if self.f32 { 4 } else { 8 });
        if self.f32 { restore::<f32>(base, p10, p, w, i0, i1, out) } else { restore::<f64>(base, p10, p, w, i0, i1, out) }
        for j in self.exc_off[b] as usize..self.exc_off[b + 1] as usize {
            let at = self.exc_pos[j] as usize;
            if (i0..i1).contains(&at) { out[at * esz..(at + 1) * esz].copy_from_slice(&self.exc_raw[j * esz..(j + 1) * esz]) }
        }
    }
    /// coc.h:1416 `cocf_lanes`: block `b`'s residuals as whole lanes (`buf`, BLK * 8, when they must be unpacked);
    /// answers them, the lane width and the residual width.
    pub fn lanes<'b>(&self, b: usize, nb: usize, buf: &'b mut [u8]) -> (&'b [u8], u8, u8) where 'a: 'b {
        let (w0, at) = (self.c.meta.width[b], self.c.meta.off[b] as usize);
        let mut w = w0;
        let p = crate::coc::lanes(&self.c.pack[at..at + crate::BLK * w0 as usize / 8], &mut w, nb, buf);
        (p, w, w0)
    }
    /// coc.h:1421 `cocf_load_blk`: block `b`'s first `nb` elements into `out`, patches applied.
    pub fn load_blk(&self, b: usize, nb: usize, out: &mut [u8]) {
        let mut lb = [0u64; crate::BLK];
        let (p, w, _) = self.lanes(b, nb, pod::bytes_mut(&mut lb));
        self.load_range(b, p, w, 0, nb, out)
    }
    /// coc.h:1432 `cocf_decode`: blocks `b0 .. b1` into `out`, block `b` at `out[b * BLK * esz ..]`.
    pub fn decode(&self, b0: usize, b1: usize, out: &mut [u8]) {
        let (n, esz) = (self.c.meta.n, if self.f32 { 4 } else { 8 });
        for b in b0..b1 {
            let lo = b * crate::BLK;
            let nb = if lo + crate::BLK < n { crate::BLK } else { n - lo };
            self.load_blk(b, nb, &mut out[lo * esz..(lo + nb) * esz])
        }
    }
}
impl Cocf<'_> {
    /// coc.h:867 `exc_val`: patch `j` widened to a double, as the reduction layer reads it.
    fn exc_val(&self, j: usize) -> f64 {
        let r = &self.exc_raw;
        if self.f32 { f32::from_ne_bytes(r[j * 4..j * 4 + 4].try_into().unwrap()) as f64 }
        else { f64::from_ne_bytes(r[j * 8..j * 8 + 8].try_into().unwrap()) }
    }
    /// coc.h:874 `alp_dec`: `d / 10^e`, cast through the column's element type; the decoder's own expression.
    fn dec(&self, d: i64, e: i32) -> f64 {
        let v = d as f64 / POW10[e as usize];
        if self.f32 { v as f32 as f64 } else { v }
    }
    /// coc.h:883 `alp_thresh`: `x < v` in the value domain is `d < t` in the block's integer domain at exponent `e`, with
    /// `t = ceil(v * 10^e)` corrected against the decoder. Out of reach either way clamps outside 2^53, so every `d`
    /// counts (or none does): a value a block could hold would answer a different question.
    pub fn thresh(&self, v: f64, e: i32) -> i64 {
        let y = ceil(v * POW10[e as usize]);
        if !(y > -P53) { return i64::MIN / 2 } // the negated form also catches NaN
        if !(y < P53) { return i64::MAX / 2 }
        let mut t = y as i64;
        for _ in 0..4 { if self.dec(t - 1, e) >= v { t -= 1 } else { break } }
        for _ in 0..4 { if self.dec(t, e) < v { t += 1 } else { break } }
        t
    }
    /// The block's first `nb`-element grid: `(lo, nb)` of block `b`.
    fn blk(&self, b: usize) -> usize { (self.c.meta.n - b * crate::BLK).min(crate::BLK) }
    /// coc.h:926 `cocf_min`: metadata and the patch list only; NaN loses every comparison, and the `+inf` seed is q's `0w`.
    /// A block of nothing but patches has no base to offer.
    pub fn min(&self) -> f64 {
        let m = (0..self.c.meta.nblk).filter(|&b| (self.exc_off[b + 1] - self.exc_off[b]) as usize != self.blk(b))
            .fold(f64::INFINITY, |m, b| { let v = self.dec(self.c.meta.base[b], self.exp[b] as i32); if v < m { v } else { m } });
        (0..self.exc_pos.len()).fold(m, |m, j| { let v = self.exc_val(j); if v < m { v } else { m } })
    }
    /// coc.h:938 `cocf_max`, dually seeded with `-inf`.
    pub fn max(&self) -> f64 {
        let m = (0..self.c.meta.nblk).filter(|&b| (self.exc_off[b + 1] - self.exc_off[b]) as usize != self.blk(b))
            .fold(f64::NEG_INFINITY, |m, b| { let v = self.dec(self.c.meta.maxv[b], self.exp[b] as i32); if v > m { v } else { m } });
        (0..self.exc_pos.len()).fold(m, |m, j| { let v = self.exc_val(j); if v > m { v } else { m } })
    }
    /// each block's threshold, from its exponent, the threshold moved into the integer domain once per exponent
    fn thresholds(&self, v: f64) -> Vec<i64> {
        let t: Vec<i64> = (0..=MAXE as i32).map(|e| self.thresh(v, e)).collect();
        self.exp[..self.c.meta.nblk].iter().map(|&e| t[e as usize]).collect()
    }
    /// coc.h:954 `cocf_count_lt`: `x < v` with C's rule that `NaN < v` is false, the integral kernel run per block at that
    /// block's threshold, whole-block skip included.
    pub fn count_lt(&self, v: f64) -> usize {
        let (ts, mut buf) = (self.thresholds(v), Vec::new());
        let mut k = 0usize;
        for (b, &t) in ts.iter().enumerate() {
            k = k.wrapping_add(self.c.count_lt_blk(b, self.blk(b), t, &mut buf));
            let counted = (self.c.meta.base[b] < t) as usize; // what the kernel scored for a residual 0
            for j in self.exc_off[b] as usize..self.exc_off[b + 1] as usize {
                k = k.wrapping_add((self.exc_val(j) < v) as usize).wrapping_sub(counted);
            }
        }
        k
    }
    /// coc.h:970 `cocf_mask_lt`: `x < v` into `out` (`ceil(n / 64)` words, zeroed here), a patch scored by its own value.
    pub fn mask_lt(&self, v: f64, out: &mut [u64]) {
        out.fill(0);
        crate::codec::mask_blks(&self.c, crate::cocops::LT, &self.thresholds(v), out);
        for b in 0..self.c.meta.nblk {
            let at = (b * crate::BLK >> 6).min(out.len());
            let w64 = &mut out[at..];
            for j in self.exc_off[b] as usize..self.exc_off[b + 1] as usize {
                let p = self.exc_pos[j] as usize;
                let one = 1u64 << (p & 63);
                // a patch past the bitmap belongs to an element a clamped view does not show; C wrote past `out` for it
                if let Some(w) = w64.get_mut(p >> 6) { *w = (*w & !one) | if self.exc_val(j) < v { one } else { 0 } }
            }
        }
    }
}
/// `cocf_load_range`'s decimals: `base + residual` as an integer over `p10`, narrowed to `F`. `p` is read at `w` bits.
fn restore<F: Flt>(base: u64, p10: f64, p: &[u8], w: u8, i0: usize, i1: usize, out: &mut [u8]) {
    let o = &mut pod::cast_mut::<F>(&mut out[i0 * size_of::<F>()..i1 * size_of::<F>()])
        .expect("qlean: cocf output misaligned for its element")[..];
    fn put<F: Flt>(o: &mut [F], i0: usize, base: u64, p10: f64, get: impl Fn(usize) -> u64) {
        for (k, x) in o.iter_mut().enumerate() { *x = F::of_f64(base.wrapping_add(get(i0 + k)) as i64 as f64 / p10) }
    }
    match w {
        0 => put(o, i0, base, p10, |_| 0),
        8 => put(o, i0, base, p10, |i| p[i] as u64),
        16 => { let q = pod::cast::<u16>(p).expect("qlean: cocf lanes misaligned"); put(o, i0, base, p10, |i| q[i] as u64) }
        32 => { let q = pod::cast::<u32>(p).expect("qlean: cocf lanes misaligned"); put(o, i0, base, p10, |i| q[i] as u64) }
        64 => { let q = pod::cast::<u64>(p).expect("qlean: cocf lanes misaligned"); put(o, i0, base, p10, |i| q[i]) }
        _ => { let m = (1u64 << w) - 1; put(o, i0, base, p10, |i| (p[(i * w as usize) >> 3] as u64 >> ((i * w as usize) & 7)) & m) }
    }
}
/// coc.h:1689 `alp_fin_blk`: block `b`'s decimals `d` (exponents `ee`, first `nb`) at the block exponent `be`
/// into the integer metadata; answers the patch count.
pub fn alp_fin_blk(m: &mut EncMeta, be: i32, d: &mut [i64], ee: &[i8], nb: usize) -> u32 {
    let nexc = exc_as_base(d, ee, nb);
    **m.exp.as_mut().expect("qlean: alp_fin_blk on metadata with no exponent slot") = be as i8;
    crate::enc::encode_meta_blk::<i64>(m, d, nb);
    nexc
}
/// `alp_fin_blk`'s first half: every exception's decimal becomes the block minimum (0 when all are), so it packs as
/// residual 0; answers the exception count.
fn exc_as_base(d: &mut [i64], ee: &[i8], nb: usize) -> u32 {
    let (d, ee) = (&mut d[..nb], &ee[..nb]);
    let nexc = ee.iter().filter(|&&e| e < 0).count();
    let mn = if nexc == nb { 0 } else { d.iter().zip(ee).filter(|&(_, &e)| e >= 0).map(|(&x, _)| x).min().unwrap() };
    for (x, &e) in d.iter_mut().zip(ee) { if e < 0 { *x = mn } }
    nexc as u32
}

// ---- A9: coc.h:2441-2600, the ALP encoder per block, one instance per `Flt` ----
const MAXE: usize = crate::layout::ALP_MAXE as usize;
/// coc.h:1319 `ALP_P53`: a product at or past 2^53 is not an exact integer.
const P53: f64 = 9007199254740992.0;
/// 2^49: `dexp`'s bound, under which three trials decide a double.
const P49: f64 = 562949953421312.0;
/// C's `nearbyint` (ties to even, the default mode) for |s| < 2^53, without libm: adding and removing 2^52 of the
/// sign of `s` rounds at the unit place; from 2^52 on every double is already an integer.
fn rint(s: f64) -> f64 { let c = 4503599627370496.0f64.copysign(s); if s.abs() < 4503599627370496.0 { (s + c) - c } else { s } }
/// libm's `ceil` below 2^52, where a double is not yet an integer; at or past it, and NaN, `x` itself (core has none).
fn ceil(x: f64) -> f64 { if x.abs() < 4503599627370496.0 { let t = x as i64 as f64; if t < x { t + 1.0 } else { t } } else { x } }
/// `cvt_nearest` for a whole block, where the intrinsic would stop the loop vectorising: `rint`, then the integer
/// read off the bits (|s| < 2^53, so the shift is at most 52 and a value under 1 shifts out to 0).
fn nearest(s: f64) -> i64 {
    let b = rint(s).to_bits();
    let m = ((b & ((1 << 52) - 1)) | 1 << 52) >> 1075u64.wrapping_sub((b >> 52) & 0x7ff).min(63);
    if (b as i64) < 0 { -(m as i64) } else { m as i64 }
}
/// coc.h:1703 `COC_SENT`: the exponent field all ones, tested on the raw bits (NaN and infinities).
fn sent<F: Flt>(x: F) -> bool { let (s, m) = if F::F32 { (23, 0xff) } else { (52, 0x7ff) }; x.bits() >> s & m == m }
/// coc.h:2448 `dec_f64`: `d / 10^e`. It divides, as ALP written with a multiply by 10^-e is another operation.
pub fn dec(d: i64, e: i32) -> f64 { d as f64 / POW10[e as usize] }
/// coc.h:2453 `dat_f32`/`dat_f64`: `x` as a decimal at exponent `e`, or `None` when it does not round-trip. The
/// comparison is on bits, so -0.0 (which decodes as +0.0) is refused.
pub fn dat<F: Flt>(x: F, e: i32) -> Option<i64> {
    let s = x.to_f64() * POW10[e as usize];
    if !(s.abs() < P53) { return None }
    let r = crate::simd::cvt_nearest(s);
    (F::of_f64(dec(r, e)).bits() == x.bits()).then_some(r)
}
/// coc.h:2471 `dexp_f32`/`dexp_f64`: the smallest exponent at which `x` round-trips; -1 = none. At `f64` a
/// non-decimal fails three trials from the largest `E` with |x| 10^E < 2^49, and then fails every exponent.
pub fn dexp<F: Flt>(x: F) -> i32 {
    if !F::F32 {
        let v = x.to_f64().abs();
        let e = (1..=MAXE).rev().find(|&e| v * POW10[e] < P49).unwrap_or(0);
        if v * POW10[e] < P49 && !(e..=(e + 2).min(MAXE)).any(|t| dat(x, t as i32).is_some()) { return -1 }
    }
    (0..=MAXE).find(|&e| dat(x, e as i32).is_some()).map_or(-1, |e| e as i32)
}
/// coc.h:2566 `dat_blk`: `dat` at one exponent over a block, branch-free so that it vectorises: `ok[i]`, and `d[i]`
/// where it is set. A sentinel is never ok, its product being NaN or infinite.
pub fn dat_blk<F: Flt>(x: &[F], e: i32, d: &mut [i64], ok: &mut [u8]) {
    let p = POW10[e as usize];
    for ((&x, d), ok) in x.iter().zip(d).zip(ok) {
        let s = x.to_f64() * p;
        let inn = s.abs() < P53;
        let r = nearest(if inn { s } else { 0.0 });
        *d = r;
        *ok = (inn & (F::of_f64(r as f64 / p).bits() == x.bits())) as u8;
    }
}
/// coc.h:2498 `alp_meta_blk`'s search: each element's own exponent into `ee` (-1 = sentinel or not a decimal) and the
/// block exponent, their maximum. At `f64` `dexp`'s three-trial refusal runs over the whole block first, and only
/// what passes pays the exponent search; at `f32` the trials are `dat_blk` passes, until every element that can hit has.
pub fn alp_exps<F: Flt>(x: &[F], nb: usize, ee: &mut [i8]) -> i32 {
    let (x, ee) = (&x[..nb], &mut ee[..nb]);
    if !F::F32 {
        let (mut ex, mut maybe) = ([0i64; crate::BLK], [0i64; crate::BLK]);
        for (m, v) in maybe.iter_mut().zip(x) { *m = !(v.to_f64().abs() < P49) as i64 }
        for e in 1..=MAXE { for (k, v) in ex.iter_mut().zip(x) { *k += (v.to_f64().abs() * POW10[e] < P49) as i64 } }
        for k in 0..3 {
            for ((m, &e), v) in maybe.iter_mut().zip(&ex).zip(x) {
                let (v, p) = (v.to_f64(), POW10[(e + k).min(MAXE as i64) as usize]);
                let s = v * p;
                let hit = (s.abs() < P53) & (rint(s) / p == v);
                *m = if *m != 0 { *m } else { hit as i64 * (k + 1) };
            }
        }
        // `maybe` is 1 + the first trial that hit: a hit at E means the smallest e may be anywhere up to E, so it is
        // searched; a first hit at E + 1 or E + 2 is the smallest, every e <= E failing with E.
        let (mut at, mut m) = ([0u16; crate::BLK], 0);
        for i in 0..nb {
            ee[i] = if maybe[i] > 1 { (ex[i] + maybe[i] - 1) as i8 } else { -1 };
            at[m] = i as u16;
            m += (maybe[i] == 1) as usize;
        }
        for &i in &at[..m] {
            let i = i as usize;
            if !sent(x[i]) { for t in 0..=MAXE { if ee[i] >= 0 { break } if dat(x[i], t as i32).is_some() { ee[i] = t as i8 } } }
        }
        return ee.iter().fold(0, |be, &e| be.max(e as i32));
    }
    let (mut d, mut ok) = ([0i64; crate::BLK], [0u8; crate::BLK]);
    for (e, &v) in ee.iter_mut().zip(x) { *e = if sent(v) { -2 } else { -1 } }
    let mut left = ee.contains(&-1);
    for e in 0..=MAXE as i8 {
        if !left { break }
        dat_blk(x, e as i32, &mut d, &mut ok);
        left = false;
        for (s, &k) in ee.iter_mut().zip(&ok) { if *s == -1 && k != 0 { *s = e } left |= *s == -1 }
    }
    for s in ee.iter_mut() { *s = (*s).max(-1) }
    ee.iter().fold(0, |be, &e| be.max(e as i32))
}
/// coc.h:2498 `alp_meta_blk`: block metadata (exponent into `m.exp`); answers the patch count.
pub fn alp_meta_blk<F: Flt>(m: &mut EncMeta, x: &[F], nb: usize) -> u32 {
    let mut ee = [0i8; crate::BLK];
    let be = alp_exps(x, nb, &mut ee);
    alp_meta_at(m, x, nb, be, &mut ee)
}
/// `alp_meta_at`'s re-check: `d` at the block exponent `be`, and an element that is not exact there becomes an exception.
fn recheck<F: Flt>(x: &[F], nb: usize, be: i32, ee: &mut [i8], d: &mut [i64]) {
    let mut ok = [0u8; crate::BLK];
    dat_blk(&x[..nb], be, d, &mut ok);
    for (e, &k) in ee[..nb].iter_mut().zip(&ok) { if k == 0 { *e = -1 } }
}
/// coc.h:2577 `alp_meta_at`: the metadata at the given block exponent `be`; per-element exponents into `ee`.
pub fn alp_meta_at<F: Flt>(m: &mut EncMeta, x: &[F], nb: usize, be: i32, ee: &mut [i8]) -> u32 {
    let mut d = [0i64; crate::BLK];
    recheck(x, nb, be, ee, &mut d);
    alp_fin_blk(m, be, &mut d, ee, nb)
}
/// coc.h:2588 `alp_exc_at`: the patch count at `be`, stopping past `lim`.
pub fn alp_exc_at<F: Flt>(x: &[F], be: i32, lim: u32) -> u32 {
    let mut n = 0;
    for &v in x { if n >= lim { break } n += (sent(v) || dat(v, be).is_none()) as u32 }
    n
}
/// coc.h:2596 `alp_meta_exp`: `alp_meta_at` for elements not searched: only a sentinel is marked beforehand.
pub fn alp_meta_exp<F: Flt>(m: &mut EncMeta, x: &[F], nb: usize, be: i32) -> u32 {
    let mut ee = [0i8; crate::BLK];
    exp_marks(x, nb, &mut ee);
    alp_meta_at(m, x, nb, be, &mut ee)
}
/// `alp_meta_exp`'s marks: only a sentinel is an exception beforehand.
fn exp_marks<F: Flt>(x: &[F], nb: usize, ee: &mut [i8]) { for (e, &v) in ee.iter_mut().zip(&x[..nb]) { *e = if sent(v) { -1 } else { 0 } } }
/// coc.h:2619 `alp_patch_blk`: block `b` of `o` with the `ix.len()` writes `ix`/`v` applied, as pass 1 wants it at
/// the block's OLD exponent, no search: `d` the old decimals patched, `ee[i]` -1 at an old exception not overwritten and
/// -2 at a new one (a sentinel, or not exact at that exponent). Answers the exponent the search would raise it to, or -1:
/// only a new value can need more than the old exponent, and the caller keeps whichever leaves fewer exceptions.
pub fn alp_patch_blk<F: Flt>(o: &Cocf, b: usize, nb: usize, ix: &[u64], v: &[F], d: &mut [i64], ee: &mut [i8]) -> i32 {
    let (e, mut alt, ee) = (o.exp[b] as i32, -1, &mut ee[..nb]);
    o.c.decode_blk(b, nb, &mut d[..nb]);
    ee.fill(0);
    for &i in &o.exc_pos[o.exc_off[b] as usize..o.exc_off[b + 1] as usize] { ee[i as usize] = -1 }
    for (&k, &v) in ix.iter().zip(v) {
        let i = (k - (b * crate::BLK) as u64) as usize;
        if sent(v) { ee[i] = -2; continue }
        if let Some(r) = dat(v, e) { d[i] = r; ee[i] = 0; continue }
        ee[i] = -2;
        let de = dexp(v);
        if de > e && de > alt { alt = de }
    }
    alt
}
/// coc.h:2640 `alp_patch_pack`: the pack step for a block `alp_patch_blk` rewrote.
pub fn alp_patch_pack<F: Flt>(p: &mut EncPack, o: &Cocf, ix: &[u64], v: &[F], d: &mut [i64], ee: &[i8], raw: &mut [F]) {
    let (b, nb, lo) = (p.b, p.nb, (p.b * crate::BLK) as u64);
    let oraw = pod::cast::<F>(o.exc_raw).expect("qlean: alp_patch_pack: old patches misaligned");
    let (mut j, mut k, mut q) = (o.exc_off[b] as usize, 0, 0);
    for i in (0..nb).filter(|&i| ee[i] < 0) {
        d[i] = p.base;
        p.pos[q] = i as u16;
        // both sources ascend by position, so one cursor each finds them
        raw[q] = if ee[i] == -2 { while ix[k] - lo != i as u64 { k += 1 } v[k] } else { while o.exc_pos[j] as usize != i { j += 1 } oraw[j] };
        q += 1;
    }
    crate::enc::pack_block(&mut *p.res, &d[..nb], nb, p.base, p.width)
}
/// coc.h:2659 `alp_pack_blk`: residuals and float patches of one block at exponent `be`. An exception is an element
/// `dat` refuses at `be`, which is pass 1's set: a sentinel fails `dat` on its magnitude, a non-decimal at every e.
pub fn alp_pack_blk<F: Flt>(p: &mut EncPack, be: i32, x: &[F], raw: &mut [F]) {
    let (nb, mut d) = (p.nb, [0i64; crate::BLK]);
    holes(&x[..nb], be, p.base, &mut d, p.pos, raw);
    crate::enc::pack_block(&mut *p.res, &d[..nb], nb, p.base, p.width)
}
/// `alp_pack_blk` before the pack: the decimals `d` with each exception's residual 0 (`d = base`), its position and bits.
fn holes<F: Flt>(x: &[F], be: i32, base: i64, d: &mut [i64], pos: &mut [u16], raw: &mut [F]) {
    let mut ok = [0u8; crate::BLK];
    dat_blk(x, be, d, &mut ok);
    for (j, i) in (0..x.len()).filter(|&i| ok[i] == 0).enumerate() { d[i] = base; pos[j] = i as u16; raw[j] = x[i] }
}


impl<'a> Cocf<'a> {
    /// coc.h `cocf_view`: `meta_view` with the pack `pv` attached; `None` as `meta_view`'s.
    pub fn view(mv: &'a [u8], pv: &'a [u8], av: &'a [u8], n: usize) -> Option<Cocf<'a>> {
        let mut f = Self::meta_view(mv, av, n)?;
        f.c.pack = pv;
        Some(f)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BLK, pod::bytes_mut};

    // Expected values from coc.h's alp_thresh: the clamps outside 2^53 and the ceil at an exponent
    #[test] fn thresh_clamps_and_rounds_up() {
        let (z, o, w) = ([0i64], [0u64], [0u8]);
        let meta = Meta { base: &z, maxv: &z, off: &o, bsum: &z, width: &w, sumnul: 0, sumn: 0, n: 1, nblk: 1, mblk: 1 };
        let f = Cocf { c: Coc { meta, pack: &[], exc: None, fdelta: None }, exp: &[0], exc_off: &[0, 0], exc_pos: &[], exc_raw: &[], f32: false };
        assert_eq!([f.thresh(f64::NAN, 0), f.thresh(1e300, 0), f.thresh(-1e300, 3), f.thresh(f64::INFINITY, 2)],
                   [i64::MIN / 2, i64::MAX / 2, i64::MIN / 2, i64::MAX / 2]);
        assert_eq!([f.thresh(2.5, 0), f.thresh(-2.5, 0), f.thresh(3.0, 0), f.thresh(1.5, 1), f.thresh(0.1, 1), f.thresh(0.3, 1)], [3, -2, 3, 15, 1, 3]);
    }
    // Expected values come from the original C: `encode_f64` of [1.5, 2.25, NaN, 100.0] (exponent 2, base 150, width 14, one
    // patch) patched by [1 -> 1.25, 3 -> 0.1234567], /data/tmp/qrs/A17/one2.c; the random comparison is /data/tmp/qrs/A17/diff.c.
    #[test] fn patch_blk_keeps_the_old_exponent_and_answers_the_one_the_search_would_pick() {
        let (base, maxv, off, bsum, width) = ([150i64], [10000i64], [0u64], [0i64], [14u8]);
        let meta = Meta { base: &base, maxv: &maxv, off: &off, bsum: &bsum, width: &width, sumnul: 0, sumn: 4, n: 4, nblk: 1, mblk: 1 };
        let mut pack = vec![0u8; BLK * 14 / 8];
        pack[..7].copy_from_slice(&[0, 192, 18, 0, 0, 232, 153]); // residuals 0, 75, 0, 9850
        let raw = f64::NAN.to_ne_bytes();
        let o = Cocf { c: Coc { meta, pack: &pack, exc: None, fdelta: None }, exp: &[2], exc_off: &[0, 1], exc_pos: &[2], exc_raw: &raw, f32: false };
        let (mut d, mut ee) = ([0i64; BLK], [0i8; BLK]);
        assert_eq!(alp_patch_blk(&o, 0, 4, &[1, 3], &[1.25f64, 0.1234567], &mut d, &mut ee), 7);
        assert_eq!((&d[..4], &ee[..4]), (&[150, 125, 150, 10000][..], &[0, 0, -1, -2][..]));
    }

    struct Cur { w: Vec<u64>, at: usize }
    impl Cur {
        fn u(&mut self) -> u64 { self.at += 1; self.w[self.at - 1] }
        fn blob(&mut self) -> (Vec<u64>, usize) {
            let len = self.u() as usize; let k = len.div_ceil(8);
            let v = self.w[self.at..self.at + k].to_vec(); self.at += k; (v, len)
        }
    }
    fn fnv(b: &[u8]) -> u64 { b.iter().fold(14695981039346656037u64, |h, &x| (h ^ x as u64).wrapping_mul(1099511628211)) }
    fn fnv_w(v: &[u64]) -> u64 { fnv(&v.iter().flat_map(|x| x.to_ne_bytes()).collect::<Vec<u8>>()) }

    // Expected values come from the original C (cocf_decode, cocf_load_blk, cocf_lanes, cocf_load_range, alp_offsets,
    // alp_fin_blk, sort.c's keys_blk_alp) on random columns of every residual width, with sentinel patches; the stream is
    // made by the generator in /data/tmp/qrs/A5/gen.c. `QRS_A5_CASES` names a bigger one than the committed sample.
    #[test] fn differential() {
        let path = std::env::var("QRS_A5_CASES").unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/alp.bin").into());
        let raw = std::fs::read(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let mut c = Cur { w: raw.chunks_exact(8).map(|x| u64::from_ne_bytes(x.try_into().unwrap())).collect(), at: 0 };
        let (mut cols, mut checks) = (0u64, 0u64);
        loop {
            match c.u() {
                0 => break,
                1 => {
                    let (n, f32) = (c.u() as usize, c.u() != 0);
                    let ((mut m, ml), (mut a, al), (mut p, pl)) = (c.blob(), c.blob(), c.blob());
                    let (m, a, p) = (&bytes_mut(&mut m)[..ml], &bytes_mut(&mut a)[..al], &bytes_mut(&mut p)[..pl]);
                    let mut f = Cocf::meta_view(m, a, n).expect("meta_view");
                    assert_eq!(f.f32, f32);
                    f.c.pack = p;
                    let esz = if f32 { 4 } else { 8 };
                    let mut out = vec![0xabababababababab_u64; n + 8];
                    f.decode(0, f.c.meta.nblk, &mut bytes_mut(&mut out)[..n * esz]);
                    assert_eq!(fnv(&bytes_mut(&mut out)[..n * esz]), c.u(), "decode n {n}");
                    for b in 0..f.c.meta.nblk {
                        let full = (n - b * BLK).min(BLK);
                        for _ in 0..3 {
                            let (mut buf, mut lb) = ([0xabababababababab_u64; BLK], [0xcdcdcdcdcdcdcdcd_u64; BLK]);
                            let nb = c.u() as usize;
                            f.load_blk(b, nb, bytes_mut(&mut buf));
                            assert_eq!(fnv_w(&buf), c.u(), "load_blk b {b} nb {nb} n {n}");
                            let (lw, lh) = (c.u() as u8, c.u());
                            let (lp, w, w0) = f.lanes(b, nb, bytes_mut(&mut lb));
                            assert_eq!((w, w0), (lw, f.c.meta.width[b]), "lanes b {b}");
                            assert_eq!(fnv(&lp[..(nb * w as usize).div_ceil(8)]), lh, "lanes b {b} nb {nb}");
                            let (i0, i1) = (c.u() as usize, c.u() as usize);
                            buf = [0xabababababababab; BLK];
                            let (lp, w, _) = f.lanes(b, i1, bytes_mut(&mut lb));
                            f.load_range(b, lp, w, i0, i1, bytes_mut(&mut buf));
                            assert_eq!(fnv_w(&buf), c.u(), "load_range b {b} {i0}..{i1} n {n}");
                            checks += 3;
                        }
                        let mut k = [0u64; BLK];
                        crate::kwin::keys_blk_alp(&f, b, &mut k[..full]);
                        assert_eq!(fnv_w(&k[..full]), c.u(), "keys_blk_alp b {b} n {n}");
                        checks += 1;
                    }
                    cols += 1; checks += 1;
                }
                2 => {
                    let nblk = c.u() as usize;
                    let mut o: Vec<u32> = (0..=nblk).map(|i| if i == 0 { 0xdeadbeef } else { c.u() as u32 }).collect();
                    assert_eq!((alp_offsets(&mut o, nblk) as u64, fnv(&o.iter().flat_map(|x| x.to_ne_bytes()).collect::<Vec<u8>>())),
                               (c.u(), c.u()), "alp_offsets nblk {nblk}");
                    checks += 1;
                }
                _ => {
                    let (nb, be) = (c.u() as usize, c.u());
                    let (mut d, mut ee) = (vec![0i64; nb], vec![0i8; nb]);
                    for i in 0..nb { d[i] = c.u() as i64; ee[i] = c.u() as i64 as i8 }
                    let (ne, exp, dh) = (c.u(), c.u(), c.u());
                    let (cb, cm, cw) = (c.u() as i64, c.u() as i64, c.u());
                    let (mut base, mut maxv, mut width, mut bsum, mut nexc, mut e) = (0i64, 0i64, 0u8, 0i64, 0u32, 0i8);
                    let (lb, over) = (core::sync::atomic::AtomicUsize::new(0), core::sync::atomic::AtomicI32::new(0));
                    let mut m = EncMeta { b: 0, base: &mut base, maxv: &mut maxv, width: &mut width, bsum: &mut bsum, frm: None,
                                          nexc: &mut nexc, exp: Some(&mut e), below: 0, lb: &lb, over: &over };
                    assert_eq!((alp_fin_blk(&mut m, be as i32, &mut d, &ee, nb) as u64, fnv_w(&d.iter().map(|&x| x as u64).collect::<Vec<_>>())),
                               (ne, dh), "alp_fin_blk nb {nb}");
                    assert_eq!((e as i64 as u64, base, maxv, width as u64), (exp, cb, cm, cw), "alp_fin_blk meta nb {nb}");
                    checks += 2;
                }
            }
        }
        eprintln!("alp differential: {cols} columns, {checks} checks");
        assert!(cols > 0);
    }

    // The encoder's per-block steps against the original C (coc.h at ec273cf: dat, dexp, dat_blk, alp_exc_at,
    // alp_meta_blk, alp_meta_exp, alp_pack_blk) on blocks of decimals at every exponent, random bits, sentinels, -0.0,
    // subnormals and values near 2^49 / 2^53, from /data/tmp/qrs/A9/gen.c. `QRS_A9_CASES` names a bigger stream.
    // `encode_meta_blk` and `pack_block` are A7's: base, maxv, width and the pack hash are read past here.
    fn check_blk<F: Flt>(c: &mut Cur, x: &[F]) -> u64 {
        let nb = x.len();
        let mut n = 0;
        for e in 0..=18 {
            let (mut d, mut ok) = (vec![0i64; nb], vec![0u8; nb]);
            dat_blk(x, e, &mut d, &mut ok);
            let full: Vec<i64> = d.clone();
            for i in 0..nb { if ok[i] == 0 { d[i] = 0 } }
            let (oks, ds): (Vec<u8>, Vec<i64>) = x.iter().map(|&v| dat(v, e).map_or((0, 0), |r| (1, r))).unzip();
            let h = |v: &[i64]| fnv(&v.iter().flat_map(|x| x.to_ne_bytes()).collect::<Vec<u8>>());
            assert_eq!((fnv(&ok), h(&d), fnv(&oks), h(&ds), h(&full)), (c.u(), c.u(), c.u(), c.u(), c.u()), "dat e {e} nb {nb}");
            n += 1;
        }
        let dx: Vec<u8> = x.iter().flat_map(|&v| dexp(v).to_ne_bytes()).collect();
        assert_eq!(fnv(&dx), c.u(), "dexp nb {nb}");
        for be in [0, 1, 2, 5, 10, 18] { for lim in [1, 3, 1 << 30] { assert_eq!(alp_exc_at(x, be, lim) as u64, c.u(), "alp_exc_at be {be} lim {lim}"); n += 1 } }
        let ee_nexc = |ee: &mut [i8], be: i32| { let mut d = vec![0i64; nb]; recheck(x, nb, be, ee, &mut d); exc_as_base(&mut d, ee, nb) as u64 };
        let mut ee = vec![0i8; nb];
        let be = alp_exps(x, nb, &mut ee);
        assert_eq!((ee_nexc(&mut ee, be), be as u64), (c.u(), c.u()), "alp_meta_blk nb {nb}");
        let base = c.u() as i64;
        c.u(); c.u(); // maxv, width: A7
        let (mut d, mut pos, mut raw) = (vec![0i64; nb], vec![0u16; nb], vec![x[0]; nb]);
        holes(x, be, base, &mut d, &mut pos, &mut raw);
        let ne = x.iter().filter(|&&v| dat(v, be).is_none()).count();
        let rb: Vec<u8> = raw[..ne].iter().flat_map(|v| v.bits().to_ne_bytes()[..size_of::<F>()].to_vec()).collect();
        assert_eq!((fnv(&pos.iter().take(ne).flat_map(|v| v.to_ne_bytes()).collect::<Vec<u8>>()), fnv(&rb)), (c.u(), c.u()), "holes nb {nb}");
        c.u(); // the pack hash: A7
        for be in [0, 1, 2, 5, 10, 18] {
            let mut ee = vec![0i8; nb];
            exp_marks(x, nb, &mut ee);
            assert_eq!(ee_nexc(&mut ee, be), c.u(), "alp_meta_exp be {be} nb {nb}");
            c.u(); c.u(); // base, width: A7
        }
        n + 8
    }
    // the vector path's `nearest` is the scalar `cvt_nearest`, ties to even, on the edges and a sweep of the range
    #[test] fn nearest_is_cvtsd2si() {
        for s in [0.0, -0.0, 0.5, -0.5, 1.5, 2.5, -2.5, 0.4999999, 4503599627370495.5, 4503599627370496.0, 9007199254740991.0,
                  -9007199254740991.0, 1e15 + 0.5] { assert_eq!(nearest(s), crate::simd::cvt_nearest(s), "{s}") }
        let mut x = 0x9e3779b97f4a7c15u64;
        for _ in 0..200000 {
            x ^= x << 13; x ^= x >> 7; x ^= x << 17;
            let s = f64::from_bits(x) % P53;
            if s.is_finite() { assert_eq!(nearest(s), crate::simd::cvt_nearest(s), "{s}") }
        }
    }
    #[test] fn differential_enc() {
        let path = std::env::var("QRS_A9_CASES").unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/alp_enc.bin").into());
        let raw = std::fs::read(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let mut c = Cur { w: raw.chunks_exact(8).map(|x| u64::from_ne_bytes(x.try_into().unwrap())).collect(), at: 0 };
        let (mut blocks, mut checks) = (0u64, 0u64);
        while c.u() != 0 {
            let (f32, nb) = (c.u() != 0, c.u() as usize);
            let bits: Vec<u64> = (0..nb).map(|_| c.u()).collect();
            checks += if f32 { check_blk(&mut c, &bits.iter().map(|&b| f32::from_bits(b as u32)).collect::<Vec<_>>()) }
                      else { check_blk(&mut c, &bits.iter().map(|&b| f64::from_bits(b)).collect::<Vec<_>>()) };
            blocks += 1;
        }
        eprintln!("alp encode differential: {blocks} blocks, {checks} checks");
        assert!(blocks > 0);
    }
}
