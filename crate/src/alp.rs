#![forbid(unsafe_code)]
//! Column (a), coc.rs: the ALP (decimal float) column. `Cocf` is the read view of coc.rs `cocf` (A5: view,
//! block loads, decode, the finishing step); the encoder's per-block steps are A9.
use crate::coc::{Coc, Meta};
use crate::layout::{Tail, exc_layout};
use crate::pod;
use crate::enc::{EncMeta, EncPack};
use crate::pod::Elt;

/// coc.rs `cocf`: the integer column `c` (the FoR encoding of the decimals `d`) plus each block's exponent and
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


// ---- A5: coc.rs, 1689 ----
/// coc.rs `POW10`: `10^e`, exact as doubles up to 1e18.
pub const POW10: [f64; 19] = [1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11, 1e12, 1e13, 1e14, 1e15,
                              1e16, 1e17, 1e18];
/// coc.rs `alp_offsets`: per-block patch counts in `exc_off[1..=nblk]` into prefix sums; answers the total.
pub fn alp_offsets(exc_off: &mut [u32], nblk: usize) -> usize {
    exc_off[0] = 0;
    for b in 0..nblk { exc_off[b + 1] = exc_off[b + 1].wrapping_add(exc_off[b]) }
    exc_off[nblk] as usize
}
impl<'a> Cocf<'a> {
    /// coc.rs `cocf_meta_view`: metadata `m` and the ALP part `a` of an `n`-element column; `None` = misaligned
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
    /// coc.rs `cocf_load_range`: elements `i0 .. i1` of block `b` (residuals `p` at width `w`) into `out` as
    /// `f32`/`f64` bytes, at their own places (`out[i * esz]`).
    pub fn load_range(&self, b: usize, p: &[u8], w: u8, i0: usize, i1: usize, out: &mut [u8]) {
        let (base, p10, esz) = (self.c.meta.base[b] as u64, POW10[self.exp[b] as usize], if self.f32 { 4 } else { 8 });
        if self.f32 { restore::<f32>(base, p10, p, w, i0, i1, out) } else { restore::<f64>(base, p10, p, w, i0, i1, out) }
        for j in self.exc_off[b] as usize..self.exc_off[b + 1] as usize {
            let at = self.exc_pos[j] as usize;
            if (i0..i1).contains(&at) { out[at * esz..(at + 1) * esz].copy_from_slice(&self.exc_raw[j * esz..(j + 1) * esz]) }
        }
    }
    /// coc.rs `cocf_lanes`: block `b`'s residuals as whole lanes (`buf`, blk * 8, when they must be unpacked);
    /// answers them, the lane width and the residual width.
    pub fn lanes<'b>(&self, b: usize, nb: usize, buf: &'b mut [u8]) -> (&'b [u8], u8, u8) where 'a: 'b {
        let (w0, at) = (self.c.meta.width[b], self.c.meta.off[b] as usize);
        let mut w = w0;
        let p = crate::coc::lanes(&self.c.pack[at..at + self.c.meta.blk() * w0 as usize / 8], &mut w, nb, buf);
        (p, w, w0)
    }
    /// coc.rs `cocf_load_blk`: block `b`'s first `nb` elements into `out`, patches applied.
    pub fn load_blk(&self, b: usize, nb: usize, out: &mut [u8]) {
        let mut lb = pod::Scr::<u64>::new(self.c.meta.blk());
        let (p, w, _) = self.lanes(b, nb, pod::bytes_mut(&mut lb));
        self.load_range(b, p, w, 0, nb, out)
    }
}
impl Cocf<'_> {
}
/// `cocf_load_range`'s decimals: `base + residual` as an integer over `p10`, narrowed to `F`. `p` is read at `w` bits.
pub fn restore<F: Elt>(base: u64, p10: f64, p: &[u8], w: u8, i0: usize, i1: usize, out: &mut [u8]) {
    let o = &mut pod::cast_mut::<F>(&mut out[i0 * size_of::<F>()..i1 * size_of::<F>()])
        .expect("qlean: cocf output misaligned for its element")[..];
    fn put<F: Elt>(o: &mut [F], i0: usize, base: u64, p10: f64, get: impl Fn(usize) -> u64) {
        for (k, x) in o.iter_mut().enumerate() { *x = F::of_f(base.wrapping_add(get(i0 + k)) as i64 as f64 / p10) }
    }
    fn at<F: Elt, const W: u32>(o: &mut [F], i0: usize, base: u64, p10: f64, p: &[u8]) { put(o, i0, base, p10, |i| crate::ids::lane::<W>(p, i)) }
    // a lane width through `by_width!`; an odd width below a byte is read where it lies
    if w & w.wrapping_sub(1) == 0 { crate::by_width!(w, at::<F>(o, i0, base, p10, p)) } else {
        let m = (1u64 << w) - 1;
        put(o, i0, base, p10, |i| (p[(i * w as usize) >> 3] as u64 >> ((i * w as usize) & 7)) & m)
    }
}
/// coc.rs `alp_fin_blk`: block `b`'s decimals `d` (exponents `ee`, first `nb`) at the block exponent `be`
/// into the integer metadata; answers the patch count.
pub fn alp_fin_blk(m: &mut EncMeta, be: i32, d: &mut [i64], ee: &[i8], nb: usize) -> u32 {
    let nexc = exc_as_base(d, ee, nb);
    **m.exp.as_mut().expect("qlean: alp_fin_blk on metadata with no exponent slot") = be as i8;
    crate::enc::encode_meta_blk::<i64>(m, d, nb);
    nexc
}
/// `alp_fin_blk`'s first half: every exception's decimal becomes the block minimum (0 when all are), so it packs as
/// residual 0; answers the exception count.
pub fn exc_as_base(d: &mut [i64], ee: &[i8], nb: usize) -> u32 {
    let (d, ee) = (&mut d[..nb], &ee[..nb]);
    let nexc = ee.iter().filter(|&&e| e < 0).count();
    let mn = if nexc == nb { 0 } else { d.iter().zip(ee).filter(|&(_, &e)| e >= 0).map(|(&x, _)| x).min().unwrap() };
    for (x, &e) in d.iter_mut().zip(ee) { if e < 0 { *x = mn } }
    nexc as u32
}

// ---- A9: coc.rs, the ALP encoder per block, one instance per `Flt` ----
pub const MAXE: usize = crate::layout::ALP_MAXE as usize;
/// coc.rs `ALP_P53`: a product at or past 2^53 is not an exact integer.
pub const P53: f64 = 9007199254740992.0;
/// 2^49: `dexp`'s bound, under which three trials decide a double.
pub const P49: f64 = 562949953421312.0;
/// C's `nearbyint` (ties to even, the default mode) for |s| < 2^53, without libm: adding and removing 2^52 of the
/// sign of `s` rounds at the unit place; from 2^52 on every double is already an integer.
pub fn rint(s: f64) -> f64 { let c = 4503599627370496.0f64.copysign(s); if s.abs() < 4503599627370496.0 { (s + c) - c } else { s } }
/// `cvt_nearest` for a whole block, where the intrinsic would stop the loop vectorising: `rint`, then the integer
/// read off the bits (|s| < 2^53, so the shift is at most 52 and a value under 1 shifts out to 0).
pub fn nearest(s: f64) -> i64 {
    let b = rint(s).to_bits();
    let m = ((b & ((1 << 52) - 1)) | 1 << 52) >> 1075u64.wrapping_sub((b >> 52) & 0x7ff).min(63);
    if (b as i64) < 0 { -(m as i64) } else { m as i64 }
}
/// coc.rs `COC_SENT`: the exponent field all ones, tested on the raw bits (NaN and infinities).
pub fn sent<F: Elt>(x: F) -> bool { let (s, m) = if F::W == 4 { (23, 0xff) } else { (52, 0x7ff) }; x.bits() >> s & m == m }
/// coc.rs `dec_f64`: `d / 10^e`. It divides, as ALP written with a multiply by 10^-e is another operation.
pub fn dec(d: i64, e: i32) -> f64 { d as f64 / POW10[e as usize] }
/// coc.rs `dat_f32`/`dat_f64`: `x` as a decimal at exponent `e`, or `None` when it does not round-trip. The
/// comparison is on bits, so -0.0 (which decodes as +0.0) is refused.
pub fn dat<F: Elt>(x: F, e: i32) -> Option<i64> {
    let s = x.f() * POW10[e as usize];
    if !(s.abs() < P53) { return None }
    let r = crate::simd::cvt_nearest(s);
    (F::of_f(dec(r, e)).bits() == x.bits()).then_some(r)
}
/// coc.rs `dat_blk`: `dat` at one exponent over a block, branch-free so that it vectorises: `ok[i]`, and `d[i]`
/// where it is set. A sentinel is never ok, its product being NaN or infinite.
pub fn dat_blk<F: Elt>(x: &[F], e: i32, d: &mut [i64], ok: &mut [u8]) {
    let p = POW10[e as usize];
    for ((&x, d), ok) in x.iter().zip(d).zip(ok) {
        let s = x.f() * p;
        let inn = s.abs() < P53;
        let r = nearest(if inn { s } else { 0.0 });
        *d = r;
        *ok = (inn & (F::of_f(r as f64 / p).bits() == x.bits())) as u8;
    }
}
/// coc.rs `alp_meta_blk`'s search: each element's own exponent into `ee` (-1 = sentinel or not a decimal) and the
/// block exponent, their maximum. At `f64` `dexp`'s three-trial refusal runs over the whole block first, and only
/// what passes pays the exponent search; at `f32` the trials are `dat_blk` passes, until every element that can hit has.
pub fn alp_exps<F: Elt>(x: &[F], nb: usize, ee: &mut [i8]) -> i32 {
    let (x, ee) = (&x[..nb], &mut ee[..nb]);
    if F::W != 4 {
        let (mut ex, mut maybe) = (pod::Scr::<i64>::new(nb), pod::Scr::<i64>::new(nb));
        for (m, v) in maybe.iter_mut().zip(x) { *m = !(v.f().abs() < P49) as i64 }
        for e in 1..=MAXE { for (k, v) in ex.iter_mut().zip(x) { *k += (v.f().abs() * POW10[e] < P49) as i64 } }
        for k in 0..3 {
            for ((m, &e), v) in maybe.iter_mut().zip(&ex).zip(x) {
                let (v, p) = (v.f(), POW10[(e + k).min(MAXE as i64) as usize]);
                let s = v * p;
                let hit = (s.abs() < P53) & (rint(s) / p == v);
                *m = if *m != 0 { *m } else { hit as i64 * (k + 1) };
            }
        }
        // `maybe` is 1 + the first trial that hit: a hit at E means the smallest e may be anywhere up to E, so it is
        // searched; a first hit at E + 1 or E + 2 is the smallest, every e <= E failing with E.
        let (mut at, mut m) = (pod::Scr::<u16>::new(nb), 0);
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
    let (mut d, mut ok) = (pod::Scr::<i64>::new(nb), pod::Scr::<u8>::new(nb));
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
/// coc.rs `alp_meta_blk`: block metadata (exponent into `m.exp`); answers the patch count.
pub fn alp_meta_blk<F: Elt>(m: &mut EncMeta, x: &[F], nb: usize) -> u32 {
    let mut ee = pod::Scr::<i8>::new(nb);
    let be = alp_exps(x, nb, &mut ee);
    alp_meta_at(m, x, nb, be, &mut ee)
}
/// `alp_meta_at`'s re-check: `d` at the block exponent `be`, and an element that is not exact there becomes an exception.
pub fn recheck<F: Elt>(x: &[F], nb: usize, be: i32, ee: &mut [i8], d: &mut [i64]) {
    let mut ok = pod::Scr::<u8>::new(nb);
    dat_blk(&x[..nb], be, d, &mut ok);
    for (e, &k) in ee[..nb].iter_mut().zip(&ok) { if k == 0 { *e = -1 } }
}
/// coc.rs `alp_meta_at`: the metadata at the given block exponent `be`; per-element exponents into `ee`.
pub fn alp_meta_at<F: Elt>(m: &mut EncMeta, x: &[F], nb: usize, be: i32, ee: &mut [i8]) -> u32 {
    let mut d = pod::Scr::<i64>::new(nb);
    recheck(x, nb, be, ee, &mut d);
    alp_fin_blk(m, be, &mut d, ee, nb)
}
/// coc.rs `alp_exc_at`: the patch count at `be`, stopping past `lim`.
pub fn alp_exc_at<F: Elt>(x: &[F], be: i32, lim: u32) -> u32 {
    let mut n = 0;
    for &v in x { if n >= lim { break } n += (sent(v) || dat(v, be).is_none()) as u32 }
    n
}
/// coc.rs `alp_meta_exp`: `alp_meta_at` for elements not searched: only a sentinel is marked beforehand.
pub fn alp_meta_exp<F: Elt>(m: &mut EncMeta, x: &[F], nb: usize, be: i32) -> u32 {
    let mut ee = pod::Scr::<i8>::new(nb);
    exp_marks(x, nb, &mut ee);
    alp_meta_at(m, x, nb, be, &mut ee)
}
/// `alp_meta_exp`'s marks: only a sentinel is an exception beforehand.
pub fn exp_marks<F: Elt>(x: &[F], nb: usize, ee: &mut [i8]) { for (e, &v) in ee.iter_mut().zip(&x[..nb]) { *e = if sent(v) { -1 } else { 0 } } }
/// coc.rs `alp_pack_blk`: residuals and float patches of one block at exponent `be`. An exception is an element
/// `dat` refuses at `be`, which is pass 1's set: a sentinel fails `dat` on its magnitude, a non-decimal at every e.
pub fn alp_pack_blk<F: Elt>(p: &mut EncPack, be: i32, x: &[F], raw: &mut [F]) {
    let (nb, mut d) = (p.nb, pod::Scr::<i64>::new(p.nb));
    holes(&x[..nb], be, p.base, &mut d, p.pos, raw);
    crate::enc::pack_block(&mut *p.res, &d[..nb], nb, p.base, p.width)
}
/// `alp_pack_blk` before the pack: the decimals `d` with each exception's residual 0 (`d = base`), its position and bits.
pub fn holes<F: Elt>(x: &[F], be: i32, base: i64, d: &mut [i64], pos: &mut [u16], raw: &mut [F]) {
    let mut ok = pod::Scr::<u8>::new(x.len());
    dat_blk(x, be, d, &mut ok);
    for (j, i) in (0..x.len()).filter(|&i| ok[i] == 0).enumerate() { d[i] = base; pos[j] = i as u16; raw[j] = x[i] }
}


impl<'a> Cocf<'a> {
    /// coc.rs `cocf_view`: `meta_view` with the pack `pv` attached; `None` as `meta_view`'s.
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

    // Expected values from coc.rs's alp_thresh: the clamps outside 2^53 and the ceil at an exponent
    // Expected values come from the original C: `encode_f64` of [1.5, 2.25, NaN, 100.0] (exponent 2, base 150, width 14, one
    // patch) patched by [1 -> 1.25, 3 -> 0.1234567], /data/tmp/qrs/A17/one2.c; the random comparison is /data/tmp/qrs/A17/diff.c.


    // Expected values come from the original C (cocf_decode, cocf_load_blk, cocf_lanes, cocf_load_range, alp_offsets,
    // alp_fin_blk, sort.rs's keys_blk_alp) on random columns of every residual width, with sentinel patches; the stream is
    // made by the generator in /data/tmp/qrs/A5/gen.c. `QRS_A5_CASES` names a bigger one than the committed sample.

    // The encoder's per-block steps against the original C (coc.rs at ec273cf: dat, dexp, dat_blk, alp_exc_at,
    // alp_meta_blk, alp_meta_exp, alp_pack_blk) on blocks of decimals at every exponent, random bits, sentinels, -0.0,
    // subnormals and values near 2^49 / 2^53, from /data/tmp/qrs/A9/gen.c. `QRS_A9_CASES` names a bigger stream.
    // `encode_meta_blk` and `pack_block` are A7's: base, maxv, width and the pack hash are read past here.
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
}
