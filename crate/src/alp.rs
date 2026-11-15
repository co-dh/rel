#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), coc.h: the ALP (decimal float) column. `Cocf` is the read view of coc.h:1443 `cocf` (A5: view,
//! block loads, decode, the finishing step); the encoder's per-block steps are A9.
use crate::coc::{Coc, Meta};
use crate::layout::{Tail, exc_layout};
use crate::pod;
use crate::enc::{EncMeta, EncPack};
use crate::pod::Pod;

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

// ---- A9: coc.h:2567-2800, the ALP encoder per block, one instance per `Flt` ----
/// coc.h:2574 `dec_f64`: `d * 10^-e`.
pub fn dec(d: i64, e: i32) -> f64 { unimplemented!("A9: dec_f64") }
/// coc.h:2579 `dat_f32`/`dat_f64`: `x` as a decimal at exponent `e`, or `None` when it does not round-trip.
pub fn dat<F: Flt>(x: F, e: i32) -> Option<i64> { unimplemented!("A9: dat") }
/// coc.h:2597 `dexp_f32`/`dexp_f64`: the smallest exponent at which `x` round-trips.
pub fn dexp<F: Flt>(x: F) -> i32 { unimplemented!("A9: dexp") }
/// coc.h:2624 `alp_meta_blk`: block metadata (exponent into `m.exp`); answers the patch count.
pub fn alp_meta_blk<F: Flt>(m: &mut EncMeta, x: &[F], nb: usize) -> u32 { unimplemented!("A9: alp_meta_blk") }
/// coc.h:2692 `dat_blk`: `dat` over a block, `ok[i]` = round-trips.
pub fn dat_blk<F: Flt>(x: &[F], e: i32, d: &mut [i64], ok: &mut [u8]) { unimplemented!("A9: dat_blk") }
/// coc.h:2703 `alp_meta_at`: the metadata at the given block exponent `be`; per-element exponents into `ee`.
pub fn alp_meta_at<F: Flt>(m: &mut EncMeta, x: &[F], nb: usize, be: i32, ee: &mut [i8]) -> u32 {
    unimplemented!("A9: alp_meta_at")
}
/// coc.h:2714 `alp_exc_at`: the patch count at `be`, stopping past `lim`.
pub fn alp_exc_at<F: Flt>(x: &[F], be: i32, lim: u32) -> u32 { unimplemented!("A9: alp_exc_at") }
/// coc.h:2722 `alp_meta_exp`: `alp_meta_at` without the per-element exponents.
pub fn alp_meta_exp<F: Flt>(m: &mut EncMeta, x: &[F], nb: usize, be: i32) -> u32 { unimplemented!("A9: alp_meta_exp") }
/// coc.h:2745 `alp_patch_blk`: block `b` of `o` with the `ix.len()` writes `ix`/`v` applied, as decimals `d`
/// and exponents `ee`; false = a written value has no decimal at the block's exponent.
pub fn alp_patch_blk<F: Flt>(o: &Cocf, b: usize, nb: usize, ix: &[u64], v: &[F], d: &mut [i64], ee: &mut [i8]) -> bool {
    unimplemented!("A9: alp_patch_blk")
}
/// coc.h:2766 `alp_patch_pack`: the pack step for a block `alp_patch_blk` rewrote.
pub fn alp_patch_pack<F: Flt>(p: &mut EncPack, o: &Cocf, ix: &[u64], v: &[F], d: &mut [i64], ee: &[i8], raw: &mut [F]) {
    unimplemented!("A9: alp_patch_pack")
}
/// coc.h:2785 `alp_pack_blk`: residuals and float patches of one block at exponent `be`.
pub fn alp_pack_blk<F: Flt>(p: &mut EncPack, be: i32, x: &[F], raw: &mut [F]) { unimplemented!("A9: alp_pack_blk") }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BLK, pod::bytes_mut};

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
}
