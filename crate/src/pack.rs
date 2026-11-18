#![forbid(unsafe_code)]
//! `Ext.Enc.packed` (Rel/Kernel/Value.lean): blocks of `2^lg` elements, block `b` a little-endian u64 base at
//! `bases[8b ..]`, a width `widths[b] <= 64`, and all `2^lg` of its residuals bit-packed LSB first from byte
//! `Σ_{c<b} 2^lg·w_c/8` of `payload`. `check` is `Enc.packedErr`, `decode` is `Enc.unpack` narrowed to a column's
//! type, `encode` is `Coc.packedOf`: per block the base is the minimum and the width the bits of maximum − minimum.
use alloc::{vec, vec::Vec};
use crate::bits::width_for;
use crate::c::{Runner, run_map, run_map2, run_map_at};
use crate::enc::Producer;
use crate::pod::{self, Elt, Scr};
use crate::{MAX_LG, QLEAN_COST_ARITH};

/// The least `lg`: from 3 up `2^lg·w/8` is a whole number of bytes at every width, so every block starts on a byte.
pub const PACK_MIN_LG: u8 = 3;

/// The parts of a `packed` column, as `Db.ownParts` writes them after `lg`.
#[derive(Clone, Copy)]
pub struct Packed<'a> { pub lg: u8, pub bases: &'a [u8], pub widths: &'a [u8], pub payload: &'a [u8] }
/// What `encode` answers: the parts, owned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pack { pub lg: u8, pub bases: Vec<u8>, pub widths: Vec<u8>, pub payload: Vec<u8> }
impl Pack {
    pub fn view(&self) -> Packed<'_> { Packed { lg: self.lg, bases: &self.bases, widths: &self.widths, payload: &self.payload } }
}

/// Why parts do not hold `n` elements: `Enc.packedErr`'s cases in its order, then an output of the wrong size.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Bad {
    Lg(u8),
    Widths { got: usize, nb: usize, lg: u8, n: usize },
    Bases { got: usize, need: usize, nb: usize },
    Width { block: usize, w: u8 },
    Payload { got: usize, need: usize },
    Out { got: usize, need: usize },
}
impl core::fmt::Display for Bad {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Bad::Lg(lg) => write!(f, "packed: lg {lg} outside {PACK_MIN_LG} .. {MAX_LG}"),
            Bad::Widths { got, nb, lg, n } => write!(f, "packed: {got} widths for {nb} blocks of 2^{lg} at n = {n}"),
            Bad::Bases { got, need, nb } => write!(f, "packed: {got} base bytes for {nb} blocks, need {need}"),
            Bad::Width { block, w } => write!(f, "packed: block {block} has width {w} > 64"),
            Bad::Payload { got, need } => write!(f, "packed: payload {got} bytes, widths need {need}"),
            Bad::Out { got, need } => write!(f, "packed: output {got} bytes, {need} elements' bytes needed"),
        }
    }
}

fn lg_ok(lg: u8) -> Result<usize, Bad> { if (PACK_MIN_LG as u32..=MAX_LG).contains(&(lg as u32)) { Ok(1 << lg) } else { Err(Bad::Lg(lg)) } }
/// `Enc.packedStarts`: each block's first payload byte, `widths.len() + 1` entries, the last the payload's size.
pub fn starts(blk: usize, widths: &[u8]) -> Vec<usize> {
    let mut s = Vec::with_capacity(widths.len() + 1);
    s.push(0);
    for &w in widths { s.push(s[s.len() - 1] + blk * w as usize / 8) }
    s
}
/// `Enc.packedErr`: the block starts when `p` holds `n` elements, else the first layout error.
pub fn check(p: &Packed, n: usize) -> Result<Vec<usize>, Bad> {
    let blk = lg_ok(p.lg)?;
    let nb = n.div_ceil(blk);
    if p.widths.len() != nb { return Err(Bad::Widths { got: p.widths.len(), nb, lg: p.lg, n }) }
    if p.bases.len() != 8 * nb { return Err(Bad::Bases { got: p.bases.len(), need: 8 * nb, nb }) }
    if let Some(block) = p.widths.iter().position(|&w| w > 64) { return Err(Bad::Width { block, w: p.widths[block] }) }
    let s = starts(blk, p.widths);
    if p.payload.len() != s[nb] { return Err(Bad::Payload { got: p.payload.len(), need: s[nb] }) }
    Ok(s)
}

fn mask(w: usize) -> u64 { if w == 64 { !0 } else { (1u64 << w) - 1 } }
/// `Column.resAt`: residual `j` of a block at `w` bits, bits `[j·w, j·w + w)` of `r` LSB first.
pub fn res_at(r: &[u8], w: u8, j: usize) -> u64 {
    let (bit, w) = (j * w as usize, w as usize);
    let (lo, sh, k) = (bit >> 3, bit & 7, ((bit & 7) + w).div_ceil(8));
    let mut t = [0u8; 16];
    t[..k].copy_from_slice(&r[lo..lo + k]);
    (u128::from_le_bytes(t) >> sh) as u64 & mask(w)
}
/// `res_at`'s inverse into a zeroed block: ORs `v`'s low `w` bits into bits `[j·w, j·w + w)` of `r` (`Coc.packRes`).
pub fn put_res(r: &mut [u8], w: u8, j: usize, v: u64) {
    let (bit, w) = (j * w as usize, w as usize);
    let (lo, sh, k) = (bit >> 3, bit & 7, ((bit & 7) + w).div_ceil(8));
    let x = ((v & mask(w)) as u128) << sh;
    for (i, b) in r[lo..lo + k].iter_mut().enumerate() { *b |= (x >> (8 * i)) as u8 }
}
fn base(p: &Packed, b: usize) -> u64 { u64::from_le_bytes(p.bases[8 * b..8 * b + 8].try_into().expect("pack: check made 8 base bytes a block")) }

/// `Enc.unpack` narrowed to `T`: element `i` is `T::wrap(base + residual)`, the low `8·T::W` bits, into `out`
/// (`n·T::W` bytes, native order), on the pool a block at a time. The layout error when `check` refuses `p`.
pub fn decode<T: Elt>(run: Runner, p: &Packed, n: usize, out: &mut [u8]) -> Result<(), Bad> {
    let s = check(p, n)?;
    if out.len() != n * T::W { return Err(Bad::Out { got: out.len(), need: n * T::W }) }
    let blk = 1usize << p.lg;
    run_map(run, out, s.len() - 1, blk * T::W, QLEAN_COST_ARITH, blk * T::W, &|lo, hi, o: &mut [u8]| {
        for b in lo..hi {
            let (bs, w, r) = (base(p, b), p.widths[b], &p.payload[s[b]..s[b + 1]]);
            let o = &mut o[(b - lo) * blk * T::W..];
            for j in 0..blk.min(n - b * blk) {
                o[j * T::W..(j + 1) * T::W].copy_from_slice(pod::bytes(&[T::wrap(bs.wrapping_add(res_at(r, w, j)))]));
            }
        }
    });
    Ok(())
}
/// `decode` at a column of `w`-byte elements.
pub fn decode_w(run: Runner, p: &Packed, n: usize, w: usize, out: &mut [u8]) -> Result<(), Bad> {
    crate::by_width!(uint w, decode(run, p, n, out))
}

/// Block `b`'s `m` elements of `src` at `T::W` bytes into `e`; `buf` is the producer's scratch.
fn read<T: Elt>(src: &(impl Producer + ?Sized), b: usize, blk: usize, m: usize, buf: &mut [u64], e: &mut [u8]) {
    src.block_into(b, b * blk, m, T::W, pod::bytes_mut(buf), &mut e[..m * T::W])
}
/// `Coc.packedOf`: the `n` elements of `src` in blocks of `2^lg`, each block's base its minimum and its width
/// `width_for(max − min)`. `T` is the storage class (`by_width!(int ..)`), whose order the minimum is taken in: unsigned
/// at one byte, signed above (`Coc.bias`), so a base is the minimum sign-extended (`Coc.unbias`).
pub fn encode<T: Elt>(run: Runner, lg: u8, src: &(impl Producer + ?Sized), n: usize) -> Result<Pack, Bad> {
    let blk = lg_ok(lg)?;
    let nb = n.div_ceil(blk);
    let (mut bases, mut widths) = (vec![0u8; 8 * nb], vec![0u8; nb]);
    run_map2(run, &mut bases, &|k| 8 * k, &mut widths, 1, nb, QLEAN_COST_ARITH, blk * T::W, &|lo, hi, bo: &mut [u8], wo: &mut [u8]| {
        let (mut buf, mut e) = (Scr::<u64>::new(2 * blk), Scr::<u8>::new(blk * T::W));
        for b in lo..hi {
            let m = blk.min(n - b * blk);
            read::<T>(src, b, blk, m, &mut buf, &mut e);
            let (mut mn, mut mx) = (T::rd(&e), T::rd(&e));
            for j in 1..m { let x = T::rd(&e[j * T::W..]); if x < mn { mn = x } if x > mx { mx = x } }
            bo[8 * (b - lo)..8 * (b - lo) + 8].copy_from_slice(&(mn.i() as u64).to_le_bytes());
            wo[b - lo] = width_for(mx.i().wrapping_sub(mn.i()) as u64);
        }
    });
    let s = starts(blk, &widths);
    let mut payload = vec![0u8; s[nb]];
    // the elements are read again rather than kept from the first pass, which would hold a copy of the whole column
    run_map_at(run, &mut payload, nb, &|k| s[k], QLEAN_COST_ARITH, blk * T::W, &|lo, hi, o: &mut [u8]| {
        let (mut buf, mut e) = (Scr::<u64>::new(2 * blk), Scr::<u8>::new(blk * T::W));
        for b in lo..hi {
            let (m, w) = (blk.min(n - b * blk), widths[b]);
            if w == 0 { continue }
            let mn = i64::from_le_bytes(bases[8 * b..8 * b + 8].try_into().expect("pack: 8 base bytes a block"));
            read::<T>(src, b, blk, m, &mut buf, &mut e);
            let r = &mut o[s[b] - s[lo]..s[b + 1] - s[lo]];
            for j in 0..m { put_res(r, w, j, T::rd(&e[j * T::W..]).i().wrapping_sub(mn) as u64) }
        }
    });
    Ok(Pack { lg, bases, widths, payload })
}
/// `encode` at a column of `w`-byte elements.
pub fn encode_w(run: Runner, lg: u8, src: &(impl Producer + ?Sized), n: usize, w: usize) -> Result<Pack, Bad> {
    crate::by_width!(int w, encode(run, lg, src, n))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c::qlean_run_c as run;
    use alloc::string::ToString;

    /// `xs` narrowed to `w` bytes a element, as a dense column holds them.
    fn dense(xs: &[i64], w: usize) -> Vec<u8> { xs.iter().flat_map(|x| x.to_le_bytes()[..w].to_vec()).collect() }
    fn enc(xs: &[i64], lg: u8, w: usize) -> Pack {
        encode_w(run, lg, &|v: &mut [i64], lo: usize| v.iter_mut().enumerate().for_each(|(k, x)| *x = xs[lo + k]), xs.len(), w).unwrap()
    }
    fn dec(p: &Pack, n: usize, w: usize) -> Result<Vec<u8>, Bad> { let mut o = vec![0u8; n * w]; decode_w(run, &p.view(), n, w, &mut o).map(|()| o) }

    #[test] fn round_trip() {
        let mut st = 0x9e3779b97f4a7c15u64;
        let mut rnd = || { st ^= st << 13; st ^= st >> 7; st ^= st << 17; st };
        let (mut saw0, mut saw64) = (false, false);
        for w in [1, 2, 4, 8] { for lg in [3u8, 4, 6, 10, 16] { for n in [0, 1, 7, 8, 9, 100, (1 << lg) * 3 + 5] { for bits in [0u32, 1, 5, 13, 31, 64] {
            let off = rnd() as i64;
            let xs: Vec<i64> = (0..n).map(|_| off.wrapping_add((if bits == 64 { rnd() } else { rnd() & ((1u64 << bits) - 1) }) as i64)).collect();
            let p = enc(&xs, lg, w);
            assert_eq!(dec(&p, n, w).unwrap(), dense(&xs, w), "w {w} lg {lg} n {n} bits {bits}");
            assert!(p.widths.iter().all(|&b| b as usize <= 8 * w));
            saw0 |= n > 0 && p.widths.contains(&0);
            saw64 |= p.widths.contains(&64);
        } } } }
        assert!(saw0 && saw64, "a width-0 block and a width-64 block were exercised");
    }

    /// `(w, lg, elements, bases, widths, payload, from packedOf)`: the `#guard` inputs of Rel/Kernel/Coc.lean and the parts
    /// `#eval` printed for them. A case `packedOf` made is also what `encode` answers; `packedAt`'s bases are 0, which
    /// is not the minimum `encode` takes, so those are decoded only.
    type Case = (usize, u8, &'static [i64], &'static [u8], &'static [u8], &'static [u8], bool);
    const LEAN: [Case; 7] = [
        // `packedOf 3 8` of the long column
        (8, 3, &[5, -3, 1000, 7, -70000, 0, 2, 2, 9, 11, -1], &[144, 238, 254, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255],
         &[17, 4], &[117, 17, 219, 34, 98, 85, 188, 139, 8, 0, 0, 46, 162, 92, 68, 185, 136, 202, 0, 0, 0], true),
        // `packedAt lg 1 13` of the bitmap `0b10110101, 0b00010110`, at lg 3 and 6
        (1, 3, &[1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1], &[0; 16], &[1, 1], &[181, 22], true),
        (1, 6, &[1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1], &[0; 8], &[1], &[181, 22, 0, 0, 0, 0, 0, 0], true),
        // `packedAt 3 3 10` of the enumeration's ids
        (8, 3, &[4, 0, 3, 1, 1, 2, 4, 4, 0, 3], &[0; 16], &[3, 3], &[196, 18, 145, 24, 0, 0], false),
        // the constant: `-7` sign-extended in both bases, width 0, read as a 4-byte `int`
        (4, 3, &[-7; 9], &[249, 255, 255, 255, 255, 255, 255, 255, 249, 255, 255, 255, 255, 255, 255, 255], &[0, 0], &[], true),
        // `packedOf 3 2` and `packedOf 3 1`: the signed order at 2 bytes, the unsigned at 1
        (2, 3, &[-300, 5, 7, -1, 0, 32767, -32768, 3, 1], &[0, 128, 255, 255, 255, 255, 255, 255, 1, 0, 0, 0, 0, 0, 0, 0],
         &[16, 0], &[212, 126, 5, 128, 7, 128, 255, 127, 0, 128, 255, 255, 0, 0, 3, 128], true),
        (1, 3, &[200, 3, 255, 0, 17, 17, 17, 17, 17], &[0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0], &[8, 0], &[200, 3, 255, 0, 17, 17, 17, 17], true),
    ];
    #[test] fn lean_parts() {
        for (k, &(w, lg, xs, bases, widths, payload, made)) in LEAN.iter().enumerate() {
            let p = Pack { lg, bases: bases.to_vec(), widths: widths.to_vec(), payload: payload.to_vec() };
            assert_eq!(dec(&p, xs.len(), w).unwrap(), dense(xs, w), "case {k}: decode");
            if made { assert_eq!(enc(xs, lg, w), p, "case {k}: encode") }
        }
    }

    #[test] fn lean_refusals() {
        let p = Pack { lg: 3, bases: vec![0; 16], widths: vec![1, 1], payload: vec![0; 3] };
        assert_eq!(dec(&p, 13, 8), Err(Bad::Payload { got: 3, need: 2 }));
        assert_eq!(Bad::Payload { got: 3, need: 2 }.to_string(), "packed: payload 3 bytes, widths need 2");
        assert_eq!(dec(&Pack { lg: 2, ..p.clone() }, 13, 8), Err(Bad::Lg(2)));
        assert_eq!(dec(&Pack { lg: 17, ..p.clone() }, 13, 8), Err(Bad::Lg(17)));
        assert_eq!(dec(&p, 17, 8), Err(Bad::Widths { got: 2, nb: 3, lg: 3, n: 17 }));
        assert_eq!(dec(&Pack { bases: vec![0; 15], ..p.clone() }, 13, 8), Err(Bad::Bases { got: 15, need: 16, nb: 2 }));
        assert_eq!(dec(&Pack { widths: vec![1, 65], ..p.clone() }, 13, 8), Err(Bad::Width { block: 1, w: 65 }));
        let ok = Pack { payload: vec![0; 2], ..p };
        let mut o = vec![0u8; 13 * 8 - 1];
        assert_eq!(decode_w(run, &ok.view(), 13, 8, &mut o), Err(Bad::Out { got: 103, need: 104 }));
        assert!(encode_w(run, 2, &|_: &mut [i64], _: usize| (), 0, 8).is_err());
    }
}
