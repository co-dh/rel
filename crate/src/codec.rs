#![forbid(unsafe_code)]
//! Column (a), coc.rs: the threaded passes behind the `qlean_coc_*` entries (A15) and the `qlean_alp_*` ones (A18).
//! The entries themselves unbox and allocate, and stay C (§1); each calls the pass here through its `qrs_*` shim.
use crate::c::{run_map, Runner};
use crate::coc::{lanes, Coc};
use crate::cocops::{EQ, GE, GT, LE, LT, NE};
use crate::enc;
use crate::simd::res_vcmp;
use crate::pod::{self, Elt};
use crate::QLEAN_COST_ARITH;

// ---- A15: coc.rs ----
/// coc.rs `qlean_coc_decode_{i16,i32,i64}` past the unboxing: the whole column into `out`, by blocks.
pub fn decode<T: Elt + Send>(run: Runner, c: &Coc, out: &mut [T]) {
    let unit = c.meta.blk() * size_of::<T>();
    run_map(run, pod::bytes_mut(out), c.meta.nblk, unit, QLEAN_COST_ARITH, unit, &|lo, hi, o: &mut [u8]| {
        let o = pod::cast_mut::<T>(o).expect("qlean_coc_decode: output misaligned for its element");
        enc::decode(&c.blocks(lo, hi), o)
    });
}

/// coc.rs `coc_cmp1`: one element of `x op v`, the exceptions a mask pass corrects.
pub fn cmp1(op: i32, x: i64, v: i64) -> bool {
    match op { EQ => x == v, NE => x != v, LT => x < v, LE => x <= v, GT => x > v, _ => x >= v }
}
/// coc.rs `coc_blk_cmp`: 1 when every pair passes `x op y` for x anywhere in [ba, ma] and y anywhere in [bb, mb], 0 when
/// none does, -1 when the residuals decide. An atom on the right is `bb = mb = v`, so one rule serves it and `x op y`.
pub fn blk_cmp(op: i32, ba: i64, ma: i64, bb: i64, mb: i64) -> i32 {
    match op {
        LT => if ma < bb { 1 } else if mb <= ba { 0 } else { -1 },
        LE => if ma <= bb { 1 } else if mb < ba { 0 } else { -1 },
        GT => if mb < ba { 1 } else if ma <= bb { 0 } else { -1 },
        GE => if mb <= ba { 1 } else if ma < bb { 0 } else { -1 },
        EQ => if ma < bb || mb < ba { 0 } else if ba == ma && bb == mb { 1 } else { -1 },
        _ => if ma < bb || mb < ba { 1 } else if ba == ma && bb == mb { 0 } else { -1 },
    }
}
/// coc.rs:~885 `coc_mask_fill`: the first `nb` bits of `w` set. Only the last block can be partial, and its last word is
/// written masked so no bit past the column is set.
pub fn mask_fill(w: &mut [u64], nb: usize) {
    let full = nb >> 6;
    w[..full].fill(!0);
    if nb & 63 != 0 { w[full] = !0 >> (64 - (nb & 63)) }
}

/// coc.rs `res_expand`: the residuals of width `W` < 8, `8 / W` to a byte, one to a byte of `out`.
pub fn expand<const W: u32>(p: &[u8], nb: usize, out: &mut [u8]) {
    let w = W as usize;
    for (o, &b) in out.chunks_mut(8 / w).zip(&p[..(nb * w).div_ceil(8)]) {
        for (t, x) in o.iter_mut().enumerate() { *x = (b >> (t * w)) & ((1u16 << W) - 1) as u8 }
    }
}
/// coc.rs `COC_MASK_WORD`: `r - lo <= span` (unsigned, flipped when `inv`) for `nb` `E`-byte residuals, a 64-bit word
/// built in a register and stored once; the width is a constant so the loop vectorises.
pub fn words<const E: usize>(p: &[u8], nb: usize, lo: u64, span: u64, inv: bool, out: &mut [u64]) {
    for (o, ch) in out.iter_mut().zip(p[..nb * E].chunks(64 * E)) {
        let mut word = 0u64;
        for (j, r) in ch.chunks_exact(E).enumerate() {
            let mut a = [0u8; 8];
            a[..E].copy_from_slice(r);
            word |= (((u64::from_le_bytes(a).wrapping_sub(lo) <= span) ^ inv) as u64) << j;
        }
        *o |= word;
    }
}
/// `res_mask_cmp` at the lane width `W`: a sub-byte lane spread a byte to a residual first (`scratch`), a whole one
/// tested where it lies.
#[inline(always)]
fn mask_at<const W: u32>(p: &[u8], nb: usize, lo: u64, span: u64, inv: bool, out: &mut [u64], scratch: &mut [u8]) {
    match W {
        // every residual is 0, so every bit is the same
        0 => if (0u64.wrapping_sub(lo) <= span) ^ inv { mask_fill(out, nb) },
        1 | 2 | 4 => { expand::<W>(p, nb, scratch); words::<1>(scratch, nb, lo, span, inv, out) }
        8 => words::<1>(p, nb, lo, span, inv, out),
        16 => words::<2>(p, nb, lo, span, inv, out),
        32 => words::<4>(p, nb, lo, span, inv, out),
        _ => words::<8>(p, nb, lo, span, inv, out),
    }
}
/// coc.rs `res_mask_cmp`: block residuals `p` at width `w` tested `r - lo <= span`, into the zeroed `out`. `scratch` is
/// `blk * 8` bytes the caller owns, so a kilobyte is not declared inside the loop over blocks.
pub fn res_mask_cmp(p: &[u8], nb: usize, w: u8, lo: u64, span: u64, inv: bool, out: &mut [u64], scratch: &mut [u8]) {
    if res_vcmp(p, w, nb, lo, span, inv, out) { return }
    if w & w.wrapping_sub(1) == 0 { return crate::by_width!(w, mask_at(p, nb, lo, span, inv, out, scratch)) }
    // an odd width unpacked to its lane (8 bits or more) in `scratch`
    let mut w = w;
    let p = lanes(p, &mut w, nb, scratch);
    crate::by_width!(w, mask_at(p, nb, lo, span, inv, out, &mut []))
}
/// coc.rs `coc_mask_cmp_blk`: block `b`'s first `nb` elements of `x op v` into its zeroed words `w64`, the patches
/// applied. A block whose range the threshold `v` leaves is a window on the residuals: `r - lo <= hi - lo`, inverted for
/// `<>`, which is never empty there.
pub fn mask_blk(c: &Coc, b: usize, nb: usize, op: i32, v: i64, w64: &mut [u64], scratch: &mut [u8]) {
    let m = &c.meta;
    match blk_cmp(op, m.base[b], m.maxv[b], v, v) {
        1 => mask_fill(w64, nb),
        0 => {}
        _ if c.bit_blk(b).is_some_and(|p| { crate::bitblk::mask_cmp(p, nb, op, v, w64); true }) => {}
        _ => {
            let f = c.frame(b) as i64;
            // a frame above v is the one case the window cannot say: every residual is then above it
            if f > v { if matches!(op, GT | GE | NE) { mask_fill(w64, nb) } } else {
                let t = (v as u64).wrapping_sub(f as u64);
                // `None`: no residual is below 0 (`LT` at `v = f`) or above the largest word, so no row matches; a
                // wrapped bound there would match every row
                let r = match op { LT => t.checked_sub(1).map(|h| (0, h)), LE => Some((0, t)), GT => t.checked_add(1).map(|l| (l, u64::MAX)),
                                   GE => Some((t, u64::MAX)), _ => Some((t, t)) };
                if let Some((lo, hi)) = r {
                    let at = m.off[b] as usize;
                    res_mask_cmp(&c.pack[at..at + m.blk() * m.w(b) as usize / 8], nb, m.w(b), lo, hi.wrapping_sub(lo), op == NE,
                                 w64, scratch)
                }
            }
        }
    }
    if let Some(e) = c.exc.filter(|e| !e.pos.is_empty()) {
        for j in e.off[b] as usize..e.off[b + 1] as usize {
            let p = e.pos[j] as usize;
            if p < nb {
                let one = 1u64 << (p & 63);
                w64[p >> 6] = (w64[p >> 6] & !one) | if cmp1(op, c.exc(j), v) { one } else { 0 };
            }
        }
    }
}

// ---- A18: coc.rs ----



