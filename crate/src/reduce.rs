#![forbid(unsafe_code)]
//! Column (a), reduce.rs: whole-vector reductions of a byte payload (A12; the byte sum is `simd::u8_sum`) and the
//! segmented reductions and bit-row folds (A13).
use alloc::vec::Vec;
use alloc::vec;
use crate::c::{run_map, Runner};

// ---- A12: reduce.rs ----




// ---- A13: reduce.rs ----
/// reduce.rs `seg_at`: segment `k`'s start (`o` the `n` starts; `k == n` answers the end).
pub fn seg_at(o: &[i64], n: usize, k: usize) -> usize {
    let x = o[k];
    if x < 0 { 0 } else if x as u64 > n as u64 { n } else { x as usize }
}



/// reduce.rs `br_load`: 64 bits of the bit matrix `m` (`nb` bytes) from bit `bit`.
pub fn br_load(m: &[u8], bit: usize) -> u64 {
    let (b, s) = (bit >> 3, bit & 7);
    let mut x = [0u8; 8];
    let t = m.get(b..).unwrap_or(&[]);
    let t = &t[..t.len().min(8)];
    x[..t.len()].copy_from_slice(t);
    let lo = u64::from_le_bytes(x);
    if s == 0 { return lo }
    let hi = if b + 8 < m.len() { m[b + 8] as u64 } else { 0 };
    (lo >> s) | (hi << (64 - s))
}
/// reduce.rs `br_store`: the low `nbits` of `v` at bit `bit`.
pub fn br_store(o: &mut [u8], bit: usize, v: u64, nbits: u32) {
    let (b, s) = (bit >> 3, (bit & 7) as u32);
    let x = (v as u128) << s;
    for t in 0..(s + nbits).div_ceil(8) as usize { o[b + t] |= (x >> (8 * t)) as u8 }
}
/// The first `n` elements of the `u1` `foR` column `c` as one bitmap, LSB first, bit `i` bit 0 of element `i`: a block
/// is its width-1 residuals copied (complemented under an odd frame), a constant at width 0, bit 0 of each residual
/// read in place at any other width, then each patch's bit 0. No element is widened to a word (`kbitrows`).
pub fn col_bits(c: &crate::coc::Coc, n: usize) -> Vec<u8> {
    let (lg, blk) = (c.meta.lg, c.meta.blk());
    let mut out = vec![0u8; n.div_ceil(8)];
    for b in 0..n.div_ceil(blk) {
        let (lo, nb) = (b << lg, (n - (b << lg)).min(blk));
        let o = &mut out[lo / 8..(lo + nb).div_ceil(8)];
        let (w, f) = (c.meta.width[b] as usize, (c.frame(b) & 1) as u8);
        let at = c.meta.off[b] as usize;
        let p = &c.pack[at..at + blk * w / 8];
        match w {
            0 => o.fill(0u8.wrapping_sub(f)),
            1 => for (x, &y) in o.iter_mut().zip(p) { *x = y ^ 0u8.wrapping_sub(f) },
            _ => for k in 0..nb { o[k / 8] |= (((p[k * w / 8] >> (k * w % 8)) & 1) ^ f) << (k % 8) },
        }
        if let Some(e) = c.exc.filter(|e| !e.pos.is_empty()) {
            for j in e.off[b] as usize..e.off[b + 1] as usize {
                let k = e.pos[j] as usize;
                if k < nb { o[k / 8] = (o[k / 8] & !(1 << (k % 8))) | (((c.exc(j) & 1) as u8) << (k % 8)) }
            }
        }
    }
    out
}

/// `qlean_k_bitrows` past its checks: per row of `w` bits, the AND (`all`) or OR of the rows
/// `idx[offs[g] .. offs[g + 1]]` of `m`, into `out`; threaded (`bit_rows_pass`).
pub fn bit_rows(run: Runner, all: bool, w: usize, offs: &[i64], idx: &[i64], m: &[u8], out: &mut [u8]) {
    let ng = offs.len().saturating_sub(1);
    let bytes = (ng * w).div_ceil(8);
    if bytes == 0 { return }
    let (nw, rows, ni) = (w.div_ceil(64), m.len() * 8 / w, idx.len());
    // a block is 64 rows, so it starts on a byte and owns `8 * w` bytes; the last is padded, then cut to `bytes`
    let blocks = ng.div_ceil(64);
    let f = |lo: usize, hi: usize, o: &mut [u8]| {
        let mut acc = vec![0u64; nw];
        for g in lo * 64..(hi * 64).min(ng) {
            acc.fill(if all { !0 } else { 0 });
            for k in seg_at(offs, ni, g)..seg_at(offs, ni, g + 1) {
                let r = idx[k].max(0) as usize;
                // a row wholly past `m` reads zeros: nothing for `|`, everything cleared for `&`
                if r > rows { if all { acc.fill(0) } continue }
                for (t, a) in acc.iter_mut().enumerate() {
                    let v = br_load(m, r * w + 64 * t);
                    if all { *a &= v } else { *a |= v }
                }
            }
            for (t, &a) in acc.iter().enumerate() {
                let nbits = (w - 64 * t).min(64) as u32;
                let v = if nbits == 64 { a } else { a & ((1u64 << nbits) - 1) };
                if v != 0 { br_store(o, (g - lo * 64) * w + 64 * t, v, nbits) }
            }
        }
    };
    let mut buf = vec![0u8; blocks * 8 * w];
    run_map(run, &mut buf, blocks, 8 * w, crate::QLEAN_COST_MATH, 8 * nw * 64, &f);
    out[..bytes].copy_from_slice(&buf[..bytes]);
}

// ---- K1: reduce.rs, the grouped fold ----











// reduce.rs `GC_*`: the cell kinds of `groupCells`.
// kind 0 (wrap) is every kind the arms below do not name



// q reduces floats in lanes and the lane count shows up in the answer: eight double lanes and sixteen float lanes,
// the tail folded in AFTER the lanes, and no split below two full groups (`sum (1e16),(k#1f),-1e16` is the strict left
// fold's 0f through n = 15 and lane-split from n = 16). The lane count is part of the specification (`Coc.Over.lanes`,
// `overFold`). A NaN is q's null and contributes nothing. Every add is a plain `+`, no FMA, so the association order
// written here is the one that runs.







/// The float verb table of `qlean_over_groups_float` and `qlean_over_segments_float`: one left fold from 0, 1, `inf`,
/// `-inf` at accumulator type `A`, the element widened to `A` first (a `real` fold in `double` widens each element).
#[macro_export]
macro_rules! of_verbs {
    ($op:expr, $go:ident) => { match $op {
        1 => $go!(A::ONE, |a: A, v: A| a * v),
        2 => $go!(A::HI, |a: A, v: A| if v < a { v } else { a }),
        3 => $go!(A::LO, |a: A, v: A| if v > a { v } else { a }),
        _ => $go!(A::ZERO, |a: A, v: A| a + v),
    } };
}







