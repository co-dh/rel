#![forbid(unsafe_code)]
//! Column (a), coc.rs: the threaded passes behind the `qlean_coc_*` entries (A15) and the `qlean_alp_*` ones (A18).
//! The entries themselves unbox and allocate, and stay C (§1); each calls the pass here through its `qrs_*` shim.
use crate::alp::{dec, Cocf};
use crate::c::{run_map, run_map_at, Runner};
use crate::coc::{lanes, Coc, Meta};
use crate::cocops::{cmp2_res, EQ, GE, GT, LE, LT, NE};
use crate::enc;
use crate::simd::res_vcmp;
use alloc::vec;
use crate::pod::{self, Elt};
use crate::{QLEAN_COST_ARITH, QLEAN_COST_GATHER};

// ---- A15: coc.rs ----
/// coc.rs `qlean_coc_decode_{i16,i32,i64}` past the unboxing: the whole column into `out`, by blocks.
pub fn decode<T: Elt + Send>(run: Runner, c: &Coc, out: &mut [T]) {
    let unit = c.meta.blk() * size_of::<T>();
    run_map(run, pod::bytes_mut(out), c.meta.nblk, unit, QLEAN_COST_ARITH, unit, &|lo, hi, o: &mut [u8]| {
        let o = pod::cast_mut::<T>(o).expect("qlean_coc_decode: output misaligned for its element");
        enc::decode(&c.blocks(lo, hi), o)
    });
}
/// coc.rs `qlean_coc_block_start`: byte offset in the pack of block `b`; past the last block, the pack's whole length.
pub fn block_start(m: &Meta, b: usize) -> usize { if b < m.mblk { m.off[b] as usize } else { m.res_end() } }
/// The deep blocks `deep` of a bitmap threaded: `f(lo, hi, o, w0)` once per slice `[lo, hi)` of them, `o` the words
/// from the slice's first deep block to the next slice's first (`deep` ascends, so no two slices overlap) and `w0`
/// the word of the whole bitmap `o[0]` is.
pub fn over_deep<F: Fn(usize, usize, &mut [u64], usize) + Sync>(run: Runner, lg: u32, out: &mut [u64], deep: &[u32], who: &str, f: &F) {
    let end = out.len() * 8;
    let at = |k: usize| if k < deep.len() { (deep[k] as usize) << lg >> 3 } else { end };
    run_map_at(run, pod::bytes_mut(out), deep.len(), &at, QLEAN_COST_ARITH, 8 << lg, &|lo, hi, o: &mut [u8]| {
        f(lo, hi, pod::cast_mut::<u64>(o).unwrap_or_else(|| panic!("{who}: bitmap misaligned")), at(lo) / 8)
    });
}
/// coc.rs `coc_cmp2_run`: `a op b` as a bitmap, the deep blocks `deep` threaded over `cmp2_res`.
pub fn cmp2(run: Runner, op: i32, a: &Coc, b: &Coc, deep: &[u32], out: &mut [u64]) {
    over_deep(run, a.meta.lg, out, deep, "qlean_coc_mask_cmp_vv", &|lo, hi, o, w0| cmp2_res(a, b, op, o, deep, lo, hi, w0))
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
/// coc.rs `coc_cmp_meta`: the bitmap wherever a block's range settles it whole, and the numbers of the blocks it does not
/// (`deep`, answering how many). `b` none is the atom form, `v` standing for the other side's range. A patched block
/// is always deep: the ranges leave its nulls out.
pub fn cmp_meta(a: &Coc, b: Option<&Coc>, op: i32, v: i64, out: &mut [u64], deep: &mut [u32]) -> usize {
    let (n, m, mut nd) = (a.meta.n, &a.meta, 0);
    out[..n.div_ceil(64)].fill(0);
    for (k, lo, nb) in crate::blocks::Blocks::from(*a).walk() {
        let whole = if a.blk_nexc(k) > 0 || b.is_some_and(|b| b.blk_nexc(k) > 0) { -1 } else {
            match b { Some(b) => blk_cmp(op, m.base[k], m.maxv[k], b.meta.base[k], b.meta.maxv[k]),
                      None => blk_cmp(op, m.base[k], m.maxv[k], v, v) }
        };
        if whole == 1 { mask_fill(&mut out[lo >> 6..], nb) } else if whole < 0 { deep[nd] = k as u32; nd += 1 }
    }
    nd
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
                    res_mask_cmp(&c.pack[at..at + m.blk() * m.width[b] as usize / 8], nb, m.width[b], lo, hi.wrapping_sub(lo), op == NE,
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
/// coc.rs `coc_mask_cmp_res`: the blocks `blocks` of `x op t(b)` into `out`, whose `out[0]` is word `w0` of the bitmap.
pub fn mask_res<T: Fn(usize) -> i64>(c: &Coc, op: i32, t: T, blocks: impl Iterator<Item = usize>, out: &mut [u64], w0: usize) {
    let mut scratch = pod::Scr::<u64>::new(c.meta.blk());
    for b in blocks {
        let (at, nb) = crate::blocks::Blocks::from(*c).span(b);
        mask_blk(c, b, nb, op, t(b), &mut out[(at >> 6) - w0..], pod::bytes_mut(&mut scratch))
    }
}
/// coc.rs `coc_mask_cmp_run` and its entry: `x op v` as a bitmap into `out` (`n.div_ceil(64)` words). The blocks the
/// metadata settles are filled on the calling thread; the deep ones are threaded.
pub fn mask_cmp(run: Runner, op: u8, v: i64, c: &Coc, out: &mut [u64]) {
    let op = op as i32;
    let mut deep = vec![0u32; c.meta.nblk];
    let nd = cmp_meta(c, None, op, v, out, &mut deep);
    let deep = &deep[..nd];
    over_deep(run, c.meta.lg, out, deep, "qlean_coc_mask_cmp", &|lo, hi, o, w0| {
        mask_res(c, op, |_| v, deep[lo..hi].iter().map(|&k| k as usize), o, w0)
    })
}
/// coc.rs `shift_fill`: the encoder's source for `qlean_coc_shift` when the metadata cannot absorb `k`:
/// elements `i0 .. i0 + reduce::with_buf(f.c.meta.blk(), |buf| reduce::f32_sum(&mut AlpBlocks(*f), f.c.meta.n, f.c.meta.blk(), buf, None)).len()` of `x + k` (`neg`: `k - x`), nulls `fill`.
pub fn shift_fill(c: &Coc, k: i64, neg: bool, fill: i64, buf: &mut [i64], i0: usize) {
    c.load_run(i0 as i64, 0, buf);
    for x in buf { *x = if *x == i64::MIN { fill } else if neg { k.wrapping_sub(*x) } else { k.wrapping_add(*x) } }
}

// ---- A18: coc.rs ----
/// Blocks `b0 .. b1` into `o`, block `b` at `o[(b - b0) * blk * esz ..]` (`o` may end inside the last block).
pub fn load_blocks(f: &Cocf, b0: usize, b1: usize, o: &mut [u8]) {
    let (s, esz, blk) = (crate::blocks::Blocks::from(*f), if f.f32 { 4 } else { 8 }, f.c.meta.blk());
    for b in b0..b1 {
        let nb = s.span(b).1;
        f.load_blk(b, nb, &mut o[(b - b0) * blk * esz..][..nb * esz])
    }
}
/// coc.rs `alp_decode_run` and its entries: the whole ALP column into `out` (`f32`/`f64` bytes), by blocks.
pub fn alp_decode(run: Runner, f: &Cocf, out: &mut [u8]) {
    let unit = f.c.meta.blk() * if f.f32 { 4 } else { 8 };
    run_map(run, out, f.c.meta.nblk, unit, QLEAN_COST_ARITH, unit, &|lo, hi, o: &mut [u8]| load_blocks(f, lo, hi, o));
}
/// coc.rs `alp_gather_run` and its entry: `f[idx[i]]` into `out`, `fill`'s bits where `idx[i]` is out of range.
pub fn alp_gather(run: Runner, fill: u64, f: &Cocf, idx: &[i64], out: &mut [u8]) {
    let (sn, esz, shape, lg) = (f.c.meta.n, if f.f32 { 4 } else { 8 }, f.c.one_width(), f.c.meta.lg);
    let blk = f.c.meta.blk();
    run_map(run, out, idx.len(), esz, QLEAN_COST_GATHER, esz + 8, &|lo, hi, o: &mut [u8]| {
        let mut buf = pod::Scr::<u64>::new(blk);
        let bb = pod::bytes_mut(&mut buf);
        // `rust/src/structural.rs`'s GATHER_RUNS rule: a run of blk / 8 indices in one block restores the block once,
        // fewer are read one at a time
        let (mut rb, mut re) = (usize::MAX, 0);
        for j in lo..hi {
            let (u, at) = (idx[j] as u64, (j - lo) * esz);
            if u >= sn as u64 { o[at..at + esz].copy_from_slice(&fill.to_ne_bytes()[..esz]); continue }
            let (u, b) = (u as usize, u as usize >> lg);
            if j >= re {
                re = j + 1;
                while re < hi && idx[re] as u64 >> lg == b as u64 { re += 1 }
                if re - j >= blk / 8 { rb = b; f.load_blk(b, crate::blocks::Blocks::from(*f).span(b).1, bb) } else { rb = usize::MAX }
            }
            if rb == b { o[at..at + esz].copy_from_slice(&bb[(u - (b << lg)) * esz..][..esz]); continue }
            if j + 16 < hi { f.c.prefetch(idx[j + 16] as usize) }
            let k = (u & (blk - 1)) as u16;
            let (l, h) = (f.exc_off[b] as usize, f.exc_off[b + 1] as usize);
            let l = l + f.exc_pos[l..h].partition_point(|&p| p < k);
            if l < h && f.exc_pos[l] == k { o[at..at + esz].copy_from_slice(&f.exc_raw[l * esz..(l + 1) * esz]); continue }
            let v = dec(f.c.get_w(shape, u), f.exp[b] as i32);
            if f.f32 { o[at..at + 4].copy_from_slice(&(v as f32).to_ne_bytes()) } else { o[at..at + 8].copy_from_slice(&v.to_ne_bytes()) }
        }
    });
}


/// `cmp2` for two columns of different block sizes: each is restored whole, then compared as one run, because no block
/// of `a` is a block of `b`. Rare (the writer picks one size), so it is serial.
pub fn cmp2_dense(op: i32, a: &Coc, b: &Coc, out: &mut [u64]) {
    let n = a.meta.n;
    let dense = |c: &Coc| { let mut v = alloc::vec![0i64; n]; for k in 0..n.div_ceil(c.meta.blk()) { c.decode_blk(k, (n - (k << c.meta.lg)).min(c.meta.blk()), &mut v[k << c.meta.lg..]) } v };
    crate::cocops::res_cmp2(&dense(a), &dense(b), op, out);
}

/// coc.rs `cocf_mask_lt`'s block loop: every block of `x op ts[b]` into the zeroed `out`, on the calling thread.
pub fn mask_blks(c: &Coc, op: i32, ts: &[i64], out: &mut [u64]) { mask_res(c, op, |b| ts[b], 0..crate::blocks::Blocks::from(*c).nblk(), out, 0) }
