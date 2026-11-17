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
use crate::pod::{self, Lane};
use crate::{QLEAN_COST_ARITH, QLEAN_COST_GATHER};

// ---- A15: coc.rs ----
/// coc.rs `qlean_coc_decode_{i16,i32,i64}` past the unboxing: the whole column into `out`, by blocks.
pub fn decode<T: Lane + Send>(run: Runner, c: &Coc, out: &mut [T]) {
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
    for k in 0..n.div_ceil(m.blk()) {
        let (lo, nb) = (k << m.lg, (n - (k << m.lg)).min(m.blk()));
        let whole = if a.blk_nexc(k) > 0 || b.is_some_and(|b| b.blk_nexc(k) > 0) { -1 } else {
            match b { Some(b) => blk_cmp(op, m.base[k], m.maxv[k], b.meta.base[k], b.meta.maxv[k]),
                      None => blk_cmp(op, m.base[k], m.maxv[k], v, v) }
        };
        if whole == 1 { mask_fill(&mut out[lo >> 6..], nb) } else if whole < 0 { deep[nd] = k as u32; nd += 1 }
    }
    nd
}

/// coc.rs `res_expand`: the residuals of width `W` < 8, `8 / W` to a byte, one to a byte of `out`.
pub fn expand<const W: usize>(p: &[u8], nb: usize, out: &mut [u8]) {
    for (o, &b) in out.chunks_mut(8 / W).zip(&p[..(nb * W).div_ceil(8)]) {
        for (t, x) in o.iter_mut().enumerate() { *x = (b >> (t * W)) & ((1u16 << W) - 1) as u8 }
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
/// coc.rs `res_mask_cmp`: block residuals `p` at width `w` tested `r - lo <= span`, into the zeroed `out`. `scratch` is
/// `blk * 8` bytes the caller owns, so a kilobyte is not declared inside the loop over blocks.
pub fn res_mask_cmp(p: &[u8], nb: usize, w: u8, lo: u64, span: u64, inv: bool, out: &mut [u64], scratch: &mut [u8]) {
    if res_vcmp(p, w, nb, lo, span, inv, out) { return }
    match w {
        // every residual is 0, so every bit is the same
        0 => if (0u64.wrapping_sub(lo) <= span) ^ inv { mask_fill(out, nb) },
        1 => { expand::<1>(p, nb, scratch); words::<1>(scratch, nb, lo, span, inv, out) }
        2 => { expand::<2>(p, nb, scratch); words::<1>(scratch, nb, lo, span, inv, out) }
        4 => { expand::<4>(p, nb, scratch); words::<1>(scratch, nb, lo, span, inv, out) }
        _ => {
            let mut w = w; // an odd width leaves w >= 8
            let p = lanes(p, &mut w, nb, scratch);
            match w { 8 => words::<1>(p, nb, lo, span, inv, out), 16 => words::<2>(p, nb, lo, span, inv, out),
                      32 => words::<4>(p, nb, lo, span, inv, out), _ => words::<8>(p, nb, lo, span, inv, out) }
        }
    }
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
                let (lo, hi) = match op { LT => (0, t.wrapping_sub(1)), LE => (0, t), GT => (t.wrapping_add(1), u64::MAX),
                                          GE => (t, u64::MAX), _ => (t, t) };
                let at = m.off[b] as usize;
                res_mask_cmp(&c.pack[at..at + m.blk() * m.width[b] as usize / 8], nb, m.width[b], lo, hi.wrapping_sub(lo), op == NE,
                             w64, scratch)
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
        let (at, nb) = (b << c.meta.lg, (c.meta.n - (b << c.meta.lg)).min(c.meta.blk()));
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
    let (n, esz, blk) = (f.c.meta.n, if f.f32 { 4 } else { 8 }, f.c.meta.blk());
    for b in b0..b1 {
        let nb = (n - b * blk).min(blk);
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
                if re - j >= blk / 8 { rb = b; f.load_blk(b, (sn - (b << lg)).min(blk), bb) } else { rb = usize::MAX }
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
pub fn mask_blks(c: &Coc, op: i32, ts: &[i64], out: &mut [u64]) { mask_res(c, op, |b| ts[b], 0..c.meta.n.div_ceil(c.meta.blk()), out, 0) }
#[cfg(test)]
mod tests {
    use crate::BLK;
    use super::*;
    use crate::c::qlean_run_c;
    // expected values: the C of b3e0b59 (/data/tmp/qrs/A15/h.c: 50625 checks, 0 mismatches)
    fn two_blocks<'a>(base: &'a [i64], off: &'a [u64], bsum: &'a [i64], width: &'a [u8], n: usize, pack: &'a [u8]) -> Coc<'a> {
        let meta = Meta { lg: crate::DEFAULT_LG, base, maxv: base, off, bsum, width, sumnul: 0, sumn: 0, n, nblk: base.len(), mblk: base.len() };
        Coc { meta, pack, exc: None, fdelta: None }
    }
    #[test] fn block_start_is_the_offset_then_the_end() {
        let c = two_blocks(&[0, 0], &[0, 0], &[0, 0], &[0, 8], 2048, &[]);
        let m = &c.meta;
        assert_eq!([block_start(m, 0), block_start(m, 1), block_start(m, 2), block_start(m, 9)], [0, 0, 1024, 1024]);
        assert_eq!(block_start(&two_blocks(&[], &[], &[], &[], 0, &[]).meta, 3), 0);
    }
    #[test] fn decode_adds_the_base_over_a_ragged_last_block() {
        let (base, off) = ([10, -5], [0u64, 0]);
        let c = two_blocks(&base, &off, &[0, 0], &[0, 0], 1030, &[]);
        let mut out = [0i16; 1030];
        decode(qlean_run_c, &c, &mut out);
        assert!(out[..1024].iter().all(|&x| x == 10) && out[1024..].iter().all(|&x| x == -5));
    }
    // the whole mask against the decoded elements, every width a block can have (the vector compare at the odd ones, the
    // unpack-then-word path where the window leaves the lane), a ragged last block, v below / at / inside / above the range
    #[test] fn mask_cmp_agrees_with_decoding_at_every_width() {
        let mut s = 0x9e3779b97f4a7c15u64;
        let mut rnd = move || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        let (n, tail) = (BLK + 6, 6);
        for w in 0..=40u8 {
            let bb = BLK * w as usize / 8;
            let pack: Vec<u8> = (0..2 * bb).map(|_| rnd() as u8).collect();
            let (base, off, width) = ([0i64, 5], [0u64, bb as u64], [w, w]);
            let mut c = two_blocks(&base, &off, &[0, 0], &width, n, &pack);
            let mut dec = vec![0i64; n];
            for b in 0..2 { let nb = if b == 0 { BLK } else { tail }; c.decode_blk(b, nb, &mut dec[b * BLK..b * BLK + nb]) }
            let maxv = [*dec[..BLK].iter().max().unwrap(), *dec[BLK..].iter().max().unwrap()];
            c.meta.maxv = &maxv;
            for v in [-1, 0, 4, 5, maxv[0] / 2, maxv[0], maxv[0] + 1, rnd() as i64 % 1000] {
                for op in 0..6u8 {
                    let mut out = [u64::MAX; BLK / 64 + 1];
                    mask_cmp(qlean_run_c, op, v, &c, &mut out);
                    for (i, &x) in dec.iter().enumerate() {
                        assert_eq!(out[i / 64] >> (i % 64) & 1 == 1, cmp1(op as i32, x, v), "w {w} op {op} v {v} i {i}");
                    }
                    assert_eq!(out[BLK / 64] >> tail, 0, "bits past the column, w {w} op {op}");
                }
            }
        }
    }
    #[test] fn shift_fill_keeps_the_null_and_shifts_the_rest() {
        let base = [i64::MIN, 7];
        let c = two_blocks(&base, &[0, 0], &[0, 0], &[0, 0], 2048, &[]);
        let mut buf = [0i64; 2];
        shift_fill(&c, 5, false, i64::MIN, &mut buf, 1023);
        assert_eq!(buf, [i64::MIN, 12]);
        shift_fill(&c, 5, true, i64::MIN, &mut buf, 1023);
        assert_eq!(buf, [i64::MIN, -2]);
    }
}
/// Columns at the smallest and the largest block size, built by hand (the writer only makes `DEFAULT_LG`): view, decode,
/// sum/min/max, gather, the moves of structural.rs, and two columns of different block sizes.
#[cfg(test)]
mod lg_tests {
    use super::*;
    use crate::c::qlean_run_c;
    use crate::{MAX_LG, MIN_LG};
    /// `vals` at block size `1 << lg`: each block its minimum as base and the width its range needs, no exceptions. The
    /// metadata is word-backed, because a view asks 8-alignment of it.
    struct Built { m: Vec<u64>, ml: usize, p: Vec<u8> }
    fn build(vals: &[i64], lg: u32) -> Built {
        let (blk, nb) = (1usize << lg, vals.len().div_ceil(1 << lg));
        let (mut base, mut maxv, mut off, mut bsum, mut width, mut p) = (vec![], vec![], vec![], vec![], vec![], vec![]);
        for b in 0..nb {
            let s = &vals[b * blk..vals.len().min((b + 1) * blk)];
            let (mn, mx) = (*s.iter().min().unwrap(), *s.iter().max().unwrap());
            let w = (64 - ((mx - mn) as u64).leading_zeros()) as u8;
            let o = p.len();
            p.resize(o + blk * w as usize / 8, 0);
            if w > 0 { for (j, &v) in s.iter().enumerate() { crate::res::res_put(&mut p[o..], w, j, (v - mn) as u64) } }
            (base.push(mn), maxv.push(mx), off.push(o as i64), bsum.push(s.iter().fold(0i64, |a, &v| a.wrapping_add(v))), width.push(w));
        }
        let mut m: Vec<u8> = [&base, &maxv, &off, &bsum].iter().flat_map(|v| v.iter().flat_map(|x| x.to_ne_bytes())).collect();
        m.extend(crate::enc::coc_sumnul(8, false).to_ne_bytes());
        m.extend((vals.len() as u64).to_ne_bytes());
        m.extend((lg as u64).to_ne_bytes());
        m.extend(&width);
        let ml = m.len();
        let w = m.chunks(8).map(|c| { let mut t = [0u8; 8]; t[..c.len()].copy_from_slice(c); u64::from_ne_bytes(t) }).collect();
        Built { m: w, ml, p }
    }
    impl Built { fn meta(&self) -> &[u8] { &crate::pod::bytes(&self.m)[..self.ml] } }
    fn col(b: &Built, n: usize) -> Coc<'_> { crate::coc::view(b.meta(), &b.p, n).unwrap_or_else(|e| panic!("{e}")) }
    /// block `b` lies in 2^(3 + 5b mod 17) of its base, so every block has its own width
    fn vals(n: usize, lg: u32) -> Vec<i64> {
        let mut s = 0x9e3779b97f4a7c15u64 ^ lg as u64;
        (0..n).map(|i| { s ^= s << 13; s ^= s >> 7; s ^= s << 17; (i >> lg) as i64 * 1000 - 7 + (s % (1u64 << (3 + 5 * (i >> lg) % 17))) as i64 }).collect()
    }
    #[test] fn view_decode_sums_gather_and_moves_at_the_smallest_and_largest_block() {
        for lg in [MIN_LG, 7, MAX_LG] {
            let blk = 1usize << lg;
            let n = 3 * blk + 5;
            let v = vals(n, lg);
            let b = build(&v, lg);
            let c = col(&b, n);
            assert_eq!((c.meta.lg, c.meta.blk(), c.meta.nblk, c.meta.n), (lg, blk, 4, n), "view at lg {lg}");
            // decode
            let mut d = vec![0i64; n];
            decode(qlean_run_c, &c, &mut d);
            assert_eq!(d, v, "decode at lg {lg}");
            // sum, min, max
            assert_eq!((c.sum(i64::MIN), c.min(i64::MIN), c.max(i64::MIN)),
                       (v.iter().fold(0u64, |a, &x| a.wrapping_add(x as u64)), *v.iter().min().unwrap(), *v.iter().max().unwrap()), "sum/min/max at lg {lg}");
            // gather: indices across every block, backwards, repeated, and two past the end that take the fill
            let idx: Vec<i64> = [0, n - 1, blk, blk - 1, 2 * blk + 1, n, n + 7, 3 * blk, 5, 5].iter().map(|&i| i as i64).collect();
            let mut out = vec![0u8; idx.len() * 8];
            crate::structural::gather_enc(qlean_run_c, 8, 0xAB, &c, &idx, &mut out);
            let want: Vec<u8> = idx.iter().flat_map(|&i| if (i as usize) < n { v[i as usize] } else { 0xAB }.to_ne_bytes()).collect();
            assert_eq!(out, want, "gather at lg {lg}");
            // encode round trip of the structural moves: reverse keeps the block size, twice is the identity
            let (bw, nw) = (build(&v[..3 * blk], lg), 3 * blk);
            let cw = col(&bw, nw);
            let (mut rm, mut rp) = (vec![0u8; 33 * cw.meta.mblk + 24], vec![]);
            rp.resize(crate::structural::reverse_meta(&cw, &mut rm), 0);
            crate::structural::reverse_enc(qlean_run_c, &cw, &mut rp);
            let rw: Vec<u64> = rm.chunks(8).map(|c| { let mut t = [0u8; 8]; t[..c.len()].copy_from_slice(c); u64::from_ne_bytes(t) }).collect();
            let r = crate::coc::view(&crate::pod::bytes(&rw)[..rm.len()], &rp, nw).unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(r.meta.lg, lg, "reverse keeps lg {lg}");
            let mut rd = vec![0i64; nw];
            decode(qlean_run_c, &r, &mut rd);
            assert_eq!(rd, v[..nw].iter().rev().copied().collect::<Vec<_>>(), "reverse at lg {lg}");
            // two columns of different block sizes compare as one run
            let b2 = build(&v, if lg == MIN_LG { 10 } else { MIN_LG });
            let c2 = col(&b2, n);
            assert!(!c.vv_ok(&c2, 0, 0, 0), "vv_ok refuses two block sizes at lg {lg}");
            let mut mask = vec![0u64; n.div_ceil(64)];
            cmp2_dense(crate::cocops::EQ, &c, &c2, &mut mask);
            assert!((0..n).all(|i| mask[i / 64] >> (i % 64) & 1 == 1), "equal columns at two block sizes, lg {lg}");
        }
    }
    #[test] fn concat_move_of_whole_blocks_keeps_lg() {
        for lg in [MIN_LG, MAX_LG] {
            let blk = 1usize << lg;
            let (va, vb) = (vals(2 * blk, lg), vals(blk + 5, lg));
            let (ba, bb) = (build(&va, lg), build(&vb, lg));
            let n = va.len() + vb.len();
            let (mut mo, mut po) = (vec![0u8; 33 * 4 + 24], vec![0u8; ba.p.len() + bb.p.len()]);
            crate::structural::concat_move(lg, &[ba.meta(), bb.meta()], &[&ba.p, &bb.p], n, 8, &mut mo, &mut po);
            let mw: Vec<u64> = mo.chunks(8).map(|c| { let mut t = [0u8; 8]; t[..c.len()].copy_from_slice(c); u64::from_ne_bytes(t) }).collect();
            let c = crate::coc::view(&crate::pod::bytes(&mw)[..mo.len()], &po, n).unwrap_or_else(|e| panic!("{e}"));
            let mut d = vec![0i64; n];
            decode(qlean_run_c, &c, &mut d);
            assert_eq!((c.meta.lg, d), (lg, [va, vb].concat()), "concat at lg {lg}");
        }
    }
}
