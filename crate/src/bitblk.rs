#![forbid(unsafe_code)]
//! A coc block of width 1, base 0 and no patch is a bit vector: its `blk / 8` payload bytes are the `Column.bits`
//! encoding of its rows, LSB first. The coc kernels ask `Coc::bit_blk` once per block, outside the element loops, and run
//! the `bits.rs` / `search.rs` word algorithms on the payload instead of unpacking it (G3: bits folded into coc).
use crate::bits::{popcount, some_bit};
use crate::coc::Coc;
use crate::cocops::{EQ, GE, GT, LE, LT, NE};
use alloc::vec::Vec;

/// word `i` of a payload (8-byte aligned in length for every block: `blk * 1 / 8` is a multiple of 8)
pub fn word(p: &[u8], i: usize) -> u64 { u64::from_le_bytes(p[i * 8..i * 8 + 8].try_into().expect("8 bytes")) }
/// the bits of word `i` that are rows of an `nb`-row block
pub fn live(nb: usize, i: usize) -> u64 { let r = nb - (i << 6).min(nb); if r >= 64 { !0 } else { !0 >> (64 - r) } }

impl<'a> Coc<'a> {
    /// Block `b`'s payload when the block is a bit vector: width 1, frame 0 (base and frame delta), no patch.
    pub fn bit_blk(&self, b: usize) -> Option<&'a [u8]> {
        let m = &self.meta;
        if m.width[b] != 1 || self.frame(b) != 0 || self.blk_nexc(b) != 0 { return None }
        let at = m.off[b] as usize;
        Some(&self.pack[at..at + m.blk() / 8])
    }
}

/// `coc_sum_blk` of a bit block: the set bits among its first `nb` rows.
pub fn ones(p: &[u8], nb: usize) -> usize { popcount(p, nb) }
/// `coc_all` of a bit block: no row is 0.
pub fn all_set(p: &[u8], nb: usize) -> bool { !some_bit(false, p, nb) }
/// The `op` of two bits `x`, `y` as the word `a op b` (rows past `nb` left to the caller's mask).
pub fn cmp_word(op: i32, a: u64, b: u64) -> u64 {
    match op { EQ => !(a ^ b), NE => a ^ b, LT => !a & b, LE => !a | b, GT => a & !b, _ => { debug_assert!(op == GE); a | !b } }
}
/// `x op v` of a bit block into the zeroed words `out`: each of the two values 0, 1 passes or not, so the answer is
/// none, all, the bits or their complement.
pub fn mask_cmp(p: &[u8], nb: usize, op: i32, v: i64, out: &mut [u64]) {
    let t = |x: i64| match op { EQ => x == v, NE => x != v, LT => x < v, LE => x <= v, GT => x > v, _ => x >= v };
    let inv = match (t(0), t(1)) { (false, false) => return, (true, true) => !0u64, (false, true) => 0, (true, false) => !0u64 };
    let fill = t(0) && t(1);
    for (i, o) in out[..nb.div_ceil(64)].iter_mut().enumerate() {
        *o = if fill { live(nb, i) } else { (word(p, i) ^ inv) & live(nb, i) }
    }
}
/// `a op b` of two bit blocks into `out` (`nb.div_ceil(64)` words, overwritten).
pub fn cmp2(pa: &[u8], pb: &[u8], nb: usize, op: i32, out: &mut [u64]) {
    for (i, o) in out[..nb.div_ceil(64)].iter_mut().enumerate() { *o = cmp_word(op, word(pa, i), word(pb, i)) & live(nb, i) }
}
/// `coc_rows_eq` of a bit block: the rows `at + i` with `x[i] == v`, appended ascending. 0 and 1 are the only values a
/// bit block holds.
pub fn rows_eq(p: &[u8], nb: usize, at: usize, v: i64, rows: &mut Vec<i64>) {
    if v != 0 && v != 1 { return }
    for i in 0..nb.div_ceil(64) {
        let mut w = (word(p, i) ^ if v == 0 { !0 } else { 0 }) & live(nb, i);
        while w != 0 { rows.push((at + (i << 6) + w.trailing_zeros() as usize) as i64); w &= w - 1 }
    }
}
/// `coc_find` of a bit block: the first row holding `v`.
pub fn find(p: &[u8], nb: usize, v: i64) -> Option<usize> {
    if v != 0 && v != 1 { return None }
    (0..nb.div_ceil(64)).find_map(|i| {
        let w = (word(p, i) ^ if v == 0 { !0 } else { 0 }) & live(nb, i);
        (w != 0).then(|| (i << 6) + w.trailing_zeros() as usize)
    })
}
/// `run_starts` of a bit block at row `at`: the rows whose bit differs from the row before, pushed at `out[*g..]`. `prev` is the
/// previous row's key (any value: one that is not 0 or 1 differs from both), left as this block's last bit.
pub fn run_starts(p: &[u8], nb: usize, at: usize, prev: &mut u64, g: &mut usize, out: &mut [i64]) {
    let mut top = *prev & 1;
    for k in 0..nb.div_ceil(64) {
        let x = word(p, k);
        let mut d = x ^ (x << 1 | top);
        if k == 0 && *prev > 1 { d |= 1 }
        top = x >> 63;
        d &= live(nb, k);
        while d != 0 { out[*g] = (at + (k << 6) + d.trailing_zeros() as usize) as i64; *g += 1; d &= d - 1 }
    }
    *prev = (p[(nb - 1) >> 3] >> ((nb - 1) & 7) & 1) as u64;
}
/// `coc_count_lt_blk` of a bit block: rows below `v`. The straddle case only: 0 < `v` <= 1 gives the zeros, v > 1 all.
pub fn count_lt(p: &[u8], nb: usize, v: i64) -> usize { if v <= 0 { 0 } else if v == 1 { nb - ones(p, nb) } else { nb } }
#[cfg(test)]
mod tests {
    use super::*;
    fn bits(s: &mut u64, nb: usize) -> Vec<u8> {
        let mut p = vec![0u8; 1024 / 8];
        for i in 0..nb { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; if *s & 1 != 0 { p[i >> 3] |= 1 << (i & 7) } }
        p
    }
    fn bit(p: &[u8], i: usize) -> i64 { (p[i >> 3] >> (i & 7) & 1) as i64 }
    #[test] fn bit_block_kernels_equal_the_per_row_answers() {
        let mut s = 88172645463325252u64;
        for nb in [1, 7, 63, 64, 65, 200, 1023, 1024] {
            let (a, b) = (bits(&mut s, nb), bits(&mut s, nb));
            assert_eq!(ones(&a, nb), (0..nb).filter(|&i| bit(&a, i) == 1).count());
            assert_eq!(all_set(&a, nb), (0..nb).all(|i| bit(&a, i) == 1));
            for op in [EQ, NE, LT, LE, GT, GE] {
                let c = |x: i64, y: i64| match op { EQ => x == y, NE => x != y, LT => x < y, LE => x <= y, GT => x > y, _ => x >= y };
                let mut o = vec![0u64; 16];
                cmp2(&a, &b, nb, op, &mut o);
                for i in 0..nb { assert_eq!(o[i >> 6] >> (i & 63) & 1 == 1, c(bit(&a, i), bit(&b, i)), "cmp2 op {op} nb {nb} i {i}") }
                for v in [-1, 0, 1, 2] {
                    let mut o = vec![0u64; 16];
                    mask_cmp(&a, nb, op, v, &mut o);
                    for i in 0..nb { assert_eq!(o[i >> 6] >> (i & 63) & 1 == 1, c(bit(&a, i), v), "mask op {op} v {v} nb {nb}") }
                    assert_eq!(o.iter().map(|w| w.count_ones() as usize).sum::<usize>(), (0..nb).filter(|&i| c(bit(&a, i), v)).count());
                }
            }
            for v in [-1, 0, 1, 2] {
                let mut r = Vec::new();
                rows_eq(&a, nb, 5, v, &mut r);
                assert_eq!(r, (0..nb).filter(|&i| bit(&a, i) == v).map(|i| (5 + i) as i64).collect::<Vec<_>>());
                assert_eq!(find(&a, nb, v), (0..nb).find(|&i| bit(&a, i) == v));
                assert_eq!(count_lt(&a, nb, v), (0..nb).filter(|&i| bit(&a, i) < v).count());
            }
        }
    }
}

/// Coc-level checks and the G3a measurement: a width-1, base-0 column built by hand against the `_bits` kernels.
#[cfg(test)]
mod coc_tests {
    use crate::coc::{view, Coc};
    use crate::cocops::{EQ, GE, GT, LE, LT, NE};
    use crate::search::{self, Blocks, Src};
    use crate::{bits, codec, pod};

    /// `n` rows of `payload` (`Column.bits`, LSB first) as a coc of block size `1 << lg`: (metadata words, pack words)
    fn build(payload: &[u8], n: usize, lg: u32) -> (Vec<u64>, Vec<u64>) {
        let (blk, nb) = (1usize << lg, n.div_ceil(1 << lg));
        let mut pack = vec![0u8; nb * blk / 8];
        pack[..payload.len()].copy_from_slice(payload);
        let mut m = vec![0u64; (33 * nb + 24).div_ceil(8) + 1];
        let any = |b: usize| (b * blk / 8..((b + 1) * blk / 8).min(payload.len())).any(|i| payload[i] != 0);
        for b in 0..nb {
            m[nb + b] = any(b) as u64; // maxv; base 0
            m[2 * nb + b] = (b * blk / 8) as u64; // off
        }
        m[4 * nb + 2] = lg as u64; // trailer: sumnul, sumn, lg
        let mb = pod::bytes_mut(&mut m);
        mb[32 * nb + 24..33 * nb + 24].fill(1); // width
        let pk = pack.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect();
        (m, pk)
    }
    fn rnd(s: &mut u64, n: usize, dens: u64) -> Vec<u8> {
        let mut p = vec![0u8; n.div_ceil(8)];
        for i in 0..n { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; if *s % dens == 0 { p[i >> 3] |= 1 << (i & 7) } }
        p
    }
    fn bit(p: &[u8], i: usize) -> i64 { (p[i >> 3] >> (i & 7) & 1) as i64 }
    fn view_of<'a>(m: &'a [u64], p: &'a [u64], n: usize, lg: u32) -> Coc<'a> {
        let nb = n.div_ceil(1 << lg);
        view(&pod::bytes(m)[..33 * nb + 24], pod::bytes(p), n).unwrap_or_else(|e| panic!("{e}"))
    }
    #[test] fn coc_w1_answers_equal_the_bits_answers() {
        let mut s = 0x9E3779B97F4A7C15u64;
        for lg in [6u32, 10, 16] { for n in [1usize, 63, 64, 65, 1000, 1024, 1025, 3000, 70000, 131073] { for dens in [1u64, 2, 16] {
            let (pa, pb) = (rnd(&mut s, n, dens), rnd(&mut s, n, dens + 1));
            let ((ma, ka), (mb, kb)) = (build(&pa, n, lg), build(&pb, n, lg));
            let (a, b) = (view_of(&ma, &ka, n, lg), view_of(&mb, &kb, n, lg));
            let ref_cnt = bits::popcount(&pa, n);
            assert_eq!(a.sum(i64::MIN), ref_cnt as u64, "sum lg {lg} n {n}");
            assert_eq!(a.all(), !bits::some_bit(false, &pa, n), "all");
            for v in [-1, 0, 1, 2] { assert_eq!(a.count_lt(v), (0..n).filter(|&i| bit(&pa, i) < v).count(), "count_lt {v}") }
            assert_eq!(search::coc_find(&a, 1), (0..n).find(|&i| bit(&pa, i) == 1).unwrap_or(n));
            assert_eq!(search::coc_find(&a, 0), (0..n).find(|&i| bit(&pa, i) == 0).unwrap_or(n));
            let mut want = vec![0i64; ref_cnt];
            assert_eq!(search::where_bits(n, &pa, &mut want), ref_cnt);
            assert_eq!(search::coc_rows_eq(&a, 1), want, "rows_eq lg {lg} n {n}");
            let (mut r1, mut r2) = (vec![0i64; n + 1], vec![0i64; n + 1]);
            let g1 = search::run_starts_bits(n, &pa, &mut r1);
            let g2 = search::run_starts(&Blocks::new(Src::For(a), n), 8, false, &mut r2);
            assert_eq!(r1[..g1], r2[..g2], "run_starts lg {lg} n {n}");
            for op in [EQ, NE, LT, LE, GT, GE] {
                let c = |x: i64, y: i64| match op { EQ => x == y, NE => x != y, LT => x < y, LE => x <= y, GT => x > y, _ => x >= y };
                for v in [-1, 0, 1, 2] {
                    let mut o = vec![0u64; n.div_ceil(64)];
                    codec::mask_cmp(crate::c::pool(), op as u8, v, &a, &mut o);
                    for i in 0..n { assert_eq!(o[i >> 6] >> (i & 63) & 1 == 1, c(bit(&pa, i), v), "mask op {op} v {v} lg {lg} n {n} i {i}") }
                    assert!(o.iter().map(|w| w.count_ones() as usize).sum::<usize>() <= n);
                }
                let mut o = vec![0u64; n.div_ceil(64)];
                let mut deep = vec![0u32; a.meta.nblk];
                let nd = codec::cmp_meta(&a, Some(&b), op, 0, &mut o, &mut deep);
                codec::cmp2(crate::c::pool(), op, &a, &b, &deep[..nd], &mut o);
                for i in 0..n { assert_eq!(o[i >> 6] >> (i & 63) & 1 == 1, c(bit(&pa, i), bit(&pb, i)), "cmp2 op {op} lg {lg} n {n} i {i}") }
                assert_eq!(o.iter().map(|w| w.count_ones() as usize).sum::<usize>(), (0..n).filter(|&i| c(bit(&pa, i), bit(&pb, i))).count());
            }
        } } }
    }

    /// `cargo test --release --lib g3a_bench -- --ignored --nocapture`, `QLEAN_THREADS=8 taskset -c 0-7`
    #[test] #[ignore] fn g3a_bench() {
        use std::time::Instant;
        fn ms(mut f: impl FnMut()) -> f64 { (0..15).map(|_| { let t = Instant::now(); f(); t.elapsed().as_secs_f64() * 1e3 }).fold(f64::MAX, f64::min) }
        let mut s = 0x9E3779B97F4A7C15u64;
        for n in [1_000_000usize, 10_000_000] {
            let sparse = rnd(&mut s, n, 16);
            let mut ones = vec![0xffu8; n.div_ceil(8)];
            if n % 8 != 0 { *ones.last_mut().unwrap() = ((1u32 << (n % 8)) - 1) as u8 }
            ones[(n - 1) >> 3] &= !(1 << ((n - 1) & 7));
            let other = rnd(&mut s, n, 3);
            println!("n = {n}\nop | bits ms | coc w1 lg10 | coc w1 lg16");
            let row = |name: &str, b: f64, c: [f64; 2]| println!("{name} | {b:.4} | {:.4} ({:.2}x) | {:.4} ({:.2}x)", c[0], c[0] / b, c[1], c[1] / b);
            let cols: Vec<_> = [10u32, 16].iter().map(|&lg| (build(&sparse, n, lg), build(&ones, n, lg), build(&other, n, lg), lg)).collect();
            let both = |f: &dyn Fn(&Coc, &Coc, &Coc) -> f64| -> [f64; 2] {
                let r: Vec<f64> = cols.iter().map(|((ms_, ks), (mo, ko), (mt, kt), lg)| f(&view_of(ms_, ks, n, *lg), &view_of(mo, ko, n, *lg), &view_of(mt, kt, n, *lg))).collect();
                [r[0], r[1]]
            };
            row("popcount / sum", ms(|| { std::hint::black_box(bits::popcount(&sparse, n)); }), both(&|a, _, _| ms(|| { std::hint::black_box(a.sum(i64::MIN)); })));
            row("some_bit clear / all", ms(|| { std::hint::black_box(bits::some_bit(false, &ones, n)); }), both(&|_, o, _| ms(|| { std::hint::black_box(o.all()); })));
            let cnt = bits::popcount(&sparse, n);
            row("where (count+index)", ms(|| { let mut o = vec![0i64; search::where_count(n, &sparse)]; search::where_bits(n, &sparse, &mut o); std::hint::black_box(&o); }),
                both(&|a, _, _| ms(|| { std::hint::black_box(search::coc_rows_eq(a, 1).len() == cnt); })));
            row("run_starts", ms(|| { let mut o = vec![0i64; n + 1]; std::hint::black_box(search::run_starts_bits(n, &sparse, &mut o)); }),
                both(&|a, _, _| ms(|| { let mut o = vec![0i64; n + 1]; std::hint::black_box(search::run_starts(&Blocks::new(Src::For(*a), n), 8, false, &mut o)); })));
            row("count of zeros / count_lt 1", ms(|| { std::hint::black_box(n - bits::popcount(&sparse, n)); }), both(&|a, _, _| ms(|| { std::hint::black_box(a.count_lt(1)); })));
            row("mask x==1 (copy) / mask_cmp", ms(|| { std::hint::black_box(sparse.clone()); }),
                both(&|a, _, _| ms(|| { let mut o = vec![0u64; n.div_ceil(64)]; codec::mask_cmp(crate::c::pool(), EQ as u8, 1, a, &mut o); std::hint::black_box(&o); })));
            row("a & !b words / mask_cmp_vv GT", ms(|| { let o: Vec<u8> = sparse.iter().zip(&other).map(|(x, y)| x & !y).collect(); std::hint::black_box(o); }),
                both(&|a, _, b| ms(|| {
                    let mut o = vec![0u64; n.div_ceil(64)];
                    let mut deep = vec![0u32; a.meta.nblk];
                    let nd = codec::cmp_meta(a, Some(b), GT, 0, &mut o, &mut deep);
                    codec::cmp2(crate::c::pool(), GT, a, b, &deep[..nd], &mut o);
                    std::hint::black_box(&o);
                })));
        }
    }
}
