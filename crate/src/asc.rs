#![forbid(unsafe_code)]
//! `asc`, the stable sort (design §4, `Kernel.kasc` in Rel/Kernel/Asc.lean): rows ordered lexicographically by the order
//! codes of several key columns, ties in row order. The Lean body is an insertion sort followed by two scatters; this is
//! the fused form over the encoded key columns: a sorted test off the block metadata, then sort.rs's grades.
//!
//! Owner approvals (PLAN 6.10): a key block is decoded into an L1 scratch one block at a time (S); the grade keeps a
//! permutation work array, and a dense array of order codes for a key that is not graded off its blocks: a column whose
//! codes do not ascend with its words, or several columns, which become one mixed-radix code per row (X).
use alloc::{vec, vec::Vec};
use core::ops::Range;
use crate::blocks::Blocks;
use crate::c::Runner;
use crate::coc::Coc;
use crate::enc::Producer;
use crate::key::SK_I64;
use crate::{kwin, pod, sort};

/// `Rel.Kernel.normalise` (Rel/Kernel/Search.lean): a float's `-0.0` to `0` and every NaN to the one quiet NaN.
pub fn normalise(w: usize, float: bool, v: u64) -> u64 {
    if !float { return v }
    let abs = v & ((1u64 << (8 * w - 1)) - 1);
    let inf = if w == 8 { 0x7ff0_0000_0000_0000 } else { 0x7f80_0000 };
    if abs == 0 { 0 } else if inf < abs { if w == 8 { 0xfff8_0000_0000_0000 } else { 0xffc0_0000 } } else { v }
}

/// `Rel.Kernel.ordKey`: the unsigned code whose order is q's order of the `w`-byte word `v`.
pub fn ord_key(w: usize, float: bool, signed: bool, v: u64) -> u64 {
    let mask = if w == 8 { u64::MAX } else { (1u64 << (8 * w)) - 1 };
    let top = 1u64 << (8 * w - 1);
    if float {
        let u = normalise(w, true, v & mask);
        if u & top != 0 { !u & mask } else { u | top }
    } else if signed { (v & mask) ^ top } else { v & mask }
}

/// `Kernel.ascOrd` at the `QAtomicType` constructor index `t` (Rel/Kernel/Value.lean's order): `ordKey`'s width, float
/// and signed flags at `orderKind t`; `None` at `general` (0) and `symbol` (9).
pub fn order(t: u8) -> Option<(usize, bool, bool)> {
    match t {
        1 | 2 | 8 => Some((1, false, false)),
        3 => Some((2, false, true)),
        4 | 11 | 12 | 15 | 16 | 17 => Some((4, false, true)),
        5 | 10 | 14 => Some((8, false, true)),
        6 => Some((4, true, false)),
        7 | 13 => Some((8, true, false)),
        _ => None,
    }
}

/// One key column of `kasc`: the encoded column, its type's `order`, and the least and greatest word as its block
/// metadata bounds them (`kwin::range`, no residual read).
#[derive(Clone, Copy)]
pub struct Key<'a> { pub c: Coc<'a>, w: usize, float: bool, signed: bool, lo: i64, hi: i64 }
impl<'a> Key<'a> {
    pub fn new(c: Coc<'a>, (w, float, signed): (usize, bool, bool)) -> Self {
        let (mn, mx) = kwin::range(SK_I64, &c);
        Key { c, w, float, signed, lo: (mn ^ 1 << 63) as i64, hi: (mx ^ 1 << 63) as i64 }
    }
    fn code(&self, v: u64) -> u64 { ord_key(self.w, self.float, self.signed, v) }
    /// Every word lies where `ord_key` is `v + s` for one `s`: the type's signed range (`s` its sign bit), its unsigned
    /// range (`s = 0`), or for a float `0 ..= +inf` (`s` the sign bit). There the column's own order is its code order.
    fn linear(&self) -> bool {
        let top = 1i128 << (8 * self.w - 1);
        let inf = if self.w == 8 { 0x7ff0_0000_0000_0000 } else { 0x7f80_0000 };
        let (a, b) = if self.float { (0, inf) } else if self.signed { (-top, top - 1) } else { (0, 2 * top - 1) };
        a <= self.lo as i128 && self.hi as i128 <= b
    }
    /// The least and greatest code: the bounds' codes where `linear`, else every code of the type's width.
    fn span(&self) -> (u64, u64) {
        if self.linear() { (self.code(self.lo as u64), self.code(self.hi as u64)) }
        else { (0, if self.w == 8 { !0 } else { (1 << (8 * self.w)) - 1 }) }
    }
    /// The codes of rows `at .. at + out.len()`, the blocks they cross decoded into `buf` one at a time (S).
    fn codes(&self, at: usize, out: &mut [u64], buf: &mut [u64]) {
        let src = Blocks::from(self.c);
        let x = src.block(0, at, out.len(), 8, pod::bytes_mut(buf));
        let x = pod::cast::<u64>(x).expect("asc: a decoded block is misaligned");
        for (o, &v) in out.iter_mut().zip(x) { *o = self.code(v) }
    }
}

/// The rows of `ks` a block at a time on the first column's grid: `f(at, codes)` with column `c`'s codes of rows
/// `at ..` at `codes[c * blk ..]`; false from `f` stops the walk.
fn blocks(ks: &[Key], mut f: impl FnMut(usize, usize, &[u64]) -> bool) {
    let g = Blocks::from(ks[0].c).g;
    let (blk, mut buf) = (g.blk(), vec![0u64; 2 * g.blk()]);
    let mut t = vec![0u64; ks.len() * blk];
    for (_, at, cnt) in g.walk() {
        for (k, o) in ks.iter().zip(t.chunks_exact_mut(blk)) { k.codes(at, &mut o[..cnt], &mut buf) }
        if !f(at, cnt, &t) { return }
    }
}

/// The rows already in `lexLe` order: for a first column in code order (`Key::linear`) first `sort::ascending_enc`, off
/// the metadata and the residuals, which decides one key alone; else one pass a block at a time over every key's codes,
/// each row against the one before it.
pub fn sorted(run: Runner, ks: &[Key], m: usize) -> bool {
    let Some(k0) = ks.first() else { return true };
    if m < 2 { return true }
    if k0.linear() {
        if !sort::ascending_enc(run, SK_I64, false, false, &k0.c) { return false }
        if ks.len() == 1 { return true }
    }
    let (blk, nk) = (Blocks::from(k0.c).g.blk(), ks.len());
    let (mut prev, mut ok) = (vec![0u64; nk], true);
    // lexicographic `a <= b` of two rows given by their code at each column: the first column where they differ decides
    let le = |a: &dyn Fn(usize) -> u64, b: &dyn Fn(usize) -> u64| (0..nk).find(|&c| a(c) != b(c)).is_none_or(|c| a(c) < b(c));
    blocks(ks, |at, cnt, t| {
        ok = (at == 0 || le(&|c| prev[c], &|c| t[c * blk])) && (1..cnt).all(|j| le(&|c| t[c * blk + j - 1], &|c| t[c * blk + j]));
        for (c, p) in prev.iter_mut().enumerate() { *p = t[c * blk + cnt - 1] }
        ok
    });
    ok
}

/// `ks` cut left to right into runs whose code spans multiply into 64 bits: each run is one mixed-radix code a row
/// (`mixed`), so one grade sorts by all of its columns.
fn groups(ks: &[Key]) -> Vec<Range<usize>> {
    let (mut g, mut at, mut p) = (Vec::new(), 0, 1u128);
    for (i, k) in ks.iter().enumerate() {
        let (a, b) = k.span();
        let s = (b - a) as u128 + 1;
        match p.checked_mul(s).filter(|&q| q <= 1 << 64) { Some(q) => p = q, None => { g.push(at..i); (at, p) = (i, s) } }
    }
    g.push(at..ks.len());
    g
}

/// The mixed-radix code of the run `ks` (its first column the most significant) at each row `i`, or at row `p[i]` under
/// a permutation (one random read a column, `Coc::get_w`), with the least and greatest of them.
fn mixed(ks: &[Key], m: usize, p: Option<&[i64]>) -> (Vec<u64>, u64, u64) {
    let sp: Vec<(u64, u64)> = ks.iter().map(Key::span).collect();
    // a span of every 64-bit code is a run of its own (`groups`), so its radix `2^64` wraps to 0 against an `acc` of 0
    let mix = |acc: u64, (a, b): (u64, u64), x: u64| acc.wrapping_mul((b - a).wrapping_add(1)).wrapping_add(x - a);
    let mut c = vec![0u64; m];
    match p {
        Some(p) => for (k, &s) in ks.iter().zip(&sp) {
            let uw = k.c.one_width();
            for (x, &i) in c.iter_mut().zip(p) { *x = mix(*x, s, k.code(k.c.get_w(uw, i as usize) as u64)) }
        },
        None => blocks(ks, |at, cnt, t| {
            let blk = t.len() / ks.len();
            for (j, x) in c[at..at + cnt].iter_mut().enumerate() { *x = sp.iter().enumerate().fold(0, |acc, (k, &s)| mix(acc, s, t[k * blk + j])) }
            true
        }),
    }
    let (mn, mx) = sort::keys_range(&c);
    (c, mn, mx)
}

/// `Kernel.ascGrade` over the key columns `ks` of `m` rows each: `None` where the rows are already in order (`sorted`),
/// else the permutation. LSD over the runs of `groups`, the least significant first, each a stable grade of its codes
/// read through the permutation so far; a lone column in code order with no permutation yet is graded straight off
/// its blocks (`sort::order_enc`), every other run through its dense codes (`sort::grade_keys`).
pub fn grade(run: Runner, ks: &[Key], m: usize) -> Option<Vec<i64>> {
    if sorted(run, ks, m) { return None }
    let mut p: Option<Vec<i64>> = None;
    for g in groups(ks).into_iter().rev() {
        let mut o = vec![0i64; m];
        match (&p, &ks[g.clone()]) {
            (None, [k]) if k.linear() => sort::order_enc(run, SK_I64, false, false, &k.c, &mut o),
            (_, ks) => { let (c, mn, mx) = mixed(ks, m, p.as_deref()); sort::grade_keys(&c, false, mn, mx, &mut o) }
        }
        p = Some(match p { None => o, Some(p) => o.iter().map(|&j| p[j as usize]).collect() });
    }
    p
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ffi::{Form, Sink};
    #[test] fn codes_order_as_q_does() {
        assert_eq!(ord_key(4, false, true, 5), 0x8000_0005);
        assert_eq!(ord_key(4, false, true, 0xffff_ffff), 0x7fff_ffff);
        assert_eq!(ord_key(8, false, true, u64::MAX), 0x7fff_ffff_ffff_ffff);
        // NaN below -1.0 below -0.0 = 0.0 below 1.0
        let f = |x: f64| ord_key(8, true, false, x.to_bits());
        assert!(f(f64::NAN) < f(-1.0) && f(-1.0) < f(0.0) && f(-0.0) == f(0.0) && f(0.0) < f(1.0));
    }
    /// The word reference: `0 .. m` stably by `keys` lexicographically, one LSD counting pass per code byte.
    fn reference(keys: &[Vec<u64>], m: usize) -> Vec<i64> {
        let mut p: Vec<usize> = (0..m).collect();
        for k in keys.iter().rev() { for b in (0..8).map(|b| 8 * b) { p.sort_by_key(|&i| (k[i] >> b) as u8) } }
        p.into_iter().map(|i| i as i64).collect()
    }
    // every column shape against the word reference: sorted, reversed, ties, patched, codes not in word order (an `int`
    // with high bits, a float with negatives and NaN), one to three keys, and spans that do not fit one code
    #[test] fn grade_is_the_reference() {
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        let mut rnd = move || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        for m in [0usize, 1, 2, 5, 1000, 3000] {
            let cols: Vec<(u8, Vec<i64>)> = vec![
                (5, (0..m as i64).collect()),
                (5, (0..m as i64).rev().collect()),
                (5, (0..m).map(|_| (rnd() % 7) as i64).collect()),
                (5, (0..m).map(|i| if i % 97 == 5 { rnd() as i64 } else { (rnd() % 1000) as i64 }).collect()),
                (4, (0..m).map(|_| rnd() as i64).collect()),
                (4, (0..m).map(|_| (rnd() % 50) as i64 - 25).collect()),
                (7, (0..m).map(|i| [f64::NAN, -0.0, 0.0, -1.5, 2.5, (i % 5) as f64][rnd() as usize % 6].to_bits() as i64).collect()),
                (7, (0..m).map(|i| (i as f64).to_bits() as i64).collect()),
                (1, (0..m).map(|_| (rnd() % 300) as i64).collect()),
                (13, (0..m).map(|_| rnd() as i64).collect()),
            ];
            let enc: Vec<(u8, [Vec<u8>; 2])> = cols.iter().map(|(t, x)| {
                let o = Sink::new(m, 8, Form::For).answer(&Blocks::dense(pod::bytes(x), 8));
                (*t, [0, 1].map(|i| o.borrow().field(i).bytes().to_vec()))
            }).collect();
            let key = |i: usize| Key::new(crate::coc::view(&enc[i].1[0], &enc[i].1[1], m).ok().expect("asc test: view"), order(enc[i].0).expect("asc test: order"));
            let codes = |i: usize| { let (w, f, g) = order(cols[i].0).expect("asc test: order"); cols[i].1.iter().map(|&v| ord_key(w, f, g, v as u64)).collect::<Vec<u64>>() };
            let n = cols.len();
            let sets: Vec<Vec<usize>> = (0..n).map(|i| vec![i]).chain((0..n).map(|i| vec![i, (i + 3) % n]))
                .chain((0..n).map(|i| vec![(i + 2) % n, i, (i + 5) % n])).chain([vec![2, 2], vec![9, 4], vec![0, 9, 2]]).collect();
            for set in sets {
                let ks: Vec<Key> = set.iter().map(|&i| key(i)).collect();
                let want = reference(&set.iter().map(|&i| codes(i)).collect::<Vec<_>>(), m);
                let got = grade(crate::c::pool(), &ks, m).unwrap_or_else(|| (0..m as i64).collect());
                assert_eq!(got, want, "columns {set:?} at m {m}");
                assert_eq!(sorted(crate::c::pool(), &ks, m), want.iter().enumerate().all(|(i, &x)| x == i as i64), "sorted {set:?} at m {m}");
            }
        }
    }
}
