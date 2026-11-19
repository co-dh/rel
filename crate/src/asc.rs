#![forbid(unsafe_code)]
//! `asc`, the stable sort (design §4, `Kernel.kasc` in Rel/Kernel/Asc.lean): rows ordered lexicographically by the order
//! codes of several key columns, ties in row order. The Lean body is an insertion sort followed by two scatters; this is
//! the fused form over the encoded key columns: a sorted test off the block metadata, then sort.rs's grades.
//!
//! Owner approvals (PLAN 6.10): a key block is decoded into an L1 scratch one block at a time (S); the grade keeps a
//! permutation work array, and a dense array of order codes for a key that is not graded off its blocks: a column whose
//! codes do not ascend with its words, or several columns, which become one mixed-radix code per row (X).
use alloc::{format, string::String, vec, vec::Vec};
use core::ops::Range;
use crate::blocks::Blocks;
use crate::c::Runner;
use crate::coc::Coc;
use crate::enc::Producer;
use crate::key::SK_I64;
use crate::{kwin, pod, sort};

/// `Rel.Kernel.ordCode` (Rel/Kernel/Asc.lean): the unsigned code of the `w`-byte word `v`, one to one on that word. A
/// signed integer flips its sign bit; a float takes IEEE 754 totalOrder (non-negative: set the sign bit; negative: flip
/// every bit), so `-0.0` and `0.0`, and every two NaNs, keep codes of their own.
pub fn ord_key(w: usize, float: bool, signed: bool, v: u64) -> u64 {
    let mask = if w == 8 { u64::MAX } else { (1u64 << (8 * w)) - 1 };
    let top = 1u64 << (8 * w - 1);
    let u = v & mask;
    if float { if u & top != 0 { u ^ mask } else { u | top } } else if signed { u ^ top } else { u }
}

/// `Kernel.ascOrd` at the `QAtomicType` constructor index `t` (Rel/Kernel/Value.lean's order): `ordCode`'s width, float
/// and signed flags at `orderKind t`; `None` at `sym` (9) and `general` (12).
pub fn order(t: u8) -> Option<(usize, bool, bool)> {
    match t {
        0 | 1 | 7 => Some((1, false, false)),
        8 => Some((1, false, true)),
        2 => Some((2, false, true)),
        3 | 10 => Some((4, false, true)),
        4 | 11 => Some((8, false, true)),
        5 => Some((4, true, false)),
        6 => Some((8, true, false)),
        _ => None,
    }
}

/// `Kernel.ascWords`' bound on a `pos` key of `m` rows: its `i64` order code `i ^ 2^63` ascends with `i` only up to
/// `2^63` rows (laws A1, A2), so past that the column is the error, word for word the Lean body's.
pub fn pos_rows(m: usize) -> Result<(), String> {
    if m as u128 <= 1 << 63 { Ok(()) } else { Err(format!("asc: a pos column of {m} rows is past 2^63, where its order codes wrap")) }
}

/// One key column of `kasc`: the encoded column, its type's `order`, and the least and greatest word as its block
/// metadata bounds them (`kwin::range`, no residual read), and `uw`, the width its blocks share (`Coc::one_width`).
#[derive(Clone, Copy)]
pub struct Key<'a> { pub c: Coc<'a>, w: usize, float: bool, signed: bool, lo: i64, hi: i64, uw: u8 }
impl<'a> Key<'a> {
    pub fn new(c: Coc<'a>, (w, float, signed): (usize, bool, bool)) -> Self {
        let (mn, mx) = kwin::range(SK_I64, &c);
        // `one_width` reads every block's width, so it is read once here and not at each word (`at`)
        Key { c, w, float, signed, lo: (mn ^ 1 << 63) as i64, hi: (mx ^ 1 << 63) as i64, uw: c.one_width() }
    }
    pub(crate) fn code(&self, v: u64) -> u64 { ord_key(self.w, self.float, self.signed, v) }
    /// Row `i`'s code, its word read at its address (`Coc::get_w`).
    pub(crate) fn at(&self, i: usize) -> u64 { self.code(self.c.get_w(self.uw, i) as u64) }
    /// Every word lies where `ord_key` is `v + s` for one `s`: the type's signed range (`s` its sign bit), its unsigned
    /// range (`s = 0`), or for a float every word with the sign bit clear, `+0.0 ..= +NaN` (`s` the sign bit, which
    /// `ord_key` sets there). There the column's own order is its code order.
    fn linear(&self) -> bool {
        let top = 1i128 << (8 * self.w - 1);
        let (a, b) = if self.float { (0, top - 1) } else if self.signed { (-top, top - 1) } else { (0, 2 * top - 1) };
        a <= self.lo as i128 && self.hi as i128 <= b
    }
    /// The least and greatest code: the bounds' codes where `linear`, else every code of the type's width.
    pub(crate) fn span(&self) -> (u64, u64) {
        if self.linear() { (self.code(self.lo as u64), self.code(self.hi as u64)) }
        else { (0, if self.w == 8 { !0 } else { (1 << (8 * self.w)) - 1 }) }
    }
    /// The codes of rows `at .. at + out.len()`, the blocks they cross decoded into `buf` one at a time (S).
    pub(crate) fn codes(&self, at: usize, out: &mut [u64], buf: &mut [u64]) {
        let src = Blocks::from(self.c);
        let x = src.block(0, at, out.len(), 8, pod::bytes_mut(buf));
        let x = pod::cast::<u64>(x).expect("asc: a decoded block is misaligned");
        for (o, &v) in out.iter_mut().zip(x) { *o = self.code(v) }
    }
}

/// A column of words read at its address: a `pos` column (word `i` is `i`) or a `foR` one (`Coc::get_w`).
#[derive(Clone, Copy)]
pub enum Ix<'a> { Pos, For(Coc<'a>, u8) }
impl<'a> Ix<'a> {
    pub fn of(c: Option<Coc<'a>>) -> Self { c.map_or(Ix::Pos, |c| Ix::For(c, c.one_width())) }
    pub fn get(&self, i: usize) -> i64 { match self { Ix::Pos => i as i64, Ix::For(c, uw) => c.get_w(*uw, i) } }
}

/// A `cells` key column (`Kernel.AscKey.cells`): row `i` names the cell `ix[i]`, that cell the payload rows
/// `lo .. hi` clamped to `0 .. c`, each payload row keyed by `els` (`Kernel.cellFns`). Every word is read at its
/// address in its encoded column, one at a time, and no column is decoded.
pub struct Cells<'a> { pub ix: Ix<'a>, pub c: usize, pub lo: Ix<'a>, pub hi: Ix<'a>, pub els: Vec<Col<'a>> }
impl Cells<'_> {
    /// Row `i`'s cell as its first payload row and its length.
    fn span(&self, i: usize) -> (usize, usize) {
        let r = self.ix.get(i) as usize;
        let s = self.lo.get(r).clamp(0, self.c as i64) as usize;
        (s, (self.hi.get(r).clamp(0, self.c as i64) as usize).saturating_sub(s))
    }
    /// Row `i`'s cell against row `j`'s in `cellFns`' `lexLe` order: the first element that differs decides, else
    /// the shorter cell, a proper prefix, comes first.
    pub fn cmp(&self, i: usize, j: usize) -> core::cmp::Ordering {
        let ((si, li), (sj, lj)) = (self.span(i), self.span(j));
        (0..li.min(lj)).map(|k| cmp_rows(&self.els, si + k, sj + k)).find(|o| o.is_ne()).unwrap_or_else(|| li.cmp(&lj))
    }
}

/// A key column of `kasc` and `kseen`: an atom column, a `pos` atom column (word `i` is `i`), or a `cells` one.
pub enum Col<'a> { Atom(Key<'a>), Pos, Cells(Cells<'a>) }

/// The atom keys of `cs`, where every column is a `foR` atom.
pub fn atoms<'a>(cs: &[Col<'a>]) -> Option<Vec<Key<'a>>> { cs.iter().map(|c| match c { Col::Atom(k) => Some(*k), _ => None }).collect() }

/// Row `i` against row `j` in `lexLe` order over the codes of `cs`: the first column where they differ decides.
pub fn cmp_rows(cs: &[Col], i: usize, j: usize) -> core::cmp::Ordering {
    cs.iter().map(|c| match c {
        Col::Atom(k) => k.at(i).cmp(&k.at(j)),
        Col::Pos => i.cmp(&j),
        Col::Cells(a) => a.cmp(i, j),
    }).find(|o| o.is_ne()).unwrap_or(core::cmp::Ordering::Equal)
}

/// `grade` over any key columns: all `foR` atoms go to `grade`; else `None` where every row is no later than the next
/// (`cmp_rows`), or a stable comparison sort of `til m` by `cmp_rows`.
pub fn grade_cols(run: Runner, cs: &[Col], m: usize) -> Option<Vec<i64>> {
    if let Some(ks) = atoms(cs) { return grade(run, &ks, m) }
    if (1..m).all(|i| cmp_rows(cs, i - 1, i).is_le()) { return None }
    let mut p: Vec<i64> = (0..m as i64).collect();
    p.sort_by(|&a, &b| cmp_rows(cs, a as usize, b as usize));
    Some(p)
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
            for (x, &i) in c.iter_mut().zip(p) { *x = mix(*x, s, k.at(i as usize)) }
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
        // totalOrder: -NaN below -inf below -1.0 below -0.0 below 0.0 below 1.0 below NaN
        let f = |x: f64| ord_key(8, true, false, x.to_bits());
        let g = |b: u64| ord_key(8, true, false, b);
        assert!(f(-1.0) < f(-0.0) && f(-0.0) < f(0.0) && f(0.0) < f(1.0) && f(1.0) < f(f64::NAN));
        assert!(g(0xfff8_0000_0000_0000) < f(f64::NEG_INFINITY) && f(f64::NEG_INFINITY) < f(-1.0));
        // f32 at its 4 bytes: the same order, the high word ignored
        let h = |x: f32| ord_key(4, true, false, x.to_bits() as u64);
        assert!(h(-1.0) < h(-0.0) && h(-0.0) < h(0.0) && h(0.0) < h(1.0) && h(1.0) < h(f32::NAN));
    }
    /// The `pos` bound with no rows allocated: `2^63` rows are in order, one more is `ascWords`' error.
    #[test] fn pos_rows_bound() {
        assert_eq!(pos_rows(1 << 63), Ok(()));
        assert_eq!(pos_rows((1 << 63) + 1).unwrap_err(),
            "asc: a pos column of 9223372036854775809 rows is past 2^63, where its order codes wrap");
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
                (4, (0..m as i64).collect()),
                (4, (0..m as i64).rev().collect()),
                (4, (0..m).map(|_| (rnd() % 7) as i64).collect()),
                (4, (0..m).map(|i| if i % 97 == 5 { rnd() as i64 } else { (rnd() % 1000) as i64 }).collect()),
                (3, (0..m).map(|_| rnd() as i64).collect()),
                (3, (0..m).map(|_| (rnd() % 50) as i64 - 25).collect()),
                (6, (0..m).map(|i| [f64::NAN, -0.0, 0.0, -1.5, 2.5, (i % 5) as f64][rnd() as usize % 6].to_bits() as i64).collect()),
                (6, (0..m).map(|i| (i as f64).to_bits() as i64).collect()),
                (0, (0..m).map(|_| (rnd() % 300) as i64).collect()),
                (6, (0..m).map(|_| rnd() as i64).collect()),
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

    /// The words `x` as a `foR` column's metadata and pack, `Coc::view`ed by `col`.
    fn enc(x: &[i64]) -> [Vec<u8>; 2] {
        let o = Sink::new(x.len(), 8, Form::For).answer(&Blocks::dense(pod::bytes(x), 8));
        [0, 1].map(|i| o.borrow().field(i).bytes().to_vec())
    }
    fn col(e: &[Vec<u8>; 2], m: usize) -> Coc<'_> { crate::coc::view(&e[0], &e[1], m).ok().expect("asc test: view") }
    fn xs(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }

    /// A `cells` table: `m` rows naming cells `ix`, the cells `lo .. hi` of a payload of atom columns `els` (type 4).
    struct T { m: usize, c: usize, ix: Vec<i64>, lo: Vec<i64>, hi: Vec<i64>, els: Vec<Vec<i64>>, atoms: Vec<(u8, Vec<i64>)> }
    struct E { ix: [Vec<u8>; 2], lo: [Vec<u8>; 2], hi: [Vec<u8>; 2], els: Vec<[Vec<u8>; 2]>, atoms: Vec<(u8, [Vec<u8>; 2])> }
    impl T {
        fn enc(&self) -> E {
            E { ix: enc(&self.ix), lo: enc(&self.lo), hi: enc(&self.hi), els: self.els.iter().map(|x| enc(x)).collect(),
                atoms: self.atoms.iter().map(|(t, x)| (*t, enc(x))).collect() }
        }
        /// the key list: the atom columns first and last around the `cells` column (none where `atoms` is empty)
        fn cols<'a>(&self, e: &'a E) -> Vec<Col<'a>> {
            let n = self.lo.len();
            let cells = Col::Cells(Cells { ix: Ix::of(Some(col(&e.ix, self.m))), c: self.c, lo: Ix::of(Some(col(&e.lo, n))),
                hi: Ix::of(Some(col(&e.hi, n))),
                els: e.els.iter().map(|x| Col::Atom(Key::new(col(x, self.c), order(4).expect("asc test: order")))).collect() });
            let atom = |(t, x): &'a (u8, [Vec<u8>; 2])| Col::Atom(Key::new(col(x, self.m), order(*t).expect("asc test: order")));
            let mut cs: Vec<Col> = e.atoms.iter().take(1).map(atom).collect();
            cs.push(cells);
            cs.extend(e.atoms.iter().skip(1).map(atom));
            cs
        }
        /// The straightforward reference: each row's keys as plain vectors, cells clamped as `Cells::span` does,
        /// compared by `Vec`'s lexicographic order (a proper prefix first), a stable sort.
        fn reference(&self) -> Vec<i64> {
            let code = |t: u8, v: i64| { let (w, f, g) = order(t).expect("asc test: order"); ord_key(w, f, g, v as u64) };
            let cell = |i: usize| {
                let r = self.ix[i] as usize;
                let s = self.lo[r].clamp(0, self.c as i64) as usize;
                let e = (self.hi[r].clamp(0, self.c as i64) as usize).max(s);
                (s..e).map(|k| self.els.iter().map(|x| code(4, x[k])).collect::<Vec<u64>>()).collect::<Vec<_>>()
            };
            let key = |i: usize| {
                let a = |j: usize| self.atoms.get(j).map(|(t, x)| code(*t, x[i]));
                (a(0), cell(i), (1..self.atoms.len()).map(|j| a(j)).collect::<Vec<_>>())
            };
            let ks: Vec<_> = (0..self.m).map(key).collect();
            let mut p: Vec<usize> = (0..self.m).collect();
            p.sort_by(|&a, &b| ks[a].cmp(&ks[b]));
            p.into_iter().map(|i| i as i64).collect()
        }
        /// `n` cells over a payload of `nel` columns: each cell a shared prefix (one of `np`, `pl` long, drawn from
        /// `alpha` symbols) and a random tail up to `tl` long; row `i` names a random cell.
        fn make(s: &mut u64, m: usize, n: usize, np: usize, pl: usize, tl: usize, alpha: u64, nel: usize) -> T {
            let pre: Vec<Vec<Vec<i64>>> = (0..np).map(|_| (0..pl).map(|_| (0..nel).map(|_| (xs(s) % alpha) as i64).collect()).collect()).collect();
            let (mut els, mut lo, mut hi) = (vec![Vec::new(); nel], Vec::new(), Vec::new());
            for _ in 0..n {
                let p = &pre[xs(s) as usize % np];
                let cut = if pl == 0 { 0 } else { xs(s) as usize % (pl + 1) };
                let t = if tl == 0 { 0 } else { xs(s) as usize % (tl + 1) };
                lo.push(els[0].len() as i64);
                for e in p[..cut].iter().cloned().chain((0..t).map(|_| (0..nel).map(|_| (xs(s) % alpha) as i64).collect())) {
                    for (c, v) in els.iter_mut().zip(e) { c.push(v) }
                }
                hi.push(els[0].len() as i64);
            }
            let c = els[0].len();
            T { m, c, ix: (0..m).map(|_| (xs(s) % n as u64) as i64).collect(), lo, hi, els, atoms: Vec::new() }
        }
    }

    // `cells` keys against the reference: shared prefixes, empty cells, equal rows (one cell named by many rows, so
    // stability decides), cells across foR blocks, patched payloads, `lo`/`hi` out of range, scalar keys around them
    #[test] fn cells_is_the_reference() {
        let mut s = 0x2545_f491_4f6c_dd1du64;
        for (m, n, np, pl, tl, alpha, nel) in [(0, 1, 1, 0, 0, 2, 1), (1, 1, 1, 3, 2, 2, 1), (7, 3, 1, 4, 2, 2, 1), (500, 40, 3, 20, 5, 3, 1),
                (3000, 3000, 5, 60, 4, 2, 1), (3000, 200, 2, 1500, 3, 2, 1), (2000, 500, 4, 8, 3, 3, 2), (2500, 2500, 1, 0, 3, 4, 1)] {
            let mut t = T::make(&mut s, m, n, np, pl, tl, alpha, nel);
            for v in 0..4 {
                if v == 1 { // patches: a rare outlier in the payload, so its blocks carry a patch list
                    for x in t.els[0].iter_mut() { if xs(&mut s) % 211 == 0 { *x = (xs(&mut s) >> 1) as i64 - (1 << 62) } }
                }
                if v == 2 { // cells out of the payload: a `lo` below 0, a `hi` past `c`, `lo` past `hi`
                    for r in 0..n { match xs(&mut s) % 9 { 0 => t.lo[r] = -5, 1 => t.hi[r] = t.c as i64 + 7, 2 => t.lo[r] = t.hi[r] + 1, _ => {} } }
                }
                if v == 3 { // scalar keys before and after the cells
                    t.atoms = vec![(4, (0..m).map(|_| (xs(&mut s) % 3) as i64).collect()), (6, (0..m).map(|_| ((xs(&mut s) % 5) as f64 - 2.0).to_bits() as i64).collect())];
                }
                let e = t.enc();
                let cs = t.cols(&e);
                let got = grade_cols(crate::c::pool(), &cs, m).unwrap_or_else(|| (0..m as i64).collect());
                assert_eq!(got, t.reference(), "cells m {m} n {n} prefix {np}x{pl} tail {tl} variant {v}");
            }
        }
    }

    /// `cargo test --release --features std -- --ignored bench_asc --nocapture`: (a) 1e6 scalar i64 rows, (b) 2e5
    /// cells of ~50 with long shared prefixes, (c) 2e5 short cells; each the median of 5 runs of `grade_cols`.
    #[test] #[ignore] fn bench_asc() {
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        let time = |what: &str, cs: &[Col], m: usize| {
            let mut t: Vec<_> = (0..5).map(|_| { let t0 = std::time::Instant::now(); core::hint::black_box(grade_cols(crate::c::pool(), cs, m)); t0.elapsed() }).collect();
            t.sort();
            std::println!("{what}: {:?}", t[2]);
        };
        let which = std::env::var("ASC_BENCH").unwrap_or_default();
        if which.is_empty() || which.contains('a') {
            let x: Vec<i64> = (0..1_000_000).map(|_| xs(&mut s) as i64).collect();
            let e = enc(&x);
            time("(a) 1e6 scalar i64", &[Col::Atom(Key::new(col(&e, x.len()), order(4).expect("order")))], x.len());
        }
        if which.is_empty() || which.contains('b') {
            let t = T::make(&mut s, 200_000, 200_000, 50, 48, 4, 3, 1);
            let e = t.enc();
            time("(b) 2e5 cells ~50, shared prefixes", &t.cols(&e), t.m);
        }
        if which.is_empty() || which.contains('c') {
            let t = T::make(&mut s, 200_000, 200_000, 1, 0, 4, 1000, 1);
            let e = t.enc();
            time("(c) 2e5 cells 0..4", &t.cols(&e), t.m);
        }
    }
}
