#![forbid(unsafe_code)]
//! Column (a), sort.c: keys and their range (A19), the grades (A20–A22), pair and id grouping (A23–A24), symbol
//! sorts and groups (A25–A26), guids (A27). The `qlean_sort_*` entries unbox and allocate and stay C (§1).
//! A grade answers into `out: &mut [i64]` of `n`; `kind` is sort.c's `SK_*`.
use alloc::vec;
use alloc::vec::Vec;
use core::sync::atomic::Ordering::Relaxed;

use crate::c::{run_map, run_slices, Runner};
use crate::coc::{lanes, Coc};
use crate::key::{self, Keys, Pass, SK_BIT, SK_I16, SK_I32, SK_I64, SK_KINDS_N, SK_U8};
use crate::ids::by_width;
use crate::sym::{sym_hash, sym_msort, Syms};
use crate::{ids, kwin, pod, BLK, QLEAN_COST_ARITH, QLEAN_COST_COPY};
/// sort.c `SK_LANE`: kind bit that makes `grade_narrow` read the payload as ids of `kind & 0x7f` bits.
const SK_LANE: u8 = 0x80;

/// sort.c:351 `ksrc`: the keys of a dense payload `p` or of an encoded column `c`, `n` of them.
#[derive(Clone, Copy)]
pub struct Ksrc<'a> { pub kind: u8, pub p: &'a [u8], pub c: Option<Coc<'a>>, pub n: usize }

// ---- A19: sort.c:183-400 (key_flip, keys_blk_foR, kwin_* are kwin.rs, B11) ----
/// sort.c:`SK_MM_*`: the least and greatest key in four independent accumulators, because one `lo`/`hi` pair makes the
/// compare a loop-carried chain a cycle long per element (measured in sort.c, kept for the same reason).
struct Mm { lo: [u64; 4], hi: [u64; 4] }
impl Mm {
    fn new() -> Self { Mm { lo: [!0; 4], hi: [0; 4] } }
    #[inline(always)]
    fn four(&mut self, v: [u64; 4]) { for j in 0..4 { self.lo[j] = self.lo[j].min(v[j]); self.hi[j] = self.hi[j].max(v[j]) } }
    #[inline(always)]
    fn one(&mut self, v: u64) { self.lo[0] = self.lo[0].min(v); self.hi[0] = self.hi[0].max(v) }
    fn done(&self) -> (u64, u64) { (self.lo.into_iter().min().unwrap(), self.hi.into_iter().max().unwrap()) }
}
/// sort.c:`SK_KEYS`: write every key and take the range in the same pass.
struct Fill<'k>(&'k mut [u64]);
impl Pass for Fill<'_> {
    type Out = (u64, u64);
    #[inline(always)]
    fn run<K: Keys>(self, mut s: K, n: usize) -> (u64, u64) {
        assert!(n <= s.len(), "qlean sort: keys_of over {n} keys of a source holding {}", s.len());
        let (k, mut m, mut i) = (&mut self.0[..n], Mm::new(), 0);
        while i + 4 <= n {
            let v = [s.at(i), s.at(i + 1), s.at(i + 2), s.at(i + 3)];
            k[i..i + 4].copy_from_slice(&v);
            m.four(v);
            i += 4;
        }
        for i in i..n { let v = s.at(i); k[i] = v; m.one(v) }
        m.done()
    }
}
/// sort.c:183 `keys_of`: every key of `p` into `k`; answers `(min, max)`, `(0, 0)` for none. `kind` is one of the eight
/// element kinds (not `SK_KEY`, `SK_WIN`); the C wrapper reports that, so here it is a panic.
pub fn keys_of(kind: u8, p: &[u8], n: usize, k: &mut [u64]) -> (u64, u64) {
    if n == 0 { return (0, 0) }
    assert!(kind < SK_KINDS_N, "qlean sort: element kind {kind} is not one of the {SK_KINDS_N} in QLean/Kernel/Scan.lean");
    key::each(kind, &p[..key::bytes(kind, n).expect("keys_of: dense kind")], n, Fill(k))
        .unwrap_or_else(|| panic!("keys_of: the payload of kind {kind} is misaligned"))
}
/// sort.c:205 `keys_range`: the same reduction over keys already written; `(0, 0)` for none.
pub fn keys_range(k: &[u64]) -> (u64, u64) {
    let (mut m, mut c) = (Mm::new(), k.chunks_exact(4));
    if k.is_empty() { return (0, 0) }
    for v in c.by_ref() { m.four([v[0], v[1], v[2], v[3]]) }
    for &v in c.remainder() { m.one(v) }
    m.done()
}
/// sort.c:`SK_DENSE_BLK`: keys `[at, at + k.len())` of a dense payload.
struct Blk<'k> { at: usize, k: &'k mut [u64] }
impl Pass for Blk<'_> {
    type Out = ();
    #[inline(always)]
    fn run<K: Keys>(self, mut s: K, _: usize) { for (j, o) in self.k.iter_mut().enumerate() { *o = s.at(self.at + j) } }
}
impl<'a> Ksrc<'a> {
    /// sort.c:354 `ksrc_blk`: block `b`'s keys into `k` (BLK long); answers their count. A dense payload of any
    /// kind that is not an element kind (`SK_KEY`) is read as keys already.
    pub fn blk(&self, b: usize, k: &mut [u64]) -> usize {
        let (at, cnt) = (b * BLK, (self.n - b * BLK).min(BLK));
        match &self.c {
            Some(c) => kwin::keys_blk(self.kind, c, b, &mut k[..cnt]),
            None => key::each(self.kind, &self.p[..key::bytes(self.kind, self.n).expect("ksrc_blk: dense kind")], self.n, Blk { at, k: &mut k[..cnt] })
                .unwrap_or_else(|| panic!("ksrc_blk: the payload of kind {} is misaligned", self.kind)),
        }
        cnt
    }
    /// sort.c:394 `ksrc_range`: off the block metadata for a pack, one pass over the keys for a dense payload;
    /// `(u64::MAX, 0)` for none, which is what the C's untouched accumulators answered.
    pub fn range(&self) -> (u64, u64) {
        if let Some(c) = &self.c { return kwin::range(self.kind, c) }
        if self.n == 0 { return (!0, 0) }
        key::each(self.kind, &self.p[..key::bytes(self.kind, self.n).expect("ksrc_range: dense kind")], self.n, key::Range)
            .unwrap_or_else(|| panic!("ksrc_range: the payload of kind {} is misaligned", self.kind))
    }
}

// ---- A20: sort.c:417-730 ----
/// sort.c:`SK_KSRC_EACH`, a block at a time: `f(i, keys)` for the keys `i ..` of `s` in order. A key array is read in
/// place; a pack or a dense payload of elements goes through `Ksrc::blk`, so an encoded column's keys never exist whole.
#[inline(always)]
fn ksrc_blocks(s: &Ksrc, mut f: impl FnMut(usize, &[u64])) {
    if s.c.is_none() && s.kind == key::SK_KEY {
        let k = crate::pod::cast::<u64>(s.p).expect("ksrc_blocks: the key array is misaligned");
        for (b, ch) in k[..s.n].chunks(BLK).enumerate() { f(b * BLK, ch) }
    } else {
        let mut kb = [0u64; BLK];
        for b in 0..s.n.div_ceil(BLK) { let c = s.blk(b, &mut kb); f(b * BLK, &kb[..c]) }
    }
}
/// `f(i, key)` for every key of `s` in order.
#[inline(always)]
fn ksrc_each(s: &Ksrc, mut f: impl FnMut(usize, u64)) {
    ksrc_blocks(s, |at, ks| for (j, &v) in ks.iter().enumerate() { f(at + j, v) })
}
/// sort.c:417 `grade_runs`: the grade when the keys are a few ascending runs; false = not that shape. A run in the
/// asked-for order answers the identity, one strictly the other way the reversed identity (strictly: `2 2 1` is
/// non-increasing but its ascending grade is `2 0 1`, so a tie inside a descending run has to reach the sort).
pub fn grade_runs(k: &[u64], desc: bool, out: &mut [i64]) -> bool {
    let n = k.len();
    if k.windows(2).all(|w| if desc { w[1] <= w[0] } else { w[1] >= w[0] }) { for (i, o) in out[..n].iter_mut().enumerate() { *o = i as i64 } return true }
    if k.windows(2).all(|w| if desc { w[1] > w[0] } else { w[1] < w[0] }) { for (i, o) in out[..n].iter_mut().enumerate() { *o = (n - 1 - i) as i64 } return true }
    false
}
/// sort.c:`SK_COUNT_MAX`: a counting table past this many buckets costs two cache misses an element to save a pass.
const SK_COUNT_MAX: u64 = 1 << 16;
/// sort.c:`SK_COUNTABLE`: a table with one bucket per key is affordable (within twice the column and in cache).
pub fn sk_countable(span: u64, n: usize) -> bool { span < n as u64 * 2 + 1024 && span < SK_COUNT_MAX }
/// A counter or an index as wide as `n` needs: `u32` below 2^32 elements, `usize` above.
trait Ix: Copy + Default {
    fn of(v: usize) -> Self;
    fn to(self) -> usize;
}
impl Ix for u32 { #[inline(always)] fn of(v: usize) -> u32 { v as u32 } #[inline(always)] fn to(self) -> usize { self as usize } }
impl Ix for usize { #[inline(always)] fn of(v: usize) -> usize { v } #[inline(always)] fn to(self) -> usize { self } }
/// One bucket per value of `d(key)`: a single stable pass, no comparisons. `d` is recomputed from the key, not read
/// out of an array: the subtraction is one instruction, the array eight bytes an element written once and read twice.
/// `N` is the table length when it is one of the literals `grade_count` picks (0 = `nb`): `d(k) < nb <= N`, so masking
/// the index with `N - 1` changes nothing and lets the compiler see the index is in range (no bounds check).
fn count<C: Ix, const N: usize>(s: &Ksrc, nb: usize, rank: bool, d: impl Fn(u64) -> u64, out: &mut [i64]) {
    let (len, m) = if N == 0 { (nb, usize::MAX) } else { (N, N - 1) };
    let mut cnt = alloc::vec![C::default(); len];
    ksrc_each(s, |_, k| { let c = &mut cnt[d(k) as usize & m]; *c = C::of(c.to() + 1) });
    let mut at = 0;
    for c in cnt[..nb].iter_mut() { let t = c.to(); *c = C::of(at); at += t }
    // the rank is where the grade would have put `i`: the same counter, stored the other way
    if rank { ksrc_each(s, |i, k| { let c = &mut cnt[d(k) as usize & m]; out[i] = c.to() as i64; *c = C::of(c.to() + 1) }) }
    else { ksrc_each(s, |i, k| { let c = &mut cnt[d(k) as usize & m]; out[c.to()] = i as i64; *c = C::of(c.to() + 1) }) }
}
/// `count` at the table length that holds `nb` buckets: 256, 4096 or 65536 (what `sk_countable` allows), else `nb`.
fn count_by<C: Ix>(s: &Ksrc, nb: usize, rank: bool, d: impl Fn(u64) -> u64, out: &mut [i64]) {
    if nb <= 256 { count::<C, 256>(s, nb, rank, d, out) }
    else if nb <= 4096 { count::<C, 4096>(s, nb, rank, d, out) }
    else if nb <= 65536 { count::<C, 65536>(s, nb, rank, d, out) }
    else { count::<C, 0>(s, nb, rank, d, out) }
}
/// sort.c:474 `grade_count`: counting sort over the key span `span`; `rank` answers ranks instead of the grade.
pub fn grade_count(s: &Ksrc, mn: u64, mx: u64, desc: bool, rank: bool, span: u64, out: &mut [i64]) {
    let nb = span as usize + 1;
    match (s.n <= u32::MAX as usize, desc) {
        (true, true) => count_by::<u32>(s, nb, rank, |k| mx - k, out),
        (true, false) => count_by::<u32>(s, nb, rank, |k| k - mn, out),
        (false, true) => count_by::<usize>(s, nb, rank, |k| mx - k, out),
        (false, false) => count_by::<usize>(s, nb, rank, |k| k - mn, out),
    }
}
/// sort.c:498 `grade_perm`: the keys are a permutation of `mn ..= mx`; false = they are not. Inverting the permutation
/// reads each element once and writes each answer once; `seen` is a bitmap (125 KB at a million, stays in L2) and a
/// column that is not a permutation exits at its first repeated key. Under `rank` the answer is the narrowed key itself.
pub fn grade_perm(s: &Ksrc, mn: u64, mx: u64, desc: bool, rank: bool, out: &mut [i64]) -> bool {
    let mut seen = alloc::vec![0u64; s.n.div_ceil(64)];
    let (mut kb, mut ok) = ([0u64; BLK], true);
    'blocks: for b in 0..s.n.div_ceil(BLK) {
        let cnt = s.blk(b, &mut kb);
        for j in 0..cnt {
            let v = if desc { mx - kb[j] } else { kb[j] - mn }; // <= span == n-1, so `seen` holds it
            let w = &mut seen[(v >> 6) as usize];
            if (*w >> (v & 63)) & 1 != 0 { ok = false; break 'blocks }
            *w |= 1 << (v & 63);
            if rank { out[b * BLK + j] = v as i64 } else { out[v as usize] = (b * BLK + j) as i64 }
        }
    }
    ok
}
/// sort.c:555 `sk_digit`: the radix digit width for `bits`-bit keys and `n` of them: 8 below 65536 elements (the
/// counter table is then the larger array), 14 above 48 bits, else the narrowest digit that takes the same number of
/// passes, rounded up into the closed set 10, 13, 16 (each a literal in `grade_radix`, so `nb` and `mask` are constants).
pub fn sk_digit(bits: u32, n: usize) -> u32 {
    if n < 65536 { return 8 }
    if bits > 48 { return 14 }
    let np = bits.div_ceil(16);
    let dig = bits.div_ceil(np);
    if dig <= 10 { 10 } else if dig <= 13 { 13 } else { 16 }
}
/// sort.c:682 `grade_radix`: LSD radix grade of keys `xr`-flipped minus `base` (`n >= 2`, `span` their range).
/// Every digit's histogram is taken in one read of the keys, which names the surviving passes first: the last writes
/// only the answer, and once what is left of the key fits beside the index (`ixb` bits) the two travel as one word.
pub fn grade_radix(s: &Ksrc, span: u64, xr: u64, base: u64, out: &mut [i64]) {
    let (bits, wid) = (64 - span.leading_zeros(), sk_digit(64 - span.leading_zeros(), s.n));
    if s.n > u32::MAX as usize { return radix::<usize, 0>(s, wid, bits, xr, base, out) }
    match wid {
        16 => radix::<u32, 16>(s, wid, bits, xr, base, out),
        14 => radix::<u32, 14>(s, wid, bits, xr, base, out),
        13 => radix::<u32, 13>(s, wid, bits, xr, base, out),
        10 => radix::<u32, 10>(s, wid, bits, xr, base, out),
        _ => radix::<u32, 0>(s, wid, bits, xr, base, out),
    }
}
/// `D` is the digit width as a literal (0 = run-time `wid`), so the common widths compile to constants.
fn radix<T: Ix, const D: u32>(s: &Ksrc, wid: u32, bits: u32, xr: u64, base: u64, out: &mut [i64]) {
    let n = s.n;
    let dig = if D == 0 { wid } else { D };
    let (nb, mask) = (1usize << dig, (1u64 << dig) - 1);
    let np = bits.div_ceil(dig) as usize;
    let ixb = 64 - (n as u64 - 1).leading_zeros() as i32; // n >= 2: a run answered above
    let d = |k: u64| (k ^ xr).wrapping_sub(base);
    let mut cnt = alloc::vec![T::default(); nb * np];
    let v0 = { let mut kb = [0u64; BLK]; s.blk(0, &mut kb); d(kb[0]) };
    // one loop per digit over a block that is in L1, not np updates an element: the shift is a constant of its loop
    ksrc_blocks(s, |_, ks| for (p, c) in cnt.chunks_exact_mut(nb).enumerate() {
        for &k in ks { let x = &mut c[((d(k) >> (p as u32 * dig)) & mask) as usize]; *x = T::of(x.to() + 1) }
    });
    let act: alloc::vec::Vec<usize> = (0..np).filter(|&p| cnt[p * nb + ((v0 >> (p as u32 * dig)) & mask) as usize].to() != n).collect();
    let na = act.len();
    if na == 0 { for (i, o) in out[..n].iter_mut().enumerate() { *o = i as i64 } return }
    let mut jp = (0..na - 1).find(|&j| bits as i32 - act[j + 1] as i32 * dig as i32 + ixb <= 64).unwrap_or(na - 1);
    let ixm = if jp + 1 < na { (((1u64 << (ixb - 1)) << 1)) - 1 } else { jp = na; 0 };
    // Two buffers serve both: a packed word is as wide as the key it replaces.
    let (mut ba, mut bb) = if na >= 2 { (alloc::vec![0u64; n], alloc::vec![0u64; n]) } else { Default::default() };
    let (mut ia, mut ib) = if jp > 0 && na >= 2 { (alloc::vec![T::default(); n], alloc::vec![T::default(); n]) } else { Default::default() };
    let (mut psh, mut packed) = (0u32, false);
    for j in 0..na {
        let sh = (act[j] as u32 * dig - psh) + if packed { ixb as u32 } else { 0 };
        let c = &mut cnt[act[j] * nb..][..nb];
        let mut at = 0;
        for x in c.iter_mut() { let t = x.to(); *x = T::of(at); at += t }
        let slot = |c: &mut [T], v: u64| { let x = &mut c[((v >> sh) & mask) as usize]; let r = x.to(); *x = T::of(r + 1); r };
        if packed {
            if j + 1 == na { for i in 0..n { let w = ba[i]; out[slot(c, w)] = (w & ixm) as i64 } }
            else { for i in 0..n { let w = ba[i]; bb[slot(c, w)] = w } core::mem::swap(&mut ba, &mut bb) }
        } else if j + 1 == na {
            if j > 0 { for i in 0..n { out[slot(c, ba[i])] = ia[i].to() as i64 } }
            else { ksrc_each(s, |i, k| out[slot(c, d(k))] = i as i64) }
        } else if j == jp {
            psh = act[j + 1] as u32 * dig;
            if j > 0 { for i in 0..n { let v = ba[i]; bb[slot(c, v)] = ((v >> psh) << ixb) | ia[i].to() as u64 } }
            else { ksrc_each(s, |i, k| { let v = d(k); bb[slot(c, v)] = ((v >> psh) << ixb) | i as u64 }) }
            core::mem::swap(&mut ba, &mut bb);
            packed = true;
        } else {
            if j > 0 { for i in 0..n { let v = ba[i]; let t = slot(c, v); bb[t] = v; ib[t] = ia[i] } }
            else { ksrc_each(s, |i, k| { let v = d(k); let t = slot(c, v); bb[t] = v; ib[t] = T::of(i) }) }
            core::mem::swap(&mut ba, &mut bb);
            core::mem::swap(&mut ia, &mut ib);
        }
    }
}
/// sort.c:713 `grade_src`: the grade (or ranks) of a key source whose presorted shapes the caller has ruled out, by the
/// key range `mn ..= mx` alone (the caller's: whoever built the keys had them in a register): a counting sort where
/// `sk_countable` says the table is affordable, else the radix. Only the radix's rank needs its grade inverted.
pub fn grade_src(s: &Ksrc, desc: bool, rank: bool, mn: u64, mx: u64, out: &mut [i64]) {
    let (n, span) = (s.n, mx - mn);
    if span == 0 { for (i, o) in out[..n].iter_mut().enumerate() { *o = if rank { 0 } else { i as i64 } } return }
    if span == n as u64 - 1 && grade_perm(s, mn, mx, desc, rank, out) { return }
    if sk_countable(span, n) { return grade_count(s, mn, mx, desc, rank, span, out) }
    let mut g = if rank { alloc::vec![0i64; n] } else { Vec::new() };
    let o = if rank { &mut g[..] } else { &mut *out };
    if desc { grade_radix(s, span, !0, !mx, o) } else { grade_radix(s, span, 0, mn, o) }
    if rank { for (i, &x) in g.iter().enumerate() { out[x as usize] = i as i64 } }
}
/// sort.c:724 `grade_keys`: `grade_src` over keys already made.
pub fn grade_keys(k: &[u64], desc: bool, mn: u64, mx: u64, out: &mut [i64]) {
    if k.is_empty() || grade_runs(k, desc, out) { return }
    grade_src(&Ksrc { kind: key::SK_KEY, p: crate::pod::bytes(k), c: None, n: k.len() }, desc, false, mn, mx, out)
}

// ---- K12: sort.c `hist_find`, `select_keys`, `xr_floor`, `xrank_src` ----
/// sort.c `hist_find`: the bucket rank `*r` falls in, `*r` made relative to that bucket's first element.
pub fn hist_find(cnt: &[usize], r: &mut usize) -> usize {
    let mut b = 0;
    while b + 1 < cnt.len() && *r >= cnt[b] { *r -= cnt[b]; b += 1 }
    b
}
/// What one `select_keys` round settles: the two keys, or the one surviving bucket's keys and the ranks inside it.
enum Round { Done(u64, u64), Next(Vec<u64>, usize, usize) }
/// One round of `select_keys`: histogram the top 16 bits of the range left (the `bits > 16` shift) and keep the buckets
/// the two ranks fall in.
fn select_round(s: &Ksrc, r1: usize, r2: usize) -> Round {
    let (mn, mx) = s.range();
    let span = mx - mn;
    let bits = if span == 0 { 0 } else { 64 - span.leading_zeros() };
    let sh = bits.saturating_sub(16);
    let mut cnt = vec![0usize; (span >> sh) as usize + 1];
    ksrc_each(s, |_, k| cnt[((k - mn) >> sh) as usize] += 1);
    let (mut q1, mut q2) = (r1, r2);
    let (b1, b2) = (hist_find(&cnt, &mut q1), hist_find(&cnt, &mut q2));
    if sh == 0 { return Round::Done(mn + b1 as u64, mn + b2 as u64) }
    // Two buckets mean `r1` is the last of `b1` and `r2 = r1 + 1` the first of `b2`, however many empty ones lie
    // between: keeping `b1 .. b2` instead re-kept the whole range forever on `0N,x`.
    if b1 != b2 {
        let (mut a, mut z) = (0u64, !0u64);
        ksrc_each(s, |_, k| {
            let b = ((k - mn) >> sh) as usize;
            if b == b1 && k > a { a = k }
            if b == b2 && k < z { z = k }
        });
        return Round::Done(a, z);
    }
    let mut next = Vec::with_capacity(cnt[b1]);
    ksrc_each(s, |_, k| if ((k - mn) >> sh) as usize == b1 { next.push(k) });
    Round::Next(next, q1, q1 + (r2 - r1))
}
/// sort.c:`select_keys`: the keys at ranks `r1 <= r2 <= r1 + 1` of `s`, selected and never sorted. One bucket that
/// survives is narrower than the round's range by 16 bits, and the ranks count from its first element.
pub fn select_keys(s: &Ksrc, r1: usize, r2: usize) -> (u64, u64) {
    let mut st = select_round(s, r1, r2);
    loop {
        match st {
            Round::Done(a, b) => return (a, b),
            Round::Next(kept, r1, r2) => st = select_round(&Ksrc { kind: key::SK_KEY, p: pod::bytes(&kept), c: None, n: kept.len() }, r1, r2),
        }
    }
}
/// sort.c `xr_floor`: toward zero and then one down where that rounded up, which is `floor` without libm. The caller
/// guarantees `|v| < 2^53`, so the cast is exact and the comparison is the whole correction.
#[inline(always)]
fn xr_floor(v: f64) -> i64 { let q = v as i64; q - (v < q as f64) as i64 }
/// sort.c `SK_XR_BITS`: 65536 digits over a million elements is fifteen ranks apiece where the keys are uniform.
const SK_XR_HB: usize = 1 << 16;
/// sort.c:`xrank_src`: `_ (<<y) * t` -- `~/q/q.k` line 16's `xrank` -- without the grade. `floor(rank * t)` is constant
/// along a run of ranks and a digit's elements occupy a contiguous run of them, so a digit whose first and last rank
/// floor alike answers with that one number; only the digits a bucket boundary falls inside are graded, as gathered
/// groups, by `grade_keys`, so ties keep the order they came in.
pub fn xrank_src(s: &Ksrc, t: f64, out: &mut [i64]) {
    let (mn, mx) = s.range();
    let span = mx - mn;
    let (mut cur, mut at, mut lut, mut amb) = (vec![0usize; SK_XR_HB], Vec::with_capacity(SK_XR_HB), Vec::with_capacity(SK_XR_HB), Vec::with_capacity(SK_XR_HB));
    let (mut sh, mut run, mut namb, mut wide) = (0, 0usize, 0usize, 0usize);
    while (span >> sh) >= SK_XR_HB as u64 { sh += 1 }
    ksrc_each(s, |_, k| cur[((k - mn) >> sh) as usize] += 1);
    for h in 0..SK_XR_HB {
        let c = cur[h];
        at.push(run);
        if c == 0 { amb.push(false); lut.push(0i64); continue }
        let l = xr_floor(run as f64 * t);
        let a = l != xr_floor((run + c - 1) as f64 * t);
        lut.push(l);
        amb.push(a);
        if a { cur[h] = namb; namb += c; wide = wide.max(c) }
        run += c;
    }
    let (mut gi, mut gk, mut sp) = (vec![0usize; namb], vec![0u64; namb], vec![0i64; wide]);
    ksrc_each(s, |i, k| {
        let d = ((k - mn) >> sh) as usize;
        if amb[d] { gi[cur[d]] = i; gk[cur[d]] = k; cur[d] += 1 } else { out[i] = lut[d] }
    });
    let mut g0 = 0;
    for h in (0..SK_XR_HB).filter(|&h| amb[h]) {
        let c = cur[h] - g0;
        let g = &gk[g0..g0 + c];
        let (smn, smx) = (g.iter().copied().min().unwrap(), g.iter().copied().max().unwrap());
        grade_keys(g, false, smn, smx, &mut sp[..c]);
        for r in 0..c { out[gi[g0 + sp[r] as usize]] = xr_floor((at[h] + r) as f64 * t) }
        g0 = cur[h];
    }
}

// ---- A21: sort.c:734-842 ----
/// The `k` bytes of `p` from `at` as a little-endian word, the rest zero.
fn load(p: &[u8], at: usize, k: usize) -> u64 {
    let mut x = [0u8; 8];
    x[..k].copy_from_slice(&p[at..at + k]);
    u64::from_le_bytes(x)
}
/// sort.c:734 `grade_bits`: a bitmap's grade (zeros then ones, stable), or under `rank` the rank. A boolean column has
/// two keys, so this is two passes over the bitmap and no sort: ascending, every clear index in order and then every
/// set one, `Order.grade`'s body at `.bit` read literally (`iasc 1001b` is `1 2 0 3`, `idesc 1001b` is `0 3 1 2`).
pub fn grade_bits(p: &[u8], n: usize, desc: bool, rank: bool, out: &mut [i64]) {
    // a word at a time: a byte load per element was 66ms of 20M
    if rank {
        // the rank of a bit: ascending, the clear bits before it, or every clear bit and the set ones before it; `desc` puts
        // the set bits first, so a set bit counts the set ones before it and a clear one follows all of them
        let full = n & !63;
        let ones = (0..full / 64).map(|w| load(p, w * 8, 8).count_ones() as usize).sum::<usize>()
            + (full..n).map(|i| (p[i >> 3] >> (i & 7)) as usize & 1).sum::<usize>();
        let (z, mut o) = (n - ones, 0usize);
        for at in (0..n).step_by(64) {
            let nb = (n - at).min(64);
            let mut v = load(p, at >> 3, nb.div_ceil(8));
            for j in 0..nb {
                let b = (v & 1) as usize;
                let (set, clear) = (o, at + j - o);
                out[at + j] = (match (b != 0, desc) { (true, false) => z + set, (false, false) => clear, (true, true) => set, (false, true) => ones + clear }) as i64;
                o += b;
                v >>= 1;
            }
        }
        return;
    }
    // each index found by `ctz` over a 64-bit word, not tested one bit at a time: on a random bitmap the per-bit
    // branch mispredicts every other element, 122ms of 20M against 9 this way
    let mut at = 0;
    for pass in 0..2 {
        for i in 0..n.div_ceil(64) {
            let nb = (n - i * 64).min(64);
            let mut v = load(p, i * 8, nb.div_ceil(8));
            // pass 0 takes the bits equal to `desc`, pass 1 the rest
            if (pass == 0) != desc { v = !v }
            if nb < 64 { v &= !0 >> (64 - nb) }
            while v != 0 {
                out[at] = (i * 64 + v.trailing_zeros() as usize) as i64;
                at += 1;
                v &= v - 1;
            }
        }
    }
}

/// sort.c `SK_NARROW_NB`: the table of a narrow kind, one count per key.
pub fn narrow_nb(kind: u8) -> usize {
    if kind == SK_U8 { 256 } else if kind & SK_LANE != 0 { 1 << (kind & 0x7f) } else { 1 << 16 }
}
/// sort.c `SK_NARROW_RUN`: `f(i, key)` at each row `i` of `[lo, hi)` with its narrow key, unsigned: a byte is its own
/// key, a `short` flips its sign bit (`key_at`'s rule), a lane is the id `id_at` reads, unpacked a chunk at a time.
#[inline(always)]
fn each_key(kind: u8, p: &[u8], lo: usize, hi: usize, mut f: impl FnMut(usize, usize)) {
    if kind == SK_U8 {
        for (i, &x) in p[lo..hi].iter().enumerate() { f(lo + i, x as usize) }
    } else if kind & SK_LANE != 0 {
        let mut kb = [0u16; 1024];
        for c in (lo..hi).step_by(kb.len()) {
            let e = (hi - c).min(kb.len());
            ids::unpack16(p, (kind & 0x7f) as u32, c, e, &mut kb[..e]);
            for (i, &x) in kb[..e].iter().enumerate() { f(c + i, x as usize) }
        }
    } else {
        assert!(kind == SK_I16, "grade_narrow: kind {kind} is not a narrow kind");
        for (i, x) in p[2 * lo..2 * hi].chunks_exact(2).enumerate() { f(lo + i, (u16::from_le_bytes([x[0], x[1]]) ^ 0x8000) as usize) }
    }
}
/// sort.c `narrow_hist_run`: one slice's histogram, per slice and in slice order, with the thread count `run` made.
fn hists(run: Runner, kind: u8, p: &[u8], n: usize) -> (u32, Vec<(usize, Vec<usize>)>) {
    run_slices(run, n, QLEAN_COST_COPY, if kind == SK_I16 { 2 } else { 1 }, &|lo, hi| {
        let mut cnt = vec![0usize; narrow_nb(kind)];
        each_key(kind, p, lo, hi, |_, key| cnt[key] += 1);
        cnt
    })
}
/// sort.c:801 `hist_narrow`: the histogram of a 1- or 2-byte payload, read straight off the payload: its keys number at
/// most 65536, so the table fits in L2 where `keys_of` would write eight bytes for every one it holds.
pub fn hist_narrow(run: Runner, kind: u8, p: &[u8], n: usize) -> Vec<usize> {
    let mut cnt = vec![0usize; narrow_nb(kind)];
    for (_, r) in hists(run, kind, p, n).1 { for (c, x) in cnt.iter_mut().zip(r) { *c += x } }
    cnt
}
/// sort.c:831 `grade_narrow`: the grade of a narrow payload: a histogram per slice, the prefix in the asked-for
/// direction taken bucket-major and slice-minor so slice `k`'s run of a bucket follows slice `k - 1`'s, and one stable
/// scatter per slice. A slice is a contiguous range of rows in row order, so the split keeps the grade stable.
pub fn grade_narrow(run: Runner, kind: u8, p: &[u8], n: usize, desc: bool, rank: bool, out: &mut [i64]) {
    let nb = narrow_nb(kind);
    let (parts, mut rows) = hists(run, kind, p, n);
    let mut at = 0;
    for j in 0..nb {
        let b = if desc { nb - 1 - j } else { j };
        for (_, r) in rows.iter_mut() { let c = r[b]; r[b] = at; at += c }
    }
    let out = pod::atomics(&mut out[..n]);
    let wide = if kind == SK_I16 { 2 } else { 1 };
    // a slice owns its row, copied: the rows stay shared and unchanged, as the C row is the slice's alone
    let again = run_map(run, &mut [], n, 0, QLEAN_COST_COPY, wide, &|lo, hi, _: &mut [u8]| {
        let k = rows.binary_search_by_key(&lo, |r| r.0).unwrap_or_else(|_| panic!("grade_narrow: the scatter split {n} rows differently from the histogram"));
        let mut at = rows[k].1.clone();
        // `at[key]` is the rank: the slot the grade would write `i` into is `i`'s rank, stored in element order
        if rank { each_key(kind, p, lo, hi, |i, key| { out[i].store(at[key] as i64, Relaxed); at[key] += 1 }) }
        else { each_key(kind, p, lo, hi, |i, key| { out[at[key]].store(i as i64, Relaxed); at[key] += 1 }) }
    });
    assert!(again == parts, "grade_narrow: the scatter split {n} rows differently from the histogram");
}

#[cfg(test)]
mod a21_tests {
    use super::*;
    use crate::c::qlean_run_c;
    fn bits(p: u8, n: usize, desc: bool, rank: bool) -> Vec<i64> { let mut o = vec![0; n]; grade_bits(&[p], n, desc, rank, &mut o); o }
    fn narrow(kind: u8, p: &[u8], n: usize, desc: bool, rank: bool) -> Vec<i64> {
        let mut o = vec![0; n];
        grade_narrow(qlean_run_c, kind, p, n, desc, rank, &mut o);
        o
    }
    // the examples sort.c's comment gives: `iasc 1001b` is `1 2 0 3`, `idesc 1001b` is `0 3 1 2`
    #[test] fn bits_grade_is_zeros_then_ones() {
        assert_eq!(bits(0b1001, 4, false, false), [1, 2, 0, 3]);
        assert_eq!(bits(0b1001, 4, true, false), [0, 3, 1, 2]);
    }
    // bits past `n` in the last byte are not elements; the rank is where the grade would put each row
    #[test] fn bits_rank_ignores_bits_past_n() {
        assert_eq!(bits(0b1111_1001, 4, false, true), [2, 0, 1, 3]);
    }
    // the rank is the grade's inverse in both directions, across word boundaries and a ragged tail
    #[test] fn bits_rank_inverts_the_grade_both_ways() {
        assert_eq!(bits(0b1001, 4, false, true), [2, 0, 1, 3]);
        assert_eq!(bits(0b1001, 4, true, true), [0, 2, 3, 1]);
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        for n in [1usize, 63, 64, 65, 130, 200] {
            let p: Vec<u8> = (0..n.div_ceil(8)).map(|_| { s ^= s << 13; s ^= s >> 7; s ^= s << 17; (s >> 24) as u8 }).collect();
            for desc in [false, true] {
                let (mut g, mut r) = (vec![0; n], vec![0; n]);
                grade_bits(&p, n, desc, false, &mut g);
                grade_bits(&p, n, desc, true, &mut r);
                for (t, &i) in g.iter().enumerate() { assert_eq!(r[i as usize], t as i64, "n {n} desc {desc} row {i}") }
            }
        }
    }
    #[test] fn u8_is_stable_on_ties() {
        let p = [3, 1, 3, 0, 1];
        assert_eq!(narrow(SK_U8, &p, 5, false, false), [3, 1, 4, 0, 2]);
        assert_eq!(narrow(SK_U8, &p, 5, true, false), [0, 2, 1, 4, 3]);
        assert_eq!(narrow(SK_U8, &p, 5, false, true), [3, 1, 4, 0, 2]);
    }
    // a `short` flips its sign bit: -32768 is the least key, -1 comes before 5
    #[test] fn i16_orders_by_sign() {
        let p: Vec<u8> = [-1i16, 5, i16::MIN, 5].iter().flat_map(|x| x.to_le_bytes()).collect();
        assert_eq!(narrow(SK_I16, &p, 4, false, false), [2, 0, 1, 3]);
        assert_eq!(hist_narrow(qlean_run_c, SK_I16, &p, 4).iter().sum::<usize>(), 4);
    }
    // a 4-bit lane: ids 2, 0, 2, 1 packed low nibble first
    #[test] fn lane_reads_ids() {
        assert_eq!(narrow(SK_LANE | 4, &[0x02, 0x12], 4, false, false), [1, 3, 0, 2]);
    }
    #[test] fn empty_and_one() {
        assert_eq!(narrow(SK_U8, &[], 0, false, false), Vec::<i64>::new());
        assert_eq!(narrow(SK_U8, &[9], 1, true, true), [0]);
    }
    // three slices (the test runner's cut): the stable prefix runs across slice boundaries
    #[test] fn slices_keep_the_grade_stable() {
        let p: Vec<u8> = (0..1000u32).map(|i| (i * 7 % 3) as u8).collect();
        let g = narrow(SK_U8, &p, 1000, false, false);
        assert!(g.windows(2).all(|w| (p[w[0] as usize], w[0]) < (p[w[1] as usize], w[1])));
    }
}

// ---- A22: sort.c:887-1120 ----
/// sort.c:941 `sk_ends`: a block's first and last key and whether it is ordered inside.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Ends { pub fst: i64, pub lst: i64, pub ok: bool }

/// coc.h:353 `sk_avail`: how many elements `bytes` hold (the bit payload answers before the width is consulted).
fn avail(kind: u8, bytes: usize) -> usize {
    if kind == SK_BIT { bytes * 8 } else { bytes / key::bytes(kind, 1).unwrap_or_else(|| panic!("qlean: element kind {kind} has no dense width")) }
}

/// sort.c:880 `SK_ASC_DIR`: no key is carried between elements, so a chunk's violations accumulate and the early exit
/// is taken at the chunk. `bad(a, b)` is the failing comparison of two adjacent keys, a closure so each of the four
/// directions is its own loop.
#[inline(always)]
fn ordered<K: Keys>(k: &mut K, m: usize, bad: impl Fn(u64, u64) -> bool) -> bool {
    const CHUNK: usize = 512;
    let mut lo = 1;
    while lo < m {
        let hi = (lo + CHUNK).min(m);
        let mut x = false;
        for i in lo..hi { x |= bad(k.at(i - 1), k.at(i)) }
        if x { return false }
        lo = hi;
    }
    true
}
/// sort.c:894 `SK_ASC`: `strict` moves the failing comparison from `>` to `>=` (a repeat breaks a strict order).
struct Asc { desc: bool, strict: bool }
impl Pass for Asc {
    type Out = bool;
    #[inline(always)]
    fn run<K: Keys>(self, mut k: K, m: usize) -> bool {
        match (self.desc, self.strict) {
            (true, true) => ordered(&mut k, m, |a, b| a <= b),
            (true, false) => ordered(&mut k, m, |a, b| a < b),
            (false, true) => ordered(&mut k, m, |a, b| a >= b),
            (false, false) => ordered(&mut k, m, |a, b| a > b),
        }
    }
}
/// sort.c:894 `qlean_sort_ascending` past the unboxing; `n` is clamped to what `p` holds.
pub fn ascending(kind: u8, desc: bool, strict: bool, p: &[u8], n: usize) -> bool {
    let m = avail(kind, p.len()).min(n);
    if m < 2 { return true }
    let b = key::bytes(kind, m).unwrap_or_else(|| panic!("qlean_sort_ascending: kind {kind} is not a dense kind"));
    key::each(kind, &p[..b], m, Asc { desc, strict })
        .unwrap_or_else(|| panic!("qlean_sort_ascending: the {}-byte payload of kind {kind} is misaligned", p.len()))
}

/// sort.c:941 `asc_blk_foR`: block `b`'s own order and its ends, read off the residuals without decoding. A block's
/// base is the same for all of it and the encoder biases a key into unsigned order before subtracting it, so the
/// residuals ascend exactly when the elements do. `ok` false = out of order (the ends are then 0).
pub fn asc_blk(c: &Coc, b: usize, desc: bool, strict: bool) -> Ends {
    /// the walk of `cnt` residuals through `rd`, a closure of the index so the width switch stays out of the loop
    fn walk(cnt: usize, desc: bool, strict: bool, rd: impl Fn(usize) -> u64) -> Option<(u64, u64)> {
        let bad = (1..cnt).fold(false, |x, j| x | match (desc, strict) {
            (true, true) => rd(j - 1) <= rd(j), (true, false) => rd(j - 1) < rd(j),
            (false, true) => rd(j - 1) >= rd(j), (false, false) => rd(j - 1) > rd(j),
        });
        if bad { None } else { Some((rd(0), rd(cnt - 1))) }
    }
    let cnt = (c.meta.n - b * BLK).min(BLK);
    // a patched block is decoded and re-biased: residuals compare unsigned, so `v ^ sign` over a base of INT64_MIN
    // keeps signed order, and `base + r` is `v` again
    let (base, r) = if c.blk_nexc(b) > 0 {
        let mut dec = [0i64; BLK];
        c.decode_blk(b, cnt, &mut dec);
        (1u64 << 63, walk(cnt, desc, strict, |j| dec[j] as u64 ^ (1 << 63)))
    } else {
        let at = c.meta.off[b] as usize;
        let mut w = c.meta.width[b];
        let mut lb = [0u64; BLK];
        let p = lanes(&c.pack[at..at + BLK * w as usize / 8], &mut w, cnt, pod::bytes_mut(&mut lb));
        let r = match w {
            // a zero-width block is its base repeated, which is not a strict order past one element
            0 => if strict && cnt > 1 { None } else { Some((0, 0)) },
            8 => walk(cnt, desc, strict, |j| p[j] as u64),
            16 => walk(cnt, desc, strict, |j| u16::from_ne_bytes([p[2 * j], p[2 * j + 1]]) as u64),
            32 => walk(cnt, desc, strict, |j| u32::from_ne_bytes(p[4 * j..4 * j + 4].try_into().unwrap()) as u64),
            64 => walk(cnt, desc, strict, |j| u64::from_ne_bytes(p[8 * j..8 * j + 8].try_into().unwrap())),
            // widths 1, 2, 4 stay packed: a shift inside one byte
            _ => walk(cnt, desc, strict, |j| ((p[j * w as usize >> 3] >> (j * w as usize & 7)) & ((1u8 << w) - 1)) as u64),
        };
        (c.frame(b), r)
    };
    match r {
        Some((r0, rl)) => Ends { fst: base.wrapping_add(r0) as i64, lst: base.wrapping_add(rl) as i64, ok: true },
        None => Ends { fst: 0, lst: 0, ok: false },
    }
}
/// sort.c:977 `qlean_sort_ascending_foR` past the unboxing, threaded (`asc_run`). The blocks are checked apart, by
/// block across the pool, and the pairs between them afterwards from their ends; the first block goes alone and first,
/// so a column that is not sorted still leaves inside it. `kind` is one of `SK_I16`, `SK_I32`, `SK_I64`.
pub fn ascending_enc(run: Runner, kind: u8, desc: bool, strict: bool, c: &Coc) -> bool {
    debug_assert!(matches!(kind, SK_I16 | SK_I32 | SK_I64));
    let nb = c.meta.nblk;
    if c.meta.n == 0 { return true }
    let f = asc_blk(c, 0, desc, strict);
    if !f.ok || nb == 1 { return f.ok }
    // block `b >= 1` lands at words `3(b-1)..3b` as (fst, lst, ok); `ok` is written last, so a block a worker never
    // reached (it stops at its first block out of order) reads as out of order
    let mut e = vec![0u64; 3 * (nb - 1)];
    let rest = c.blocks(1, nb);
    run_map(run, pod::bytes_mut(&mut e), nb - 1, 24, QLEAN_COST_ARITH, BLK * 8, &|lo, hi, o: &mut [u8]| {
        let o = pod::cast_mut::<u64>(o).expect("ascending_enc: the block ends are misaligned");
        for (k, b) in (lo..hi).enumerate() {
            let r = asc_blk(&rest, b, desc, strict);
            if !r.ok { return }
            o[3 * k] = r.fst as u64; o[3 * k + 1] = r.lst as u64; o[3 * k + 2] = 1;
        }
    });
    // between each pair of neighbours: the last of one against the first of the next
    let ends = |b: usize| if b == 0 { (f.fst, f.lst, true) } else { (e[3 * b - 3] as i64, e[3 * b - 2] as i64, e[3 * b - 1] != 0) };
    (1..nb).all(|b| {
        let ((_, pl, _), (nf, _, ok)) = (ends(b - 1), ends(b));
        let bad = match (desc, strict) { (true, true) => pl <= nf, (true, false) => pl < nf, (false, true) => nf <= pl, (false, false) => nf < pl };
        ok && !bad
    })
}
/// sort.c:1012 `qlean_sort_invert`: the inverse permutation. The scatter runs from the top so that a repeated entry
/// keeps its first position, which only a payload that is not a permutation has; a grade always is one.
pub fn invert(p: &[i64], out: &mut [i64]) {
    let m = p.len();
    out[..m].fill(m as i64);
    for j in (0..m).rev() { if (p[j] as u64) < m as u64 { out[p[j] as usize] = j as i64 } }
}
/// sort.c:1025 `order_runs`: the grade of an already ordered column (`asc`), or reversed (`desc_strict`); both are
/// involutions, so they are their own rank as well.
pub fn order_runs(asc: bool, desc_strict: bool, out: &mut [i64]) -> bool {
    let n = out.len();
    if asc { out.iter_mut().enumerate().for_each(|(i, o)| *o = i as i64); true }
    else if desc_strict { out.iter_mut().enumerate().for_each(|(i, o)| *o = (n - 1 - i) as i64); true }
    else { false }
}
/// sort.c:1034 `order_dense` past the allocation: grade or ranks of a dense payload, `n` already clamped to what `p`
/// holds. A wide payload is never copied into a key array: its range is one read of it and every engine reads the
/// keys straight off it.
pub fn order(run: Runner, kind: u8, desc: bool, rank: bool, p: &[u8], n: usize, out: &mut [i64]) {
    if n == 0 { return }
    let p = &p[..key::bytes(kind, n).unwrap_or_else(|| panic!("qlean_sort_grade: kind {kind} is not a dense kind"))];
    if kind == SK_BIT { return grade_bits(p, n, desc, rank, out) }
    if kind == SK_U8 || kind == SK_I16 { return grade_narrow(run, kind, p, n, desc, rank, out) }
    let a = ascending(kind, desc, false, p, n);
    if !order_runs(a, !a && ascending(kind, !desc, true, p, n), out) {
        let s = Ksrc { kind, p, c: None, n };
        let (mn, mx) = s.range();
        grade_src(&s, desc, rank, mn, mx, out)
    }
}
/// sort.c:1068 `order_foR` past the allocation: `order` off the pack. The range is the block metadata's, so the only
/// passes over the residuals are the ones the chosen engine makes, each decoding a block at a time into L1.
pub fn order_enc(run: Runner, kind: u8, desc: bool, rank: bool, c: &Coc, out: &mut [i64]) {
    if c.meta.n == 0 { return }
    let a = ascending_enc(run, kind, desc, false, c);
    if !order_runs(a, !a && ascending_enc(run, kind, !desc, true, c), out) {
        let s = Ksrc { kind, p: &[], c: Some(*c), n: c.meta.n };
        let (mn, mx) = s.range();
        grade_src(&s, desc, rank, mn, mx, out)
    }
}
/// sort.c:1093 `qlean_sort_grade_lane` past the unboxing: the grade of `n` ids at `w` bits, `n` already clamped to
/// what `ids` holds. Up to sixteen bits it is `grade_narrow`'s counting sort at the lane, a `2^w` table and nothing
/// widened; at width zero every key is `0` and the stable answer is `til n`. Past sixteen bits the table is not
/// affordable and the ids become `grade_keys`' unsigned keys.
pub fn grade_lane(run: Runner, desc: bool, w: u32, ids: &[u8], n: usize, out: &mut [i64]) {
    if n == 0 { return }
    if w == 0 { out.iter_mut().enumerate().for_each(|(i, o)| *o = i as i64) }
    else if w == 1 { grade_bits(ids, n, desc, false, out) } // a one-bit lane is `.bit`'s layout
    else if w <= 16 { grade_narrow(run, SK_LANE | w as u8, ids, n, desc, false, out) }
    else {
        let mut k = vec![0u64; n];
        let (mn, mx) = ids_keys(ids, w, n, &mut k); // needs A23
        grade_keys(&k, desc, mn, mx, out)
    }
}

#[cfg(test)]
mod tests_a22 {
    use super::*;
    use crate::c::qlean_run_c;
    use crate::key::SK_F64;
    fn le<T: crate::pod::Pod>(v: &[T]) -> alloc::vec::Vec<u8> { pod::bytes(v).to_vec() }
    // the cases of /data/tmp/qrs/A22/diff.c's `edge`, whose C answers (14bdbcd) these are
    #[test] fn ascending_ties_strict_desc() {
        let p = le(&[1i64, 2, 2, 5]);
        assert!(ascending(SK_I64, false, false, &p, 4));
        assert!(!ascending(SK_I64, false, true, &p, 4), "a repeat breaks a strict order");
        assert!(!ascending(SK_I64, true, false, &p, 4));
        assert!(ascending(SK_I64, true, false, &le(&[5i64, 2, 2, 1]), 4));
        assert!(ascending(SK_I64, true, true, &le(&[5i64, 3, 2, 1]), 4));
        assert!(ascending(SK_I16, false, false, &le(&[-5i16, 3]), 2), "the sign bit is flipped into key order");
        assert!(ascending(SK_I64, false, false, &p, 1) && ascending(SK_I64, false, true, &p, 0), "under two elements");
        assert!(ascending(SK_I64, false, false, &p, 9), "n clamps to what the payload holds");
        assert!(ascending(SK_BIT, false, false, &[0b1100_0000u8], 8) && !ascending(SK_BIT, false, false, &[0b0000_0010u8], 8));
    }
    #[test] fn ascending_floats_nan_first() {
        // NaN's key is 0, below every number
        assert!(ascending(SK_F64, false, true, &le(&[f64::NAN, -1.0, 0.0, f64::INFINITY]), 4));
        assert!(!ascending(SK_F64, false, false, &le(&[1.0f64, f64::NAN]), 2));
    }
    #[test] fn invert_first_position_and_m_where_none() {
        let mut o = [9i64; 4];
        invert(&[2, 0, 2, 7], &mut o);
        assert_eq!(o, [1, 4, 0, 4]);
        invert(&[], &mut []);
    }
    #[test] fn order_runs_shapes() {
        let mut o = [9i64; 3];
        assert!(order_runs(true, true, &mut o) && o == [0, 1, 2]);
        assert!(order_runs(false, true, &mut o) && o == [2, 1, 0]);
        o = [9; 3];
        assert!(!order_runs(false, false, &mut o) && o == [9; 3]);
    }
    #[test] fn order_sorted_and_reversed_i64_skip_the_engine() {
        let mut o = [0i64; 4];
        order(qlean_run_c, SK_I64, false, false, &le(&[1i64, 2, 2, 5]), 4, &mut o);
        assert_eq!(o, [0, 1, 2, 3]);
        order(qlean_run_c, SK_I64, false, true, &le(&[9i64, 5, 2, 1]), 4, &mut o);
        assert_eq!(o, [3, 2, 1, 0], "strictly descending: til n reversed, its own rank");
        order(qlean_run_c, SK_I64, true, false, &le(&[5i64, 2, 2, 1]), 4, &mut o);
        assert_eq!(o, [0, 1, 2, 3]);
    }
    #[test] fn grade_lane_zero_width_is_til() {
        let mut o = [9i64; 5];
        grade_lane(qlean_run_c, false, 0, &[], 5, &mut o);
        assert_eq!(o, [0, 1, 2, 3, 4]);
    }
}

// ---- A23: sort.c:1631, 2293-2400, 3386 ----
/// sort.c:1631 `group_bound`: `group`'s scratch numbers groups and counts buckets in `u32`, so a column past that many
/// rows cannot be cut this way; the row count is the one bound, and the message names it instead of an allocation failing.
pub fn group_bound(n: usize) {
    if n > u32::MAX as usize { panic!("qlean: group cuts at most {} rows into buckets, not {n}", u32::MAX) }
}
/// sort.c:2293 `pair_fits`: two spans pack into one 64-bit key.
pub fn pair_fits(sx: u64, sy: u64) -> bool {
    // a whole-range side first: `2^64 * 2^64` wraps to 0 in a 128-bit product
    if sx == u64::MAX || sy == u64::MAX { return sx == 0 || sy == 0 }
    (sx as u128 + 1) * (sy as u128 + 1) <= 1u128 << 64
}
/// sort.c:2301 `pair_narrow`: keys `k` replaced by their group ids, which are equal exactly where the keys are and span
/// less than `k.len()`; answers `(mn, span)` = `(0, ng - 1)`. The numbering is serial (no `run` in this signature, and
/// the path is only for pairs whose spans do not fit 64 bits) and keeps its table; `first` is scratch of `k.len()`. The range given to the numbering is `k`'s own: it only decides direct against hashed.
pub fn pair_narrow(k: &mut [u64], first: &mut [usize]) -> (u64, u64) {
    let (mn, mx) = keys_range(k);
    let m = k.len();
    let (ng, t) = crate::group::number(crate::key::SK_KEY, crate::pod::bytes_mut(k), m, mn, mx, first)
        .expect("qlean: pair_narrow: number refused SK_KEY keys");
    for e in k.iter_mut() { *e = t.at(*e) as u64 }
    (0, ng.saturating_sub(1) as u64)
}
/// sort.c:2314 `pair_ids` past the allocation: the group id of each pair `(x[i], y[i])` into `gid` at
/// `max(8, id_width(ng))` bits, the first index of each group into `first`; answers `ng`.
/// The pair is made one injective key, `(x - mnx) * (sy + 1) + (y - mny)`; a pair whose spans do not fit 64 bits has
/// its wider side, then the other, narrowed to its group ids first, which leaves at most `m * m` codes.
pub fn pair_ids(run: Runner, x: &mut [u64], y: &mut [u64], mnx: u64, sx: u64, mny: u64, sy: u64, gid: &mut [u8],
                first: &mut [usize]) -> usize {
    let m = x.len();
    let (mut mnx, mut sx, mut mny, mut sy) = (mnx, sx, mny, sy);
    // `first` is the numbering's scratch here and the answer's once the key is built
    for _ in 0..2 {
        if pair_fits(sx, sy) { break }
        if sx >= sy { (mnx, sx) = pair_narrow(x, first) } else { (mny, sy) = pair_narrow(y, first) }
    }
    if !pair_fits(sx, sy) {
        panic!("qlean sort: groupIdsPair over {m} rows: {} x {} codes do not fit one 64-bit key", sx.wrapping_add(1), sy.wrapping_add(1))
    }
    // the combined key goes back into `x`, which C owns and frees; `sy + 1` wraps to 0 only where `sy` is the whole
    // range, and `pair_fits` then has `sx` at 0
    // the range taken in the same pass, as sort.c does: `keys_range` after it was a second read of `x`
    let (mut lo, mut hi) = (u64::MAX, 0u64);
    for (a, &b) in x.iter_mut().zip(y.iter()) {
        let c = a.wrapping_sub(mnx).wrapping_mul(sy.wrapping_add(1)).wrapping_add(b.wrapping_sub(mny));
        (*a, lo, hi) = (c, lo.min(c), hi.max(c));
    }
    crate::group::group_ids(run, crate::key::SK_KEY, crate::pod::bytes_mut(x), m, lo, hi, gid, first)
        .expect("qlean: pair_ids: group_ids refused SK_KEY keys")
}
/// sort.c:2366 `ids_keys`: `m` ids at `w` bits as keys; answers `(min, max)`.
/// Below a byte the range is the lane's own, `0 .. 2^w - 1`: `pair_ids` needs only a bound there.
pub fn ids_keys(v: &[u8], w: u32, m: usize, k: &mut [u64]) -> (u64, u64) {
    if m == 0 { return (0, 0) }
    by_width!(w, keys_at(v, &mut k[..m]))
}
// `ids_keys` at the constant width `W`; from a byte up the range is taken in the unpacking pass, as sort.c's `KEY_PUT`.
fn keys_at<const W: u32>(v: &[u8], k: &mut [u64]) -> (u64, u64) {
    if W < 8 {
        crate::ids::unpack::<W, u64>(v, k, |_, e, x| *e = x as u64);
        return (0, (1u64 << W) - 1)
    }
    let (mut lo, mut hi) = (u64::MAX, 0u64);
    crate::ids::unpack::<W, u64>(v, k, |_, e, x| { *e = x as u64; (lo, hi) = (lo.min(x as u64), hi.max(x as u64)) });
    (lo, hi)
}
/// sort.c:3386 `pair_ids_narrow` past the allocation: as `pair_ids` for two id payloads that fit a byte together
/// (`wa + wb <= 8`): the code `a << wb | b` at its own lane `id_width(2^(wa+wb))`, numbered by `ids::firsts`, and the
/// ids written by `ids::map` at exactly `id_width(ng)` bits (`ids_bytes(m, id_width(ng))` bytes of `gid`, packed).
pub fn pair_ids_narrow(run: Runner, wa: u32, wb: u32, m: usize, pa: &[u8], pb: &[u8], gid: &mut [u8], first: &mut [usize])
    -> usize {
    use crate::ids::{firsts, id_at, id_width, ids_bytes, map, pack};
    // both lanes constant, as sort.c's nested `IDS_WIDTHS`, and the code packed a word at a time (`IDS_PACK`)
    fn code<const WA: u32, const WB: u32>(c: &mut [u8], wc: u32, m: usize, pa: &[u8], pb: &[u8]) {
        pack(c, wc, m, |i| (id_at(pa, WA, i) << WB | id_at(pb, WB, i)) as u64)
    }
    fn code_a<const WA: u32>(wb: u32, c: &mut [u8], wc: u32, m: usize, pa: &[u8], pb: &[u8]) {
        match wb { 0 => code::<WA, 0>(c, wc, m, pa, pb), 1 => code::<WA, 1>(c, wc, m, pa, pb), 2 => code::<WA, 2>(c, wc, m, pa, pb),
                   4 => code::<WA, 4>(c, wc, m, pa, pb), _ => code::<WA, 8>(c, wc, m, pa, pb) }
    }
    let wc = id_width(1 << (wa + wb));
    let nd = 1usize << wc;
    let mut c = alloc::vec![0u8; ids_bytes(m, wc)];
    match wa { 0 => code_a::<0>(wb, &mut c, wc, m, pa, pb), 1 => code_a::<1>(wb, &mut c, wc, m, pa, pb),
               2 => code_a::<2>(wb, &mut c, wc, m, pa, pb), 4 => code_a::<4>(wb, &mut c, wc, m, pa, pb),
               _ => code_a::<8>(wb, &mut c, wc, m, pa, pb) }
    let mut slot = alloc::vec![usize::MAX; nd + 1];
    let ng = firsts(&c, m, wc, nd, &mut slot, first);
    map(run, &c, m, wc, nd, &slot, id_width(ng), gid);
    ng
}

// ---- A24: sort.c:2475-2550 ----
/// Element `k` of `rank_slices`' payload at the pass's width `W` (65 = an odd width, read at the runtime `w`): a
/// whole-byte lane is one load, a sub-byte lane one byte load (it never straddles a byte), any other `res_get_in`.
fn rs_elem<const W: u32>(v: &[u8], w: u32, end: usize, k: usize) -> u64 {
    match W {
        0 => 0,
        8 => v[k] as u64,
        16 => u16::from_le_bytes(v[2 * k..2 * k + 2].try_into().unwrap()) as u64,
        32 => u32::from_le_bytes(v[4 * k..4 * k + 4].try_into().unwrap()) as u64,
        64 => u64::from_le_bytes(v[8 * k..8 * k + 8].try_into().unwrap()),
        1 | 2 | 4 => ((v[k * W as usize >> 3] >> (k * W as usize & 7)) & ((1u32 << W) - 1) as u8) as u64,
        _ => crate::res::res_get_in(v, w as u8, k, end),
    }
}
/// The hashed pass at one width: `groupIds`' hashed numbering with each segment's hash as the key and a compare of
/// the elements only where two hashes agree. The length seeds the hash, so runs of one value at different lengths
/// do not collide.
fn rs_pass<const W: u32>(w: u32, v: &[u8], o: &[i64], out: &mut [i64]) {
    let g = out.len();
    let (cap, end) = (crate::group::cap_for(g), v.len());
    let (mask, sh) = (cap - 1, 64 - cap.trailing_zeros());
    let (mut slot, mut gkey, mut rep) = (vec![0usize; cap], vec![0u64; g], vec![0usize; g]);
    let el = |k: usize| rs_elem::<W>(v, w, end, k);
    let mut ng = 0;
    for j in 0..g {
        let (a, len) = (o[j] as usize, (o[j + 1] - o[j]) as usize);
        let mut h = (len as u64).wrapping_mul(crate::group::PHI64);
        // a lane width reads the segment's own slice through `ids::each`: one bounds test a segment, not one an element
        if matches!(W, 1 | 2 | 4 | 8 | 16 | 32 | 64) && (a * W as usize) % 8 == 0 {
            let sub = &v[a * W as usize / 8..((a + len) * W as usize).div_ceil(8)];
            crate::ids::each::<W>(sub, len, |_, x| h = (h ^ x as u64).wrapping_mul(0xc2b2ae3d27d4eb4f));
        } else { for k in a..a + len { h = (h ^ el(k)).wrapping_mul(0xc2b2ae3d27d4eb4f) } }
        let key = h ^ (h >> 29);
        let same = |r: usize| {
            let b = o[r] as usize;
            if (o[r + 1] - o[r]) as usize != len { return false }
            // at a whole-byte width both segments start on a byte, so their bytes are their elements
            if matches!(W, 8 | 16 | 32 | 64) { let by = W as usize / 8; v[a * by..(a + len) * by] == v[b * by..(b + len) * by] }
            else { (0..len).all(|t| el(a + t) == el(b + t)) }
        };
        let mut s = (key.wrapping_mul(crate::group::PHI64) >> sh) as usize;
        while slot[s] != 0 && (gkey[slot[s] - 1] != key || !same(rep[slot[s] - 1])) { s = (s + 1) & mask }
        if slot[s] == 0 { ng += 1; slot[s] = ng; gkey[ng - 1] = key; rep[ng - 1] = j }
        out[j] = (slot[s] - 1) as i64;
    }
}
/// sort.c `qlean_sort_rank_slices` past the unboxing and the validation (`w` at most 64, `o` ascending inside `v`):
/// each of `o`'s `out.len()` segments of `v`'s `w`-bit elements numbered by first occurrence, segments equal as
/// sequences.
pub fn rank_slices(w: usize, v: &[u8], o: &[i64], out: &mut [i64]) {
    let w = w as u32;
    match w {
        0 => rs_pass::<0>(w, v, o, out), 1 => rs_pass::<1>(w, v, o, out), 2 => rs_pass::<2>(w, v, o, out),
        4 => rs_pass::<4>(w, v, o, out), 8 => rs_pass::<8>(w, v, o, out), 16 => rs_pass::<16>(w, v, o, out),
        32 => rs_pass::<32>(w, v, o, out), 64 => rs_pass::<64>(w, v, o, out), _ => rs_pass::<65>(w, v, o, out),
    }
}
fn sizes<const W: u32>(ng: usize, n: usize, ids: &[u8], out: &mut [i64]) {
    let out = &mut out[..ng];
    out.fill(0);
    // `out` is `ng` long, so `get_mut` is the `v < ng` test and the store's bounds test in one
    crate::ids::each::<W>(ids, n, |_, v| if let Some(o) = out.get_mut(v) { *o += 1 });
}
/// sort.c `qlean_sort_group_sizes`: the size of each of `ng` groups of the ids `gid` (`n` at `w` bits), `n` already
/// clamped to what `gid` holds.
pub fn group_sizes(ng: usize, w: u32, n: usize, gid: &[u8], out: &mut [i64]) { by_width!(w, sizes(ng, n, gid, out)) }
fn lasts<const W: u32>(ng: usize, n: usize, ids: &[u8], out: &mut [i64]) {
    let out = &mut out[..ng];
    out.fill(0);
    crate::ids::each::<W>(ids, n, |i, v| if let Some(o) = out.get_mut(v) { *o = i as i64 });
}
/// sort.c `qlean_sort_group_lasts`: each group's last index, 0 for one no row names.
pub fn group_lasts(ng: usize, w: u32, n: usize, gid: &[u8], out: &mut [i64]) { by_width!(w, lasts(ng, n, gid, out)) }
fn longs<const W: u32>(n: usize, ids: &[u8], out: &mut [i64]) {
    let out = &mut out[..n];
    crate::ids::unpack::<W, i64>(ids, out, |_, e, v| *e = v as i64);
}
/// sort.c `qlean_sort_id_longs`: the first `n` ids at `w` bits as longs.
pub fn id_longs(n: usize, w: u32, ids: &[u8], out: &mut [i64]) { by_width!(w, longs(n, ids, out)) }

// ---- A25: sort.c:2814-2990 ----
/// sort.c:2884 `symgroups`: the distinct symbols' keys, first indices, group ids and counts.
/// `dk` is empty exactly when a symbol did not pack; `gid`, `cnt` are empty unless `want` asked for them.
pub struct SymGroups { pub dk: Vec<u64>, pub first: Vec<usize>, pub ng: usize, pub gid: Vec<u32>, pub cnt: Vec<u32> }
/// sym.h:153 `SYM_KEY_BLOCK`: a block is checked, then packed while it is in cache.
const SYM_KEY_BLOCK: usize = 4096;
/// sort.c:2829 `sym_dedup`: group ids and counts of the sorted symbols `v`; answers the group count.
/// An empty `gid` (or `cnt`) is C's NULL.
pub fn sym_dedup(v: &[&[u8]], gid: &mut [u32], cnt: &mut [u32], first: &mut [usize]) -> usize {
    let n = v.len();
    if n == 0 { return 0 }
    let (cap, mut ng) = (crate::group::cap_for(n), 0);
    let mut tab = alloc::vec![0usize; cap];
    for i in 0..n {
        let mut s = (sym_hash(v[i]) as usize) & (cap - 1);
        while tab[s] != 0 && !crate::sym::sym_eq(v[first[tab[s] - 1]], v[i]) { s = (s + 1) & (cap - 1) }
        if tab[s] == 0 { ng += 1; tab[s] = ng; first[ng - 1] = i; if !cnt.is_empty() { cnt[ng - 1] = 0 } }
        if !gid.is_empty() { gid[i] = (tab[s] - 1) as u32; if !cnt.is_empty() { cnt[tab[s] - 1] += 1 } }
    }
    ng
}
/// sort.c:2848 `sym_heads`: each group's first symbol.
pub fn sym_heads<'a>(s: &Syms<'a>, first: &[usize]) -> Vec<&'a [u8]> { first.iter().map(|&i| s.at(i)).collect() }
/// sort.c:2886 `sym_group`: `want` says which fields are filled (C's bit flags: 0 firsts, 1 gids, 2 gids and counts).
pub fn sym_group(s: &Syms, n: usize, want: i32) -> SymGroups {
    if want != 0 { group_bound(n) }
    // pushed in order, never zero-filled: only the first `ng` of `first`/`dk`/`cnt` are written, and a zeroed `n`-long vector is
    // 8 MB of memset once malloc has stopped handing out fresh mmap pages (C's xalloc does not zero)
    let mut gid = Vec::with_capacity(if want != 0 { n } else { 0 });
    let (mut cnt, mut first, mut dk) = (Vec::with_capacity(if want == 2 { n } else { 0 }), Vec::with_capacity(n), Vec::with_capacity(n));
    let cap = crate::group::cap_for(n);
    let (sh, mut tab, mut packed) = (64 - cap.trailing_zeros(), alloc::vec![0usize; cap], true);
    for at in (0..n).step_by(SYM_KEY_BLOCK) {
        let blk = (n - at).min(SYM_KEY_BLOCK);
        let b = Syms { blob: s.blob, offs: &s.offs[at..] };
        if !b.packs(blk) { packed = false; break }
        // `packs` saw every tag bit of the block set, so the starts unbox without a test; `lo` is carried, as C's loop does
        let mut lo = s.offs[at] >> 1;
        for i in at..at + blk {
            let hi = s.offs[i + 1] >> 1;
            let key = s.key_of(lo, hi);
            lo = hi;
            let mut t = (key.wrapping_mul(crate::group::PHI64) >> sh) as usize;
            while tab[t] != 0 && dk[tab[t] - 1] != key { t = (t + 1) & (cap - 1) }
            if tab[t] == 0 { dk.push(key); tab[t] = dk.len(); first.push(i); if want == 2 { cnt.push(0) } }
            let g = tab[t] - 1;
            if want != 0 { gid.push(g as u32); if want == 2 { cnt[g] += 1 } }
        }
    }
    let ng = if packed { dk.len() } else {
        dk = Vec::new();
        (gid, cnt, first) = (alloc::vec![0; if want != 0 { n } else { 0 }], alloc::vec![0; if want == 2 { n } else { 0 }], alloc::vec![0; n]);
        sym_dedup(&s.slices(n), &mut gid, &mut cnt, &mut first)
    };
    first.truncate(ng);
    cnt.truncate(ng);
    SymGroups { dk, first, ng, gid, cnt }
}
/// sort.c:2934 `sym_ranks`: each symbol's rank in q's symbol order.
pub fn sym_ranks(s: &Syms, n: usize) -> Vec<u64> {
    let g = sym_group(s, n, 1);
    let mut ord: Vec<usize> = (0..g.ng).collect();
    if !g.dk.is_empty() { ord.sort_unstable_by_key(|&t| g.dk[t]) } // keys are distinct, so unstable is the stable order
    else { sym_msort(&sym_heads(s, &g.first), &mut ord, &mut alloc::vec![0usize; g.ng]) }
    let mut rank = alloc::vec![0usize; g.ng];
    for (t, &o) in ord.iter().enumerate() { rank[o] = t }
    g.gid.iter().map(|&x| rank[x as usize] as u64).collect()
}
/// sort.c:2964 `qlean_sort_grade_syms` past the unboxing.
/// Ranks are dense in `0 .. ng`, so the grade is one stable counting pass (`grade_keys` would pick `grade_count`).
pub fn grade_syms(desc: bool, s: &Syms, out: &mut [i64]) {
    let n = s.count();
    if n == 0 { return }
    let k = sym_ranks(s, n);
    let mx = k.iter().copied().max().unwrap_or(0);
    grade_count(&Ksrc { kind: key::SK_KEY, p: crate::pod::bytes(&k), c: None, n }, 0, mx, desc, false, mx, out)
}

#[cfg(test)]
mod a24_tests {
    use super::*;
    fn longs(x: &[u64]) -> Vec<u8> { x.iter().flat_map(|v| v.to_le_bytes()).collect() }
    fn rank(w: usize, v: &[u8], o: &[i64]) -> Vec<i64> { let mut r = vec![0; o.len() - 1]; rank_slices(w, v, o, &mut r); r }
    // expected values are SortTest.lean's `rankSlices` guards (the C's answers)
    #[test]
    fn rank_longs() {
        assert_eq!(rank(64, &longs(&[1, 2, 2, 1, 1, 2]), &[0, 2, 4, 6]), [0, 1, 0]);
        assert_eq!(rank(64, &longs(&[0; 6]), &[0, 0, 1, 3, 3, 6]), [0, 1, 2, 0, 3]);
        assert_eq!(rank(64, &longs(&[7, 8, 7, 8, 7, 8]), &[0, 2, 4, 6]), [0, 0, 0]);
        assert_eq!(rank(64, &longs(&[9, 1, 2, 1, 2]), &[1, 3, 5]), [0, 0]);
    }
    #[test]
    fn rank_odd_and_narrow_widths() {
        // 3-bit elements 1,2,1,2 pack to the bytes 81, 4
        assert_eq!(rank(3, &[81, 4], &[0, 2, 4]), [0, 0]);
        assert_eq!(rank(3, &[81, 4], &[0, 1, 2, 3, 4]), [0, 1, 0, 1]);
        assert_eq!(rank(1, &[0b0101_0101], &[0, 2, 4, 6, 8]), [0, 0, 0, 0]);
        assert_eq!(rank(0, &[], &[0, 3, 5, 8]), [0, 1, 0]); // one value: segments equal iff their lengths are
    }
    #[test]
    fn id_passes() {
        let g = [0u8, 1, 1, 3, 1];
        let (mut s, mut l, mut c) = ([9i64; 4], [9i64; 4], [0i64; 5]);
        group_sizes(4, 8, 5, &g, &mut s);
        group_lasts(4, 8, 5, &g, &mut l);
        id_longs(5, 8, &g, &mut c);
        assert_eq!((s, l, c), ([1, 3, 0, 1], [0, 4, 0, 3], [0, 1, 1, 3, 1]));
        let mut z = [9i64; 3];
        group_sizes(3, 0, 4, &[], &mut z); // width 0: every id is 0
        assert_eq!(z, [4, 0, 0]);
        let mut p = [0i64; 4];
        id_longs(4, 2, &[0b11_10_01_00], &mut p);
        assert_eq!(p, [0, 1, 2, 3]);
    }
}

#[cfg(test)]
mod a25_tests {
    use super::*;
    use alloc::vec;
    /// `offs` for the symbols `ss`, each NUL-terminated in the blob, boxed; `pad` extra blob bytes make the 8-byte load whole
    fn col(ss: &[Vec<u8>], pad: usize) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (vec![], vec![1]);
        for s in ss { b.extend_from_slice(s); b.push(0); o.push(b.len() << 1 | 1) }
        b.extend(core::iter::repeat(7).take(pad));
        (b, o)
    }
    fn rnd(x: &mut u64) -> u64 { *x ^= *x << 13; *x ^= *x >> 7; *x ^= *x << 17; *x }
    /// The spec: `0 .. n-1` ordered by `sym_cmp`, ties in original order (descending: by key, ties still original).
    fn oracle(ss: &[Vec<u8>], desc: bool) -> Vec<i64> {
        let mut v: Vec<i64> = (0..ss.len() as i64).collect();
        v.sort_by(|&a, &b| { let c = ss[a as usize].cmp(&ss[b as usize]); if desc { c.reverse() } else { c } });
        v
    }
    #[test] fn grade_matches_oracle() {
        let mut x = 0x9e3779b97f4a7c15u64;
        let mut cases = 0;
        for round in 0..3000 {
            let n = (rnd(&mut x) % 40) as usize + (round % 7 == 0) as usize * 5000;
            let (maxlen, alpha) = [(8, 3), (3, 2), (12, 4), (8, 200), (1, 255)][round % 5];
            let ss: Vec<Vec<u8>> = (0..n).map(|_| {
                let l = (rnd(&mut x) % (maxlen + 1)) as usize;
                (0..l).map(|_| 1 + (rnd(&mut x) % alpha) as u8).collect()
            }).collect();
            for pad in [0, 9] {
                let (b, o) = col(&ss, pad);
                let s = Syms { blob: &b, offs: &o };
                for desc in [false, true] {
                    let mut out = vec![0i64; n];
                    grade_syms(desc, &s, &mut out);
                    assert_eq!(out, oracle(&ss, desc), "n {n} desc {desc} pad {pad}");
                    cases += 1;
                }
            }
        }
        assert_eq!(cases, 12000);
    }
    #[test] fn group_fields() {
        let ss: Vec<Vec<u8>> = ["b", "a", "b", "", "a", "b"].iter().map(|s| s.as_bytes().to_vec()).collect();
        let (b, o) = col(&ss, 0);
        let s = Syms { blob: &b, offs: &o };
        let g = sym_group(&s, 6, 2);
        assert_eq!((g.ng, g.first.clone(), g.gid.clone(), g.cnt.clone()), (3, vec![0, 1, 3], vec![0, 1, 0, 2, 1, 0], vec![3, 2, 1]));
        assert_eq!(g.dk.len(), 3);
        assert_eq!(sym_group(&s, 6, 0).first, vec![0, 1, 3]);
        let long: Vec<Vec<u8>> = ["abcdefghij", "a", "abcdefghij"].iter().map(|s| s.as_bytes().to_vec()).collect();
        let (b, o) = col(&long, 0);
        let g = sym_group(&Syms { blob: &b, offs: &o }, 3, 2);
        assert_eq!((g.ng, g.dk.len(), g.first, g.gid, g.cnt), (2, 0, vec![0, 1], vec![0, 1, 0], vec![2, 1]));
        assert_eq!(sym_ranks(&Syms { blob: &b, offs: &o }, 3), vec![1, 0, 1]);
        let (b, o) = col(&long[1..2], 0);
    }
}

// ---- A26: sort.c:3060-3460 ----
/// sort.c:3060 `id_rank`: id `i`'s rank among the dictionary keys `dk`; an id past the dictionary reads rank 0.
pub fn id_rank(ids: &[u8], w: u32, i: usize, dk: &[u64]) -> usize { dk.get(crate::ids::id_at(ids, w, i)).map_or(0, |&r| r as usize) }
/// The rank of each id, `n` ids, counted into four private tables of `nr` entries (the lanes break the dependent
/// read-modify-write a small dictionary makes), then summed into the first.
fn rank_counts<const W: u32>(ids: &[u8], n: usize, dk: &[u64], nr: usize) -> Vec<usize> {
    let mut c = alloc::vec![0usize; 4 * nr];
    let rk = |i: usize| id_rank(ids, W, i, dk);
    let mut i = 0;
    while i + 4 <= n { for l in 0..4 { c[l * nr + rk(i + l)] += 1 } i += 4 }
    while i < n { c[rk(i)] += 1; i += 1 }
    for k in 0..nr { c[k] += c[nr + k] + c[2 * nr + k] + c[3 * nr + k] }
    c.truncate(nr);
    c
}
/// Each rank's starting slot, ascending or descending by rank: `at[r]` becomes the rows before rank `r`'s.
fn starts(cnt: &[usize], desc: bool) -> Vec<usize> {
    let (mut at, mut run) = (alloc::vec![0usize; cnt.len()], 0);
    let mut put = |r: usize| { at[r] = run; run += cnt[r] };
    if desc { (0..cnt.len()).rev().for_each(&mut put) } else { (0..cnt.len()).for_each(&mut put) }
    at
}
/// The dictionary's ranks, or none for an empty dictionary (every id then reads rank 0).
fn dict_ranks(dict: &Syms) -> Vec<u64> { if dict.count() == 0 { Vec::new() } else { sym_ranks(dict, dict.count()) } }
fn scatter<const W: u32>(ids: &[u8], n: usize, dk: &[u64], at: &mut [usize], out: &mut [i64]) {
    for i in 0..n { let r = id_rank(ids, W, i, dk); out[at[r]] = i as i64; at[r] += 1 }
}
/// sort.c:3079 `qlean_sort_grade_ids` past the unboxing: the grade of `n` ids at `w` into the dictionary `dict`.
/// A counting sort over the dictionary's dense ranks, stable both ways round.
pub fn grade_ids(desc: bool, n: usize, dict: &Syms, ids: &[u8], w: u32, out: &mut [i64]) {
    if n == 0 { return }
    if dict.count() != 0 { group_bound(dict.count()) }
    let dk = dict_ranks(dict);
    let mut at = starts(&by_width!(w, rank_counts(ids, n, &dk, dk.len().max(1))), desc);
    by_width!(w, scatter(ids, n, &dk, &mut at, out))
}
/// sort.c:3136 `qlean_sort_sorted_ids`: the ids in dictionary order, into `out` (zeroed, `ids_bytes(n, w)` long) at `w` bits.
/// A rank's rows all name one id, so each rank is one `ids_fill` run; `rid` inverts the rank.
pub fn sorted_ids(desc: bool, n: usize, dict: &Syms, ids: &[u8], w: u32, out: &mut [u8]) {
    if n == 0 { return }
    if dict.count() != 0 { group_bound(dict.count()) }
    let dk = dict_ranks(dict);
    let cnt = by_width!(w, rank_counts(ids, n, &dk, dk.len().max(1)));
    let mut rid = alloc::vec![0u64; cnt.len()];
    for (u, &r) in dk.iter().enumerate() { rid[r as usize] = u as u64 }
    for (r, at) in starts(&cnt, desc).into_iter().enumerate() { crate::ids::ids_fill(out, w, at, cnt[r], rid[r]) }
}
/// sort.c:3220 `qlean_sort_distinct_syms` past the allocation: each distinct symbol's first index, in order of
/// appearance, into `first`; answers the count.
pub fn distinct_syms(s: &Syms, first: &mut [usize]) -> usize {
    let n = s.count();
    if n == 0 { return 0 }
    let g = sym_group(s, n, 0);
    first[..g.ng].copy_from_slice(&g.first);
    g.ng
}
fn group_at<const W: u32>(ids: &[u8], n: usize, nd: usize, mut gid: Option<&mut [u8]>, cnt: &mut [u32]) -> Vec<usize> {
    let (mut slot, mut first) = (alloc::vec![usize::MAX; nd + 1], Vec::with_capacity(n.min(nd + 1)));
    for i in 0..n {
        let v = crate::ids::id_at(ids, W, i).min(nd);
        if slot[v] == usize::MAX { slot[v] = first.len(); cnt[first.len()] = 0; first.push(i) }
        let k = slot[v];
        if let Some(g) = gid.as_deref_mut() { g[4 * i..4 * i + 4].copy_from_slice(&(k as u32).to_ne_bytes()) }
        cnt[k] += 1;
    }
    first
}
/// sort.c:3265 `ids_group`: group ids (`gid`, `u32`s as bytes, null for none) and counts (`nd + 1` long) of `n` ids at
/// `w` into a dictionary of `nd`, an id from `nd` up naming the one empty symbol; answers each group's first index.
pub fn ids_group(ids: &[u8], n: usize, w: u32, nd: usize, gid: Option<&mut [u8]>, cnt: &mut [u32]) -> Vec<usize> {
    group_bound(n);
    by_width!(w, group_at(ids, n, nd, gid, cnt))
}
/// sort.c:3288 `ids_heads`: the dictionary symbol of each group's first id; an id past the dictionary reads the empty symbol.
pub fn ids_heads<'a>(dict: &Syms<'a>, ids: &[u8], w: u32, first: &[usize]) -> Vec<&'a [u8]> {
    first.iter().map(|&f| { let u = crate::ids::id_at(ids, w, f); if u < dict.count() { dict.at(u) } else { &dict.blob[..0] } }).collect()
}
/// sort.c:3400 `qlean_sort_parted_ids`: the ids are parted (each id's run contiguous). The distinct count is
/// `firsts`' and runs are never fewer, so the run walk stops past `ng`.
pub fn parted_ids(strict: bool, d: usize, n: usize, w: u32, ids: &[u8]) -> bool {
    if n == 0 { return true }
    let (mut slot, mut first) = (alloc::vec![usize::MAX; d + 1], alloc::vec![0usize; n.min(d + 1)]);
    let ng = crate::ids::firsts(ids, n, w, d, &mut slot, &mut first);
    ng == if strict { n } else { crate::ids::runs(ids, n, w, d, ng, &mut []) }
}
/// `g` packed `w` bits an id into `out`, the last byte's fields past `g` zero.
fn pack_gids(g: &[u32], w: u32, out: &mut [u8]) {
    match w {
        0 => {}
        1 | 2 | 4 => for (o, c) in out.iter_mut().zip(g.chunks((8 / w) as usize)) {
            *o = c.iter().enumerate().fold(0u8, |b, (t, &v)| b | (v as u8 & ((1u8 << w) - 1)) << (t as u32 * w));
        },
        _ => { let k = (w / 8) as usize; for (o, &v) in out.chunks_exact_mut(k).zip(g) { o.copy_from_slice(&(v as u64).to_le_bytes()[..k]) } }
    }
}
/// sort.c:3423 `qlean_sort_intern_syms` past the allocation: the id of each symbol into `out` at `id_width(ng)` bits,
/// the distinct symbols' first indices into `first`; answers the count `ng`. The width is the group count's, which
/// the caller learns only from the answer, so `out` is sized for `w = id_width(n)`, an upper bound, and read at
/// `ids_bytes(n, id_width(ng))`.
pub fn intern_syms(s: &Syms, w: u32, out: &mut [u8], first: &mut [usize]) -> usize {
    let n = s.count();
    if n == 0 { return 0 }
    let g = sym_group(s, n, 1);
    let wo = crate::ids::id_width(g.ng);
    assert!(wo <= w, "qlean: intern_syms: {} ids need {wo} bits, past the {w} the buffer was sized for", g.ng);
    pack_gids(&g.gid, wo, out);
    first[..g.ng].copy_from_slice(&g.first);
    g.ng
}

#[cfg(test)]
mod a26_tests {
    use super::*;
    use alloc::vec;
    fn col(ss: &[Vec<u8>]) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (vec![], vec![1]);
        for s in ss { b.extend_from_slice(s); b.push(0); o.push(b.len() << 1 | 1) }
        (b, o)
    }
    fn rnd(x: &mut u64) -> u64 { *x ^= *x << 13; *x ^= *x >> 7; *x ^= *x << 17; *x }
    /// `n` ids over a dictionary of `nd` symbols (some ids past it), packed at `id_width(nd)`.
    fn ids_of(x: &mut u64, n: usize, nd: usize) -> (Vec<usize>, Vec<u8>, u32) {
        let w = crate::ids::id_width(nd);
        let v: Vec<usize> = (0..n).map(|_| { let u = (rnd(x) as usize) % (nd + 1); if w == 0 { 0 } else if w < 32 { u & ((1 << w) - 1) } else { u } }).collect();
        let mut p = vec![0u8; crate::ids::ids_bytes(n, w)];
        for (i, &u) in v.iter().enumerate() { crate::ids::id_put(&mut p, w, i, u as u64) }
        (v, p, w)
    }
    #[test] fn ids_against_the_spec() {
        let mut x = 0x2545f4914f6cdd1du64;
        for round in 0..2000 {
            let nd = (rnd(&mut x) % 12) as usize + (round % 9 == 0) as usize * 300;
            let ss: Vec<Vec<u8>> = (0..nd).map(|_| (0..rnd(&mut x) % 10).map(|_| 1 + (rnd(&mut x) % 3) as u8).collect()).collect();
            let (b, o) = col(&ss);
            let d = Syms { blob: &b, offs: &o };
            let n = (rnd(&mut x) % 50) as usize + 1;
            let (v, p, w) = ids_of(&mut x, n, nd);
            let sym = |u: usize| if u < nd { ss[u].clone() } else { vec![] };
            for desc in [false, true] {
                let mut want: Vec<i64> = (0..n as i64).collect();
                // the spec: the grade by each id's rank among the distinct symbols (0-based, an id past the dictionary reading 0), ties in row order
                let mut dd = ss.clone(); dd.sort(); dd.dedup();
                let rk = |i: i64| { let u = v[i as usize]; if u < nd { dd.iter().position(|s| *s == ss[u]).unwrap() } else { 0 } };
                want.sort_by(|&a, &c| { let k = rk(a).cmp(&rk(c)); if desc { k.reverse() } else { k } });
                let mut out = vec![0i64; n];
                grade_ids(desc, n, &d, &p, w, &mut out);
                assert_eq!(out, want);
                let mut s = vec![0u8; p.len()];
                sorted_ids(desc, n, &d, &p, w, &mut s);
                if nd > 0 { for (k, &i) in out.iter().enumerate() { assert_eq!(sym(crate::ids::id_at(&s, w, k)), dd[rk(i)]) } }
            }
            let mut cnt = vec![0u32; nd + 1];
            let mut gid = vec![0u8; 4 * n];
            let first = ids_group(&p, n, w, nd, Some(&mut gid), &mut cnt);
            let mut seen = vec![]; for &u in &v { let u = u.min(nd); if !seen.contains(&u) { seen.push(u) } }
            assert_eq!(first.iter().map(|&f| v[f].min(nd)).collect::<Vec<_>>(), seen);
            assert_eq!(first.iter().map(|&f| ids_heads(&d, &p, w, &[f])[0].to_vec()).collect::<Vec<_>>(), seen.iter().map(|&u| sym(u)).collect::<Vec<_>>());
            let runs = (0..n).filter(|&i| i == 0 || v[i].min(nd) != v[i - 1].min(nd)).count();
            assert_eq!(parted_ids(false, nd, n, w, &p), first.len() == runs);
            assert_eq!(parted_ids(true, nd, n, w, &p), first.len() == n);
        }
    }
    #[test] fn intern_and_distinct() {
        let mut x = 0x9e3779b97f4a7c15u64;
        for round in 0..2000 {
            let n = (rnd(&mut x) % 40) as usize + 1;
            let ss: Vec<Vec<u8>> = (0..n).map(|_| (0..rnd(&mut x) % (3 + 9 * (round % 2) as u64)).map(|_| 1 + (rnd(&mut x) % 3) as u8).collect()).collect();
            let (b, o) = col(&ss);
            let s = Syms { blob: &b, offs: &o };
            let mut want: Vec<usize> = vec![]; for i in 0..n { if !want.iter().any(|&f| ss[f] == ss[i]) { want.push(i) } }
            let mut first = vec![0usize; n];
            assert_eq!(distinct_syms(&s, &mut first), want.len());
            assert_eq!(&first[..want.len()], &want[..]);
            let wn = crate::ids::id_width(n);
            let mut out = vec![0u8; crate::ids::ids_bytes(n, wn)];
            let ng = intern_syms(&s, wn, &mut out, &mut first);
            assert_eq!(ng, want.len());
            let wo = crate::ids::id_width(ng);
            for i in 0..n { assert_eq!(ss[want[crate::ids::id_at(&out, wo, i)]], ss[i]) }
        }
    }
}

// ---- A27: sort.c:3471-3500 ----
/// sort.c:3471 `guid_words`: the 8-byte word at byte `at` of each of `n` guids, in the order `perm` (empty: as stored).
pub fn guid_words(p: &[u8], n: usize, at: usize, perm: &[i64], k: &mut [u64]) -> (u64, u64) {
    let (mut lo, mut hi) = (u64::MAX, 0);
    for i in 0..n {
        let g = if perm.is_empty() { i } else { perm[i] as usize };
        let w = u64::from_be_bytes(p[16 * g + at..16 * g + at + 8].try_into().unwrap());
        k[i] = w; lo = lo.min(w); hi = hi.max(w);
    }
    (lo, hi)
}
/// sort.c:3483 `qlean_sort_grade_guid` past the unboxing: two big-endian words, the low one graded first, so a stable grade
/// by the high word over that order is the order of the pair; the low pass runs only when two high words tie.
pub fn grade_guid(desc: bool, p: &[u8], out: &mut [i64]) {
    let n = out.len();
    if n == 0 { return }
    let mut k = vec![0u64; n];
    let (mn, mx) = guid_words(p, n, 0, &[], &mut k);
    grade_keys(&k, desc, mn, mx, out);
    if (1..n).any(|i| k[out[i] as usize] == k[out[i - 1] as usize]) {
        let mut lo = vec![0i64; n];
        let (mn, mx) = guid_words(p, n, 8, &[], &mut k);
        grade_keys(&k, desc, mn, mx, &mut lo);
        let (mn, mx) = guid_words(p, n, 0, &lo, &mut k);
        grade_keys(&k, desc, mn, mx, out);
        for o in out.iter_mut() { *o = lo[*o as usize] }
    }
}
#[cfg(test)]
mod a27_tests {
    use super::*;
    fn rnd(x: &mut u64) -> u64 { *x ^= *x << 13; *x ^= *x >> 7; *x ^= *x << 17; *x }
    #[test] fn grade_matches_oracle() {
        let mut x = 0x9e3779b97f4a7c15u64;
        for round in 0..3000 {
            let n = (rnd(&mut x) % 40) as usize;
            let m = 1 + (round % 4) as u64; // few distinct bytes so words and whole guids tie
            let p: Vec<u8> = (0..16 * n).map(|i| if i % 16 < 7 { 0 } else { (rnd(&mut x) % m) as u8 }).collect();
            for desc in [false, true] {
                let mut want: Vec<i64> = (0..n as i64).collect();
                want.sort_by(|&a, &b| { let c = p[16 * a as usize..][..16].cmp(&p[16 * b as usize..][..16]); if desc { c.reverse() } else { c } });
                let mut out = vec![0i64; n];
                grade_guid(desc, &p, &mut out);
                assert_eq!(out, want);
            }
        }
    }
}

#[cfg(test)]
mod a23_tests {
    use super::*;
    use crate::ids::{id_at, id_put, id_width, ids_bytes};
    use alloc::collections::BTreeMap;
    use alloc::vec;
    fn rnd(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }
    /// first-occurrence numbering of the pairs: each pair's group and each group's first index
    fn naive(x: &[u64], y: &[u64]) -> (Vec<usize>, Vec<usize>) {
        let (mut seen, mut g, mut first) = (BTreeMap::new(), Vec::new(), Vec::new());
        for i in 0..x.len() { let n = seen.len(); let e = *seen.entry((x[i], y[i])).or_insert(n); if e == n { first.push(i) } g.push(e) }
        (g, first)
    }
    fn range(k: &[u64]) -> (u64, u64) { (*k.iter().min().unwrap(), *k.iter().max().unwrap()) }
    #[test] fn bound() {
        group_bound(0);
        group_bound(u32::MAX as usize);
    }
    #[test] #[should_panic(expected = "qlean: group cuts at most 4294967295 rows into buckets, not 4294967296")]
    fn bound_past() { group_bound(u32::MAX as usize + 1) }
    #[test] fn fits() {
        assert!(pair_fits(0, u64::MAX) && pair_fits(u64::MAX, 0) && !pair_fits(1, u64::MAX) && !pair_fits(u64::MAX, u64::MAX));
        assert!(pair_fits(u32::MAX as u64, u32::MAX as u64) && !pair_fits(u32::MAX as u64 + 1, u32::MAX as u64));
        assert!(pair_fits(0, 0) && pair_fits((1 << 63) - 1, 1));
    }
    #[test] fn keys_of_ids() {
        let mut s = 7;
        for w in [0u32, 1, 2, 4, 8, 16, 32, 64] {
            for m in [0usize, 1, 5, 64, 1000] {
                let mut v = vec![0u8; ids_bytes(m, w)];
                let mask = if w == 0 { 0 } else if w == 64 { !0 } else { (1u64 << w) - 1 };
                for i in 0..m { id_put(&mut v, w, i, rnd(&mut s) & mask) }
                let mut k = vec![9u64; m];
                let (mn, mx) = ids_keys(&v, w, m, &mut k);
                for i in 0..m { assert_eq!(k[i], id_at(&v, w, i) as u64) }
                if m == 0 { assert_eq!((mn, mx), (0, 0)) }
                else if w < 8 { assert_eq!((mn, mx), (0, (1u64 << w) - 1)) }
                else { assert_eq!((mn, mx), range(&k)) }
            }
        }
    }
    #[test] fn narrow_ids() {
        let mut s = 11;
        let mut k: Vec<u64> = (0..300).map(|_| rnd(&mut s) % 7 * (1 << 50)).collect();
        let want = naive(&k, &vec![0; 300]).0;
        let (mn, span) = pair_narrow(&mut k, &mut vec![0; 300]);
        assert_eq!((mn, span), (0, 6));
        assert_eq!(k, want.iter().map(|&g| g as u64).collect::<Vec<_>>());
    }
    fn check_pair(x: &[u64], y: &[u64], widen: (u64, u64)) {
        let m = x.len();
        let ((mnx, mxx), (mny, mxy)) = (range(x), range(y));
        let (want, wfirst) = naive(x, y);
        let ng = wfirst.len();
        let lane = id_width(ng).max(8);
        let (mut gid, mut first) = (vec![0u8; m * 8], vec![0usize; m]);
        let (mut x, mut y) = (x.to_vec(), y.to_vec());
        let got = pair_ids(crate::c::qlean_run_c, &mut x, &mut y, mnx.saturating_sub(widen.0), mxx - mnx + widen.0, mny, mxy - mny + widen.1,
                           &mut gid, &mut first);
        assert_eq!(got, ng);
        assert_eq!(&first[..ng], &wfirst[..]);
        for i in 0..m { assert_eq!(id_at(&gid, lane, i), want[i], "row {i}") }
    }
    #[test] fn pairs_match_naive() {
        let mut s = 99;
        for (m, dx, dy) in [(1usize, 1u64, 1u64), (50, 3, 4), (1000, 1000, 1000), (1000, 1 << 20, 1 << 20), (2000, 1 << 33, 1 << 33),
                            (2000, 1 << 33, 5), (2000, 5, 1 << 40), (2000, u64::MAX, u64::MAX), (3000, 300, 1 << 63), (500, 2, 2)] {
            let pool = |r: &mut u64, d: u64| (0..40).map(|_| rnd(r) % d).collect::<Vec<u64>>();
            let (px, py) = (pool(&mut s, dx), pool(&mut s, dy));
            let x: Vec<u64> = (0..m).map(|_| px[rnd(&mut s) as usize % 40]).collect();
            let y: Vec<u64> = (0..m).map(|_| py[rnd(&mut s) as usize % 40]).collect();
            check_pair(&x, &y, (0, 0));
            check_pair(&x, &y, (3, 7));
        }
        // 3000 distinct pairs: ids past one byte
        let x: Vec<u64> = (0..3000).map(|i| i as u64 * (1 << 40)).collect();
        check_pair(&x, &x.iter().map(|&v| v >> 3).collect::<Vec<_>>(), (0, 0));
    }
    #[test] fn narrow_pairs_match_naive() {
        let mut s = 5;
        for (wa, wb) in [(0u32, 0u32), (0, 8), (8, 0), (1, 1), (2, 2), (4, 4), (1, 4), (2, 1), (4, 2), (0, 4)] {
            for m in [1usize, 7, 64, 1000] {
                let (mut pa, mut pb) = (vec![0u8; ids_bytes(m, wa)], vec![0u8; ids_bytes(m, wb)]);
                let (ma, mb) = (if wa == 0 { 0 } else { (1u64 << wa) - 1 }, if wb == 0 { 0 } else { (1u64 << wb) - 1 });
                // few distinct values, so groups repeat
                let (va, vb) = (rnd(&mut s) & ma, rnd(&mut s) & mb);
                let a: Vec<u64> = (0..m).map(|_| if rnd(&mut s) % 3 == 0 { rnd(&mut s) & ma } else { va }).collect();
                let b: Vec<u64> = (0..m).map(|_| if rnd(&mut s) % 3 == 0 { rnd(&mut s) & mb } else { vb }).collect();
                for i in 0..m { id_put(&mut pa, wa, i, a[i]); id_put(&mut pb, wb, i, b[i]) }
                let (want, wfirst) = naive(&a, &b);
                let ng = wfirst.len();
                let wc = id_width(1 << (wa + wb));
                let wm = id_width(m.min(1 << (wa + wb)));
                let (mut gid, mut first) = (vec![0u8; ids_bytes(m, wm)], vec![0usize; m.min((1usize << wc) + 1)]);
                let got = pair_ids_narrow(crate::c::qlean_run_c, wa, wb, m, &pa, &pb, &mut gid, &mut first);
                assert_eq!(got, ng, "wa {wa} wb {wb} m {m}");
                assert_eq!(&first[..ng], &wfirst[..]);
                for i in 0..m { assert_eq!(id_at(&gid, id_width(ng), i), want[i]) }
            }
        }
    }
}

#[cfg(test)]
mod tests_a19 {
    use super::*;
    use crate::key::{SK_F64, SK_I16, SK_I64, SK_KEY, SK_U8};
    use crate::pod;
    // the empty cases are the ones the C's untouched accumulators answer: keys_of / keys_range (0, 0), ksrc_range (MAX, 0)
    #[test] fn empty_answers() {
        assert_eq!(keys_of(SK_I64, &[], 0, &mut []), (0, 0));
        assert_eq!(keys_range(&[]), (0, 0));
        let s = Ksrc { kind: SK_I64, p: &[], c: None, n: 0 };
        assert_eq!(s.range(), (u64::MAX, 0));
    }
    #[test] fn keys_flip_the_sign_within_the_width() {
        let p = pod::bytes(&[-1i16, 0, 5]).to_vec();
        let mut k = [0u64; 3];
        assert_eq!(keys_of(SK_I16, &p, 3, &mut k), (0x7fff, 0x8005));
        assert_eq!(k, [0x7fff, 0x8000, 0x8005]);
    }
    #[test] fn nan_is_key_zero_and_negative_zero_is_positive_zero() {
        let p = pod::bytes(&[f64::NAN, -0.0, 0.0]).to_vec();
        let mut k = [9u64; 3];
        assert_eq!(keys_of(SK_F64, &p, 3, &mut k), (0, 1 << 63));
        assert_eq!(k, [0, 1 << 63, 1 << 63]);
    }
    #[test] fn range_tail_past_a_multiple_of_four() {
        let k: Vec<u64> = (0..7).map(|i| 10 + (i * 5) % 7).collect();
        assert_eq!(keys_range(&k), (10, 16));
    }
    #[test] fn blk_cuts_at_blk_and_key_payload_is_read_as_is() {
        let v: Vec<u64> = (0..BLK as u64 + 3).collect();
        let s = Ksrc { kind: SK_KEY, p: pod::bytes(&v), c: None, n: v.len() };
        let mut k = [0u64; BLK];
        assert_eq!(s.blk(0, &mut k), BLK);
        assert_eq!(k[BLK - 1], BLK as u64 - 1);
        assert_eq!(s.blk(1, &mut k), 3);
        assert_eq!(&k[..3], &[BLK as u64, BLK as u64 + 1, BLK as u64 + 2]);
        assert_eq!(s.range(), (0, BLK as u64 + 2));
    }
    #[test] fn u8_keys_are_their_own() {
        let mut k = [0u64; 3];
        assert_eq!(keys_of(SK_U8, &[7, 0, 255], 3, &mut k), (0, 255));
        assert_eq!(k, [7, 0, 255]);
    }
}

#[cfg(test)]
mod a20_tests {
    use super::*;
    use alloc::vec;
    fn grade(k: &[u64], desc: bool) -> Vec<i64> {
        let mut o = vec![0i64; k.len()];
        let (mn, mx) = keys_range(k);
        grade_keys(k, desc, mn, mx, &mut o);
        o
    }
    // expected values: the C's own comments (sort.c "the grade": `iasc 9 1 9 1 9`, `idesc 9 1 9 1 9`, `2 2 1`)
    #[test] fn stable_ties() {
        assert_eq!(grade(&[9, 1, 9, 1, 9], false), vec![1, 3, 0, 2, 4]);
        assert_eq!(grade(&[9, 1, 9, 1, 9], true), vec![0, 2, 4, 1, 3]);
        assert_eq!(grade(&[2, 2, 1], false), vec![2, 0, 1]);
        assert_eq!(grade(&[2, 2, 1], true), vec![0, 1, 2]);
    }
    #[test] fn runs() {
        let mut o = vec![0i64; 3];
        assert!(!grade_runs(&[2, 2, 1], false, &mut o));
        assert!(grade_runs(&[3, 2, 1], false, &mut o) && o == vec![2, 1, 0]);
        assert!(!grade_runs(&[2, 2, 1], true, &mut o) || o == vec![0, 1, 2]);
        assert!(grade_runs(&[], false, &mut []));
    }
    // expected values: /data/tmp/qrs/A20/diff.c, sk_digit of sort.c at 86afb0f
    #[test] fn digit_bands() {
        assert_eq!((sk_digit(20, 1000), sk_digit(20, 65536), sk_digit(30, 1 << 20), sk_digit(49, 1 << 20)), (8, 10, 16, 14));
        assert_eq!((sk_digit(17, 1 << 20), sk_digit(20, 1 << 20), sk_digit(25, 1 << 20), sk_digit(48, 1 << 20)), (10, 10, 13, 16));
        assert!(sk_countable(999, 10) && !sk_countable(1 << 16, 1 << 20));
    }
    #[test] fn rank_of_perm_is_the_key() {
        let k = [2u64, 0, 1];
        let mut o = vec![0i64; 3];
        let s = Ksrc { kind: key::SK_KEY, p: crate::pod::bytes(&k), c: None, n: 3 };
        grade_src(&s, false, true, 0, 2, &mut o);
        assert_eq!(o, vec![2, 0, 1]);
    }
}

#[cfg(test)]
mod tests_k12 {
    use super::*;
    fn keys(k: &[u64]) -> Ksrc<'_> { Ksrc { kind: key::SK_KEY, p: pod::bytes(k), c: None, n: k.len() } }
    #[test] fn hist_find_relative_rank() {
        let mut r = 5; assert_eq!(hist_find(&[2, 0, 4, 9], &mut r), 2); assert_eq!(r, 3);
        let mut r = 99; assert_eq!(hist_find(&[1], &mut r), 0, "one bucket takes every rank"); assert_eq!(r, 99, "the last bucket subtracts nothing");
    }
    #[test] fn select_two_buckets_wide_range() {
        // `0N,x` shape: two far-apart keys, r1 last of the low bucket and r2 = r1 + 1 first of the high one
        let k = [1u64 << 63, 0, 0, 1 << 63];
        assert_eq!(select_keys(&keys(&k), 1, 2), (0, 1 << 63));
        assert_eq!(select_keys(&keys(&[7, 7, 7]), 1, 1), (7, 7));
        let k: Vec<u64> = (0..100_000u64).map(|i| i * 40_009 % 100_003 * 3).collect();
        let mut s = k.clone(); s.sort();
        assert_eq!(select_keys(&keys(&k), 49_999, 50_000), (s[49_999], s[50_000]));
    }
    #[test] fn xrank_floors_scaled_ranks() {
        let k = [30u64, 10, 20, 10];
        let mut o = [0i64; 4]; xrank_src(&keys(&k), 0.5, &mut o);
        assert_eq!(o, [1, 0, 1, 0], "ranks 3 0 2 1 scaled by 0.5, ties in index order");
        xrank_src(&keys(&k), 1.0, &mut o); assert_eq!(o, [3, 0, 2, 1]);
        assert_eq!(xr_floor(-0.5), -1); assert_eq!(xr_floor(2.0), 2);
    }
}
