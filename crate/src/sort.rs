#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), sort.c: keys and their range (A19), the grades (A20–A22), pair and id grouping (A23–A24), symbol
//! sorts and groups (A25–A26), guids (A27). The `qlean_sort_*` entries unbox and allocate and stay C (§1).
//! A grade answers into `out: &mut [i64]` of `n`; `kind` is sort.c's `SK_*`.
use alloc::vec;
use alloc::vec::Vec;
use core::sync::atomic::Ordering::Relaxed;

use crate::c::{run_map, run_slices, Runner};
use crate::coc::Coc;
use crate::key::{self, Keys, Pass, SK_I16, SK_KINDS_N, SK_U8};
use crate::{kwin, BLK};
use crate::sym::{sym_cmp, sym_hash, sym_msort, Syms};
use crate::{ids, pod, QLEAN_COST_COPY};

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
pub fn grade_radix(run: Runner, s: &Ksrc, span: u64, xr: u64, base: u64, out: &mut [i64]) {
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
pub fn grade_src(run: Runner, s: &Ksrc, desc: bool, rank: bool, mn: u64, mx: u64, out: &mut [i64]) {
    let (n, span) = (s.n, mx - mn);
    if span == 0 { for (i, o) in out[..n].iter_mut().enumerate() { *o = if rank { 0 } else { i as i64 } } return }
    if span == n as u64 - 1 && grade_perm(s, mn, mx, desc, rank, out) { return }
    if sk_countable(span, n) { return grade_count(s, mn, mx, desc, rank, span, out) }
    let mut g = if rank { alloc::vec![0i64; n] } else { Vec::new() };
    let o = if rank { &mut g[..] } else { &mut *out };
    if desc { grade_radix(run, s, span, !0, !mx, o) } else { grade_radix(run, s, span, 0, mn, o) }
    if rank { for (i, &x) in g.iter().enumerate() { out[x as usize] = i as i64 } }
}
/// sort.c:724 `grade_keys`: `grade_src` over keys already made.
pub fn grade_keys(run: Runner, k: &[u64], desc: bool, mn: u64, mx: u64, out: &mut [i64]) {
    if k.is_empty() || grade_runs(k, desc, out) { return }
    grade_src(run, &Ksrc { kind: key::SK_KEY, p: crate::pod::bytes(k), c: None, n: k.len() }, desc, false, mn, mx, out)
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
        // the rank of a bit is how many clear bits precede it, or every clear bit and the set ones before it
        let full = n & !63;
        let ones = (0..full / 64).map(|w| load(p, w * 8, 8).count_ones() as usize).sum::<usize>()
            + (full..n).map(|i| (p[i >> 3] >> (i & 7)) as usize & 1).sum::<usize>();
        let (z, mut o) = (n - ones, 0usize);
        for at in (0..n).step_by(64) {
            let nb = (n - at).min(64);
            let mut v = load(p, at >> 3, nb.div_ceil(8));
            for j in 0..nb {
                let b = (v & 1) as usize;
                out[at + j] = (if b != 0 { z + o } else { at + j - o }) as i64;
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
    // bits past `n` in the last byte are not elements; the rank is where the grade would put each row (ascending only, as `rank` is)
    #[test] fn bits_rank_ignores_bits_past_n() {
        assert_eq!(bits(0b1111_1001, 4, false, true), [2, 0, 1, 3]);
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
/// sort.c:894 `qlean_sort_ascending` past the unboxing.
pub fn ascending(kind: u8, desc: bool, strict: bool, p: &[u8], n: usize) -> bool { unimplemented!("A22: qlean_sort_ascending") }
/// sort.c:941 `asc_blk_foR`
pub fn asc_blk(c: &Coc, b: usize, desc: bool, strict: bool) -> Ends { unimplemented!("A22: asc_blk_foR") }
/// sort.c:977 `qlean_sort_ascending_foR` past the unboxing, threaded (`asc_run`).
pub fn ascending_enc(run: Runner, kind: u8, desc: bool, strict: bool, c: &Coc) -> bool {
    unimplemented!("A22: qlean_sort_ascending_foR")
}
/// sort.c:1012 `qlean_sort_invert`: the inverse permutation.
pub fn invert(p: &[i64], out: &mut [i64]) { unimplemented!("A22: qlean_sort_invert") }
/// sort.c:1025 `order_runs`: the grade of an already ordered column (`asc`), or reversed (`desc_strict`).
pub fn order_runs(asc: bool, desc_strict: bool, out: &mut [i64]) -> bool { unimplemented!("A22: order_runs") }
/// sort.c:1034 `order_dense` past the allocation: grade or ranks of a dense payload.
pub fn order(run: Runner, kind: u8, desc: bool, rank: bool, p: &[u8], n: usize, out: &mut [i64]) {
    unimplemented!("A22: order_dense")
}
/// sort.c:1068 `order_foR` past the allocation
pub fn order_enc(run: Runner, kind: u8, desc: bool, rank: bool, c: &Coc, out: &mut [i64]) { unimplemented!("A22: order_foR") }
/// sort.c:1093 `qlean_sort_grade_lane` past the unboxing: the grade of `n` ids at `w` bits.
pub fn grade_lane(run: Runner, desc: bool, w: u32, ids: &[u8], n: usize, out: &mut [i64]) {
    unimplemented!("A22: qlean_sort_grade_lane")
}

// ---- A23: sort.c:1631, 2293-2400, 3386 ----
/// sort.c:1631 `group_bound`: aborts when `n` groups cannot be numbered.
pub fn group_bound(n: usize) { unimplemented!("A23: group_bound") }
/// sort.c:2293 `pair_fits`: two spans pack into one 64-bit key.
pub fn pair_fits(sx: u64, sy: u64) -> bool { unimplemented!("A23: pair_fits") }
/// sort.c:2301 `pair_narrow`: keys `k` renumbered densely (`ids`, `first`); answers `(mn, span)`.
pub fn pair_narrow(k: &mut [u64], ids: &mut [usize], first: &mut [usize]) -> (u64, u64) { unimplemented!("A23: pair_narrow") }
/// sort.c:2314 `pair_ids` past the allocation: the group id of each pair `(x[i], y[i])` into `gid` at
/// `max(8, id_width(ng))` bits, the first index of each group into `first`; answers `ng`.
pub fn pair_ids(run: Runner, x: &[u64], y: &[u64], mnx: u64, sx: u64, mny: u64, sy: u64, gid: &mut [u8],
                first: &mut [usize]) -> usize {
    unimplemented!("A23: pair_ids")
}
/// sort.c:2366 `ids_keys`: `m` ids at `w` bits as keys; answers `(min, max)`.
pub fn ids_keys(v: &[u8], w: u32, m: usize, k: &mut [u64]) -> (u64, u64) { unimplemented!("A23: ids_keys") }
/// sort.c:3386 `pair_ids_narrow` past the allocation: as `pair_ids` for two id payloads.
pub fn pair_ids_narrow(run: Runner, wa: u32, wb: u32, m: usize, pa: &[u8], pb: &[u8], gid: &mut [u8], first: &mut [usize])
    -> usize {
    unimplemented!("A23: pair_ids_narrow")
}

/// `f::<W>(args)` for the run-time width `w`, so `id_at`'s match folds as the C's `IDS_WIDTHS` does.
macro_rules! by_width {
    ($w:expr, $f:ident($($a:expr),*)) => { match $w {
        0 => $f::<0>($($a),*), 1 => $f::<1>($($a),*), 2 => $f::<2>($($a),*), 4 => $f::<4>($($a),*),
        8 => $f::<8>($($a),*), 16 => $f::<16>($($a),*), 32 => $f::<32>($($a),*), _ => $f::<64>($($a),*),
    } };
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
        for k in a..a + len { h = (h ^ el(k)).wrapping_mul(0xc2b2ae3d27d4eb4f) }
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
    out.fill(0);
    for i in 0..n { let v = crate::ids::id_at(ids, W, i); if v < ng { out[v] += 1 } }
}
/// sort.c `qlean_sort_group_sizes`: the size of each of `ng` groups of the ids `gid` (`n` at `w` bits), `n` already
/// clamped to what `gid` holds.
pub fn group_sizes(ng: usize, w: u32, n: usize, gid: &[u8], out: &mut [i64]) { by_width!(w, sizes(ng, n, gid, out)) }
fn lasts<const W: u32>(ng: usize, n: usize, ids: &[u8], out: &mut [i64]) {
    out.fill(0);
    for i in 0..n { let v = crate::ids::id_at(ids, W, i); if v < ng { out[v] = i as i64 } }
}
/// sort.c `qlean_sort_group_lasts`: each group's last index, 0 for one no row names.
pub fn group_lasts(ng: usize, w: u32, n: usize, gid: &[u8], out: &mut [i64]) { by_width!(w, lasts(ng, n, gid, out)) }
fn longs<const W: u32>(n: usize, ids: &[u8], out: &mut [i64]) {
    for (i, o) in out[..n].iter_mut().enumerate() { *o = crate::ids::id_at(ids, W, i) as i64 }
}
/// sort.c `qlean_sort_id_longs`: the first `n` ids at `w` bits as longs.
pub fn id_longs(n: usize, w: u32, ids: &[u8], out: &mut [i64]) { by_width!(w, longs(n, ids, out)) }

// ---- A25: sort.c:2814-2990 ----
/// sort.c:2884 `symgroups`: the distinct symbols' keys, first indices, group ids and counts.
/// `dk` is empty exactly when a symbol did not pack; `gid`, `cnt` are empty unless `want` asked for them.
pub struct SymGroups { pub dk: Vec<u64>, pub first: Vec<usize>, pub ng: usize, pub gid: Vec<u32>, pub cnt: Vec<u32> }
/// sym.h:153 `SYM_KEY_BLOCK`: a block is checked, then packed while it is in cache.
const SYM_KEY_BLOCK: usize = 4096;
/// sym.h `SYM_PAD`: the mask keeping a symbol's first `len` bytes of an 8-byte big-endian load.
fn sym_pad(len: usize) -> u64 { if len == 0 { 0 } else { !0u64 << (8 * (8 - len)) } }
/// The packed key of symbol `i` (len <= 8); `whole` says an 8-byte load at its start stays inside the blob.
fn sym_key(s: &Syms, i: usize, whole: bool) -> u64 {
    let (lo, hi) = (s.off(i), s.off(i + 1));
    let len = hi - lo - 1;
    if len == 0 { 0 } else if whole { u64::from_be_bytes(s.blob[lo..lo + 8].try_into().unwrap()) & sym_pad(len) }
    else { s.blob[lo..lo + len].iter().fold(0, |w, &b| w << 8 | b as u64) << (8 * (8 - len)) }
}
/// sort.c:2814 `sym_whole`: the column packs into 8-byte keys whole, i.e. an 8-byte load at the start of any of the
/// first `n` symbols stays inside the blob (C answers how many symbols it holds for; the last is the farthest).
pub fn sym_whole(s: &Syms, n: usize) -> bool { n == 0 || (s.off(n - 1) + 8 <= s.blob.len()) }
/// sort.c:2829 `sym_dedup`: group ids and counts of the sorted symbols `v`; answers the group count.
/// An empty `gid` (or `cnt`) is C's NULL.
pub fn sym_dedup(v: &[&[u8]], gid: &mut [u32], cnt: &mut [u32], first: &mut [usize]) -> usize {
    let n = v.len();
    if n == 0 { return 0 }
    let (cap, mut ng) = (crate::group::cap_for(n), 0);
    let mut tab = alloc::vec![0usize; cap];
    for i in 0..n {
        let mut s = (sym_hash(v[i]) as usize) & (cap - 1);
        while tab[s] != 0 && sym_cmp(v[first[tab[s] - 1]], v[i]).is_ne() { s = (s + 1) & (cap - 1) }
        if tab[s] == 0 { ng += 1; tab[s] = ng; first[ng - 1] = i; if !cnt.is_empty() { cnt[ng - 1] = 0 } }
        if !gid.is_empty() { gid[i] = (tab[s] - 1) as u32; if !cnt.is_empty() { cnt[tab[s] - 1] += 1 } }
    }
    ng
}
/// sort.c:2848 `sym_heads`: each group's first symbol.
pub fn sym_heads<'a>(s: &Syms<'a>, first: &[usize]) -> Vec<&'a [u8]> { first.iter().map(|&i| s.at(i)).collect() }
/// sort.c:2886 `sym_group`: `want` says which fields are filled (C's bit flags: 0 firsts, 1 gids, 2 gids and counts).
pub fn sym_group(s: &Syms, n: usize, want: i32) -> SymGroups {
    if want != 0 && n > u32::MAX as usize { panic!("qlean: group cuts at most {} rows into buckets, not {n}", u32::MAX) }
    let mut gid = if want != 0 { alloc::vec![0u32; n] } else { Vec::new() };
    let mut cnt = if want == 2 { alloc::vec![0u32; n] } else { Vec::new() };
    let (cap, mut first, mut dk) = (crate::group::cap_for(n), alloc::vec![0usize; n], Vec::<u64>::new());
    let (sh, mut tab, mut packed) = (64 - cap.trailing_zeros(), alloc::vec![0usize; cap], true);
    for at in (0..n).step_by(SYM_KEY_BLOCK) {
        let blk = (n - at).min(SYM_KEY_BLOCK);
        let b = Syms { blob: s.blob, offs: &s.offs[at..] };
        if !b.packs(blk) { packed = false; break }
        let whole = sym_whole(&b, blk);
        for i in at..at + blk {
            let key = sym_key(s, i, whole);
            let mut t = (key.wrapping_mul(crate::group::PHI64) >> sh) as usize;
            while tab[t] != 0 && dk[tab[t] - 1] != key { t = (t + 1) & (cap - 1) }
            if tab[t] == 0 { dk.push(key); tab[t] = dk.len(); first[dk.len() - 1] = i; if want == 2 { cnt[dk.len() - 1] = 0 } }
            let g = tab[t] - 1;
            if want != 0 { gid[i] = g as u32; if want == 2 { cnt[g] += 1 } }
        }
    }
    let ng = if packed { dk.len() } else {
        dk = Vec::new();
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
pub fn grade_syms(_run: Runner, desc: bool, s: &Syms, out: &mut [i64]) {
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
                    grade_syms(crate::c::qlean_run_c, desc, &s, &mut out);
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
        assert!(!sym_whole(&Syms { blob: &b, offs: &o }, 1));
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
pub fn grade_ids(_run: Runner, desc: bool, n: usize, dict: &Syms, ids: &[u8], w: u32, out: &mut [i64]) {
    if n == 0 { return }
    let dk = dict_ranks(dict);
    let mut at = starts(&by_width!(w, rank_counts(ids, n, &dk, dk.len().max(1))), desc);
    by_width!(w, scatter(ids, n, &dk, &mut at, out))
}
/// sort.c:3136 `qlean_sort_sorted_ids`: the ids in dictionary order, into `out` (zeroed, `ids_bytes(n, w)` long) at `w` bits.
/// A rank's rows all name one id, so each rank is one `ids_fill` run; `rid` inverts the rank.
pub fn sorted_ids(_run: Runner, desc: bool, n: usize, dict: &Syms, ids: &[u8], w: u32, out: &mut [u8]) {
    if n == 0 { return }
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
                grade_ids(crate::c::qlean_run_c, desc, n, &d, &p, w, &mut out);
                assert_eq!(out, want);
                let mut s = vec![0u8; p.len()];
                sorted_ids(crate::c::qlean_run_c, desc, n, &d, &p, w, &mut s);
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
/// Stable grade of the keys `k`, ties in their original order whichever way `desc` runs.
/// needs A20: `grade_keys(run, k, desc, mn, mx, out)` is the radix grade; its Rust body is still a stub, so a stable sort answers.
fn grade_words(k: &[u64], desc: bool, out: &mut [i64]) {
    for (i, o) in out.iter_mut().enumerate() { *o = i as i64 }
    if desc { out.sort_by(|&a, &b| k[b as usize].cmp(&k[a as usize])) } else { out.sort_by_key(|&i| k[i as usize]) }
}
/// sort.c:3483 `qlean_sort_grade_guid` past the unboxing: two big-endian words, the low one graded first, so a stable grade
/// by the high word over that order is the order of the pair; the low pass runs only when two high words tie.
pub fn grade_guid(run: Runner, desc: bool, p: &[u8], out: &mut [i64]) {
    let n = out.len();
    if n == 0 { return }
    let mut k = vec![0u64; n];
    guid_words(p, n, 0, &[], &mut k);
    grade_words(&k, desc, out);
    if (1..n).any(|i| k[out[i] as usize] == k[out[i - 1] as usize]) {
        let mut lo = vec![0i64; n];
        guid_words(p, n, 8, &[], &mut k);
        grade_words(&k, desc, &mut lo);
        guid_words(p, n, 0, &lo, &mut k);
        grade_words(&k, desc, out);
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
                grade_guid(crate::c::qlean_run_c, desc, &p, &mut out);
                assert_eq!(out, want);
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
        grade_keys(crate::c::qlean_run_c, k, desc, mn, mx, &mut o);
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
        grade_src(crate::c::qlean_run_c, &s, false, true, 0, 2, &mut o);
        assert_eq!(o, vec![2, 0, 1]);
    }
}
