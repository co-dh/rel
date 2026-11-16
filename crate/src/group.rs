#![forbid(unsafe_code)]
//! sort.c's `dedup` (the numbering of `distinct` and `group`, three engines: bitmap, direct, hashed, and the radix
//! partition), `gather`, and `groupIds`: `number` the groups on one thread, then `fill` each element's id threaded at the lane
//! `ng` fixes.
use alloc::borrow::Cow;
use alloc::vec;
use alloc::vec::Vec;

use crate::c::{run_map, Runner};
use crate::coc::Coc;
use crate::kwin::Kwin;
use crate::ids::id_width;
use crate::simd::prefetch;
use crate::pod::uninit;
use crate::key::{each, Keys, Pass};

pub const PHI64: u64 = 0x9e3779b97f4a7c15;
/// How many elements ahead the hashed numbering starts a slot's cache line (sort.c's `group_prefetch` users). The
/// sweep is flat -- 4.74 ms unprefetched at a million distinct longs, 4.03 at 32, 3.98 at 64 -- so 32 is where it
/// stops paying.
pub const SK_AHEAD: usize = 32;

/// `cap_for` (coc.h:387): the least power of two, at least 8, holding `n` keys at load 1/2.
pub fn cap_for(n: usize) -> usize { n.saturating_mul(2).next_power_of_two().max(8) }

/// `group_find` (sort.c:1985): a key the numbering has already put in the table.
fn find(slot: &[usize], gkey: &[u64], sh: u32, key: u64) -> usize {
    let mask = slot.len() - 1;
    let mut s = (key.wrapping_mul(PHI64) >> sh) as usize & mask;
    while gkey[slot[s] - 1] != key { s = (s + 1) & mask }
    slot[s] - 1
}

/// One monomorphic loop per lane width and table kind: `g` is the table lookup, inlined into the loop.
fn lanes<K: Keys, G: Fn(u64) -> usize + Sync + Copy>(run: Runner, k: &K, n: usize, lane: u32, gid: &mut [u8], g: G) {
    let f = |lo: usize, hi: usize, o: &mut [u8]| {
        let (mut k, g) = (k.fork(), g); // own copies: a captured reference reloads every row past the output stores
        assert!(hi <= k.len(), "qlean group: ids over keys {lo}..{hi} of a source holding {}", k.len());
        match lane {
            8 => for (i, b) in (lo..hi).zip(o.iter_mut()) { *b = g(k.at(i)) as u8 },
            16 => for (i, b) in (lo..hi).zip(o.chunks_exact_mut(2)) { b.copy_from_slice(&(g(k.at(i)) as u16).to_ne_bytes()) },
            32 => for (i, b) in (lo..hi).zip(o.chunks_exact_mut(4)) { b.copy_from_slice(&(g(k.at(i)) as u32).to_ne_bytes()) },
            _ => for (i, b) in (lo..hi).zip(o.chunks_exact_mut(8)) { b.copy_from_slice(&(g(k.at(i)) as u64).to_ne_bytes()) },
        }
    };
    run_map(run, gid, n, lane as usize / 8, crate::QLEAN_COST_ARITH, 8, &f);
}

struct Fill<'t, 'a, 'g> { run: Runner, t: &'t Table<'a>, lane: u32, gid: &'g mut [u8] }
impl Pass for Fill<'_, '_, '_> {
    type Out = ();
    fn run<K: Keys>(self, k: K, n: usize) {
        match self.t {
            Table::Direct { tab, mn } => {
                let (tab, mn): (&[u32], u64) = (tab, *mn);
                lanes(self.run, &k, n, self.lane, self.gid, move |key| (tab[(key - mn) as usize] - 1) as usize)
            }
            Table::Hashed { slot, gkey, sh } => {
                let (slot, gkey, sh): (&[usize], &[u64], u32) = (slot, gkey, *sh);
                lanes(self.run, &k, n, self.lane, self.gid, move |key| find(slot, gkey, sh, key))
            }
        }
    }
}

/// The numbering's table. Borrowed when C built it (`qrs_group_fill`), owned when `number` did.
/// `Direct`: `tab[key - mn]` is the group + 1, 0 = none yet. `Hashed`: `slot` is a power of two long, `slot[s]` is
/// the group + 1 whose key `gkey[group]` hashes to `s` (`(key * PHI64) >> sh`, linear probing).
pub enum Table<'a> {
    Direct { tab: Cow<'a, [u32]>, mn: u64 },
    Hashed { slot: Cow<'a, [usize]>, gkey: Cow<'a, [u64]>, sh: u32 },
}

impl Table<'_> {
    /// The group of a key the numbering has put in the table.
    pub fn at(&self, key: u64) -> usize {
        match self {
            Table::Direct { tab, mn } => (tab[(key - mn) as usize] - 1) as usize,
            Table::Hashed { slot, gkey, sh } => find(slot, gkey, *sh, key),
        }
    }
}

/// What a numbering pass does with the group an element fell in -- the consumer's shape (sort.c's `SK_GID_*` and
/// `SK_NEW_*`), a type and not a test in the loop: `Nothing` for `distinct`, `Bucket` for `group`, whose `gid` is
/// scratch of four bytes an element and whose `cnt` is counted by the pass that numbers the groups.
pub trait Put {
    /// `Bucket` writes `gid`, so a pass that has seen every slot cannot stop early on its account.
    const BUCKET: bool;
    fn new(&mut self, g: usize);
    fn put(&mut self, i: usize, g: usize);
    /// The scratch cut to `n` entries, so a loop over `0..n` sees the length and drops the bounds test on `gid[i]`.
    fn fit(&mut self, n: usize);
    fn parts(&mut self) -> (&mut [u32], &mut [u32]);
}
pub struct Nothing;
impl Put for Nothing {
    const BUCKET: bool = false;
    #[inline(always)] fn new(&mut self, _: usize) {}
    #[inline(always)] fn put(&mut self, _: usize, _: usize) {}
    fn fit(&mut self, _: usize) {}
    fn parts(&mut self) -> (&mut [u32], &mut [u32]) { (&mut [], &mut []) }
}
pub struct Bucket<'a> { pub gid: &'a mut [u32], pub cnt: &'a mut [u32] }
impl Put for Bucket<'_> {
    const BUCKET: bool = true;
    // zeroed where the group is made, beside its `first`: `cnt` arrives unwritten, and one test in the loop's new-group
    // arm moves the whole arm out of line
    #[inline(always)] fn new(&mut self, g: usize) { self.cnt[g] = 0 }
    #[inline(always)] fn put(&mut self, i: usize, g: usize) { self.gid[i] = g as u32; self.cnt[g] += 1 }
    #[inline(always)] fn fit(&mut self, n: usize) {
        let (g, c) = (core::mem::take(&mut self.gid), core::mem::take(&mut self.cnt));
        (self.gid, self.cnt) = (&mut g[..n], &mut c[..n]);
    }
    fn parts(&mut self) -> (&mut [u32], &mut [u32]) { (self.gid, self.cnt) }
}

/// The direct table is at most four slots an element, and a group number has to fit its `u32` slot.
fn direct_ok(span: u64, n: usize) -> bool { span < (n as u64).saturating_mul(4) + 1024 && span != u64::MAX && n <= u32::MAX as usize }
fn shift(cap: usize) -> u32 { 64 - cap.trailing_zeros() }

/// `SK_DIRECT`: the table is indexed by `key - mn` and a probe is one load. Answers `ng` and the table.
fn direct<K: Keys, P: Put>(mut k: K, n: usize, mn: u64, span: u64, first: &mut [usize], mut put: P) -> (usize, Vec<u32>) {
    put.fit(n);
    // the cut slice and `min` carry the bounds of `first[ng - 1]`, `k.at(i)` and the scratch; `t` is the one test of `tab`
    let (n, first) = (n.min(k.len()), &mut first[..n]);
    let slots = span as usize + 1;
    let mut tab = vec![0u32; slots];
    let mut ng = 0;
    for i in 0..n {
        let t = &mut tab[k.at(i).wrapping_sub(mn) as usize];
        if *t == 0 {
            ng += 1;
            *t = ng as u32;
            first[ng - 1] = i;
            put.new(ng - 1);
            if !P::BUCKET && ng == slots { break } // every slot filled: the rest cannot name a new group
        }
        put.put(i, *t as usize - 1);
    }
    (ng, tab)
}

/// `SK_HASHED` over the first `end` elements: `slot` (a power of two long) holds group + 1, `gkey[g]` is its key, linear
/// probing from `(key * PHI64) >> shift`; each element's slot is prefetched `SK_AHEAD` before its probe. Answers `ng`;
/// `gkey` and `first` hold `end` entries, written before they are read.
fn hashed<K: Keys, P: Put>(mut k: K, end: usize, slot: &mut [usize], gkey: &mut [u64], first: &mut [usize], mut put: P) -> usize {
    put.fit(end);
    // the cut slices and `min` carry the bounds, so the loop tests only `slot` and `gkey` at a probe; the mask is the
    // shift's own range, said where LLVM can see that it is a bound
    let (end, first, gkey) = (end.min(k.len()), &mut first[..end], &mut gkey[..end]);
    let (mask, sh, mut ng) = (slot.len() - 1, shift(slot.len()), 0);
    for i in 0..end {
        if i + SK_AHEAD < end { prefetch(&slot[(k.at(i + SK_AHEAD).wrapping_mul(PHI64) >> sh) as usize & mask]) }
        let key = k.at(i);
        let mut s = (key.wrapping_mul(PHI64) >> sh) as usize & mask;
        let g = loop {
            let g = slot[s];
            if g == 0 {
                (gkey[ng], slot[s], first[ng]) = (key, ng + 1, i);
                put.new(ng);
                ng += 1;
                break ng;
            }
            if gkey[g - 1] == key { break g }
            s = (s + 1) & mask;
        };
        put.put(i, g - 1);
    }
    ng
}

/// The numbering pass: groups in order of first occurrence, `first[g]` its first element; answers `ng` and the table.
/// None = an unknown kind or a misaligned `p`, which C never produces.
pub fn number(kind: u8, p: &[u8], n: usize, mn: u64, mx: u64, first: &mut [usize]) -> Option<(usize, Table<'static>)> {
    if first.len() < n { return None }
    each(kind, p, n, Number { mn, mx, first })
}

struct Number<'f> { mn: u64, mx: u64, first: &'f mut [usize] }
impl Pass for Number<'_> {
    type Out = (usize, Table<'static>);
    fn run<K: Keys>(self, k: K, n: usize) -> Self::Out {
        assert!(n <= k.len(), "qlean group: number over {n} keys of a source holding {}", k.len());
        let (mn, first, span) = (self.mn, self.first, self.mx.wrapping_sub(self.mn));
        if direct_ok(span, n) {
            let (ng, tab) = direct(k, n, mn, span, first, Nothing);
            return (ng, Table::Direct { tab: Cow::Owned(tab), mn });
        }
        let cap = cap_for(n);
        let (mut slot, mut gkey) = (vec![0usize; cap], uninit::<u64>(n));
        let ng = hashed(k, n, &mut slot, &mut gkey, first, Nothing);
        gkey.truncate(ng);
        (ng, Table::Hashed { slot: Cow::Owned(slot), gkey: Cow::Owned(gkey), sh: shift(cap) })
    }
}

/// Where the partitioned pass runs: a column this long, and the hashed loop's first `SK_PART_PREFIX` elements measure how
/// many of them were new.
const SK_PART_MIN: usize = 1 << 19;
const SK_PART_PREFIX: usize = 1 << 16;

/// Twelve bytes and not sixteen: the scatter writes one an element and the marking pass reads them all back, so the
/// four bytes of padding are 8MB of traffic at a million elements across the two. `at` is `u32` because the pass only
/// runs below `u32::MAX` rows.
#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct KeyAt { key: u64, at: u32 }

/// `part_dedup`: distinct by radix partition. The keys are scattered into `2^kb` buckets by the hash's top bits, each
/// bucket then probes a table of its own that stays in L1, and a new group in a bucket sets a bit at the element's own
/// index, so the walk of the bitmap finds the first occurrences in index order. With `GID` (`group`) the bucket pass
/// writes each element's group's first-occurrence index into `gid` and a last pass maps it to the group number.
#[inline(never)] // one copy per key type and mode, and a symbol `reach.sh` can break on
fn part<K: Keys, const GID: bool>(mut k: K, n: usize, first: &mut [usize], gid: &mut [u32], cnt: &mut [u32]) -> usize {
    let (n, mut kb) = (n.min(k.len()), 6u32);
    while kb < 10 && (1usize << (kb + 11)) < n { kb += 1 }
    let (nb, nblk) = (1usize << kb, n.div_ceil(64));
    let mut at = vec![0usize; nb + 1];
    let mut buf = uninit::<KeyAt>(n);
    let mut mark = vec![0u64; nblk];
    let mut rank = if GID { uninit::<u32>(n) } else { Vec::new() };
    // `& (nb - 1)` is the shift's own range, said where LLVM can see it is a bound of `at`
    for i in 0..n { at[(k.at(i).wrapping_mul(PHI64) >> (64 - kb)) as usize & (nb - 1)] += 1 }
    let bmax = at[..nb].iter().copied().max().unwrap_or(0);
    let mut bb = 3u32;
    while (1usize << bb) < bmax * 2 { bb += 1 }
    let bcap = 1usize << bb;
    let mut tab = uninit::<u32>(bcap);
    let mut run = 0;
    for c in &mut at[..nb] { let c0 = *c; *c = run; run += c0 }
    for i in 0..n {
        let key = k.at(i);
        let d = &mut at[(key.wrapping_mul(PHI64) >> (64 - kb)) as usize & (nb - 1)];
        buf[*d] = KeyAt { key, at: i as u32 };
        *d += 1;
    }
    // the scatter left `at[b]` one past bucket `b`, so the buckets are the runs it cuts
    let mut lo = 0;
    for b in 0..nb {
        let hi = at[b];
        if hi == lo { continue }
        tab.fill(0);
        let run = &buf[lo..hi];
        for (j, e) in run.iter().enumerate() {
            let (key, ai) = (e.key, e.at as usize);
            let mut s = (key.wrapping_mul(PHI64) >> (64 - kb - bb)) as usize & (bcap - 1);
            while tab[s] != 0 && run[tab[s] as usize - 1].key != key { s = (s + 1) & (bcap - 1) }
            if tab[s] == 0 {
                tab[s] = (j + 1) as u32;
                mark[ai >> 6] |= 1 << (ai & 63);
            }
            if GID { gid[ai] = run[tab[s] as usize - 1].at }
        }
        lo = hi;
    }
    let mut w = 0;
    for (blk, &m) in mark.iter().enumerate() {
        let mut m = m;
        while m != 0 {
            let x = blk * 64 + m.trailing_zeros() as usize;
            first[w] = x;
            if GID { rank[x] = w as u32 }
            w += 1;
            m &= m - 1;
        }
    }
    if GID {
        cnt[..w].fill(0);
        for g in gid[..n].iter_mut() { *g = rank[*g as usize]; cnt[*g as usize] += 1 }
    }
    w
}

/// Calling it marks the branch it is in unlikely, which rustc 1.93 has no stable hint for: it puts the word switch out of
/// the way of the run of keys in one word, as sort.c's loop is laid out.
#[cold] #[inline(never)] fn cold() {}

/// The `distinct` engine over a range of at most 64 slots an element: the table is a bitmap, a 64th of the direct table's
/// bytes. Answers `ng`.
fn bitmap<K: Keys>(mut k: K, n: usize, span: u64, mn: u64, first: &mut [usize]) -> usize {
    // `min` and the cut slices state the bounds the loop's indexes need, so no test stays in it
    let (n, first) = (n.min(k.len()), &mut first[..n]);
    let slots = span as usize + 1;
    let mut bm = vec![0u64; (span / 64) as usize + 1];
    let cap = slots.min(n);
    let mut rest = &mut first[..cap];
    let (mut cw, mut cv) = (0usize, bm[0]);
    // the word last touched is held in `cv` and written back only when the walk leaves it: a column with locality
    // would otherwise read each word straight after its own store. `rest` is the part of `first` not yet written: no
    // count to keep beside it, and it runs out exactly when every slot is seen (or at the last element, which ends the loop)
    for i in 0..n {
        let d = k.at(i).wrapping_sub(mn);
        let m = 1u64 << (d & 63);
        if (d >> 6) as usize != cw { cold(); bm[cw] = cv; cw = (d >> 6) as usize; cv = bm[cw] }
        if cv & m == 0 {
            cv |= m;
            let Some((o, r)) = core::mem::take(&mut rest).split_first_mut() else { unreachable!("qlean group: more groups than slots") };
            (*o, rest) = (i, r);
            if rest.is_empty() { break }
        }
    }
    cap - rest.len()
}

/// `dedup`: `first[..ng]` the first occurrence of each distinct key in order of first occurrence, and answers `ng`;
/// under `Bucket` also each element's group in `gid` and the group sizes in `cnt`. `mn`, `mx` the keys' range (it only
/// chooses the engine). `first` and `gid` / `cnt` hold `n` entries.
pub fn dedup<K: Keys, P: Put>(k: K, n: usize, mn: u64, mx: u64, first: &mut [usize], mut put: P) -> usize {
    if n == 0 { return 0 }
    assert!(n <= k.len() && first.len() >= n, "qlean group: dedup over {n} keys of a source holding {}, first {}", k.len(), first.len());
    let span = mx.wrapping_sub(mn);
    // `distinct` asks only whether a key was seen -- a bit, so the table is a bitmap over the range, a 64th of the direct
    // table's bytes, which serves a range of up to 64 slots an element and not 4
    if !P::BUCKET && span != u64::MAX && span / 64 < n as u64 { return bitmap(k, n, span, mn, first) }
    if direct_ok(span, n) { return direct(k, n, mn, span, first, put).0 }
    // `part_dedup` carries an element index in four bytes, so a longer column stays on the hashed loop
    let part_ok = n >= SK_PART_MIN && n <= u32::MAX as usize;
    if part_ok {
        // the first `2^16` elements of the hashed loop are the estimate of the distinct count: `ng / 2^16` is `1 - 2^16/2d`
        // for `d` roughly equal values, so 15/16 puts `d` at half a million, where a slot per value stops fitting the L3
        // and the partition measured ahead. Its table is sized for the estimate, not the column.
        let (mut slot, mut gkey) = (vec![0usize; cap_for(SK_PART_PREFIX)], uninit::<u64>(SK_PART_PREFIX));
        let ng = hashed(k.fork(), SK_PART_PREFIX, &mut slot, &mut gkey, first, Nothing);
        if ng * 16 >= SK_PART_PREFIX * 15 {
            let (gid, cnt) = put.parts();
            return if P::BUCKET { part::<K, true>(k, n, first, gid, cnt) } else { part::<K, false>(k, n, first, gid, cnt) };
        }
    }
    let (mut slot, mut gkey) = (vec![0usize; cap_for(n)], uninit::<u64>(n));
    hashed(k, n, &mut slot, &mut gkey, first, put)
}

/// `dedup`'s kind switch: a dense column through `key::each`, an encoded one through `Kwin`.
pub struct Dedup<'a> { pub mn: u64, pub mx: u64, pub first: &'a mut [usize], pub bucket: Option<(&'a mut [u32], &'a mut [u32])> }
impl Pass for Dedup<'_> {
    type Out = usize;
    fn run<K: Keys>(self, k: K, n: usize) -> usize {
        match self.bucket {
            None => dedup(k, n, self.mn, self.mx, self.first, Nothing),
            Some((gid, cnt)) => {
                assert!(gid.len() >= n && cnt.len() >= n, "qlean group: dedup scratch holds {} and {}, wants {n}", gid.len(), cnt.len());
                dedup(k, n, self.mn, self.mx, self.first, Bucket { gid, cnt })
            }
        }
    }
}

/// `gather`: the elements at `first` written back at their own width (a bit as a whole byte), not rebuilt from the key,
/// which keeps `distinct (-0.0;0.0;-0.0)` answering `-0f`. `out` is `first.len() * width` bytes. None = a short `out`,
/// a `p` too short for `first`, or an unknown kind.
pub fn gather(kind: u8, p: &[u8], first: &[usize], out: &mut [u8]) -> Option<()> {
    use crate::key::{SK_BIT, SK_C8, SK_F32, SK_F64, SK_I16, SK_I32, SK_I64, SK_U8};
    fn go<T: crate::pod::Pod>(p: &[u8], first: &[usize], out: &mut [u8]) -> Option<()> {
        let (q, o) = (crate::pod::cast::<T>(p)?, crate::pod::cast_mut::<T>(out)?);
        if o.len() != first.len() { return None }
        for (o, &f) in o.iter_mut().zip(first) { *o = *q.get(f)? }
        Some(())
    }
    match kind {
        SK_BIT => {
            if out.len() != first.len() { return None }
            for (o, &f) in out.iter_mut().zip(first) { *o = (p.get(f >> 3)? >> (f & 7)) & 1 }
            Some(())
        }
        SK_U8 | SK_C8 => go::<u8>(p, first, out),
        SK_I16 => go::<u16>(p, first, out),
        SK_I32 | SK_F32 => go::<u32>(p, first, out),
        SK_I64 | SK_F64 => go::<u64>(p, first, out),
        _ => None,
    }
}

/// `ids_run`: element `i`'s group into `gid` at `lane` (8, 16, 32 or 64) bits, threaded by `c::run_map`. False =
/// an unknown kind, or `gid` shorter than `n * lane / 8`.
pub fn fill(run: Runner, kind: u8, p: &[u8], n: usize, t: &Table, lane: u32, gid: &mut [u8]) -> bool {
    if !matches!(lane, 8 | 16 | 32 | 64) || n.checked_mul(lane as usize / 8).is_none_or(|b| b > gid.len()) { return false }
    each(kind, p, n, Fill { run, t, lane, gid }).is_some()
}

/// `number` then `fill` at `max(8, id_width(ng))`: answers `ng`.
pub fn group_ids(run: Runner, kind: u8, p: &[u8], n: usize, mn: u64, mx: u64, gid: &mut [u8], first: &mut [usize])
    -> Option<usize> {
    if n == 0 { return Some(0) }
    let (ng, t) = number(kind, p, n, mn, mx, first)?;
    fill(run, kind, p, n, &t, id_width(ng).max(8), gid).then_some(ng)
}

/// `group_ids` over an encoded column's keys, read through `kwin::Kwin` (`qlean_sort_group_ids_foR`, sort.c:2685);
/// `mn`, `mx` from `kwin::range`. `gid` holds `n` ids at the lane `max(8, id_width(ng))` fixes. A refusal (`gid` too
/// short for that lane, `first` shorter than `n`) is None: C aborts.
pub fn group_ids_win(run: Runner, kind: u8, c: Coc, n: usize, mn: u64, mx: u64, gid: &mut [u8], first: &mut [usize])
    -> Option<usize> {
    if n == 0 { return Some(0) }
    if first.len() < n { return None }
    let (ng, t) = Number { mn, mx, first }.run(Kwin::new(kind, c), n);
    let lane = id_width(ng).max(8);
    if n.checked_mul(lane as usize / 8)? > gid.len() { return None }
    Fill { run, t: &t, lane, gid }.run(Kwin::new(kind, c), n);
    Some(ng)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::key::SK_KEY;
    // expected values: /data/tmp/qrs/B4/drv.c (sort.c's group_find over the slot table it prints), run
    const K: [u64; 8] = [30, 10, 30, 20, 10, 1_000_000_007, 20, 1_000_000_007];
    const IDS: [usize; 8] = [0, 1, 0, 2, 1, 3, 2, 3];
    fn keys() -> Vec<u8> { K.iter().flat_map(|k| k.to_ne_bytes()).collect() }
    fn hashed() -> Table<'static> {
        Table::Hashed { slot: Cow::Owned(vec![4, 2, 3, 0, 1, 0, 0, 0]), gkey: Cow::Owned(vec![30, 10, 20, 1_000_000_007]),
                        sh: 61 }
    }
    fn ids(g: &[u8], lane: u32) -> Vec<usize> {
        g.chunks_exact(lane as usize / 8).map(|c| match lane {
            8 => c[0] as usize, 16 => u16::from_ne_bytes(c.try_into().unwrap()) as usize,
            32 => u32::from_ne_bytes(c.try_into().unwrap()) as usize, _ => u64::from_ne_bytes(c.try_into().unwrap()) as usize,
        }).collect()
    }
    #[test] fn hashed_every_lane() {
        for lane in [8u32, 16, 32, 64] {
            let mut g = vec![0xffu8; 8 * lane as usize / 8];
            assert!(fill(crate::c::qlean_run_c, SK_KEY, &keys(), 8, &hashed(), lane, &mut g));
            assert_eq!(ids(&g, lane), IDS, "lane {lane}");
        }
    }
    #[test] fn direct_every_lane() {
        let mut tab = vec![0u32; 21];
        tab[20] = 1; tab[0] = 2; tab[10] = 3;
        let t = Table::Direct { tab: Cow::Owned(tab), mn: 10 };
        let k: Vec<u8> = [30u64, 10, 30, 20, 10].iter().flat_map(|k| k.to_ne_bytes()).collect();
        for lane in [8u32, 16, 32, 64] {
            let mut g = vec![0xffu8; 5 * lane as usize / 8];
            assert!(fill(crate::c::qlean_run_c, SK_KEY, &k, 5, &t, lane, &mut g));
            assert_eq!(ids(&g, lane), [0, 1, 0, 2, 1], "lane {lane}");
        }
    }
    #[test] fn number_hashed_matches_c() {
        let mut first = [9usize; 8];
        let (ng, t) = number(SK_KEY, &keys(), 8, 10, 1_000_000_007, &mut first).unwrap();
        assert_eq!((ng, &first[..4]), (4, &[0, 1, 3, 5][..]));
        let Table::Hashed { slot, gkey, sh } = t else { panic!("range 1e9 is hashed") };
        assert_eq!((&slot[..], &gkey[..], sh), (&[0, 4, 2, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0][..], &[30, 10, 20, 1_000_000_007][..], 60));
    }
    #[test] fn number_direct_and_group_ids() {
        let k: Vec<u8> = [30u64, 10, 30, 20, 10].iter().flat_map(|k| k.to_ne_bytes()).collect();
        let mut first = [0usize; 5];
        let (ng, t) = number(SK_KEY, &k, 5, 10, 30, &mut first).unwrap();
        assert!(matches!(t, Table::Direct { .. }));
        assert_eq!((ng, &first[..3]), (3, &[0, 1, 3][..]));
        let mut g = [0xffu8; 5];
        assert_eq!(group_ids(crate::c::qlean_run_c, SK_KEY, &k, 5, 10, 30, &mut g, &mut first), Some(3));
        assert_eq!(g, [0, 1, 0, 2, 1]);
        assert_eq!(group_ids(crate::c::qlean_run_c, SK_KEY, &[], 0, 0, 0, &mut [], &mut []), Some(0));
        assert_eq!(group_ids(crate::c::qlean_run_c, crate::key::SK_WIN, &k, 5, 10, 30, &mut g, &mut first), None);
    }
    // expected values: sort.c's `distinct 3 1 3 2 1` is `3 1 2` and `group 9 1 9` is `9 1!(0 2;,1)` (the C's comments)
    fn dd(k: &[u64], mn: u64, mx: u64, bucket: bool) -> (usize, Vec<usize>, Vec<u32>, Vec<u32>) {
        let b = crate::pod::bytes(k);
        let (mut first, mut gid, mut cnt) = (vec![usize::MAX; k.len()], vec![u32::MAX; k.len()], vec![u32::MAX; k.len()]);
        let bk = bucket.then(|| (&mut gid[..], &mut cnt[..]));
        let ng = each(SK_KEY, b, k.len(), Dedup { mn, mx, first: &mut first, bucket: bk }).unwrap();
        (ng, first[..ng].to_vec(), gid, cnt[..ng].to_vec())
    }
    #[test] fn dedup_every_engine() {
        for scale in [1u64, 1000, 1_000_000_000_000] { // bitmap and direct, then hashed: the range grows past 64 slots an element
            let k: Vec<u64> = [3u64, 1, 3, 2, 1].iter().map(|x| x * scale).collect();
            let (mn, mx) = (scale, 3 * scale);
            assert_eq!(dd(&k, mn, mx, false).1, [0, 1, 3], "distinct, scale {scale}");
            let (ng, first, gid, cnt) = dd(&k, mn, mx, true);
            assert_eq!((ng, &first[..], &gid[..], &cnt[..]), (3, &[0usize, 1, 3][..], &[0u32, 1, 0, 2, 1][..], &[2u32, 2, 1][..]), "group, scale {scale}");
        }
        assert_eq!(dd(&[], 0, 0, true).0, 0);
        assert_eq!(dd(&[u64::MAX, 0, u64::MAX], 0, u64::MAX, false).1, [0, 1]); // a whole-range span skips the bitmap
    }
    #[test] fn dedup_partitioned() {
        let n = SK_PART_MIN + 3;
        let k: Vec<u64> = (0..n as u64).map(|i| (i * 7919) % n as u64 * 1_000_003 + 11).collect(); // all distinct, hashed, long
        let (mn, mx) = (*k.iter().min().unwrap(), *k.iter().max().unwrap());
        let (ng, first, ..) = dd(&k, mn, mx, false);
        assert_eq!((ng, first), (n, (0..n).collect::<Vec<_>>()));
        let (ng, first, gid, cnt) = dd(&k, mn, mx, true);
        assert!(ng == n && first.iter().enumerate().all(|(i, &f)| f == i) && gid.iter().enumerate().all(|(i, &g)| g as usize == i) && cnt.iter().all(|&c| c == 1));
    }
    #[test] fn gather_every_width() {
        let mut o = [0u8; 3];
        assert_eq!(gather(crate::key::SK_BIT, &[0b0000_0101, 0b10], &[0, 1, 9], &mut o), Some(()));
        assert_eq!(o, [1, 0, 1]);
        let p: Vec<u8> = [10u16, 20, 30].iter().flat_map(|x| x.to_ne_bytes()).collect();
        let mut o = [0u8; 4];
        assert_eq!(gather(crate::key::SK_I16, &p, &[2, 0], &mut o), Some(()));
        assert_eq!(o, [30, 0, 10, 0]);
        assert_eq!(gather(crate::key::SK_I16, &p, &[3], &mut [0; 2]), None);  // past the payload
        assert_eq!(gather(crate::key::SK_I16, &p, &[0], &mut [0; 1]), None);  // short out
        assert_eq!(gather(crate::key::SK_KEY, &p, &[0], &mut [0; 8]), None);  // no write width
    }
    #[test] fn refuses() {
        let mut g = vec![0u8; 64];
        assert!(!fill(crate::c::qlean_run_c, SK_KEY, &keys(), 8, &hashed(), 24, &mut g));       // lane
        assert!(!fill(crate::c::qlean_run_c, SK_KEY, &keys(), 8, &hashed(), 64, &mut g[..63])); // gid short
        assert!(!fill(crate::c::qlean_run_c, 99, &keys(), 8, &hashed(), 8, &mut g));            // unknown kind
        assert!(!fill(crate::c::qlean_run_c, crate::key::SK_WIN, &keys(), 8, &hashed(), 8, &mut g));
    }
    #[test] fn many_rows_split_across_workers() {
        let n = 300_000usize;
        let k: Vec<u8> = (0..n as u64).flat_map(|i| (i % 5).to_ne_bytes()).collect();
        let t = Table::Direct { tab: Cow::Owned((1..=5).collect()), mn: 0 };
        let mut g = vec![0u8; n];
        assert!(fill(crate::c::qlean_run_c, SK_KEY, &k, n, &t, 8, &mut g));
        assert!(g.iter().enumerate().all(|(i, &b)| b as usize == i % 5));
    }
}
