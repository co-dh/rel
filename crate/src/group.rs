#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: group_ids_win still unimplemented (B11)
//! `dedup`'s `groupIds` arm (sort.c:2025, `gid` given, no `cnt`) and `ids_run` (sort.c:2006): number the groups on
//! one thread, then write each element's group id threaded at the lane `ng` fixes.
use alloc::borrow::Cow;
use alloc::vec;
use alloc::vec::Vec;

use crate::c::{run_map, Runner};
use crate::coc::Coc;
use crate::ids::id_width;
use crate::simd::prefetch;
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
    let mut s = (key.wrapping_mul(PHI64) >> sh) as usize;
    while gkey[slot[s] - 1] != key { s = (s + 1) & mask }
    slot[s] - 1
}

/// One monomorphic loop per lane width and table kind: `g` is the table lookup, inlined into the loop.
fn lanes<K: Keys, G: Fn(u64) -> usize + Sync + Copy>(run: Runner, k: &K, n: usize, lane: u32, gid: &mut [u8], g: G) {
    let f = |lo: usize, hi: usize, o: &mut [u8]| {
        let (mut k, g) = (k.fork(), g); // own copies: a captured reference reloads every row past the output stores
        match lane {
            8 => for (i, b) in (lo..hi).zip(o.iter_mut()) { *b = g(k.at(i)) as u8 },
            16 => for (i, b) in (lo..hi).zip(o.chunks_exact_mut(2)) { b.copy_from_slice(&(g(k.at(i)) as u16).to_ne_bytes()) },
            32 => for (i, b) in (lo..hi).zip(o.chunks_exact_mut(4)) { b.copy_from_slice(&(g(k.at(i)) as u32).to_ne_bytes()) },
            _ => for (i, b) in (lo..hi).zip(o.chunks_exact_mut(8)) { b.copy_from_slice(&(g(k.at(i)) as u64).to_ne_bytes()) },
        }
    };
    run_map(run, gid, n, lane as usize / 8, 4, 8, &f);
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

/// The numbering pass: groups in order of first occurrence, `first[g]` its first element; answers `ng` and the
/// table. None = an unknown kind or a misaligned `p`, which C never produces.
pub fn number(kind: u8, p: &[u8], n: usize, mn: u64, mx: u64, first: &mut [usize]) -> Option<(usize, Table<'static>)> {
    if first.len() < n { return None }
    each(kind, p, n, Number { mn, mx, first })
}

struct Number<'f> { mn: u64, mx: u64, first: &'f mut [usize] }
impl Pass for Number<'_> {
    type Out = (usize, Table<'static>);
    fn run<K: Keys>(self, mut k: K, n: usize) -> Self::Out {
        let (mn, first, span) = (self.mn, self.first, self.mx.wrapping_sub(self.mn));
        // a table of at most four slots an element, and group numbers that fit one
        if span < (n as u64).saturating_mul(4) + 1024 && span != u64::MAX && n <= u32::MAX as usize {
            let slots = span as usize + 1;
            let mut tab = vec![0u32; slots];
            let mut ng = 0;
            for i in 0..n {
                let d = (k.at(i) - mn) as usize;
                if tab[d] == 0 {
                    ng += 1;
                    tab[d] = ng as u32;
                    first[ng - 1] = i;
                    if ng == slots { break } // every slot filled: the rest cannot name a new group
                }
            }
            return (ng, Table::Direct { tab: Cow::Owned(tab), mn });
        }
        let cap = cap_for(n);
        let (mask, sh) = (cap - 1, 64 - cap.trailing_zeros());
        let mut slot = vec![0usize; cap];
        let mut gkey: Vec<u64> = Vec::with_capacity(n);
        for i in 0..n {
            if i + SK_AHEAD < n { prefetch(&slot[(k.at(i + SK_AHEAD).wrapping_mul(PHI64) >> sh) as usize]) }
            let key = k.at(i);
            let mut s = (key.wrapping_mul(PHI64) >> sh) as usize;
            while slot[s] != 0 && gkey[slot[s] - 1] != key { s = (s + 1) & mask }
            if slot[s] == 0 {
                gkey.push(key);
                slot[s] = gkey.len();
                first[gkey.len() - 1] = i;
            }
        }
        (gkey.len(), Table::Hashed { slot: Cow::Owned(slot), gkey: Cow::Owned(gkey), sh })
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
/// `mn`, `mx` from `kwin::range`.
pub fn group_ids_win(kind: u8, c: Coc, n: usize, mn: u64, mx: u64, gid: &mut [u8], first: &mut [usize]) -> usize {
    unimplemented!()
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
