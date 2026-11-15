#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), sort.c: keys and their range (A19), the grades (A20–A22), pair and id grouping (A23–A24), symbol
//! sorts and groups (A25–A26), guids (A27). The `qlean_sort_*` entries unbox and allocate and stay C (§1).
//! A grade answers into `out: &mut [i64]` of `n`; `kind` is sort.c's `SK_*`.
use alloc::vec::Vec;

use crate::c::Runner;
use crate::coc::Coc;
use crate::sym::{sym_cmp, sym_hash, sym_msort, Syms};

/// sort.c:351 `ksrc`: the keys of a dense payload `p` or of an encoded column `c`, `n` of them.
#[derive(Clone, Copy)]
pub struct Ksrc<'a> { pub kind: u8, pub p: &'a [u8], pub c: Option<Coc<'a>>, pub n: usize }

// ---- A19: sort.c:183-400 (key_flip, keys_blk_foR, kwin_* are kwin.rs, B11) ----
/// sort.c:183 `keys_of`: every key of `p` into `k`; answers `(min, max)`.
pub fn keys_of(kind: u8, p: &[u8], n: usize, k: &mut [u64]) -> (u64, u64) { unimplemented!("A19: keys_of") }
/// sort.c:205 `keys_range`
pub fn keys_range(k: &[u64]) -> (u64, u64) { unimplemented!("A19: keys_range") }
impl<'a> Ksrc<'a> {
    /// sort.c:354 `ksrc_blk`: block `b`'s keys into `k` (BLK long); answers their count.
    pub fn blk(&self, b: usize, k: &mut [u64]) -> usize { unimplemented!("A19: ksrc_blk") }
    /// sort.c:394 `ksrc_range`
    pub fn range(&self) -> (u64, u64) { unimplemented!("A19: ksrc_range") }
}

// ---- A20: sort.c:417-730 ----
/// sort.c:417 `grade_runs`: the grade when the keys are a few ascending runs; false = not that shape.
pub fn grade_runs(k: &[u64], desc: bool, out: &mut [i64]) -> bool { unimplemented!("A20: grade_runs") }
/// sort.c:474 `grade_count`: counting sort over the key span `span`; `rank` answers ranks instead of the grade.
pub fn grade_count(s: &Ksrc, mn: u64, mx: u64, desc: bool, rank: bool, span: u64, out: &mut [i64]) {
    unimplemented!("A20: grade_count")
}
/// sort.c:498 `grade_perm`: the keys are a permutation of `mn ..= mx`; false = they are not.
pub fn grade_perm(s: &Ksrc, mn: u64, mx: u64, desc: bool, rank: bool, out: &mut [i64]) -> bool {
    unimplemented!("A20: grade_perm")
}
/// sort.c:555 `sk_digit`: the radix digit width for `bits`-bit keys and `n` of them.
pub fn sk_digit(bits: u32, n: usize) -> u32 { unimplemented!("A20: sk_digit") }
/// sort.c:682 `grade_radix`: LSD radix grade of keys `xr`-flipped minus `base`.
pub fn grade_radix(run: Runner, s: &Ksrc, span: u64, xr: u64, base: u64, out: &mut [i64]) { unimplemented!("A20: grade_radix") }
/// sort.c:713 `grade_src`: the grade (or ranks) of a key source, picking runs, permutation, count or radix.
pub fn grade_src(run: Runner, s: &Ksrc, desc: bool, rank: bool, mn: u64, mx: u64, out: &mut [i64]) {
    unimplemented!("A20: grade_src")
}
/// sort.c:724 `grade_keys`: `grade_src` over keys already made.
pub fn grade_keys(run: Runner, k: &[u64], desc: bool, mn: u64, mx: u64, out: &mut [i64]) { unimplemented!("A20: grade_keys") }

// ---- A21: sort.c:734-842 ----
/// sort.c:734 `grade_bits`: a bitmap's grade (zeros then ones, stable).
pub fn grade_bits(p: &[u8], n: usize, desc: bool, rank: bool, out: &mut [i64]) { unimplemented!("A21: grade_bits") }
/// sort.c:801 `hist_narrow`: the histogram of a 1- or 2-byte payload (256 or 65536 counts per slice).
pub fn hist_narrow(run: Runner, kind: u8, p: &[u8], n: usize) -> Vec<usize> { unimplemented!("A21: hist_narrow") }
/// sort.c:831 `grade_narrow`: counting grade of a 1- or 2-byte payload, threaded (`narrow_hist_run`, `narrow_scatter_run`).
pub fn grade_narrow(run: Runner, kind: u8, p: &[u8], n: usize, desc: bool, rank: bool, out: &mut [i64]) {
    unimplemented!("A21: grade_narrow")
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

// ---- A24: sort.c:2475-2550 ----
/// sort.c:2475 `qlean_sort_rank_slices` past the unboxing.
pub fn rank_slices(w: usize, v: &[u8], o: &[i64], out: &mut [i64]) { unimplemented!("A24: qlean_sort_rank_slices") }
/// sort.c:2509 `qlean_sort_group_sizes`: the size of each of `ng` groups of the ids `gid` (`n` at `w` bits).
pub fn group_sizes(ng: usize, w: u32, n: usize, gid: &[u8], out: &mut [i64]) { unimplemented!("A24: qlean_sort_group_sizes") }
/// sort.c:2522 `qlean_sort_group_lasts`: each group's last index.
pub fn group_lasts(ng: usize, w: u32, n: usize, gid: &[u8], out: &mut [i64]) { unimplemented!("A24: qlean_sort_group_lasts") }
/// sort.c:2536 `qlean_sort_id_longs`: `n` ids at `w` bits as longs.
pub fn id_longs(n: usize, w: u32, ids: &[u8], out: &mut [i64]) { unimplemented!("A24: qlean_sort_id_longs") }

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
    let ng = k.iter().max().map_or(0, |&m| m as usize + 1);
    let (mut c, mut at, mut acc) = (alloc::vec![0usize; ng], alloc::vec![0usize; ng], 0);
    for &r in &k { c[r as usize] += 1 }
    if desc { for r in (0..ng).rev() { at[r] = acc; acc += c[r] } } else { for r in 0..ng { at[r] = acc; acc += c[r] } }
    for (i, &r) in k.iter().enumerate() { out[at[r as usize]] = i as i64; at[r as usize] += 1 }
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
/// `f::<W>(args)` for the run-time width `w`, so `id_at`'s match folds as the C's `IDS_WIDTHS` does.
macro_rules! by_width {
    ($w:expr, $f:ident($($a:expr),*)) => { match $w {
        0 => $f::<0>($($a),*), 1 => $f::<1>($($a),*), 2 => $f::<2>($($a),*), 4 => $f::<4>($($a),*),
        8 => $f::<8>($($a),*), 16 => $f::<16>($($a),*), 32 => $f::<32>($($a),*), _ => $f::<64>($($a),*),
    } };
}
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
/// sort.c:3471 `guid_words`: the 8-byte word at byte `at` of each of `n` guids, in the order `perm`.
pub fn guid_words(p: &[u8], n: usize, at: usize, perm: &[i64], k: &mut [u64]) -> (u64, u64) { unimplemented!("A27: guid_words") }
/// sort.c:3483 `qlean_sort_grade_guid` past the unboxing.
pub fn grade_guid(run: Runner, desc: bool, p: &[u8], out: &mut [i64]) { unimplemented!("A27: qlean_sort_grade_guid") }
