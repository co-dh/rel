#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), sort.c: keys and their range (A19), the grades (A20–A22), pair and id grouping (A23–A24), symbol
//! sorts and groups (A25–A26), guids (A27). The `qlean_sort_*` entries unbox and allocate and stay C (§1).
//! A grade answers into `out: &mut [i64]` of `n`; `kind` is sort.c's `SK_*`.
use alloc::vec;
use alloc::vec::Vec;

use crate::c::{run_map, Runner};
use crate::coc::{lanes, Coc};
use crate::key::{self, Keys, Pass, SK_BIT, SK_I16, SK_I32, SK_I64, SK_U8};
use crate::{pod, BLK, QLEAN_COST_ARITH};
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
/// sort.c `SK_LANE`: kind bit that makes `grade_narrow` read the payload as ids of `kind & 0x7f` bits.
const SK_LANE: u8 = 0x80;
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
        grade_src(run, &s, desc, rank, mn, mx, out)
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
        grade_src(run, &s, desc, rank, mn, mx, out)
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
        grade_keys(run, &k, desc, mn, mx, out)
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
