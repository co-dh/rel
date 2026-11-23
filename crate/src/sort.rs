#![forbid(unsafe_code)]
//! Column (a), sort.rs: keys and their range (A19), the grades (A20–A22), pair and id grouping (A23–A24), symbol
//! sorts and groups (A25–A26). The `qlean_sort_*` entries unbox and allocate and stay C (§1).
//! A grade answers into `out: &mut [i64]` of `n`; `kind` is sort.rs's `SK_*`.
use alloc::string::String;
use alloc::vec::Vec;
use crate::blocks::{Blocks, Src};

use crate::c::{run_map, Runner};
use crate::coc::{lanes, Coc};
use crate::key::{self, Keys, Pass, SK_C8, SK_I8, SK_I16, SK_I32, SK_I64, SK_U8};
use crate::pod::Elt;
use crate::{kwin, pod, QLEAN_COST_ARITH};

/// sort.rs `ksrc`: the keys of a dense payload `p` or of an encoded column `c`, `n` of them.
#[derive(Clone, Copy)]
pub struct Ksrc<'a> { pub kind: u8, pub p: &'a [u8], pub c: Option<Coc<'a>>, pub n: usize }

// ---- A19: sort.rs (key_flip, keys_blk_foR, kwin_* are kwin.rs, B11) ----
/// sort.rs:`SK_MM_*`: the least and greatest key in four independent accumulators, because one `lo`/`hi` pair makes the
/// compare a loop-carried chain a cycle long per element (measured in sort.rs, kept for the same reason).
pub struct Mm { lo: [u64; 4], hi: [u64; 4] }
impl Mm {
    fn new() -> Self { Mm { lo: [!0; 4], hi: [0; 4] } }
    #[inline(always)]
    fn four(&mut self, v: [u64; 4]) { for j in 0..4 { self.lo[j] = self.lo[j].min(v[j]); self.hi[j] = self.hi[j].max(v[j]) } }
    #[inline(always)]
    fn one(&mut self, v: u64) { self.lo[0] = self.lo[0].min(v); self.hi[0] = self.hi[0].max(v) }
    fn done(&self) -> (u64, u64) { (self.lo.into_iter().min().unwrap(), self.hi.into_iter().max().unwrap()) }
}
/// sort.rs `keys_range`: the same reduction over keys already written; `(0, 0)` for none.
pub fn keys_range(k: &[u64]) -> (u64, u64) {
    let (mut m, mut c) = (Mm::new(), k.chunks_exact(4));
    if k.is_empty() { return (0, 0) }
    for v in c.by_ref() { m.four([v[0], v[1], v[2], v[3]]) }
    for &v in c.remainder() { m.one(v) }
    m.done()
}
/// sort.rs:`SK_DENSE_BLK`: keys `[at, at + k.len())` of a dense payload.
pub struct Blk<'k> { at: usize, k: &'k mut [u64] }
impl Pass for Blk<'_> {
    type Out = ();
    #[inline(always)]
    fn run<K: Keys>(self, mut s: K, _: usize) { for (j, o) in self.k.iter_mut().enumerate() { *o = s.at(self.at + j) } }
}
impl<'a> Ksrc<'a> {
    /// This source's grid: the column's own blocks, or the writer's for a dense payload.
    pub fn grid(&self) -> Blocks<'a> { self.c.map_or(Blocks::new(Src::Dense(self.p), self.n), Blocks::from) }
    /// sort.rs `ksrc_blk`: block `b`'s keys into `k` (`grid().blk()` long); answers their count. A dense payload of any
    /// kind that is not an element kind (`SK_KEY`) is read as keys already.
    pub fn blk(&self, b: usize, k: &mut [u64]) -> usize {
        let (at, cnt) = self.grid().span(b);
        match &self.c {
            Some(c) => kwin::keys_blk(self.kind, c, b, &mut k[..cnt]),
            None => key::each(self.kind, &self.p[..key::bytes(self.kind, self.n).expect("ksrc_blk: dense kind")], self.n, Blk { at, k: &mut k[..cnt] })
                .unwrap_or_else(|| panic!("ksrc_blk: the payload of kind {} is misaligned", self.kind)),
        }
        cnt
    }
    /// sort.rs `ksrc_range`: off the block metadata for a pack, one pass over the keys for a dense payload;
    /// `(u64::MAX, 0)` for none, which is what the C's untouched accumulators answered.
    pub fn range(&self) -> (u64, u64) {
        if let Some(c) = &self.c { return kwin::range(self.kind, c) }
        if self.n == 0 { return (!0, 0) }
        key::each(self.kind, &self.p[..key::bytes(self.kind, self.n).expect("ksrc_range: dense kind")], self.n, key::Range)
            .unwrap_or_else(|| panic!("ksrc_range: the payload of kind {} is misaligned", self.kind))
    }
}

// ---- A20: sort.rs ----
/// sort.rs:`SK_KSRC_EACH`, a block at a time: `f(i, keys)` for the keys `i ..` of `s` in order. A key array is read in
/// place; a pack or a dense payload of elements goes through `Ksrc::blk`, so an encoded column's keys never exist whole.
#[inline(always)]
pub fn ksrc_blocks(s: &Ksrc, mut f: impl FnMut(usize, &[u64])) {
    if s.c.is_none() && s.kind == key::SK_KEY {
        let k = crate::pod::cast::<u64>(s.p).expect("ksrc_blocks: the key array is misaligned");
        for (b, ch) in k[..s.n].chunks(s.grid().blk()).enumerate() { f(b * s.grid().blk(), ch) }
    } else {
        let mut kb = pod::Scr::<u64>::new(s.grid().blk());
        for (b, at, _) in s.grid().walk() { let c = s.blk(b, &mut kb); f(at, &kb[..c]) }
    }
}
/// `f(i, key)` for every key of `s` in order.
#[inline(always)]
pub fn ksrc_each(s: &Ksrc, mut f: impl FnMut(usize, u64)) {
    ksrc_blocks(s, |at, ks| for (j, &v) in ks.iter().enumerate() { f(at + j, v) })
}
/// sort.rs `grade_runs`: the grade when the keys are a few ascending runs; false = not that shape. A run in the
/// asked-for order answers the identity, one strictly the other way the reversed identity (strictly: `2 2 1` is
/// non-increasing but its ascending grade is `2 0 1`, so a tie inside a descending run has to reach the sort).
pub fn grade_runs(k: &[u64], desc: bool, out: &mut [i64]) -> bool {
    let n = k.len();
    if k.windows(2).all(|w| if desc { w[1] <= w[0] } else { w[1] >= w[0] }) { for (i, o) in out[..n].iter_mut().enumerate() { *o = i as i64 } return true }
    if k.windows(2).all(|w| if desc { w[1] > w[0] } else { w[1] < w[0] }) { for (i, o) in out[..n].iter_mut().enumerate() { *o = (n - 1 - i) as i64 } return true }
    false
}
/// sort.rs:`SK_COUNT_MAX`: a counting table past this many buckets costs two cache misses an element to save a pass.
pub const SK_COUNT_MAX: u64 = 1 << 16;
/// sort.rs:`SK_COUNTABLE`: a table with one bucket per key is affordable (within twice the column and in cache).
pub fn sk_countable(span: u64, n: usize) -> bool { span < n as u64 * 2 + 1024 && span < SK_COUNT_MAX }
/// One bucket per value of `d(key)`: a single stable pass, no comparisons. `d` is recomputed from the key, not read
/// out of an array: the subtraction is one instruction, the array eight bytes an element written once and read twice.
/// `N` is the table length when it is one of the literals `grade_count` picks (0 = `nb`): `d(k) < nb <= N`, so masking
/// the index with `N - 1` changes nothing and lets the compiler see the index is in range (no bounds check).
pub fn count<C: Elt, const N: usize>(s: &Ksrc, nb: usize, rank: bool, d: impl Fn(u64) -> u64, out: &mut [i64]) -> Result<(), String> {
    let (len, m) = if N == 0 { (nb, usize::MAX) } else { (N, N - 1) };
    let mut cnt = pod::vec_of("asc", "a counting sort's buckets", len, C::default())?;
    ksrc_each(s, |_, k| { let c = &mut cnt[d(k) as usize & m]; *c = C::wrap(c.bits() + 1) });
    let mut at = 0;
    for c in cnt[..nb].iter_mut() { let t = c.bits() as usize; *c = C::wrap(at as u64); at += t }
    // the rank is where the grade would have put `i`: the same counter, stored the other way
    if rank { ksrc_each(s, |i, k| { let c = &mut cnt[d(k) as usize & m]; out[i] = c.bits() as usize as i64; *c = C::wrap(c.bits() + 1) }) }
    else { ksrc_each(s, |i, k| { let c = &mut cnt[d(k) as usize & m]; out[c.bits() as usize] = i as i64; *c = C::wrap(c.bits() + 1) }) }
    Ok(())
}
/// `count` at the table length that holds `nb` buckets: 256, 4096 or 65536 (what `sk_countable` allows), else `nb`.
pub fn count_by<C: Elt>(s: &Ksrc, nb: usize, rank: bool, d: impl Fn(u64) -> u64, out: &mut [i64]) -> Result<(), String> {
    if nb <= 256 { count::<C, 256>(s, nb, rank, d, out) }
    else if nb <= 4096 { count::<C, 4096>(s, nb, rank, d, out) }
    else if nb <= 65536 { count::<C, 65536>(s, nb, rank, d, out) }
    else { count::<C, 0>(s, nb, rank, d, out) }
}
/// sort.rs `grade_count`: counting sort over the key span `span`; `rank` answers ranks instead of the grade.
pub fn grade_count(s: &Ksrc, mn: u64, mx: u64, desc: bool, rank: bool, span: u64, out: &mut [i64]) -> Result<(), String> {
    let nb = span as usize + 1;
    match (s.n <= u32::MAX as usize, desc) {
        (true, true) => count_by::<u32>(s, nb, rank, |k| mx - k, out),
        (true, false) => count_by::<u32>(s, nb, rank, |k| k - mn, out),
        (false, true) => count_by::<usize>(s, nb, rank, |k| mx - k, out),
        (false, false) => count_by::<usize>(s, nb, rank, |k| k - mn, out),
    }
}
/// sort.rs `grade_perm`: the keys are a permutation of `mn ..= mx`; false = they are not. Inverting the permutation
/// reads each element once and writes each answer once; `seen` is a bitmap (125 KB at a million, stays in L2) and a
/// column that is not a permutation exits at its first repeated key. Under `rank` the answer is the narrowed key itself.
pub fn grade_perm(s: &Ksrc, mn: u64, mx: u64, desc: bool, rank: bool, out: &mut [i64]) -> Result<bool, String> {
    let mut seen = pod::vec_of("asc", "a permutation test's bitmap", s.n.div_ceil(64), 0u64)?;
    let (mut kb, mut ok, bl) = (pod::Scr::<u64>::new(s.grid().blk()), true, s.grid().blk());
    'blocks: for b in 0..s.n.div_ceil(bl) {
        let cnt = s.blk(b, &mut kb);
        for j in 0..cnt {
            let v = if desc { mx - kb[j] } else { kb[j] - mn }; // <= span == n-1, so `seen` holds it
            let w = &mut seen[(v >> 6) as usize];
            if (*w >> (v & 63)) & 1 != 0 { ok = false; break 'blocks }
            *w |= 1 << (v & 63);
            if rank { out[b * bl + j] = v as i64 } else { out[v as usize] = (b * bl + j) as i64 }
        }
    }
    Ok(ok)
}
/// sort.rs `sk_digit`: the radix digit width for `bits`-bit keys and `n` of them: 8 below 65536 elements (the
/// counter table is then the larger array), 14 above 48 bits, else the narrowest digit that takes the same number of
/// passes, rounded up into the closed set 10, 13, 16 (each a literal in `grade_radix`, so `nb` and `mask` are constants).
pub fn sk_digit(bits: u32, n: usize) -> u32 {
    if n < 65536 { return 8 }
    if bits > 48 { return 14 }
    let np = bits.div_ceil(16);
    let dig = bits.div_ceil(np);
    if dig <= 10 { 10 } else if dig <= 13 { 13 } else { 16 }
}
/// sort.rs `grade_radix`: LSD radix grade of keys `xr`-flipped minus `base` (`n >= 2`, `span` their range).
/// Every digit's histogram is taken in one read of the keys, which names the surviving passes first: the last writes
/// only the answer, and once what is left of the key fits beside the index (`ixb` bits) the two travel as one word.
pub fn grade_radix(s: &Ksrc, span: u64, xr: u64, base: u64, out: &mut [i64]) -> Result<(), String> {
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
pub fn radix<T: Elt, const D: u32>(s: &Ksrc, wid: u32, bits: u32, xr: u64, base: u64, out: &mut [i64]) -> Result<(), String> {
    let n = s.n;
    let dig = if D == 0 { wid } else { D };
    let (nb, mask) = (1usize << dig, (1u64 << dig) - 1);
    let np = bits.div_ceil(dig) as usize;
    let ixb = 64 - (n as u64 - 1).leading_zeros() as i32; // n >= 2: a run answered above
    let d = |k: u64| (k ^ xr).wrapping_sub(base);
    let mut cnt = pod::vec_of("asc", "a radix sort's digit counts", nb * np, T::default())?;
    let v0 = { let mut kb = pod::Scr::<u64>::new(s.grid().blk()); s.blk(0, &mut kb); d(kb[0]) };
    // one loop per digit over a block that is in L1, not np updates an element: the shift is a constant of its loop
    ksrc_blocks(s, |_, ks| for (p, c) in cnt.chunks_exact_mut(nb).enumerate() {
        for &k in ks { let x = &mut c[((d(k) >> (p as u32 * dig)) & mask) as usize]; *x = T::wrap(x.bits() + 1) }
    });
    let act: alloc::vec::Vec<usize> = (0..np).filter(|&p| cnt[p * nb + ((v0 >> (p as u32 * dig)) & mask) as usize].bits() as usize != n).collect();
    let na = act.len();
    if na == 0 { for (i, o) in out[..n].iter_mut().enumerate() { *o = i as i64 } return Ok(()) }
    let mut jp = (0..na - 1).find(|&j| bits as i32 - act[j + 1] as i32 * dig as i32 + ixb <= 64).unwrap_or(na - 1);
    let ixm = if jp + 1 < na { (((1u64 << (ixb - 1)) << 1)) - 1 } else { jp = na; 0 };
    // Two buffers serve both: a packed word is as wide as the key it replaces.
    let (mut ba, mut bb) = if na >= 2 { (pod::vec_of("asc", "a radix sort's key buffer", n, 0u64)?, pod::vec_of("asc", "a radix sort's key buffer", n, 0u64)?) } else { Default::default() };
    let (mut ia, mut ib) = if jp > 0 && na >= 2 { (pod::vec_of("asc", "a radix sort's index buffer", n, T::default())?, pod::vec_of("asc", "a radix sort's index buffer", n, T::default())?) } else { Default::default() };
    let (mut psh, mut packed) = (0u32, false);
    for j in 0..na {
        let sh = (act[j] as u32 * dig - psh) + if packed { ixb as u32 } else { 0 };
        let c = &mut cnt[act[j] * nb..][..nb];
        let mut at = 0;
        for x in c.iter_mut() { let t = x.bits() as usize; *x = T::wrap(at as u64); at += t }
        let slot = |c: &mut [T], v: u64| { let x = &mut c[((v >> sh) & mask) as usize]; let r = x.bits() as usize; *x = T::wrap(r as u64 + 1); r };
        if packed {
            if j + 1 == na { for i in 0..n { let w = ba[i]; out[slot(c, w)] = (w & ixm) as i64 } }
            else { for i in 0..n { let w = ba[i]; bb[slot(c, w)] = w } core::mem::swap(&mut ba, &mut bb) }
        } else if j + 1 == na {
            if j > 0 { for i in 0..n { out[slot(c, ba[i])] = ia[i].bits() as usize as i64 } }
            else { ksrc_each(s, |i, k| out[slot(c, d(k))] = i as i64) }
        } else if j == jp {
            psh = act[j + 1] as u32 * dig;
            if j > 0 { for i in 0..n { let v = ba[i]; bb[slot(c, v)] = ((v >> psh) << ixb) | ia[i].bits() as usize as u64 } }
            else { ksrc_each(s, |i, k| { let v = d(k); bb[slot(c, v)] = ((v >> psh) << ixb) | i as u64 }) }
            core::mem::swap(&mut ba, &mut bb);
            packed = true;
        } else {
            if j > 0 { for i in 0..n { let v = ba[i]; let t = slot(c, v); bb[t] = v; ib[t] = ia[i] } }
            else { ksrc_each(s, |i, k| { let v = d(k); let t = slot(c, v); bb[t] = v; ib[t] = T::wrap(i as u64) }) }
            core::mem::swap(&mut ba, &mut bb);
            core::mem::swap(&mut ia, &mut ib);
        }
    }
    Ok(())
}
/// sort.rs `grade_src`: the grade (or ranks) of a key source whose presorted shapes the caller has ruled out, by the
/// key range `mn ..= mx` alone (the caller's: whoever built the keys had them in a register): a counting sort where
/// `sk_countable` says the table is affordable, else the radix. Only the radix's rank needs its grade inverted.
pub fn grade_src(s: &Ksrc, desc: bool, rank: bool, mn: u64, mx: u64, out: &mut [i64]) -> Result<(), String> {
    let (n, span) = (s.n, mx - mn);
    if span == 0 { for (i, o) in out[..n].iter_mut().enumerate() { *o = if rank { 0 } else { i as i64 } } return Ok(()) }
    if span == n as u64 - 1 && grade_perm(s, mn, mx, desc, rank, out)? { return Ok(()) }
    if sk_countable(span, n) { return grade_count(s, mn, mx, desc, rank, span, out) }
    let mut g = if rank { pod::vec_of("asc", "a rank's grade", n, 0i64)? } else { Vec::new() };
    let o = if rank { &mut g[..] } else { &mut *out };
    if desc { grade_radix(s, span, !0, !mx, o)? } else { grade_radix(s, span, 0, mn, o)? }
    if rank { for (i, &x) in g.iter().enumerate() { out[x as usize] = i as i64 } }
    Ok(())
}
/// sort.rs `grade_keys`: `grade_src` over keys already made.
pub fn grade_keys(k: &[u64], desc: bool, mn: u64, mx: u64, out: &mut [i64]) -> Result<(), String> {
    if k.is_empty() || grade_runs(k, desc, out) { return Ok(()) }
    grade_src(&Ksrc { kind: key::SK_KEY, p: crate::pod::bytes(k), c: None, n: k.len() }, desc, false, mn, mx, out)
}


// ---- A21: sort.rs ----



// ---- A22: sort.rs ----
/// sort.rs `sk_ends`: a block's first and last key and whether it is ordered inside.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Ends { pub fst: i64, pub lst: i64, pub ok: bool }



/// sort.rs `asc_blk_foR`: block `b`'s own order and its ends, read off the residuals without decoding. A block's
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
    let cnt = crate::blocks::Blocks::from(*c).span(b).1;
    // a patched block is decoded and re-biased: residuals compare unsigned, so `v ^ sign` over a base of INT64_MIN
    // keeps signed order, and `base + r` is `v` again
    let (base, r) = if c.blk_nexc(b) > 0 {
        let mut dec = pod::Scr::<i64>::new(c.meta.blk());
        c.decode_blk(b, cnt, &mut dec);
        (1u64 << 63, walk(cnt, desc, strict, |j| dec[j] as u64 ^ (1 << 63)))
    } else {
        let at = c.meta.off[b] as usize;
        let mut w = c.meta.w(b);
        let mut lb = pod::Scr::<u64>::new(c.meta.blk());
        let p = lanes(&c.pack[at..at + c.meta.blk() * w as usize / 8], &mut w, cnt, pod::bytes_mut(&mut lb));
        fn ends_at<const W: u32>(p: &[u8], cnt: usize, desc: bool, strict: bool) -> Option<(u64, u64)> {
            walk(cnt, desc, strict, |j| crate::ids::lane::<W>(p, j))
        }
        // a zero-width block is its base repeated, which is not a strict order past one element
        let r = if w == 0 && strict && cnt > 1 { None } else { crate::by_width!(w, ends_at(p, cnt, desc, strict)) };
        (c.frame(b), r)
    };
    match r {
        Some((r0, rl)) => Ends { fst: base.wrapping_add(r0) as i64, lst: base.wrapping_add(rl) as i64, ok: true },
        None => Ends { fst: 0, lst: 0, ok: false },
    }
}
/// sort.rs `qlean_sort_ascending_foR` past the unboxing, threaded (`asc_run`). The blocks are checked apart, by
/// block across the pool, and the pairs between them afterwards from their ends; the first block goes alone and first,
/// so a column that is not sorted still leaves inside it. `kind` is one `ffi::sort::for_kind` admits.
pub fn ascending_enc(run: Runner, kind: u8, desc: bool, strict: bool, c: &Coc) -> Result<bool, String> {
    debug_assert!(matches!(kind, SK_U8 | SK_C8 | SK_I8 | SK_I16 | SK_I32 | SK_I64));
    let nb = c.meta.nblk;
    if c.meta.n == 0 { return Ok(true) }
    let f = asc_blk(c, 0, desc, strict);
    if !f.ok || nb == 1 { return Ok(f.ok) }
    // block `b >= 1` lands at words `3(b-1)..3b` as (fst, lst, ok); `ok` is written last, so a block a worker never
    // reached (it stops at its first block out of order) reads as out of order
    let mut e = pod::vec_of("asc", "the key blocks' ends", 3 * (nb - 1), 0u64)?;
    let rest = c.blocks(1, nb);
    run_map(run, pod::bytes_mut(&mut e), nb - 1, 24, QLEAN_COST_ARITH, c.meta.blk() * 8, &|lo, hi, o: &mut [u8]| {
        let o = pod::cast_mut::<u64>(o).expect("ascending_enc: the block ends are misaligned");
        for (k, b) in (lo..hi).enumerate() {
            let r = asc_blk(&rest, b, desc, strict);
            if !r.ok { return }
            o[3 * k] = r.fst as u64; o[3 * k + 1] = r.lst as u64; o[3 * k + 2] = 1;
        }
    });
    // between each pair of neighbours: the last of one against the first of the next
    let ends = |b: usize| if b == 0 { (f.fst, f.lst, true) } else { (e[3 * b - 3] as i64, e[3 * b - 2] as i64, e[3 * b - 1] != 0) };
    Ok((1..nb).all(|b| {
        let ((_, pl, _), (nf, _, ok)) = (ends(b - 1), ends(b));
        let bad = match (desc, strict) { (true, true) => pl <= nf, (true, false) => pl < nf, (false, true) => nf <= pl, (false, false) => nf < pl };
        ok && !bad
    }))
}
/// sort.rs `order_runs`: the grade of an already ordered column (`asc`), or reversed (`desc_strict`); both are
/// involutions, so they are their own rank as well.
pub fn order_runs(asc: bool, desc_strict: bool, out: &mut [i64]) -> bool {
    let n = out.len();
    if asc { out.iter_mut().enumerate().for_each(|(i, o)| *o = i as i64); true }
    else if desc_strict { out.iter_mut().enumerate().for_each(|(i, o)| *o = (n - 1 - i) as i64); true }
    else { false }
}
/// sort.rs `order_foR` past the allocation: `order` off the pack. The range is the block metadata's, so the only
/// passes over the residuals are the ones the chosen engine makes, each decoding a block at a time into L1.
pub fn order_enc(run: Runner, kind: u8, desc: bool, rank: bool, c: &Coc, out: &mut [i64]) -> Result<(), String> {
    if c.meta.n == 0 { return Ok(()) }
    let a = ascending_enc(run, kind, desc, false, c)?;
    if !order_runs(a, !a && ascending_enc(run, kind, !desc, true, c)?, out) {
        let s = Ksrc { kind, p: &[], c: Some(*c), n: c.meta.n };
        let (mn, mx) = s.range();
        return grade_src(&s, desc, rank, mn, mx, out)
    }
    Ok(())
}



// ---- A23: sort.rs, 2293-2400, 3386 ----
// `ids_keys` at the constant width `W`; from a byte up the range is taken in the unpacking pass, as sort.rs's `KEY_PUT`.

// ---- A24: sort.rs ----

// ---- A25: sort.rs ----
/// `f::<G>(args)` for `G` the `gid_lane(n)` lane: switched once for the call, never per element.
#[macro_export]
macro_rules! by_gid {
    ($n:expr, $f:ident($($a:expr),*)) => { if $crate::sort::gid_lane($n) == 4 { $f::<u32>($($a),*) } else { $f::<u64>($($a),*) } };
}



// ---- A26: sort.rs ----














// ---- K13: sort.rs `radix_values`, `take_graded`, `sort_values` ----
