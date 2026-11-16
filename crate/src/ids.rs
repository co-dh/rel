#![forbid(unsafe_code)]
//! ids.h:19, 25, 40; own.c:231, 245.
use crate::bits::{lane_width, width_for};
use crate::QLEAN_COST_ARITH;
use crate::c::Runner;

/// `f::<W>(args)` for the run-time width `w`, so `id_at`'s match folds as the C's `IDS_WIDTHS` does.
macro_rules! by_width {
    ($w:expr, $f:ident($($a:expr),*)) => { match $w {
        0 => $f::<0>($($a),*), 1 => $f::<1>($($a),*), 2 => $f::<2>($($a),*), 4 => $f::<4>($($a),*),
        8 => $f::<8>($($a),*), 16 => $f::<16>($($a),*), 32 => $f::<32>($($a),*), _ => $f::<64>($($a),*),
    } };
}
pub(crate) use by_width;

/// `c::run_map`'s wide for the id map; its cost is `QLEAN_COST_ARITH`.
const WIDE: usize = 8;

/// `Column.idWidth`: zero at one entry and at none -- there is one id, so nothing is stored.
pub fn id_width(nd: usize) -> u32 { if nd < 2 { 0 } else { lane_width(width_for((nd - 1) as u64)) as u32 } }

/// Bytes `n` ids occupy at `w` bits: `⌈n·w/8⌉`, wrapping like the C `size_t` arithmetic.
pub fn ids_bytes(n: usize, w: u32) -> usize { n.wrapping_mul(w as usize).wrapping_add(7) / 8 }
/// `ids_avail`: how many ids a payload of `len` bytes holds at `w` bits, which every kernel clamps the count Lean handed it
/// to (`ids_bytes` is not invertible, so this rounds down). `usize::MAX` at width 0: a one-entry dictionary stores nothing
/// and `id_at` answers 0 at every index.
pub fn ids_avail(len: usize, w: u32) -> usize { if w == 0 { usize::MAX } else { len.wrapping_mul(8) / w as usize } }

/// `Column.idAt`. Narrow widths share a byte, low field first; eight and above are whole elements. Inlined with a
/// fixed-width load per arm, as ids.h's `static inline` is: an out-of-line call per element was most of `find` ids.
#[inline(always)]
pub fn id_at(p: &[u8], w: u32, i: usize) -> usize {
    match w {
        0 => 0,
        1 => (p[i >> 3] >> (i & 7) & 1) as usize,
        2 => (p[i >> 2] >> ((i & 3) * 2) & 3) as usize,
        4 => (p[i >> 1] >> ((i & 1) * 4) & 15) as usize,
        8 => p[i] as usize,
        16 => u16::from_le_bytes(le(p, i)) as usize,
        32 => u32::from_le_bytes(le(p, i)) as usize,
        _ => u64::from_le_bytes(le(p, i)) as usize,
    }
}
/// Element `i` of `p` at `W` bytes.
#[inline(always)]
fn le<const W: usize>(p: &[u8], i: usize) -> [u8; W] { p[i * W..(i + 1) * W].try_into().unwrap() }

/// `IDS_UNPACK` (ids.h:144): `f(i, &mut out[i], id)` for each element of `out` and the id of the same index at the
/// constant width `W`. Below a byte one word holds `64 / W` ids at constant shifts, a whole-byte lane is a chunked
/// load, and `out` is walked in step: no per-id bounds test or index shift, which `id_at` at a running index has,
/// so the loop vectorises as the C's does.
#[inline(always)]
pub fn unpack<const W: u32, T>(p: &[u8], out: &mut [T], mut f: impl FnMut(usize, &mut T, usize)) {
    let mut i = 0;
    match W {
        0 => out.iter_mut().enumerate().for_each(|(i, e)| f(i, e, 0)),
        1 | 2 | 4 => {
            let (per, m) = (64 / W as usize, (1u64 << W) - 1);
            for (c, x) in out.chunks_exact_mut(per).zip(p.chunks_exact(8)) {
                let x = u64::from_le_bytes(x.try_into().unwrap());
                for (t, e) in c.iter_mut().enumerate() { f(i + t, e, (x >> (t as u32 * W) & m) as usize) }
                i += per;
            }
            for (j, e) in out[i..].iter_mut().enumerate() { f(i + j, e, id_at(p, W, i + j)) }
        }
        _ => {
            for (j, (e, c)) in out.iter_mut().zip(p.chunks_exact(whole_bytes(W))).enumerate() { f(j, e, word::<W>(c)) }
        }
    }
}
/// Bytes of one id at a whole-byte width `w` (1 below a byte, where no caller reads whole ids).
const fn whole_bytes(w: u32) -> usize { if w >= 8 { w as usize / 8 } else { 1 } }
/// The id `c` holds at the whole-byte width `W`, `c` exactly `whole_bytes(W)` long: a load of that width.
#[inline(always)]
fn word<const W: u32>(c: &[u8]) -> usize {
    match W { 8 => c[0] as usize, 16 => u16::from_le_bytes([c[0], c[1]]) as usize,
              32 => u32::from_le_bytes([c[0], c[1], c[2], c[3]]) as usize, _ => u64::from_le_bytes(c.try_into().unwrap()) as usize }
}
/// `unpack` with no output: `f(i, id)` for the first `n` ids (a slice of `()` takes no memory).
#[inline(always)]
pub fn each<const W: u32>(p: &[u8], n: usize, mut f: impl FnMut(usize, usize)) {
    unpack::<W, ()>(p, &mut alloc::vec![(); n], |i, _, v| f(i, v))
}

/// `IDS_PACK` (ids.h:167): `n` fields `val(i)` into `out` at `w` bits, `w` matched once outside the loop. Below a
/// byte eight output bytes are built in a register a word at a time, where `id_put`'s read-modify-write of a shared
/// byte per field is a dependent chain through memory.
#[inline(always)]
pub fn pack(out: &mut [u8], w: u32, n: usize, val: impl Fn(usize) -> u64) {
    #[inline(always)]
    fn sub<const W: u32>(out: &mut [u8], n: usize, val: impl Fn(usize) -> u64) {
        let (per, m) = (8 / W as usize, (1u64 << W) - 1);
        let byte = |j: usize, cnt: usize| (0..cnt).fold(0u64, |b, t| b | (val(j * per + t) & m) << (t as u32 * W)) as u8;
        let full = n / per;
        for (j8, c) in out[..full / 8 * 8].chunks_exact_mut(8).enumerate() {
            let mut x = 0u64;
            for t in 0..64 / W as usize { x |= (val(j8 * (64 / W as usize) + t) & m) << (t as u32 * W) }
            c.copy_from_slice(&x.to_le_bytes());
        }
        for j in full / 8 * 8..full { out[j] = byte(j, per) }
        if n % per != 0 { out[full] = byte(full, n % per) }
    }
    #[inline(always)]
    fn whole<const K: usize>(out: &mut [u8], n: usize, val: impl Fn(usize) -> u64) {
        for (i, c) in out[..n * K].chunks_exact_mut(K).enumerate() { c.copy_from_slice(&val(i).to_le_bytes()[..K]) }
    }
    match w {
        0 => {}
        1 => sub::<1>(out, n, val), 2 => sub::<2>(out, n, val), 4 => sub::<4>(out, n, val),
        8 => whole::<1>(out, n, val), 16 => whole::<2>(out, n, val), 32 => whole::<4>(out, n, val), _ => whole::<8>(out, n, val),
    }
}

// The largest of whole bytes' fields at a constant narrow width: a const generic so the field loop unrolls.
fn narrow_max<const W: u32>(p: &[u8]) -> u8 {
    p.iter().fold(0, |a, &b| (0..8 / W).map(|k| b >> (k * W) & ((1 << W) - 1)).fold(a, u8::max))
}

fn wide_max<const K: usize>(p: &[u8], n: usize) -> usize {
    p.chunks_exact(K).take(n).map(|c| c.iter().rev().fold(0usize, |a, &b| a << 8 | b as usize)).max().unwrap_or(0)
}

/// The largest of `n` ids at `w` bits, in one pass.
pub fn ids_max(p: &[u8], w: u32, n: usize) -> usize {
    match w {
        0 => 0,
        8 => wide_max::<1>(p, n),
        16 => wide_max::<2>(p, n),
        32 => wide_max::<4>(p, n),
        64 => wide_max::<8>(p, n),
        _ => {
            let nb = n / (8 / w as usize);
            let m = match w { 1 => narrow_max::<1>(&p[..nb]), 2 => narrow_max::<2>(&p[..nb]), _ => narrow_max::<4>(&p[..nb]) } as usize;
            (nb * (8 / w as usize)..n).fold(m, |m, i| m.max(id_at(p, w, i)))
        }
    }
}

/// `ids_firsts` (ids.h:271): each group's first row into `first` (`min(n, nd + 1)` long) and into `slot` (`nd + 1`
/// entries, all `usize::MAX` on entry) the group of each value `min(id, nd)`; answers the group count.
pub fn firsts(ids: &[u8], n: usize, w: u32, nd: usize, slot: &mut [usize], first: &mut [usize]) -> usize {
    match w {
        0 => go::<0>(ids, n, nd, slot, first), 1 => go::<1>(ids, n, nd, slot, first), 2 => go::<2>(ids, n, nd, slot, first),
        4 => go::<4>(ids, n, nd, slot, first), 8 => go::<8>(ids, n, nd, slot, first), 16 => go::<16>(ids, n, nd, slot, first),
        32 => go::<32>(ids, n, nd, slot, first), _ => go::<64>(ids, n, nd, slot, first),
    }
}

// `W` const so `id_at`'s match folds, as the C's `IDS_WIDTHS` does.
fn go<const W: u32>(ids: &[u8], n: usize, nd: usize, slot: &mut [usize], first: &mut [usize]) -> usize {
    let top = if W < 64 && 1usize << W <= nd { 1usize << W } else { nd + 1 };
    let (mut ng, mut i) = (0, 0);
    while i < n {
        let v = id_at(ids, W, i).min(nd);
        i += 1;
        if slot[v] == usize::MAX {
            slot[v] = ng;
            first[ng] = i - 1;
            ng += 1;
            if ng == top || (ng == nd && slot[nd] == usize::MAX) { break; }
        }
    }
    if ng == top || i >= n || slot[nd] != usize::MAX { return ng; }
    // A word at a time up to 32 bits: the even and odd fields spread over `2w` bits plus `2^w - nd`, so a field
    // from `nd` up carries into bit `w` of its slot (the `k` mask).
    let wide = W == 0 || W > 32;
    let per = if wide { 1 } else { 64 / W as usize };
    let (mut e, mut c, mut k) = (0u64, 0u64, 0u64);
    if !wide {
        for s in (0..64).step_by(2 * W as usize) {
            e |= ((1u64 << W) - 1) << s;
            c |= (1u64 << W).wrapping_sub(nd as u64) << s;
            k |= 1u64 << (s + W);
        }
    }
    let word = |i: usize| u64::from_le_bytes(ids[i * W as usize / 8..][..8].try_into().unwrap());
    let hit1 = |x: u64| (x & e).wrapping_add(c) | ((x >> W) & e).wrapping_add(c);
    let mut j = None;
    while i < n && j.is_none() && (wide || i % per != 0) {
        if id_at(ids, W, i) >= nd { j = Some(i); }
        i += 1;
    }
    // 32 words with no exit between them, so the compiler vectorises the test; the word walk finds which
    if !wide && j.is_none() {
        let mut hit = 0u64;
        while hit & k == 0 && i + 32 * per <= n {
            // one slice check for the 32 words, so the loop body has no bounds test to block vectorising
            for ch in ids[i * W as usize / 8..][..256].chunks_exact(8) { hit |= hit1(u64::from_le_bytes(ch.try_into().unwrap())); }
            if hit & k == 0 { i += 32 * per; }
        }
        while i + per <= n {
            if hit1(word(i)) & k != 0 { break; }
            i += per;
        }
    }
    while i < n && j.is_none() {
        if id_at(ids, W, i) >= nd { j = Some(i); }
        i += 1;
    }
    if let Some(j) = j { slot[nd] = ng; first[ng] = j; ng += 1; }
    ng
}

/// `map` at an output lane of `U` bytes: `w` is matched once a slice, so the row loop has a constant-width load and
/// store, which `id_at` and a `copy_from_slice` of a run-time length are not.
fn wide<const U: usize>(run: Runner, out: &mut [u8], ids: &[u8], w: u32, n: usize, nd: usize, slot: &[usize]) {
    #[inline(always)]
    fn sweep<const U: usize>(o: &mut [u8], lo: usize, hi: usize, nd: usize, slot: &[usize], id: impl Fn(usize) -> usize) {
        for (i, c) in (lo..hi).zip(o.chunks_exact_mut(U)) {
            let v = slot[id(i).min(nd)].to_le_bytes();
            c.copy_from_slice(&v[..U]);
        }
    }
    crate::c::run_map(run, out, n, U, QLEAN_COST_ARITH, WIDE, &|lo, hi, o: &mut [u8]| {
        let (ids, slot) = (ids, slot); // own copies: a captured reference reloads every row past the output stores
        let le = |k: usize| move |i: usize| ids[i * k..i * k + k].iter().rev().fold(0usize, |a, &b| a << 8 | b as usize);
        match w {
            0 => sweep::<U>(o, lo, hi, nd, slot, |_| 0),
            1 => sweep::<U>(o, lo, hi, nd, slot, |i| (ids[i >> 3] >> (i & 7) & 1) as usize),
            2 => sweep::<U>(o, lo, hi, nd, slot, |i| (ids[i >> 2] >> ((i & 3) * 2) & 3) as usize),
            4 => sweep::<U>(o, lo, hi, nd, slot, |i| (ids[i >> 1] >> ((i & 1) * 4) & 15) as usize),
            8 => sweep::<U>(o, lo, hi, nd, slot, |i| ids[i] as usize),
            16 => sweep::<U>(o, lo, hi, nd, slot, le(2)),
            32 => sweep::<U>(o, lo, hi, nd, slot, le(4)),
            _ => sweep::<U>(o, lo, hi, nd, slot, le(8)),
        }
    });
}

/// `idGroups`' second pass (sort.c:3283-3315, 3400-3414): row `i`'s group `slot[min(id, nd)]` into `out` at `wo`
/// bits, `ids_bytes(n, wo)` bytes, the bits past `n` zero; threaded by `c::run_map`.
pub fn map(run: Runner, ids: &[u8], n: usize, w: u32, nd: usize, slot: &[usize], wo: u32, out: &mut [u8]) {
    let ob = ids_bytes(n, wo);
    if ob == 0 { return; }
    let at = |v: usize| slot[v.min(nd)];
    let out = &mut out[..ob];
    if wo >= 8 {
        match wo { 8 => wide::<1>(run, out, ids, w, n, nd, slot), 16 => wide::<2>(run, out, ids, w, n, nd, slot),
                   32 => wide::<4>(run, out, ids, w, n, nd, slot), _ => wide::<8>(run, out, ids, w, n, nd, slot) }
    } else if (1..8).contains(&w) && wo <= w {
        // below a byte, a byte of ids is a byte of table entries: one load a byte; a wider output (a renaming that
        // grows the dictionary's width) takes the byte-per-output loop below
        let mut tab = [0u8; 256];
        for (b, e) in tab.iter_mut().enumerate() {
            *e = (0..8 / w).fold(0u32, |v, t| v | ((at((b >> (t * w)) & ((1 << w) - 1)) & ((1 << wo) - 1)) as u32) << (t * wo)) as u8;
        }
        // `wo <= w`, as `ng <= 2^w`: an input byte is `k` output bits, `r` of them an output byte
        let (k, r) = (8 / w * wo, 8 / (8 / w * wo));
        let ib = ids_bytes(n, w);
        crate::c::run_map(run, out, ob, 1, QLEAN_COST_ARITH, WIDE, &|lo, hi, o: &mut [u8]| {
            for (b, e) in (lo..hi).zip(o.iter_mut()) {
                *e = (0..r as usize).take_while(|t| b * r as usize + t < ib)
                    .fold(0u32, |v, t| v | (tab[ids[b * r as usize + t] as usize] as u32) << (t as u32 * k)) as u8;
            }
        });
    } else {
        let per = 8 / wo as usize;
        // `w >= 8` here: each id a whole element, read at a width fixed outside the byte loop
        #[inline(always)]
        fn narrow(o: &mut [u8], lo: usize, (per, n, nd, wo): (usize, usize, usize, u32), slot: &[usize], id: impl Fn(usize) -> usize) {
            for (b, e) in (lo..lo + o.len()).zip(o.iter_mut()) {
                *e = (0..per).take_while(|t| b * per + t < n)
                    .fold(0u32, |v, t| v | (slot[id(b * per + t).min(nd)] << (t as u32 * wo)) as u32) as u8;
            }
        }
        let g = (per, n, nd, wo);
        crate::c::run_map(run, out, ob, 1, QLEAN_COST_ARITH, WIDE, &|lo, _hi, o: &mut [u8]| match w {
            8 => narrow(o, lo, g, slot, |i| ids[i] as usize),
            _ => narrow(o, lo, g, slot, |i| id_at(ids, w, i)),
        });
    }
    // the fields past `n` in the last input byte were mapped too; the tail bits stay zero
    if (n * wo as usize) & 7 != 0 { out[ob - 1] &= ((1u32 << ((n * wo as usize) & 7)) - 1) as u8; }
}

/// `IDS_PACK` (ids.h:167) in place: `n` ids one byte each in `g` packed to `w < 8` bits from `g[0]`.
/// Byte `j` reads the ids at `j·per ..` and lands at `g[j]`, which is at or below them, so ascending order reads
/// every id before its byte is stored. The last byte's fields past `n` stay zero.
pub fn pack_in_place(g: &mut [u8], w: u32, n: usize) {
    if w == 0 { return; }
    assert!(matches!(w, 1 | 2 | 4) && g.len() >= n, "pack_in_place: width {w} (must be 1, 2 or 4), {n} ids in {} bytes", g.len());
    // whole output bytes from a copied block, as a const-width loop the compiler vectorises: the block is read
    // before its bytes are stored, which the borrow checker cannot see in `g` alone (a plain fold was 4x slower)
    match w { 1 => pack_whole::<1, 8>(g, n), 2 => pack_whole::<2, 4>(g, n), _ => pack_whole::<4, 2>(g, n) }
    let (per, mask) = (8 / w as usize, (1u8 << w) - 1);
    for j in n / per..ids_bytes(n, w) {
        let ids = &g[j * per..n.min(j * per + per)];
        g[j] = ids.iter().enumerate().fold(0u8, |b, (t, &v)| b | (v & mask) << (t as u32 * w));
    }
}

/// The `n / PER` output bytes of `pack_in_place` that hold `PER` ids each, `W` bits an id.
fn pack_whole<const W: u32, const PER: usize>(g: &mut [u8], n: usize) {
    const BLOCK: usize = 2048;
    let (mut buf, mut j, full) = ([0u8; BLOCK], 0, n / PER);
    while j < full {
        let take = (full - j).min(BLOCK / PER);
        buf[..take * PER].copy_from_slice(&g[j * PER..(j + take) * PER]);
        for (o, c) in g[j..j + take].iter_mut().zip(buf[..take * PER].chunks_exact(PER)) {
            let mut b = 0u8;
            for t in 0..PER { b |= (c[t] & ((1u8 << W) - 1)) << (t as u32 * W) }
            *o = b;
        }
        j += take;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn widths() {
        assert_eq!((width_for(0), width_for(1), width_for(255), width_for(256), width_for(u64::MAX)), (0, 1, 8, 9, 64));
        assert_eq!([0, 1, 2, 3, 4, 5, 8, 9, 16, 17, 32, 33, 64].map(lane_width), [0, 1, 2, 4, 4, 8, 8, 16, 16, 32, 32, 64, 64]);
        assert_eq!([0, 1, 2, 3, 4, 5, 256, 257, 65537].map(id_width), [0, 0, 1, 2, 2, 4, 8, 16, 32]);
        assert_eq!((ids_bytes(0, 4), ids_bytes(3, 1), ids_bytes(5, 2), ids_bytes(3, 64)), (0, 1, 2, 24));
    }
    // `pack` and `unpack` against the per-id `id_put` and `id_at` they replace, across the word boundary and its tail
    #[test] fn pack_unpack_match_id_put_id_at() {
        fn go<const W: u32>() {
            for n in [0usize, 1, 7, 63, 64, 65, 200, 517] {
                let mask = if W == 64 { !0 } else { (1u64 << W) - 1 };
                let val = |i: usize| (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(17) & mask;
                let (mut a, mut b) = (vec![0u8; ids_bytes(n, W)], vec![0u8; ids_bytes(n, W)]);
                pack(&mut a, W, n, val);
                (0..n).for_each(|i| id_put(&mut b, W, i, val(i)));
                assert_eq!(a, b, "pack w={W} n={n}");
                let mut got = vec![usize::MAX; n];
                unpack::<W, usize>(&a, &mut got, |i, e, v| { assert!(*e == usize::MAX); *e = v; assert_eq!(v, id_at(&a, W, i)) });
                assert!(got.iter().enumerate().all(|(i, &v)| v == id_at(&a, W, i)), "unpack w={W} n={n}");
                let mut runs_out = vec![0i64; n + 1];
                let g = runs(&a, n, W, usize::MAX, n, &mut runs_out);
                let want: Vec<i64> = (0..n).filter(|&i| i == 0 || id_at(&a, W, i) != id_at(&a, W, i - 1)).map(|i| i as i64).collect();
                assert_eq!(&runs_out[..g], &want[..], "runs w={W} n={n}");
            }
        }
        go::<0>(); go::<1>(); go::<2>(); go::<4>(); go::<8>(); go::<16>(); go::<32>(); go::<64>();
    }
    #[test] fn pack_roundtrip() {
        for w in [1u32, 2, 4] {
            for n in 0..70usize {
                let src: Vec<u8> = (0..n).map(|i| (i * 7 + 3) as u8 & ((1 << w) - 1)).collect();
                let mut g = src.clone();
                pack_in_place(&mut g, w, n);
                assert!(src.iter().enumerate().all(|(i, &v)| id_at(&g, w, i) == v as usize), "w={w} n={n}");
            }
        }
    }
    #[test] fn at_and_max() {
        let p = [0b1110_0100u8, 0b0000_0011, 5, 0, 0, 0, 0, 0, 0, 0];
        assert_eq!([0, 1, 2, 3].map(|i| id_at(&p, 2, i)), [0, 1, 2, 3]);
        assert_eq!(id_at(&p, 4, 1), 14);
        assert_eq!(id_at(&p, 16, 1), 5);
        assert_eq!(id_at(&p, 0, 99), 0);
        for w in [1u32, 2, 4, 8, 16, 32, 64] {
            for n in 0..(80 / w as usize).min(10) {
                assert_eq!(ids_max(&p, w, n), (0..n).map(|i| id_at(&p, w, i)).max().unwrap_or(0), "w={w} n={n}");
            }
        }
        assert_eq!(ids_max(&p, 0, 5), 0);
    }
}

#[cfg(test)]
mod firsts_tests {
    use super::*;
    // The C driver (/data/tmp/qrs/B1/drv.c) answered (ng, first[1]) = (2, pos), or (1, 0) with no id >= nd, for
    // every (w, nd, pos) of this table; the ids are all 0 but `v` at `pos`.
    #[test] fn firsts_cases() {
        let n = 130;
        for w in [1u32, 2, 4, 8, 16, 32, 64] {
            let nds: &[usize] = if w <= 16 { &[1 << w, (1 << w) - 1] } else { &[3] };
            for &nd in nds {
                let v: u64 = if w >= 32 { 5 } else { (nd as u64).min((1 << w) - 1) };
                for pos in [Some(0), Some(63), Some(64), Some(n - 1), None] {
                    let mut p = vec![0u8; n * 8 + 16];
                    if let Some(i) = pos {
                        if w < 8 { p[i * w as usize / 8] |= (v << (i * w as usize % 8)) as u8 }
                        else { let k = w as usize / 8; p[i * k..(i + 1) * k].copy_from_slice(&v.to_le_bytes()[..k]) }
                    }
                    let (mut slot, mut first) = (vec![usize::MAX; nd + 1], vec![0; n.min(nd + 1)]);
                    let ng = firsts(&p[..ids_bytes(n, w)], n, w, nd, &mut slot, &mut first);
                    let (wng, wf1) = match pos { Some(i) if i != 0 => (2, i), Some(_) => (2, 1), None => (1, 0) };
                    assert_eq!((ng, if ng > 1 { first[1] } else { 0 }), (wng, wf1), "w={w} nd={nd} pos={pos:?}");
                }
            }
        }
    }
}

#[cfg(test)]
mod map_tests {
    use super::*;
    // The C `ids_map_run` + table agreed (/data/tmp/qrs/B2/h.c, 26268 random cases); here the per-row definition.
    #[test] fn map_is_slot_of_id() {
        let mut s = 7u64;
        let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        for w in [1u32, 2, 4, 8, 16, 32, 64] {
            for n in [0usize, 1, 3, 7, 8, 9, 63, 130] {
                let ids: Vec<u8> = (0..ids_bytes(n, w) + 8).map(|_| rnd() as u8).collect();
                let nd = if w <= 8 { 1 << w } else { 5 };
                let slot: Vec<usize> = (0..=nd).map(|v| v % 3).collect();
                for wo in [2u32, 8, 16, 32, 64].into_iter().filter(|&wo| wo >= 8 || w >= 2) {
                    let mut out = vec![0u8; ids_bytes(n, wo)];
                    map(crate::c::qlean_run_c, &ids, n, w, nd, &slot, wo, &mut out);
                    for i in 0..n { assert_eq!(id_at(&out, wo, i), slot[id_at(&ids, w, i).min(nd)], "w={w} n={n} wo={wo} i={i}"); }
                    if (n * wo as usize) & 7 != 0 { assert_eq!(out[out.len() - 1] >> ((n * wo as usize) & 7), 0); }
                }
            }
        }
    }
}

// ---- A10: ids.h:56-281 (per element: C keeps these bodies while a C caller remains) ----
/// ids.h:56 `id_put`: id `v` at index `i`, `w` bits each; a narrow field is a read-modify-write of its shared byte.
#[inline(always)]
pub fn id_put(p: &mut [u8], w: u32, i: usize, v: u64) {
    // a store of `k` bytes, `k` a constant in each arm once inlined, so no `memcpy` call per element
    #[inline(always)]
    fn put(p: &mut [u8], i: usize, k: usize, v: u64) { p[i * k..i * k + k].copy_from_slice(&v.to_le_bytes()[..k]) }
    match w {
        0 => {}
        1 | 2 | 4 => {
            let (b, s, m) = (i * w as usize >> 3, (i * w as usize & 7) as u32, (1u8 << w) - 1);
            p[b] = p[b] & !(m << s) | ((v as u8 & m) << s);
        }
        8 => p[i] = v as u8,
        16 => put(p, i, 2, v),
        32 => put(p, i, 4, v),
        _ => put(p, i, 8, v),
    }
}

/// ids.h:76 `ids_fill`: `cnt` copies of `v` from index `at`; at a narrow width the aligned middle is a byte pattern.
pub fn ids_fill(out: &mut [u8], w: u32, at: usize, cnt: usize, v: u64) {
    if w == 0 || cnt == 0 { return; }
    let end = at + cnt;
    if w >= 8 { (at..end).for_each(|i| id_put(out, w, i, v)); return; }
    let per = (8 / w) as usize;
    let f = (v & ((1 << w) - 1)) as u8;
    let pat = (0..per).fold(0u8, |a, j| a | f << (j as u32 * w));
    let lo = at.div_ceil(per).saturating_mul(per).min(end);
    let hi = (end / per * per).max(lo);
    (at..lo).for_each(|i| id_put(out, w, i, v));
    out[lo / per..hi / per].fill(pat);
    (hi..end).for_each(|i| id_put(out, w, i, v));
}

// One destination byte of `bitcopy`: up to the byte's end of the `bits - i` left, from bit `sb + i` of the source.
fn bitcopy_byte(dst: &mut [u8], db: usize, src: &[u8], sb: usize, bits: usize, i: usize) -> usize {
    let (dbit, s) = ((db + i) & 7, sb + i);
    let (sk, sbit) = (s >> 3, (s & 7) as u32);
    let take = (8 - dbit).min(bits - i);
    let mut v = (src[sk] >> sbit) as u32;
    if sbit != 0 && sk + 1 < src.len() { v |= (src[sk + 1] as u32) << (8 - sbit); }
    dst[(db + i) >> 3] |= ((v & ((1u32 << take) - 1)) << dbit) as u8;
    i + take
}

/// ids.h:201 `ids_bitcopy`: `bits` bits of `src` from bit `sb` to bit `db` of `dst`, which arrives zeroed.
pub fn bitcopy(dst: &mut [u8], db: usize, src: &[u8], sb: usize, bits: usize) {
    let mut i = 0;
    if db & 7 != 0 && bits != 0 { i = bitcopy_byte(dst, db, src, sb, bits, i); }
    let rd = |at: usize| u64::from_le_bytes(src[at..at + 8].try_into().unwrap());
    // eight destination bytes an iteration; a run starting inside a byte reads the next eight as well
    while bits - i >= 64 && ((sb + i) >> 3) + if (sb + i) & 7 != 0 { 16 } else { 8 } <= src.len() {
        let (s, sbit) = (sb + i, ((sb + i) & 7) as u32);
        let v = if sbit != 0 { rd(s >> 3) >> sbit | rd((s >> 3) + 8) << (64 - sbit) } else { rd(s >> 3) };
        let d = (db + i) >> 3;
        dst[d..d + 8].copy_from_slice(&v.to_le_bytes());
        i += 64;
    }
    while i < bits { i = bitcopy_byte(dst, db, src, sb, bits, i); }
}

/// ids.h:230 `ids_slice_elems`: elements per copy slice at `w`, a whole byte's worth so two threads never share one.
pub fn slice_elems(w: u32) -> usize { if w != 0 && w < 8 { (8 / w) as usize } else { 1 } }

fn unpack16_at<const W: u32>(p: &[u8], from: usize, m: usize, dst: &mut [u16]) {
    let per = slice_elems(W);
    let mut j = 0;
    if per > 1 {
        while j < m && (from + j) % per != 0 { dst[j] = id_at(p, W, from + j) as u16; j += 1; }
        let b = (from + j) / per;
        for (k, &x) in p[b..].iter().enumerate().take((m - j) / per) {
            for t in 0..per { dst[j + k * per + t] = ((x as u32 >> (t as u32 * W)) & 1u32.checked_shl(W).unwrap_or(0).wrapping_sub(1)) as u16; }
        }
        j += (m - j) / per * per;
    }
    while j < m { dst[j] = id_at(p, W, from + j) as u16; j += 1; }
}

/// ids.h:251 `ids_unpack16`: `m` ids from `from` widened to u16, whole bytes split by constant shifts.
pub fn unpack16(p: &[u8], w: u32, from: usize, m: usize, dst: &mut [u16]) {
    match w {
        0 => unpack16_at::<0>(p, from, m, dst), 1 => unpack16_at::<1>(p, from, m, dst), 2 => unpack16_at::<2>(p, from, m, dst),
        4 => unpack16_at::<4>(p, from, m, dst), 8 => unpack16_at::<8>(p, from, m, dst), 16 => unpack16_at::<16>(p, from, m, dst),
        32 => unpack16_at::<32>(p, from, m, dst), _ => unpack16_at::<64>(p, from, m, dst),
    }
}

// The head test of `runs`: field `i` raw value `raw` is a head where `min(raw, nd)` differs from the field before.
// Taken by value into `runs_at`, so its fields live in registers; `get_mut` is the C's `if (out)` and the store's
// bounds test in one compare (a non-empty `out` holds every head).
struct Heads<'a> { out: &'a mut [i64], nd: usize, g: usize, prev: usize }
impl Heads<'_> {
    #[inline(always)]
    fn at(&mut self, i: usize, raw: usize) {
        let v = raw.min(self.nd);
        if i == 0 || v != self.prev {
            if let Some(o) = self.out.get_mut(self.g) { *o = i as i64 }
            self.g += 1;
        }
        self.prev = v;
    }
}

fn runs_at<const W: u32>(p: &[u8], n: usize, most: usize, mut h: Heads) -> usize {
    if W >= 8 {
        for (i, c) in p.chunks_exact(whole_bytes(W)).take(n).enumerate() { if h.g > most { break } h.at(i, word::<W>(c)) }
        return h.g
    }
    let (per, mask, mut i) = ((8 / W.max(1)) as usize, (1u32 << W) - 1, 0);
    let mut rep = 0u8;
    for (b, &x) in p[..if W == 0 { 0 } else { n / per }].iter().enumerate() {
        if h.g > most { break; }
        if b != 0 && x == rep { continue; }
        for t in 0..per { h.at(b * per + t, (x as u32 >> (t as u32 * W) & mask) as usize); }
        rep = ((x as u32 >> ((per as u32 - 1) * W)) * (0xFF / mask.max(1))) as u8;
    }
    if W != 0 { i = n / per * per }
    while i < n && h.g <= most { h.at(i, id_at(p, W, i)); i += 1; }
    h.g
}

/// ids.h:281 `ids_runs`: the run heads of `n` ids, each read as `min(id, nd)`, into `out` (empty: only counted); the
/// walk stops once there are more than `most`. A sub-byte byte repeating the last field is skipped whole.
pub fn runs(p: &[u8], n: usize, w: u32, nd: usize, most: usize, out: &mut [i64]) -> usize {
    let h = Heads { out, nd, g: 0, prev: 0 };
    match w {
        0 => runs_at::<0>(p, n, most, h), 1 => runs_at::<1>(p, n, most, h), 2 => runs_at::<2>(p, n, most, h),
        4 => runs_at::<4>(p, n, most, h), 8 => runs_at::<8>(p, n, most, h), 16 => runs_at::<16>(p, n, most, h),
        32 => runs_at::<32>(p, n, most, h), _ => runs_at::<64>(p, n, most, h),
    }
}

#[cfg(test)]
mod a10_tests {
    use super::*;

    struct Rng(u64);
    impl Rng {
        fn rnd(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 >> 33 }
        fn rnd64(&mut self) -> u64 { let a = self.rnd(); a << 31 ^ self.rnd() }
    }
    fn hb(h: &mut u64, b: &[u8]) { for &x in b { *h = (*h ^ x as u64).wrapping_mul(1099511628211); } }
    fn h16(h: &mut u64, d: &[u16]) { for x in d { hb(h, &x.to_le_bytes()); } }

    // The same random walk as the C harness over ids.h at 98305ab: the expected hashes are the C's output.
    #[test]
    fn matches_c() {
        let mut r = Rng(0x9E3779B97F4A7C15);
        let [mut hp, mut hf, mut hu, mut hr, mut hc] = [14695981039346656037u64; 5];
        for _ in 0..3000 {
            for w in [0u32, 1, 2, 4, 8, 16, 32, 64] {
                let cap = if w != 0 { 64 * 8 / w as usize } else { 100 };
                let buf: Vec<u8> = (0..64).map(|_| r.rnd() as u8).collect();
                let mut b2 = buf.clone();
                let i = r.rnd() as usize % cap; let v = r.rnd64();
                id_put(&mut b2, w, i, v); hb(&mut hp, &b2);
                let mut b2 = buf.clone();
                let at = r.rnd() as usize % (cap + 1); let cnt = r.rnd() as usize % (cap - at + 1); let v = r.rnd64();
                ids_fill(&mut b2, w, at, cnt, v); hb(&mut hf, &b2);
                let p: Vec<u8> = (0..64).map(|_| r.rnd() as u8).collect();
                let from = r.rnd() as usize % (cap + 1); let m = r.rnd() as usize % (cap - from + 1);
                let mut d = [0u16; 800];
                unpack16(&p, w, from, m, &mut d); h16(&mut hu, &d[..m]);
                let n = r.rnd() as usize % (cap + 1); let nd = 1 + r.rnd() as usize % 300;
                let mut most = if r.rnd() % 4 != 0 { r.rnd() as usize % (n + 2) } else { usize::MAX };
                let mut prev = 0u8;
                let p: Vec<u8> = (0..40).map(|_| { if r.rnd() % 4 == 0 { prev = r.rnd() as u8; } prev }).collect();
                let n = n.min(40 * 8 / w.max(1) as usize);
                let mut o = [-1i64; 400];
                let g = if r.rnd() % 3 != 0 { most = n; runs(&p, n, w, nd, most, &mut o[..most]) } else { runs(&p, n, w, nd, most, &mut []) };
                hb(&mut hr, &(g as u64).to_le_bytes());
                for x in &o[..g.min(400)] { hb(&mut hr, &x.to_le_bytes()); }
            }
            let src: Vec<u8> = (0..40).map(|_| r.rnd() as u8).collect();
            let ss = 24 + r.rnd() as usize % 17; let sb = r.rnd() as usize % (ss * 8); let db = r.rnd() as usize % 64;
            let lim = (ss * 8 - sb).min(320 - db); let bits = r.rnd() as usize % (lim + 1);
            let mut dst = [0u8; 40];
            bitcopy(&mut dst, db, &src[..ss], sb, bits); hb(&mut hc, &dst);
        }
        assert_eq!([hp, hf, hu, hr, hc], [0x6a45bdefcd81525e, 0xad88878f87de21f7, 0xf8cd5342bebc2451, 0x60ea9b1386f531b5, 0x2ad203a0f427c6ff]);
    }

    #[test]
    fn edges() {
        assert_eq!(slice_elems(0), 1); assert_eq!(slice_elems(2), 4); assert_eq!(slice_elems(8), 1);
        assert_eq!(runs(&[], 0, 8, 3, 5, &mut []), 0);
        let mut o = [0i64; 3];
        assert_eq!(runs(&[1, 1, 2], 3, 8, 9, 9, &mut o), 2); assert_eq!(o[..2], [0, 2]);
        // ids past nd read as nd: 5 and 9 are one run at nd = 3
        assert_eq!(runs(&[5, 9], 2, 8, 3, 9, &mut []), 1);
    }
}
