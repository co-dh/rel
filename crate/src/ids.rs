#![forbid(unsafe_code)]
//! ids.h:19, 25, 40; own.c:231, 245.
use crate::bits::{lane_width, width_for};
use crate::c::Runner;

/// `c::run_map`'s cost and wide for the id map (`QLEAN_COST_ARITH`, 8).
const COST: u32 = 4;
const WIDE: usize = 8;

/// `Column.idWidth`: zero at one entry and at none -- there is one id, so nothing is stored.
pub fn id_width(nd: usize) -> u32 { if nd < 2 { 0 } else { lane_width(width_for((nd - 1) as u64)) as u32 } }

/// Bytes `n` ids occupy at `w` bits: `⌈n·w/8⌉`, wrapping like the C `size_t` arithmetic.
pub fn ids_bytes(n: usize, w: u32) -> usize { n.wrapping_mul(w as usize).wrapping_add(7) / 8 }

/// `Column.idAt`. Narrow widths share a byte, low field first; eight and above are whole elements.
pub fn id_at(p: &[u8], w: u32, i: usize) -> usize {
    let le = |k: usize| p[i * k..i * k + k].iter().rev().fold(0usize, |a, &b| a << 8 | b as usize);
    match w {
        0 => 0,
        1 => (p[i >> 3] >> (i & 7) & 1) as usize,
        2 => (p[i >> 2] >> ((i & 3) * 2) & 3) as usize,
        4 => (p[i >> 1] >> ((i & 1) * 4) & 15) as usize,
        8 => p[i] as usize,
        16 => le(2),
        32 => le(4),
        _ => le(8),
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

/// `idGroups`' second pass (sort.c:3283-3315, 3400-3414): row `i`'s group `slot[min(id, nd)]` into `out` at `wo`
/// bits, `ids_bytes(n, wo)` bytes, the bits past `n` zero; threaded by `c::run_map`.
pub fn map(run: Runner, ids: &[u8], n: usize, w: u32, nd: usize, slot: &[usize], wo: u32, out: &mut [u8]) {
    let ob = ids_bytes(n, wo);
    if ob == 0 { return; }
    let at = |v: usize| slot[v.min(nd)];
    let out = &mut out[..ob];
    if wo >= 8 {
        let u = wo as usize / 8;
        crate::c::run_map(run, out, n, u, COST, WIDE, &|lo, hi, o: &mut [u8]| {
            for (i, c) in (lo..hi).zip(o.chunks_exact_mut(u)) { c.copy_from_slice(&at(id_at(ids, w, i)).to_le_bytes()[..u]); }
        });
    } else if (1..8).contains(&w) {
        // below a byte, a byte of ids is a byte of table entries: one load a byte
        let mut tab = [0u8; 256];
        for (b, e) in tab.iter_mut().enumerate() {
            *e = (0..8 / w).fold(0u32, |v, t| v | ((at((b >> (t * w)) & ((1 << w) - 1)) & ((1 << wo) - 1)) as u32) << (t * wo)) as u8;
        }
        // `wo <= w`, as `ng <= 2^w`: an input byte is `k` output bits, `r` of them an output byte
        let (k, r) = (8 / w * wo, 8 / (8 / w * wo));
        let ib = ids_bytes(n, w);
        crate::c::run_map(run, out, ob, 1, COST, WIDE, &|lo, hi, o: &mut [u8]| {
            for (b, e) in (lo..hi).zip(o.iter_mut()) {
                *e = (0..r as usize).take_while(|t| b * r as usize + t < ib)
                    .fold(0u32, |v, t| v | (tab[ids[b * r as usize + t] as usize] as u32) << (t as u32 * k)) as u8;
            }
        });
    } else {
        let per = 8 / wo as usize;
        crate::c::run_map(run, out, ob, 1, COST, WIDE, &|lo, hi, o: &mut [u8]| {
            for (b, e) in (lo..hi).zip(o.iter_mut()) {
                *e = (0..per).take_while(|t| b * per + t < n)
                    .fold(0u32, |v, t| v | (at(id_at(ids, w, b * per + t)) << (t as u32 * wo)) as u32) as u8;
            }
        });
    }
    // the fields past `n` in the last input byte were mapped too; the tail bits stay zero
    if (n * wo as usize) & 7 != 0 { out[ob - 1] &= ((1u32 << ((n * wo as usize) & 7)) - 1) as u8; }
}

/// `IDS_PACK` (ids.h:167) in place: `n` ids one byte each in `g` packed to `w < 8` bits from `g[0]`.
#[allow(unused_variables)] // scaffold: B6 fills it
pub fn pack_in_place(g: &mut [u8], w: u32, n: usize) { unimplemented!() }

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn widths() {
        assert_eq!((width_for(0), width_for(1), width_for(255), width_for(256), width_for(u64::MAX)), (0, 1, 8, 9, 64));
        assert_eq!([0, 1, 2, 3, 4, 5, 8, 9, 16, 17, 32, 33, 64].map(lane_width), [0, 1, 2, 4, 4, 8, 8, 16, 16, 32, 32, 64, 64]);
        assert_eq!([0, 1, 2, 3, 4, 5, 256, 257, 65537].map(id_width), [0, 0, 1, 2, 2, 4, 8, 16, 32]);
        assert_eq!((ids_bytes(0, 4), ids_bytes(3, 1), ids_bytes(5, 2), ids_bytes(3, 64)), (0, 1, 2, 24));
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
