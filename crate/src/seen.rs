#![forbid(unsafe_code)]
//! `seen` (PLAN D.12, `Kernel.kseen` in Rel/Kernel/Seen.lean): each row's group, groups numbered by first occurrence
//! under the equality of `kasc`'s order codes, and each group's first row. Two engines, each reading the key columns a
//! block at a time and writing both answers through the encoder's block step (`ffi::Sink`):
//! - direct addressing: one table slot per code in the keys' range, the range from the block metadata (`asc::Key::span`);
//! - runs: rows already in `kasc` order, where a group is a run of equal rows, so any range is served with no table.
//!
//! A range too wide for the table on rows out of order is the error: it needs a hash, which is not built (PLAN D.12).
//! Owner approval (PLAN 6.10) S: one block decoded into an L1 scratch counts as per block.
use alloc::{collections::BTreeMap, format, string::String, vec, vec::Vec};
use crate::asc::{self, Key};
use crate::blocks::{Blocks, Grid};
use crate::c::Runner;
use crate::ffi::{Form, Sink};
use crate::{group, lean};

/// `Kernel.kseen`'s word model over the code columns `cs` at `n` rows: `(g, first)`. The model both engines are tested
/// against.
pub fn words(cs: &[Vec<u64>], n: usize) -> (Vec<u64>, Vec<u64>) {
    let (mut ids, mut first) = (BTreeMap::new(), Vec::new());
    let g = (0..n).map(|i| *ids.entry(cs.iter().map(|c| c[i]).collect::<Vec<u64>>()).or_insert_with(|| { first.push(i as u64); first.len() as u64 - 1 })).collect();
    (g, first)
}

/// The codes of rows `at .. at + cnt` of every key, key `c`'s at `t[c * cnt ..]`, each block decoded into `buf` (S).
fn codes(ks: &[Key], at: usize, cnt: usize, t: &mut [u64], buf: &mut [u64]) {
    for (k, o) in ks.iter().zip(t.chunks_exact_mut(cnt.max(1))) { k.codes(at, &mut o[..cnt], buf) }
}

/// `kseen` past its column checks, on the keys `ks` of types `ts` (`QAtomicType` indices) at `n` rows:
/// `(k, g, first)`, `g` and `first` as `Coc.encode 8` writes them. Direct addressing where the product of the keys' code
/// spans passes `group::direct_ok`, else runs where the rows are in `kasc` order (`asc::sorted`), else the error.
pub fn blocks(run: Runner, ts: &[u8], ks: &[Key], n: usize) -> Result<(usize, lean::O, lean::O), String> {
    let sink = |m| Sink::new(m, 8, Form::For).enc();
    if n == 0 { return Ok((0, sink(0).answer(&Blocks::pos(0)), sink(0).answer(&Blocks::pos(0)))) }
    let sp: Vec<(u64, u64)> = ks.iter().map(Key::span).collect();
    let r = sp.iter().fold(1u128, |p, &(a, b)| p.saturating_mul((b - a) as u128 + 1));
    if r <= 1 << 64 && group::direct_ok((r - 1) as u64, n) { return Ok(direct(ks, &sp, r as usize, n)) }
    if asc::sorted(run, ks, n) { return Ok(runs(ks, n)) }
    let cols: Vec<String> = ts.iter().zip(&sp).enumerate().map(|(i, (t, (a, b)))| format!("es[{i}] type {t} codes {a:#x}..={b:#x}")).collect();
    Err(format!("seen: key range of {r} codes ({}) over {n} rows out of order needs a hash, not built (PLAN D.12)", cols.join(", ")))
}

/// Direct addressing: a row's slot is its mixed-radix code over `sp` (first key the most significant), `r` slots.
/// Pass 1 numbers the slots in row order (slot holds group + 1, `first` each group's row); pass 2 writes `g` per block
/// by looking each row's slot up again, so no per-row word is kept between the passes.
fn direct(ks: &[Key], sp: &[(u64, u64)], r: usize, n: usize) -> (usize, lean::O, lean::O) {
    let slot = |t: &[u64], cnt: usize, j: usize| sp.iter().enumerate().fold(0usize, |s, (c, &(a, b))| s * (b - a + 1) as usize + (t[c * cnt + j] - a) as usize);
    let g = Grid { n, lg: crate::DEFAULT_LG };
    let (mut tab, mut first) = (vec![0u32; r], Vec::new());
    let (mut t, mut buf) = (vec![0u64; ks.len() * g.blk()], vec![0u64; 2 * g.blk()]);
    for (_, lo, nb) in g.walk() {
        codes(ks, lo, nb, &mut t, &mut buf);
        for j in 0..nb {
            let s = &mut tab[slot(&t, nb, j)];
            if *s == 0 { first.push((lo + j) as u64); *s = first.len() as u32 }
        }
    }
    let go = Sink::new(n, 8, Form::For).enc().answer(&|o: &mut [i64], i0: usize| {
        let cnt = o.len();
        let (mut t, mut buf) = (vec![0u64; ks.len() * cnt], vec![0u64; 2 * cnt]);
        codes(ks, i0, cnt, &mut t, &mut buf);
        for (j, x) in o.iter_mut().enumerate() { *x = tab[slot(&t, cnt, j)] as i64 - 1 }
    });
    let fo = Sink::new(first.len(), 8, Form::For).enc().answer(&Blocks::dense(crate::pod::bytes(&first), 8));
    (first.len(), go, fo)
}

/// Runs, on rows in `kasc` order: pass 1 sets bit `i` of a bitmap (`n` bits) where row `i` starts a run (row 0, and
/// each row some key's code changes at); `first` is the set bits, `g` a row's count of starts up to it, less one.
fn runs(ks: &[Key], n: usize) -> (usize, lean::O, lean::O) {
    let g = Grid { n, lg: crate::DEFAULT_LG };
    let (blk, wb) = (g.blk(), g.blk() / 64);
    let (mut bits, mut t, mut buf) = (vec![0u64; n.div_ceil(64)], vec![0u64; ks.len() * blk], vec![0u64; 2 * blk]);
    // `last[c]`: key `c`'s code at the row before the block
    let mut last = vec![0u64; ks.len()];
    for (_, lo, nb) in g.walk() {
        codes(ks, lo, nb, &mut t, &mut buf);
        let w = &mut bits[lo / 64..(lo + nb).div_ceil(64)];
        if lo == 0 { w[0] |= 1 }
        for (c, l) in last.iter_mut().enumerate() {
            let x = &t[c * nb..c * nb + nb];
            if lo > 0 && *l != x[0] { w[0] |= 1 }
            for k in 1..nb { w[k >> 6] |= ((x[k] != x[k - 1]) as u64) << (k & 63) }
            *l = x[nb - 1];
        }
    }
    let bit = |i: usize| bits[i >> 6] >> (i & 63) & 1 == 1;
    // `at[b]`: the starts before block `b`
    let mut at = vec![0usize; g.nblk() + 1];
    for b in 0..g.nblk() { at[b + 1] = at[b] + bits[b * wb..(b * wb + wb).min(bits.len())].iter().map(|w| w.count_ones() as usize).sum::<usize>() }
    let k = at[g.nblk()];
    let go = Sink::new(n, 8, Form::For).enc().answer(&|o: &mut [i64], i0: usize| {
        let mut c = at[i0 / blk] + (i0 / blk * blk..i0).filter(|&i| bit(i)).count();
        for (j, x) in o.iter_mut().enumerate() { c += bit(i0 + j) as usize; *x = c as i64 - 1 }
    });
    // answer position `p` lies in the first row block whose `at` passes it
    let fo = Sink::new(k, 8, Form::For).enc().answer(&|o: &mut [i64], p0: usize| {
        let (mut b, mut i) = (at.partition_point(|&a| a <= p0) - 1, 0usize);
        let mut skip = p0 - at[b];
        'out: loop {
            for (j, &w0) in bits[b * wb..(b * wb + wb).min(bits.len())].iter().enumerate() {
                let mut w = w0;
                while w != 0 {
                    if skip == 0 { o[i] = ((b * wb + j) * 64 + w.trailing_zeros() as usize) as i64; i += 1; if i == o.len() { break 'out } } else { skip -= 1 }
                    w &= w - 1;
                }
            }
            b += 1;
        }
    });
    (k, go, fo)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use crate::{coc, pod};

    #[test] fn words_numbers_by_first_occurrence() {
        // `B A B`, and two columns (1,0) (2,0) (1,0) (2,1) (1,0); no column: one group; no row: none
        assert_eq!(words(&[vec![2, 1, 2]], 3), (vec![0, 1, 0], vec![0, 1]));
        assert_eq!(words(&[vec![1, 2, 1, 2, 1], vec![0, 0, 0, 1, 0]], 5), (vec![0, 1, 0, 2, 0], vec![0, 1, 3]));
        assert_eq!(words(&[], 3), (vec![0, 0, 0], vec![0]));
        assert_eq!(words(&[vec![]], 0), (vec![], vec![]));
    }
    // `blocks` writes the bytes `Coc.encode` writes for `words`' answer, on `i64` keys (codes `v ^ 2^63`, one-to-one with
    // the words): direct addressing (small ranges, unsorted), runs (wide ranges, sorted; one with a patch at the end), at
    // block edges; a wide unsorted range is the error
    #[test] fn blocks_is_encode_of_words() {
        let enc = |ws: &[u64]| { let o = Sink::new(ws.len(), 8, Form::For).answer(&Blocks::dense(pod::bytes(ws), 8)); [0, 1].map(|i| o.borrow().field(i).bytes().to_vec()) };
        let bytes = |o: &lean::O| [0, 1].map(|i| o.borrow().field(i).bytes().to_vec());
        for n in [0usize, 1, 1024, 1025, 5000] {
            let a: Vec<u64> = (0..n as u64).map(|i| (i * 7919) % 97).collect();
            let b: Vec<u64> = (0..n as u64).map(|i| (i / 300) % 2).collect();
            let s: Vec<u64> = (0..n as u64).map(|i| (i / 7) << 30).collect();
            let p: Vec<u64> = (0..n as u64).map(|i| i / 7 + if i + 1 == n as u64 { 1 << 40 } else { 0 }).collect();
            // constant on each run of `s`, so `[s, c]` is in order
            let c: Vec<u64> = (0..n as u64).map(|i| (i / 14) % 3).collect();
            let wide: Vec<u64> = a.iter().map(|x| x << 30).collect();
            for (cs, ok) in [(vec![a.clone()], true), (vec![a.clone(), b.clone()], true), (vec![b.clone()], true), (vec![s.clone()], true),
                             (vec![s.clone(), c.clone()], true), (vec![p.clone()], true), (vec![], true), (vec![wide.clone()], n < 2)] {
                let parts: Vec<[Vec<u8>; 2]> = cs.iter().map(|c| enc(c)).collect();
                let ks: Vec<Key> = parts.iter().map(|[m, q]| Key::new(coc::view(m, q, n).unwrap_or_else(|e| panic!("test column does not view: {e}")), (8, false, true))).collect();
                let ts = vec![4u8; ks.len()];
                match blocks(crate::c::pool(), &ts, &ks, n) {
                    Ok((k, g, f)) => {
                        assert!(ok, "n {n}: a wide unsorted key answered");
                        let (wg, wf) = words(&cs, n);
                        assert_eq!(k, wf.len(), "n {n}");
                        let want = |w: &[u64]| bytes(&Sink::new(w.len(), 8, Form::For).enc().answer(&Blocks::dense(pod::bytes(w), 8)));
                        assert_eq!(bytes(&g), want(&wg), "g, n {n}");
                        assert_eq!(bytes(&f), want(&wf), "first, n {n}");
                    }
                    Err(e) => assert!(!ok && e.starts_with("seen: key range of ") && e.contains("es[0] type 4"), "n {n}: {e}"),
                }
            }
        }
    }
}
