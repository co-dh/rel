#![forbid(unsafe_code)]
//! `seen` (PLAN D.12, `Kernel.kseen` in Rel/Kernel/Seen.lean): over rows already in `kasc` order, each row's group,
//! groups numbered by first occurrence under the equality of `kasc`'s order codes, and each group's first row. Callers
//! compose `kasc ≫ kseen`, so a group is a run of adjacent equal rows and one pass, each row against the one before it,
//! finds the runs: no hash, no direct-addressing table. Rows out of order are the error, naming the first such pair.
//! Owner approval (PLAN 6.10) S: one block decoded into an L1 scratch counts as per block.
use alloc::{format, string::String, vec};
use core::cmp::Ordering;
use crate::asc::Col;
use crate::blocks::{Blocks, Grid};
use crate::ffi::{Form, Sink};
use crate::lean;


/// `Kernel.kseen`'s error where row `i + 1` sorts before row `i`, word for word the Lean body's.
pub fn unsorted(i: usize) -> String {
    format!("seen: row {} sorts before row {i}; kseen takes rows in kasc order, so sort them with kasc first", i + 1)
}

/// `kseen` past its column checks, on the keys `ks` at `n` rows: `(k, g, first)`, `g` and `first` as `Coc.encode 8`
/// writes them. `pos` says a `pos` column follows `ks` (the columns after it neither order nor split rows): every row
/// is then its own group, `til n` twice, and `ks` need only be in order with ties. Rows out of `lexLe` order are the
/// error (`unsorted`).
pub fn blocks(ks: &[Col], n: usize, pos: bool) -> Result<(usize, lean::O, lean::O), String> {
    let g = Grid { n, lg: crate::DEFAULT_LG };
    let (blk, wb) = (g.blk(), g.blk() / 64);
    // bit `i` of `bits`: row `i` starts a run (row 0, and each row greater than the one before it)
    let (mut bits, mut x, mut buf) = (vec![0u64; n.div_ceil(64)], vec![0u64; blk], vec![0u64; 2 * blk]);
    // `last[c]`: atom key `c`'s code at the row before the block; `st[j]`: row `j` against the row before it, 0 equal so
    // far, 1 greater, 2 less, decided by the first column where the two differ
    let (mut last, mut st) = (vec![0u64; ks.len()], vec![0u8; blk]);
    for (_, lo, nb) in g.walk() {
        st[..nb].fill(0);
        for (k, l) in ks.iter().zip(last.iter_mut()) {
            match k {
                Col::Atom(k) => {
                    k.codes(lo, &mut x[..nb], &mut buf);
                    for (j, s) in st[..nb].iter_mut().enumerate() {
                        let p = if j == 0 { *l } else { x[j - 1] };
                        if *s == 0 && (lo > 0 || j > 0) && x[j] != p { *s = if x[j] > p { 1 } else { 2 } }
                    }
                    *l = x[nb - 1];
                }
                // a row against the one before it, its cells read where they lie (`Cells::cmp`)
                Col::Cells(a) => for (j, s) in st[..nb].iter_mut().enumerate() {
                    if *s == 0 && lo + j > 0 { *s = match a.cmp(lo + j - 1, lo + j) { Ordering::Less => 1, Ordering::Greater => 2, Ordering::Equal => 0 } }
                },
                // a `pos` column ascends with no ties: every row after the first is greater
                Col::Pos => for (j, s) in st[..nb].iter_mut().enumerate() { if *s == 0 && lo + j > 0 { *s = 1 } },
            }
        }
        if let Some(j) = st[..nb].iter().position(|&s| s == 2) { return Err(unsorted(lo + j - 1)) }
        let w = &mut bits[lo / 64..(lo + nb).div_ceil(64)];
        if lo == 0 { w[0] |= 1 }
        for (j, &s) in st[..nb].iter().enumerate() { w[j >> 6] |= ((s == 1) as u64) << (j & 63) }
    }
    if pos {
        let til = || Sink::new(n, 8, Form::For).enc().answer(&Blocks::pos(n));
        return Ok((n, til(), til()))
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
    Ok((k, go, fo))
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
    /// The first `i` with row `i + 1` lexicographically below row `i` over the code columns `cs`: `kseen`'s order test.
    fn first_unsorted(cs: &[Vec<u64>], n: usize) -> Option<usize> {
        (0..n.saturating_sub(1)).find(|&i| cs.iter().map(|c| c[i + 1]).lt(cs.iter().map(|c| c[i])))
    }
    // `blocks` writes the bytes `Coc.encode` writes for `words`' answer on sorted `i64` keys (codes `v ^ 2^63`,
    // one-to-one with the words), narrow and wide, ties across a block edge, a patch at the end, two columns; on keys out
    // of order, the first such row, at a block edge too; with a `pos` column after them, `til n` or the same error
    #[test] fn blocks_is_encode_of_words() {
        let enc = |ws: &[u64]| { let o = Sink::new(ws.len(), 8, Form::For).answer(&Blocks::dense(pod::bytes(ws), 8)); [0, 1].map(|i| o.borrow().field(i).bytes().to_vec()) };
        let bytes = |o: &lean::O| [0, 1].map(|i| o.borrow().field(i).bytes().to_vec());
        let want = |w: &[u64]| bytes(&Sink::new(w.len(), 8, Form::For).enc().answer(&Blocks::dense(pod::bytes(w), 8)));
        for n in [0usize, 1, 2, 1024, 1025, 5000] {
            let a: Vec<u64> = (0..n as u64).map(|i| (i * 7919) % 97).collect();
            let b: Vec<u64> = (0..n as u64).map(|i| (i / 300) % 2).collect();
            let s: Vec<u64> = (0..n as u64).map(|i| (i / 7) << 30).collect();
            let p: Vec<u64> = (0..n as u64).map(|i| i / 7 + if i + 1 == n as u64 { 1 << 40 } else { 0 }).collect();
            // constant on each run of `s`, so `[s, c]` is in order; `[s, d]` breaks it inside a run of `s`
            let c: Vec<u64> = (0..n as u64).map(|i| (i / 14) % 3).collect();
            let d: Vec<u64> = (0..n as u64).map(|i| (i + 3) % 7).collect();
            // one tie across the block edge at 1024, then a drop at the edge itself
            let e: Vec<u64> = (0..n as u64).map(|i| (i >= 1020) as u64).collect();
            let f: Vec<u64> = (0..n as u64).map(|i| (i < 1024) as u64).collect();
            for cs in [vec![a.clone()], vec![b.clone()], vec![s.clone()], vec![s.clone(), c.clone()], vec![s.clone(), d.clone()],
                       vec![p.clone()], vec![e.clone()], vec![f.clone()], vec![b.clone(), a.clone()], vec![]] {
                let parts: Vec<[Vec<u8>; 2]> = cs.iter().map(|c| enc(c)).collect();
                let ks: Vec<Col> = parts.iter().map(|[m, q]| Col::Atom(crate::asc::Key::new(coc::view(m, q, n).unwrap_or_else(|e| panic!("test column does not view: {e}")), (8, false, true)))).collect();
                let bad = first_unsorted(&cs, n);
                for pos in [false, true] {
                    match (blocks(&ks, n, pos), bad) {
                        (Ok((k, g, f)), None) => {
                            let (wg, wf) = if pos { ((0..n as u64).collect(), (0..n as u64).collect()) } else { words(&cs, n) };
                            assert_eq!(k, wf.len(), "n {n}");
                            assert_eq!(bytes(&g), want(&wg), "g, n {n}");
                            assert_eq!(bytes(&f), want(&wf), "first, n {n}");
                        }
                        (Err(e), Some(i)) => assert_eq!(e, unsorted(i), "n {n}"),
                        (r, bad) => panic!("n {n} pos {pos}: answered {:?}, first row out of order {bad:?}", r.map(|r| r.0)),
                    }
                }
            }
        }
    }
}
