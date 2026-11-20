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

    // `blocks` writes the bytes `Coc.encode` writes for `words`' answer on sorted `i64` keys (codes `v ^ 2^63`,
    // one-to-one with the words), narrow and wide, ties across a block edge, a patch at the end, two columns; on keys out
    // of order, the first such row, at a block edge too; with a `pos` column after them, `til n` or the same error
}
