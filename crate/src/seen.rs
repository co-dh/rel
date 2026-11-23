#![forbid(unsafe_code)]
//! `seen` (PLAN D.12, `Kernel.kseen` in Rel/Kernel/Seen.lean): over rows already in `kasc` order, each row's group,
//! groups numbered by first occurrence under the equality of `kasc`'s order codes, and each group's first row. Callers
//! compose `kasc ≫ kseen`, so a group is a run of adjacent equal rows and one pass, each row against the one before it,
//! finds the runs: no hash, no direct-addressing table. Rows out of order are the error, naming the first such pair.
//! Owner approval (PLAN 6.10) S: one block decoded into an L1 scratch counts as per block.
use alloc::{format, string::String, vec, vec::Vec};
use crate::asc::{self, Col};
use crate::pod;
use crate::blocks::{Blocks, Grid};
use crate::ffi::Sink;
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
    let (mut bits, mut x, mut buf) = (pod::vec_of("seen", "the run starts' bits", n.div_ceil(64), 0u64)?, vec![0u64; blk], vec![0u64; 2 * blk]);
    // `last[c]`: atom key `c`'s code at the row before the block; `st[j]`: row `j` against the row before it, 0 equal so
    // far, 1 greater, 2 less, decided by the first column where the two differ
    // a `cells` or `Nul` column's working keys (`asc::work`: a cell's rank a row; a null's flag, then its code), built
    // once and then read as an atom's codes; `src` every code column in `ascCol`'s order, `None` a `pos` one
    let cc: Vec<Vec<Vec<u64>>> = ks.iter().map(|k| match k { Col::Atom(_) | Col::Pos => Ok(Vec::new()), k => asc::work(k, n) }).collect::<Result<_, String>>()?;
    let src: Vec<Option<Result<&asc::Key, &[u64]>>> = ks.iter().zip(&cc).flat_map(|(k, c)| match k {
        Col::Atom(k) => vec![Some(Ok(k))],
        Col::Pos => vec![None],
        _ => c.iter().map(|v| Some(Err(&v[..]))).collect(),
    }).collect();
    let (mut last, mut st) = (vec![0u64; src.len()], vec![0u8; blk]);
    for (_, lo, nb) in g.walk() {
        st[..nb].fill(0);
        for (k, l) in src.iter().zip(last.iter_mut()) {
            let x: &[u64] = match k {
                Some(Ok(k)) => { k.codes(lo, &mut x[..nb], &mut buf); &x[..nb] }
                Some(Err(c)) => &c[lo..lo + nb],
                // a `pos` column ascends with no ties: every row after the first is greater
                None => { for (j, s) in st[..nb].iter_mut().enumerate() { if *s == 0 && lo + j > 0 { *s = 1 } } continue }
            };
            for (j, s) in st[..nb].iter_mut().enumerate() {
                let p = if j == 0 { *l } else { x[j - 1] };
                if *s == 0 && (lo > 0 || j > 0) && x[j] != p { *s = if x[j] > p { 1 } else { 2 } }
            }
            *l = x[nb - 1];
        }
        if let Some(j) = st[..nb].iter().position(|&s| s == 2) { return Err(unsorted(lo + j - 1)) }
        let w = &mut bits[lo / 64..(lo + nb).div_ceil(64)];
        if lo == 0 { w[0] |= 1 }
        for (j, &s) in st[..nb].iter().enumerate() { w[j >> 6] |= ((s == 1) as u64) << (j & 63) }
    }
    if pos {
        let til = || Sink::new(n, 8)?.enc().answer(&Blocks::pos(n));
        return Ok((n, til()?, til()?))
    }
    let bit = |i: usize| bits[i >> 6] >> (i & 63) & 1 == 1;
    // `at[b]`: the starts before block `b`
    let mut at = pod::vec_of("seen", "the blocks' start counts", g.nblk() + 1, 0usize)?;
    for b in 0..g.nblk() { at[b + 1] = at[b] + bits[b * wb..(b * wb + wb).min(bits.len())].iter().map(|w| w.count_ones() as usize).sum::<usize>() }
    let k = at[g.nblk()];
    let go = Sink::new(n, 8)?.enc().answer(&|o: &mut [i64], i0: usize| {
        let mut c = at[i0 / blk] + (i0 / blk * blk..i0).filter(|&i| bit(i)).count();
        for (j, x) in o.iter_mut().enumerate() { c += bit(i0 + j) as usize; *x = c as i64 - 1 }
    });
    // answer position `p` lies in the first row block whose `at` passes it
    let fo = Sink::new(k, 8)?.enc().answer(&|o: &mut [i64], p0: usize| {
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
    Ok((k, go?, fo?))
}
