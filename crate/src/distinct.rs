#![forbid(unsafe_code)]
//! `distinct` (design §4, `Kernel.kdistinct` in Rel/Kernel/Distinct.lean): on rows whose equal ones are contiguous,
//! the position of the first row of each run. The Lean body is `scan` (adjacent compare) then `scatter` (compact);
//! this is the fused form: the columns read a block at a time into a bitmap of run starts, the positions written from
//! it by the encoder's block step (`ffi::Sink`), so no column is decoded whole.
use alloc::{vec, vec::Vec};
use crate::blocks::{Blocks, Grid};
use crate::enc::Producer;
use crate::ffi::{Form, Sink};
use crate::{lean, pod};

/// `Kernel.distinctWords n cs`: the rows that start a run, row 0 and each row some column of `cs` changes at. The word
/// model `blocks` is tested against.
pub fn words(cs: &[Vec<u64>], n: usize) -> Vec<u64> {
    (0..n).filter(|&i| i == 0 || cs.iter().any(|c| c[i] != c[i - 1])).map(|i| i as u64).collect()
}

/// `kdistinct` past its layout checks: `distinctWords` of the `n` rows of `cs`, as `(k, Coc.encode 8 of the k starts)`
/// (`Enc.foR`). Pass 1 reads each column a block at a time and sets bit `i` of a bitmap (`n` bits) where row `i` starts
/// a run; pass 2 writes answer block `b`, positions `b * 2^lg ..`, from the bitmap words the per-block counts point it to.
/// Owner approval (PLAN 6.10) S: one block decoded into an L1 scratch (8 KiB) counts as per block.
pub fn blocks(cs: &[Blocks], n: usize) -> (usize, lean::O) {
    let g = Grid { n, lg: crate::DEFAULT_LG };
    let (wb, sc) = (g.blk() / 64, cs.iter().map(|c| c.blk()).max().unwrap_or(0).max(g.blk()));
    let (mut bits, mut buf) = (vec![0u64; n.div_ceil(64)], pod::uninit::<u64>(sc));
    // `last[c]`: column `c`'s row before the block, `None` before row 0 (which starts a run with or without columns)
    let mut last: Vec<Option<u64>> = vec![None; cs.len()];
    for (b, lo, nb) in g.walk() {
        let w = &mut bits[b * wb..(lo + nb).div_ceil(64)];
        if lo == 0 { w[0] |= 1 }
        for (c, l) in cs.iter().zip(&mut last) {
            let x = pod::cast::<u64>(c.block(0, lo, nb, 8, pod::bytes_mut(&mut buf))).expect("qlean distinct: a block of words is misaligned");
            if l.is_some_and(|p| p != x[0]) { w[0] |= 1 }
            for k in 1..nb { w[k >> 6] |= ((x[k] != x[k - 1]) as u64) << (k & 63) }
            *l = Some(x[nb - 1]);
        }
    }
    // `at[b]`: the starts before block `b` of the rows, so answer position `p` lies in the first row block whose `at` passes it
    let mut at = vec![0usize; g.nblk() + 1];
    for b in 0..g.nblk() { at[b + 1] = at[b] + bits[b * wb..(b * wb + wb).min(bits.len())].iter().map(|w| w.count_ones() as usize).sum::<usize>() }
    let k = at[g.nblk()];
    let o = Sink::new(k, 8, Form::For).enc().answer(&|o: &mut [i64], p0: usize| {
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
    (k, o)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use crate::coc;

    #[test] fn a_run_starts_where_any_column_changes() {
        // rows (1,0) (1,0) (2,0) (2,1) (2,1): runs start at 0, 2, 3
        assert_eq!(words(&[vec![1, 1, 2, 2, 2], vec![0, 0, 0, 1, 1]], 5), vec![0, 2, 3]);
        // no column: every row is the empty row, one run; no row: no run
        assert_eq!(words(&[], 3), vec![0]);
        assert_eq!(words(&[vec![]], 0), Vec::<u64>::new());
    }
    // `blocks` writes the bytes `Coc.encode` writes for `words`' answer: runs crossing block edges, a change on an edge,
    // two columns, every row a start, no column, no row
    #[test] fn blocks_is_encode_of_words() {
        let enc = |ws: &[u64]| { let o = Sink::new(ws.len(), 8, Form::For).answer(&Blocks::dense(pod::bytes(ws), 8)); [0, 1].map(|i| o.borrow().field(i).bytes().to_vec()) };
        for n in [0usize, 1, 1024, 1025, 5000] {
            let a: Vec<u64> = (0..n as u64).map(|i| i / 7 + if i % 1024 == 0 { 1 << 40 } else { 0 }).collect();
            let b: Vec<u64> = (0..n as u64).map(|i| (i / 300) % 2).collect();
            let all: Vec<u64> = (0..n as u64).collect();
            for cs in [vec![a.clone()], vec![a.clone(), b.clone()], vec![b.clone()], vec![all], vec![]] {
                let parts: Vec<[Vec<u8>; 2]> = cs.iter().map(|c| enc(c)).collect();
                let bl: Vec<Blocks> = parts.iter().map(|[m, p]| Blocks::from(coc::view(m, p, n).unwrap_or_else(|e| panic!("test column does not view: {e}")))).collect();
                let (k, got) = blocks(&bl, n);
                let w = words(&cs, n);
                let want = Sink::new(w.len(), 8, Form::For).enc().answer(&Blocks::dense(pod::bytes(&w), 8));
                assert_eq!(k, w.len(), "n {n}");
                assert_eq!([0, 1].map(|i| got.borrow().field(i).bytes().to_vec()), [0, 1].map(|i| want.borrow().field(i).bytes().to_vec()), "n {n}");
            }
        }
    }
}
