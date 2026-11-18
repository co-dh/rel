#![forbid(unsafe_code)]
//! `scatter`, the primitive that writes data to computed positions (design §4, `Kernel.kscatter` in
//! Rel/Kernel/Scatter.lean): `out[ix[k]] = e[k]` over `n` cells that start as `fill`. An index `>= n` is an error naming
//! it, never dropped; a composition that discards a row sends it to a spare cell and cuts that cell off (WHERE,
//! doc/rel-kernels.md). Its `foR` arguments are read a block at a time (`blocks`) and its answer written by the encoder's
//! block step (`ffi::Sink`), so no column is decoded whole.
use alloc::{format, string::String, vec, vec::Vec};
use crate::blocks::{Blocks, Grid};
use crate::enc::Producer;
use crate::ffi::{Form, Sink};
use crate::{lean, pod};

/// `Kernel.scatterWords is es n fill`: rows in order, so the last row naming a cell is the one it keeps; the first row
/// whose index is not below `n` is the error. The word model `blocks` is tested against.
pub fn words(is: &[u64], es: &[u64], n: usize, fill: u64) -> Result<Vec<u64>, String> {
    let mut o = vec![fill; n];
    for (k, (&i, &x)) in is.iter().zip(es).enumerate() {
        if i >= n as u64 { return Err(format!("scatter: index {i} at row {k} is not below n = {n}")) }
        o[i as usize] = x;
    }
    Ok(o)
}

/// Rows `lo .. lo + nb` of `bl` as words, in `buf` (`16 * nb` bytes, 8-aligned) unless they lie in place.
fn rows<'s>(bl: &'s Blocks, lo: usize, nb: usize, buf: &'s mut [u8]) -> &'s [u64] {
    pod::cast(bl.block(0, lo, nb, 8, buf)).expect("qlean scatter: a block of words is misaligned")
}

/// `kscatter` past its layout checks: `scatterWords` of the rows of `ix` and `e` (one length), encoded as `Coc.encode 8`
/// (`Enc.foR`), which the encoder's block step writes byte for byte. Pass 1 reads `ix` a block at a time for the bounds
/// error, the rows of each answer block and whether `ix` ascends; pass 2 writes each answer block from its rows alone.
/// Owner approvals (PLAN 6.10): S, one block decoded into an L1 scratch (8 KiB) counts as per block; V, an index that
/// does not ascend is grouped by answer block first (two passes, `m` positions of 2 bytes and values of 8, no dense
/// array of `n` cells), each answer block then written in row order, so the last row naming a cell still wins.
pub fn blocks(ix: &Blocks, e: &Blocks, n: usize, fill: u64) -> Result<lean::O, String> {
    let g = Grid { n, lg: crate::DEFAULT_LG };
    // a 2-byte offset in pass V's groups holds a block of at most 2^16
    let (lg, blk, sc) = (g.lg, g.blk(), ix.blk().max(e.blk()));
    const { assert!(crate::DEFAULT_LG <= 16) }
    let mut buf = pod::uninit::<u64>(sc);
    // `at[b] .. at[b + 1]`: the rows answer block `b` takes, in row order once grouped
    let (mut at, mut asc, mut prev) = (vec![0usize; g.nblk() + 1], true, 0u64);
    for (_, lo, nb) in ix.walk() {
        for (k, &i) in rows(ix, lo, nb, pod::bytes_mut(&mut buf)).iter().enumerate() {
            if i >= n as u64 { return Err(format!("scatter: index {i} at row {} is not below n = {n}", lo + k)) }
            (asc, prev) = (asc && prev <= i, i);
            at[(i >> lg) as usize + 1] += 1;
        }
    }
    for b in 0..g.nblk() { at[b + 1] += at[b] }
    let s = Sink::new(n, 8, Form::For).enc();
    if asc {
        // an ascending index hands answer block `b` the contiguous rows `at[b] .. at[b + 1]`, cut on `ix`'s own grid
        return Ok(s.answer(&|o: &mut [i64], i0: usize| {
            o.fill(fill as i64);
            let (b, mut bi, mut be) = (i0 >> lg, pod::uninit::<u64>(sc), pod::uninit::<u64>(sc));
            for (_, _, r0, r1) in ix.tiles(at[b], at[b + 1]) {
                let (is, es) = (rows(ix, r0, r1 - r0, pod::bytes_mut(&mut bi)), rows(e, r0, r1 - r0, pod::bytes_mut(&mut be)));
                for (&i, &x) in is.iter().zip(es) { o[i as usize - i0] = x as i64 }
            }
        }))
    }
    // V: each row's offset in its answer block and its value, grouped by answer block in row order
    let (mut pos, mut val, mut cur) = (pod::uninit::<u16>(ix.n), pod::uninit::<u64>(ix.n), at.clone());
    let mut eb = pod::uninit::<u64>(sc);
    for (_, lo, nb) in ix.walk() {
        let (is, es) = (rows(ix, lo, nb, pod::bytes_mut(&mut buf)), rows(e, lo, nb, pod::bytes_mut(&mut eb)));
        for (&i, &x) in is.iter().zip(es) {
            let c = &mut cur[(i >> lg) as usize];
            (pos[*c], val[*c], *c) = ((i & (blk as u64 - 1)) as u16, x, *c + 1);
        }
    }
    Ok(s.answer(&|o: &mut [i64], i0: usize| {
        o.fill(fill as i64);
        let b = i0 >> lg;
        for j in at[b]..at[b + 1] { o[pos[j] as usize] = val[j] as i64 }
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coc;

    #[test] fn last_write_wins_and_fill_stays() {
        assert_eq!(words(&[2, 0, 2], &[10, 11, 12], 4, 7), Ok(vec![11, 7, 12, 7]));
    }
    #[test] fn index_past_n_is_an_error() {
        assert_eq!(words(&[1, 5, 9], &[1, 2, 3], 3, 0), Err("scatter: index 5 at row 1 is not below n = 3".into()));
    }
    /// `Coc.encode 8` of `ws` as `(meta, pack)`, the form a `foR` argument holds
    fn enc(ws: &[u64]) -> [Vec<u8>; 2] {
        let o = Sink::new(ws.len(), 8, Form::For).answer(&Blocks::dense(pod::bytes(ws), 8));
        [0, 1].map(|i| o.borrow().field(i).bytes().to_vec())
    }
    fn answer(o: &lean::O) -> [Vec<u8>; 2] { [0, 1].map(|i| o.borrow().field(i).bytes().to_vec()) }
    // `blocks` writes the bytes `Coc.encode` writes for `words`' answer: ascending with repeats, a permutation, a sparse
    // index, repeats out of order, and no rows; and the bounds error names the first row in order
    #[test] fn blocks_is_encode_of_words() {
        let n = 5000usize;
        let perm: Vec<u64> = (0..n as u64).map(|k| (k * 2654435761) % n as u64).collect();
        let cases: [Vec<u64>; 5] = [(0..3000u64).map(|k| k * 5 / 3).collect(), perm, (0..40u64).map(|k| k * 117).collect(),
            (0..4000u64).map(|k| (k * 7919) % 900 + (k % 3) * 1500).collect(), vec![]];
        for is in cases {
            let es: Vec<u64> = (0..is.len() as u64).map(|k| 1000 + (k * 31) % 777 + if k % 97 == 5 { k << 30 } else { 0 }).collect();
            let ([mi, pi], [me, pe]) = (enc(&is), enc(&es));
            let (ci, ce) = (coc::view(&mi, &pi, is.len()).unwrap_or_else(|e| panic!("test column does not view: {e}")), coc::view(&me, &pe, es.len()).unwrap_or_else(|e| panic!("test column does not view: {e}")));
            let got = blocks(&Blocks::from(ci), &Blocks::from(ce), n, 9).unwrap();
            let want = Sink::new(n, 8, Form::For).enc().answer(&Blocks::dense(pod::bytes(&words(&is, &es, n, 9).unwrap()), 8));
            assert_eq!(answer(&got), answer(&want), "m {}", is.len());
        }
        let is: Vec<u64> = (0..3000u64).map(|k| if k == 2100 || k == 2500 { n as u64 + k } else { k }).collect();
        let [mi, pi] = enc(&is);
        let b = Blocks::from(coc::view(&mi, &pi, is.len()).unwrap_or_else(|e| panic!("test column does not view: {e}")));
        assert_eq!(blocks(&b, &b, n, 0).err(), words(&is, &is, n, 0).err());
    }
}
