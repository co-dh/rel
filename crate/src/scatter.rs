#![forbid(unsafe_code)]
//! `scatter`, the primitive that writes data to computed positions (design §4, `Kernel.kscatter` in
//! Rel/Kernel/Scatter.lean): `out[ix[k]] := op(out[ix[k]], e[k])` in row order over `n` cells that start as `fill`, `op`
//! an `Op` constructor index (`scan::op_eval`); `last` (19) is the plain write. An index `>= n` is an error naming
//! it, never dropped; a composition that discards a row sends it to a spare cell and cuts that cell off (WHERE,
//! doc/rel-kernels.md). Its `foR` arguments are read a block at a time (`blocks`) and its answer written by the encoder's
//! block step (`ffi::Sink`), so no column is decoded whole.
use alloc::{format, string::String};
use crate::blocks::{Blocks, Grid};
use crate::enc::Producer;
use crate::ffi::Sink;
use crate::scan::{op_eval, op_word};
use crate::{lean, pod};


/// Rows `lo .. lo + nb` of `bl` as words, in `buf` (`16 * nb` bytes, 8-aligned) unless they lie in place.
fn rows<'s>(bl: &'s Blocks, lo: usize, nb: usize, buf: &'s mut [u8]) -> &'s [u64] {
    pod::cast(bl.block(0, lo, nb, 8, buf)).expect("qlean scatter: a block of words is misaligned")
}

/// `kscatter` past its layout checks: `scatterWords op` of the rows of `ix` and `e` (one length), encoded as
/// `Coc.encode 8` (`Enc.foR`), which the encoder's block step writes byte for byte. Pass 1 reads `ix` a block at a time
/// (and `e`, for an op that can fail) for the first error, the rows of each answer block and whether `ix` ascends; pass 2
/// writes each answer block from its rows alone, each cell `fill` folded under `op_word` over its rows.
/// Owner approvals (PLAN 6.10): S, one block decoded into an L1 scratch (8 KiB) counts as per block; V, an index that
/// does not ascend is grouped by answer block first (two passes, `m` positions of 2 bytes and values of 8, no dense
/// array of `n` cells), each answer block then written in row order, so every cell folds its rows under `op` in row order.
pub fn blocks(op: u8, ix: &Blocks, e: &Blocks, n: usize, fill: u64) -> Result<lean::O, String> {
    let g = Grid { n, lg: crate::DEFAULT_LG };
    // a 2-byte offset in pass V's groups holds a block of at most 2^16
    let (lg, blk, sc) = (g.lg, g.blk(), ix.blk().max(e.blk()));
    const { assert!(crate::DEFAULT_LG <= 16) }
    let (mut buf, mut eb) = (pod::uninit::<u64>(sc), pod::uninit::<u64>(sc));
    // `Op.eval` fails on the element alone (`div`/`mod` by 0), never on the cell, so pass 1 finds the first failing row
    // from `e` without the cells; `e` is read here only for an op that can fail at all
    let fails = op_eval(op, 0, 0).is_err();
    // `at[b] .. at[b + 1]`: the rows answer block `b` takes, in row order once grouped
    let (mut at, mut asc, mut prev) = (pod::vec_of("scatter", "the answer blocks' row counts", g.nblk() + 1, 0usize)?, true, 0u64);
    for (_, lo, nb) in ix.walk() {
        let es: &[u64] = if fails { rows(e, lo, nb, pod::bytes_mut(&mut eb)) } else { &[] };
        for (k, &i) in rows(ix, lo, nb, pod::bytes_mut(&mut buf)).iter().enumerate() {
            if i >= n as u64 { return Err(format!("scatter: index {i} at row {} is not below n = {n}", lo + k)) }
            if fails && let Err(s) = op_eval(op, 0, es[k]) { return Err(format!("scatter: {s} at row {}", lo + k)) }
            (asc, prev) = (asc && prev <= i, i);
            at[(i >> lg) as usize + 1] += 1;
        }
    }
    for b in 0..g.nblk() { at[b + 1] += at[b] }
    let s = Sink::new(n, 8).enc();
    if asc {
        // an ascending index hands answer block `b` the contiguous rows `at[b] .. at[b + 1]`, cut on `ix`'s own grid
        return Ok(s.answer(&|o: &mut [i64], i0: usize| {
            o.fill(fill as i64);
            let (b, mut bi, mut be) = (i0 >> lg, pod::uninit::<u64>(sc), pod::uninit::<u64>(sc));
            for (_, _, r0, r1) in ix.tiles(at[b], at[b + 1]) {
                let (is, es) = (rows(ix, r0, r1 - r0, pod::bytes_mut(&mut bi)), rows(e, r0, r1 - r0, pod::bytes_mut(&mut be)));
                for (&i, &x) in is.iter().zip(es) { let c = &mut o[i as usize - i0]; *c = op_word(op, *c as u64, x) as i64 }
            }
        }))
    }
    // V: each row's offset in its answer block and its value, grouped by answer block in row order
    let (mut pos, mut val) = (pod::try_uninit::<u16>("scatter", "the rows' offsets", ix.n)?, pod::try_uninit::<u64>("scatter", "the rows' values", ix.n)?);
    let mut cur = pod::vec_of("scatter", "the answer blocks' cursors", at.len(), 0usize)?;
    cur.copy_from_slice(&at);
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
        for j in at[b]..at[b + 1] { let c = &mut o[pos[j] as usize]; *c = op_word(op, *c as u64, val[j]) as i64 }
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coc;
    use alloc::{vec, vec::Vec};

    /// `Kernel.scatterWords op is es n fill`: rows in order, each cell becoming `op_eval(op, cell, e)`; the first row whose
    /// index is not below `n`, or whose step fails, is the error. The word model `blocks` is tested against.
    fn words(op: u8, is: &[u64], es: &[u64], n: usize, fill: u64) -> Result<Vec<u64>, String> {
        let mut o = vec![fill; n];
        for (k, (&i, &x)) in is.iter().zip(es).enumerate() {
            if i >= n as u64 { return Err(format!("scatter: index {i} at row {k} is not below n = {n}")) }
            o[i as usize] = op_eval(op, o[i as usize], x).map_err(|s| format!("scatter: {s} at row {k}"))?;
        }
        Ok(o)
    }

    // `Op` constructor indices (Rel/Kernel/Op.lean)
    const DIV: u8 = 3;
    const LAST: u8 = 19;

    #[test] fn index_past_n_is_an_error() {
        assert_eq!(words(LAST, &[1, 5, 9], &[1, 2, 3], 3, 0), Err("scatter: index 5 at row 1 is not below n = 3".into()));
    }
    #[test] fn op_error_names_its_row() {
        assert_eq!(words(DIV, &[0, 0], &[5, 0], 1, 100), Err("scatter: Op.div: integer division by 0 at row 1".into()));
    }
    /// `Coc.encode 8` of `ws` as `(meta, pack)`, the form a `foR` argument holds
    fn enc(ws: &[u64]) -> [Vec<u8>; 2] {
        let o = Sink::new(ws.len(), 8).answer(&Blocks::dense(pod::bytes(ws), 8));
        [0, 1].map(|i| o.borrow().field(i).bytes().to_vec())
    }
    fn answer(o: &lean::O) -> [Vec<u8>; 2] { [0, 1].map(|i| o.borrow().field(i).bytes().to_vec()) }
    fn run(op: u8, is: &[u64], es: &[u64], n: usize, fill: u64) -> Result<[Vec<u8>; 2], String> {
        let ([mi, pi], [me, pe]) = (enc(is), enc(es));
        let ci = coc::view(&mi, &pi, is.len()).unwrap_or_else(|e| panic!("test column does not view: {e}"));
        let ce = coc::view(&me, &pe, es.len()).unwrap_or_else(|e| panic!("test column does not view: {e}"));
        blocks(op, &Blocks::from(ci), &Blocks::from(ce), n, fill).map(|o| answer(&o))
    }
    // the first error in row order, the bounds and the op's alike, on an ascending and on an unordered index
    #[test] fn blocks_errors_are_words_errors() {
        let n = 5000usize;
        let es: Vec<u64> = (0..3000u64).map(|k| if k == 1500 { 0 } else { k + 1 }).collect();
        for bad in [1000u64, 2100] {
            for is in [(0..3000u64).collect::<Vec<_>>(), (0..3000u64).map(|k| (k * 7919) % 3000).collect()] {
                let is: Vec<u64> = is.iter().enumerate().map(|(k, &i)| if k as u64 == bad { n as u64 + 3 } else { i }).collect();
                for op in [LAST, DIV] {
                    let want = words(op, &is, &es, n, 0).unwrap_err();
                    assert_eq!(run(op, &is, &es, n, 0), Err(want), "op {op} bad {bad}");
                }
            }
        }
    }
}
