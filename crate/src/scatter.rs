#![forbid(unsafe_code)]
//! `scatter`, the primitive that writes data to computed positions (design §4, `Kernel.kscatter` in
//! Rel/Kernel/Scatter.lean): `out[ix[k]] := op(out[ix[k]], e[k])` in row order over `n` cells that start as `fill`, `op`
//! an `Op` constructor index (`scan::op_eval`); `last` (19) is the plain write. An index `>= n` is an error naming
//! it, never dropped; a composition that discards a row sends it to a spare cell and cuts that cell off (WHERE,
//! doc/rel-kernels.md). Its `foR` arguments are read a block at a time (`blocks`) and its answer written by the encoder's
//! block step (`ffi::Sink`), so no column is decoded whole.
use alloc::{format, string::String, vec};
use crate::blocks::{Blocks, Grid};
use crate::enc::Producer;
use crate::ffi::{Form, Sink};
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
    let (mut at, mut asc, mut prev) = (vec![0usize; g.nblk() + 1], true, 0u64);
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
    let s = Sink::new(n, 8, Form::For).enc();
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
        for j in at[b]..at[b + 1] { let c = &mut o[pos[j] as usize]; *c = op_word(op, *c as u64, val[j]) as i64 }
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coc;

    // `Op` constructor indices (Rel/Kernel/Op.lean)

    // `blocks` writes the bytes `Coc.encode` writes for `words`' answer under each op: ascending with repeats, a
    // permutation, a sparse index, repeats out of order, and no rows; collisions straddle the 1024-row blocks
    // the first error in row order, the bounds and the op's alike, on an ascending and on an unordered index
}
