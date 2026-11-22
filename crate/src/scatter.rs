#![forbid(unsafe_code)]
//! `scatter`, the primitive that writes data to computed positions (design §4, `Kernel.kscatter` in
//! Rel/Kernel/Scatter.lean): `out[ix[k]] := op(out[ix[k]], e[k])` in row order over `n` cells that start as `fill`, `op`
//! an `Op` constructor index (`scan::op_eval`); `last` (19) is the plain write. An index `>= n` is an error naming
//! it, never dropped; a composition that discards a row sends it to a spare cell and cuts that cell off (WHERE,
//! doc/rel-kernels.md). Its `foR` arguments are read a block at a time (`blocks`) and its answer written by the encoder's
//! block step (`ffi::Sink`), so no column is decoded whole.
use alloc::{format, string::String};
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
use crate::blocks::{Blocks, Grid, Src};
use crate::enc::Producer;
use crate::ffi::Sink;
use crate::scan::{op_eval, op_word};
use crate::{lean, pod};


/// Rows `lo .. lo + nb` of `bl` as words, in `buf` (`16 * nb` bytes, 8-aligned) unless they lie in place.
fn rows<'s>(bl: &'s Blocks, lo: usize, nb: usize, buf: &'s mut [u8]) -> &'s [u64] {
    pod::cast(bl.block(0, lo, nb, 8, buf)).expect("qlean scatter: a block of words is misaligned")
}

/// Block `k` of `ix` as the least and the greatest index it holds, from its metadata alone: a `foR` block's `base`/`maxv`
/// where the least is not negative (as words they are then the unsigned bounds) and it holds no null, a `Pos` block its
/// own rows; `None` where only its elements could tell.
fn bounds(ix: &Blocks, k: usize) -> Option<(u64, u64)> {
    let (lo, nb) = ix.span(k);
    match ix.src {
        Src::For(c) if !c.meta.nul(k) && c.meta.base[k] >= 0 => Some((c.meta.base[k] as u64, c.meta.maxv[k] as u64)),
        Src::Pos => Some((lo as u64, (lo + nb - 1) as u64)),
        _ => None,
    }
}

/// `blocks` in one pass over `ix` and `e` where `ix`'s metadata orders its blocks (each block's greatest index at most the
/// next block's least): answer block `b` takes its rows from the `ix` blocks whose bounds meet its cells, found by binary
/// search on the metadata, and cuts them out of each decoded block by binary search. The answer block holding a block's
/// least index checks that block ascends; `None` where one does not (nothing is answered, the caller's general path runs).
/// The first error is the least row among the op's failures, which the answer blocks record, and the first index `>= n`.
fn ordered(op: u8, ix: &Blocks, e: &Blocks, n: usize, fill: u64) -> Option<Result<lean::O, String>> {
    let sp = (0..ix.nblk()).map(|k| bounds(ix, k)).collect::<Option<alloc::vec::Vec<_>>>()?;
    if sp.windows(2).any(|w| w[0].1 > w[1].0) { return None }
    let (sc, fails) = (ix.blk().max(e.blk()), op_eval(op, 0, 0).is_err());
    let (bad, err) = (AtomicBool::new(false), AtomicUsize::new(usize::MAX));
    let o = Sink::new(n, 8).enc().answer(&|o: &mut [i64], i0: usize| {
        o.fill(fill as i64);
        let (c0, c1) = (i0 as u64, (i0 + o.len()) as u64);
        let (mut bi, mut be) = (pod::uninit::<u64>(sc), pod::uninit::<u64>(sc));
        for k in sp.partition_point(|s| s.1 < c0)..sp.partition_point(|s| s.0 < c1) {
            let (lo, nb) = ix.span(k);
            let is = rows(ix, lo, nb, pod::bytes_mut(&mut bi));
            if sp[k].0 >= c0 && !is.is_sorted() { return bad.store(true, Relaxed) }
            let (r0, r1) = (is.partition_point(|&i| i < c0), is.partition_point(|&i| i < c1));
            let es = rows(e, lo + r0, r1 - r0, pod::bytes_mut(&mut be));
            for (j, (&i, &x)) in is[r0..r1].iter().zip(es).enumerate() {
                if fails && op_eval(op, 0, x).is_err() { err.fetch_min(lo + r0 + j, Relaxed); continue }
                let c = &mut o[(i - c0) as usize]; *c = op_word(op, *c as u64, x) as i64
            }
        }
    });
    if bad.load(Relaxed) { return None }
    // the first index `>= n`: in the first block reaching `n`, a block that ascends when its least index is below `n`
    let kb = sp.partition_point(|s| s.1 < n as u64);
    let past = (kb < sp.len()).then(|| {
        let (lo, nb) = ix.span(kb);
        let mut bi = pod::uninit::<u64>(sc);
        let is = rows(ix, lo, nb, pod::bytes_mut(&mut bi));
        let r = is.partition_point(|&i| i < n as u64);
        (lo + r, is[r])
    });
    let r = err.load(Relaxed);
    Some(match past {
        Some((p, i)) if p < r => Err(format!("scatter: index {i} at row {p} is not below n = {n}")),
        _ if r != usize::MAX => {
            let mut be = pod::uninit::<u64>(sc);
            let x = rows(e, r, 1, pod::bytes_mut(&mut be))[0];
            Err(format!("scatter: {} at row {r}", op_eval(op, 0, x).expect_err("qlean scatter: a recorded failure fails again")))
        }
        _ => Ok(o),
    })
}

/// `kscatter` past its layout checks: `scatterWords op` of the rows of `ix` and `e` (one length), encoded as
/// `Coc.encode 8` (`Enc.foR`), which the encoder's block step writes byte for byte. An index whose metadata orders its
/// blocks is written in one pass (`ordered`). Else pass 1 reads `ix` a block at a time (and `e`, for an op that can fail)
/// for the first error, the rows of each answer block and whether `ix` ascends; pass 2 writes each answer block from its
/// rows alone, each cell `fill` folded under `op_word` over its rows.
/// Owner approvals (PLAN 6.10): S, one block decoded into an L1 scratch (8 KiB) counts as per block; V, an index that
/// does not ascend is grouped by answer block first (two passes, `m` positions of 2 bytes and values of 8, no dense
/// array of `n` cells), each answer block then written in row order, so every cell folds its rows under `op` in row order.
pub fn blocks(op: u8, ix: &Blocks, e: &Blocks, n: usize, fill: u64) -> Result<lean::O, String> {
    if let Some(r) = ordered(op, ix, e, n, fill) { return r }
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
    /// The scatter bench (PLAN 6.10 scatter-once): `blocks` over 2^24 cells, 2^23 rows, ascending and unordered, `last`;
    /// `cargo test --release scatter::tests::bench -- --ignored --nocapture` prints the median wall time of each.
    #[test] #[ignore] fn bench() {
        extern crate std;
        let (n, m) = (1usize << 24, 1usize << 23);
        let es: Vec<u64> = (0..m as u64).map(|k| k * 3 + 1).collect();
        for (name, is) in [("asc", (0..m as u64).map(|k| 2 * k).collect::<Vec<_>>()), ("unordered", (0..m as u64).map(|k| (k * 7919) % n as u64).collect())] {
            let ([mi, pi], [me, pe]) = (enc(&is), enc(&es));
            let ci = coc::view(&mi, &pi, m).unwrap_or_else(|e| panic!("bench index does not view: {e}"));
            let ce = coc::view(&me, &pe, m).unwrap_or_else(|e| panic!("bench values do not view: {e}"));
            let mut ts: Vec<u128> = (0..15).map(|_| {
                let t = std::time::Instant::now();
                let o = blocks(LAST, &Blocks::from(ci), &Blocks::from(ce), n, 0).expect("bench scatter");
                core::hint::black_box(&o);
                t.elapsed().as_micros()
            }).collect();
            ts.sort();
            std::println!("scatter bench {name}: median {} us, min {} us", ts[7], ts[0]);
        }
    }
    // `blocks` against `words` on indices `ordered` answers (ascending, repeated, ending past `n`, sparse) and on ones it
    // hands back (a block out of order inside under ordered metadata), the answer or the first error alike
    #[test] fn ordered_is_words() {
        let (n, m) = (30000usize, 20000u64);
        let ups: Vec<u64> = (0..m).map(|k| k * 3 / 2).collect();
        let mut inside = ups.clone();
        inside.swap(5000, 5001);
        let cases = [ups.clone(), (0..m).map(|k| k / 7).collect(), (0..m).map(|k| if k < 19990 { k } else { n as u64 + k }).collect(),
                     (0..m / 100).map(|k| k * 297).collect(), inside, (0..m).map(|k| k * k % 29989).collect()];
        let ess = [(0..m).map(|k| k + 1).collect::<Vec<u64>>(), (0..m).map(|k| if k == 12345 { 0 } else { k + 1 }).collect()];
        for (c, is) in cases.iter().enumerate() {
            for es in &ess {
                for op in [LAST, DIV] {
                    let want = words(op, is, es, n, 7).map(|w| enc(&w));
                    assert_eq!(run(op, is, es, n, 7), want, "case {c} op {op}");
                }
            }
        }
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
