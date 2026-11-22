#![forbid(unsafe_code)]
//! `gather`, the kernel that reads data at computed positions (design §4, `Kernel.kgather` in Rel/Kernel/Gather.lean):
//! `out[i] = e[ix[i]]`. The Lean body is the composition concat → asc → scan fill → scatter; this is its fused form, one
//! read per row (`Rel.Verify.gatherWords_eq`). An index `>= n` is an error naming it, never a fill.
use alloc::{format, string::String, vec::Vec};
use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use crate::{blocks::Blocks, coc::Coc, codec, enc::Producer, ffi::Sink, lean, pod, structural};


/// `words` on the encoded columns `ix` (`ix.meta.n` rows) and `e` (`e.meta.n` elements), answered as `Coc.encode 8`
/// writes `words`' result (`Enc.foR`), with `words`' error text.
///
/// Per block (owner approval S, PLAN 6.10: one block decoded into an L1 scratch of 8 KiB at a time is per-block work):
/// answer block `b` decodes index rows `b`'s span only, reads `e` only where they point (`structural::enc`: a flat
/// address where `e` has one width and no patch, else `Coc::get` by address, a long run in one block decoding that block
/// into the scratch), and goes to the encoder's block step through `Sink`. The index column is never decoded whole and
/// no per-row `Result` is collected: a row past `n` is read as 0 and marked, and the first marked row is the error.
///
/// Decodes the source once when #idx ≥ #src and the source is not flat (approved 2026-11-18: the decode is O(n) ≤ the
/// O(m) output, and a flat column already reads in one load): each read is then one load from the dense words. Not flat
/// is `structural::enc`'s own test, `one_width() == 255` (blocks of unequal widths, or a patch list).
pub fn enc(ix: &Blocks, e: &Coc) -> Result<lean::O, String> {
    let sw = e.one_width();
    let d = if ix.n >= e.meta.n && sw == 255 {
        let mut d = pod::vec_of("gather", "the dense e", e.meta.n, 0i64)?;
        codec::decode(crate::c::pool(), e, &mut d);
        Some(d)
    } else { None };
    let t = Take { ix: *ix, e: *e, sw, d, bad: AtomicUsize::new(usize::MAX) };
    // a null of `e` is a value: its bit (`Coc::nuls`, read on the flagged blocks) is gathered by the same indices, a
    // block of `ix` at a time; an index past `e` reads no bit, and is the error below
    let nul = match e.nuls() {
        None => None,
        Some(en) => {
            let (mut o, mut buf) = (pod::vec_of("gather", "the answer's null bits", ix.n.div_ceil(8), 0u8)?, pod::Scr::<u64>::new(ix.blk()));
            for (b, lo, _) in ix.walk() {
                let x = pod::cast::<i64>(ix.view(b, 8, pod::bytes_mut(&mut buf))).expect("qlean gather: an index block buffer is misaligned for i64");
                for (k, &u) in x.iter().enumerate() {
                    if (u as u64) < e.meta.n as u64 && crate::enc::is_nul(&en, u as usize) { o[(lo + k) >> 3] |= 1 << ((lo + k) & 7) }
                }
            }
            Some(o)
        }
    };
    let o = Sink::new(ix.n, 8).enc().write_nul(&t, false, nul.as_deref().unwrap_or(&[])).expect("qlean gather: a write with no size test has an answer");
    match t.bad.into_inner() {
        usize::MAX => Ok(o),
        k => Err(format!("gather: index {} at row {k} is not below n = {}", row(ix, k), e.meta.n)),
    }
}

/// Row `k` of `ix` as a word.
fn row(ix: &Blocks, k: usize) -> u64 { let mut b = [0u8; 8]; ix.range(k, 1, 8, &mut b); u64::from_le_bytes(b) }

/// `words` where `e` is the positions `0 .. n` (`Enc.pos`), law G2: `e[ix[i]] = ix[i]`, so the answer is `ix` re-encoded
/// as `Coc.encode 8` writes it, once a walk over `ix`'s blocks finds every index below `n`; else `words`' error.
pub fn of_pos(ix: &Blocks, n: usize) -> Result<lean::O, String> {
    let mut buf = pod::Scr::<u64>::new(ix.blk());
    for (b, lo, _) in ix.walk() {
        let x = pod::cast::<i64>(ix.view(b, 8, pod::bytes_mut(&mut buf))).expect("qlean gather: an index block buffer is misaligned for i64");
        if let Some(k) = x.iter().position(|&u| u as u64 >= n as u64) {
            return Err(format!("gather: index {} at row {} is not below n = {n}", x[k] as u64, lo + k))
        }
    }
    Ok(Sink::new(ix.n, 8).enc().answer(ix))
}
/// `enc`'s producer: answer block `lo .. lo + nb` is `e` at index rows `lo .. lo + nb`; `d` the decoded `e` when there
/// is one; `bad` the first row past `e`.
struct Take<'a> { ix: Blocks<'a>, e: Coc<'a>, sw: u8, d: Option<Vec<i64>>, bad: AtomicUsize }
impl Take<'_> {
    // `i` the index rows' scratch (`8 * nb` bytes), `o` the answer's `nb * w` bytes
    fn fill(&self, b: usize, lo: usize, nb: usize, w: usize, i: &mut [u8], o: &mut [u8]) {
        let x = pod::cast::<i64>(self.ix.block(b, lo, nb, 8, i)).expect("qlean gather: an index block buffer is misaligned for i64");
        let n = self.e.meta.n;
        if !structural::all_below(n, x) {
            let k = x.iter().position(|&u| u as u64 >= n as u64).expect("qlean gather: all_below found a row past n");
            self.bad.fetch_min(lo + k, Relaxed);
        }
        match &self.d {
            // a row past `n` (negative included) misses `d` and reads 0, as `structural::enc`'s fill
            Some(d) => for (o, &u) in o.chunks_exact_mut(w).zip(x) {
                o.copy_from_slice(&structural::word::<16>(usize::try_from(u as u64).ok().and_then(|k| d.get(k)).map_or(0, |&v| v as u64))[..w])
            },
            None => structural::enc(w, &self.e, self.sw, 0, x, o),
        }
    }
}
impl Producer for Take<'_> {
    fn block<'s>(&'s self, b: usize, lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8] {
        let (i, o) = buf.split_at_mut(8 * nb);
        let o = &mut o[..nb * w];
        self.fill(b, lo, nb, w, i, o);
        o
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Kernel.gatherWords is es`: `es[is[i]]` for each row `i`; the first row whose index is not below `es.len()` is the
    /// error.
    fn words(is: &[u64], es: &[u64]) -> Result<Vec<u64>, String> {
        is.iter().enumerate().map(|(k, &i)| if i < es.len() as u64 { Ok(es[i as usize]) }
            else { Err(format!("gather: index {i} at row {k} is not below n = {}", es.len())) }).collect()
    }

    #[test] fn index_past_n_is_an_error() {
        assert_eq!(words(&[1, 3, 9], &[1, 2, 3]), Err("gather: index 3 at row 1 is not below n = 3".into()));
        // above `usize::MAX` on a 32-bit target too: the `u64` comparison, not the cast, decides
        assert_eq!(words(&[u64::MAX], &[1]), Err(format!("gather: index {} at row 0 is not below n = 1", u64::MAX)));
    }
}
