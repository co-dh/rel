#![forbid(unsafe_code)]
//! `gather`, the kernel that reads data at computed positions (design §4, `Kernel.kgather` in Rel/Kernel/Gather.lean):
//! `out[i] = e[ix[i]]`. The Lean body is the composition concat → asc → scan fill → scatter; this is its fused form, one
//! read per row (`Rel.Verify.gatherWords_eq`). An index `>= n` is an error naming it, never a fill.
use alloc::{format, string::String, vec::Vec};
use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use crate::{blocks::Blocks, coc::Coc, enc::Producer, ffi::{Form, Sink}, lean, pod, structural};

/// `Kernel.gatherWords is es`: `es[is[i]]` for each row `i`; the first row whose index is not below `es.len()` is the
/// error.
pub fn words(is: &[u64], es: &[u64]) -> Result<Vec<u64>, String> {
    is.iter().enumerate().map(|(k, &i)| if i < es.len() as u64 { Ok(es[i as usize]) }
        else { Err(format!("gather: index {i} at row {k} is not below n = {}", es.len())) }).collect()
}

/// `words` on the encoded columns `ix` (`ix.meta.n` rows) and `e` (`e.meta.n` elements), answered as `Coc.encode 8`
/// writes `words`' result (`Enc.foR`), with `words`' error text.
///
/// Per block (owner approval S, PLAN 6.10: one block decoded into an L1 scratch of 8 KiB at a time is per-block work):
/// answer block `b` decodes index rows `b`'s span only, reads `e` only where they point (`structural::enc`: a flat
/// address where `e` has one width and no patch, else `Coc::get` by address, a long run in one block decoding that block
/// into the scratch), and goes to the encoder's block step through `Sink`. Neither column is decoded whole and no
/// per-row `Result` is collected: a row past `n` is read as 0 and marked, and the first marked row is the error.
pub fn enc(ix: &Coc, e: &Coc) -> Result<lean::O, String> {
    let t = Take { ix: Blocks::from(*ix), e: *e, sw: e.one_width(), bad: AtomicUsize::new(usize::MAX) };
    let o = Sink::new(ix.meta.n, 8, Form::For).enc().answer(&t);
    match t.bad.into_inner() {
        usize::MAX => Ok(o),
        k => Err(format!("gather: index {} at row {k} is not below n = {}", ix.get(k) as u64, e.meta.n)),
    }
}
/// `enc`'s producer: answer block `lo .. lo + nb` is `e` at index rows `lo .. lo + nb`; `bad` the first row past `e`.
struct Take<'a> { ix: Blocks<'a>, e: Coc<'a>, sw: u8, bad: AtomicUsize }
impl Take<'_> {
    // `i` the index rows' scratch (`8 * nb` bytes), `o` the answer's `nb * w` bytes
    fn fill(&self, b: usize, lo: usize, nb: usize, w: usize, i: &mut [u8], o: &mut [u8]) {
        let x = pod::cast::<i64>(self.ix.block(b, lo, nb, 8, i)).expect("qlean gather: an index block buffer is misaligned for i64");
        let n = self.e.meta.n;
        if !structural::all_below(n, x) {
            let k = x.iter().position(|&u| u as u64 >= n as u64).expect("qlean gather: all_below found a row past n");
            self.bad.fetch_min(lo + k, Relaxed);
        }
        structural::enc(w, &self.e, self.sw, 0, x, o)
    }
}
impl Producer for Take<'_> {
    fn block<'s>(&'s self, b: usize, lo: usize, nb: usize, w: usize, buf: &'s mut [u8]) -> &'s [u8] {
        let (i, o) = buf.split_at_mut(8 * nb);
        let o = &mut o[..nb * w];
        self.fill(b, lo, nb, w, i, o);
        o
    }
    fn block_into(&self, b: usize, lo: usize, nb: usize, w: usize, buf: &mut [u8], out: &mut [u8]) { self.fill(b, lo, nb, w, buf, out) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test] fn reads_each_row() {
        assert_eq!(words(&[2, 0, 2, 3], &[10, 11, 12, 13]), Ok(vec![12, 10, 12, 13]));
    }
    #[test] fn index_past_n_is_an_error() {
        assert_eq!(words(&[1, 3, 9], &[1, 2, 3]), Err("gather: index 3 at row 1 is not below n = 3".into()));
        // above `usize::MAX` on a 32-bit target too: the `u64` comparison, not the cast, decides
        assert_eq!(words(&[u64::MAX], &[1]), Err(format!("gather: index {} at row 0 is not below n = 1", u64::MAX)));
    }
    // `enc` writes the bytes the encoder writes for `words`' answer, and fails as `words` does, on a source with patches
    // (read by address, and decoded a block at a time under a long run) and one of one width (the flat address)
    #[test] fn enc_is_words_encoded() {
        let fr = |v: &[u64]| Sink::new(v.len(), 8, Form::For).answer(&Blocks::dense(pod::bytes(v), 8));
        let parts = |o: &lean::O| [0, 1].map(|i| o.borrow().field(i).bytes().to_vec());
        let n = 3000usize;
        let patched: Vec<u64> = (0..n as u64).map(|i| if i % 97 == 5 { i * 1_000_003 } else { 1000 + (i * 7919) % 8000 }).collect();
        let flat: Vec<u64> = (0..n as u64).map(|i| (i * 7919) % 4096).collect();
        let runs: Vec<u64> = (0..2500u64).map(|k| if k < 1500 { 1024 + k % 700 } else { (k * 2654435761) % n as u64 }).collect();
        let rnd: Vec<u64> = (0..1100u64).map(|k| (k * 2654435761) % n as u64).collect();
        for src in [&patched, &flat] {
            let [em, ep] = parts(&fr(src));
            let ec = crate::coc::view(&em, &ep, n).unwrap_or_else(|e| panic!("gather test: source does not view: {e}"));
            for ix in [&runs, &rnd, &alloc::vec![7u64; 70], &alloc::vec![]] {
                let [im, ip] = parts(&fr(ix));
                let ic = crate::coc::view(&im, &ip, ix.len()).unwrap_or_else(|e| panic!("gather test: index does not view: {e}"));
                let want = fr(&words(ix, src).expect("gather test: indices in range"));
                let got = enc(&ic, &ec).expect("gather test: enc answers");
                assert_eq!([0, 1].map(|i| got.borrow().field(i).bytes().to_vec()), parts(&want), "{} indices", ix.len());
                assert_eq!(got.borrow().tag(), 3, "the answer is `Enc.foR`");
            }
            let mut bad = rnd.clone();
            (bad[700], bad[1050]) = (n as u64 + 4, u64::MAX);
            let [im, ip] = parts(&fr(&bad));
            let ic = crate::coc::view(&im, &ip, bad.len()).unwrap_or_else(|e| panic!("gather test: index does not view: {e}"));
            assert_eq!(enc(&ic, &ec).err(), words(&bad, src).err());
        }
    }
}
