#![forbid(unsafe_code)]
//! Column (a), sym.h (A11): a symbol column as a byte blob plus the `Array Nat` of starts. Rust never sees a
//! `lean_object`: C passes `lean_array_cptr(offs)` as `*const usize`, the boxed words themselves, and `Syms`
//! unboxes them (`w >> 1`; an unboxed word, a bignum pointer, aborts as `off_at` does).
use alloc::vec::Vec;
use core::cmp::Ordering;

/// A symbol column: `offs[i]` is symbol `i`'s start in `blob`, boxed; symbol `i` runs to `offs[i + 1]`.
#[derive(Clone, Copy)]
pub struct Syms<'a> { pub blob: &'a [u8], pub offs: &'a [usize] }

impl<'a> Syms<'a> {
    /// sym.h:28 `off_at`: start `i`, unboxed. Per element: C keeps its body while a C caller remains.
    #[inline]
    pub fn off(&self, i: usize) -> usize { {
        let w = self.offs[i];
        if w & 1 == 0 { panic!("qlean: symbol offset {i} is a bignum; an offset is bounded by the blob's byte count and cannot reach 2^63") }
        w >> 1
    } }
    /// sym.h:40 `sym_at`
    #[inline]
    pub fn at(&self, i: usize) -> &'a [u8] { {
        let (lo, hi) = (self.off(i), self.off(i + 1));
        let n = hi.saturating_sub(lo + 1); // an empty symbol never reads the blob, as C's `sym_at` does not (`dof` may point past an empty dictionary)
        if n == 0 { &self.blob[..0] } else { &self.blob[lo..lo + n] }
    } }
    /// sym.h:47 `sym_count`: the symbol count, `offs.len() - 1` (0 for an empty `offs`).
    pub fn count(&self) -> usize { self.offs.len().saturating_sub(1) }
    /// sym.h `sym_pad` + the load of search.c `sym_pack`: symbol `i` (at most 8 bytes) as a big-endian key, zero padded.
    #[inline]
    pub fn key(&self, i: usize) -> u64 { self.key_of(self.off(i), self.off(i + 1)) }
    /// `key` of the symbol at the unboxed starts `lo`, `hi`: one 8-byte load and a mask while the load stays inside the
    /// blob (the C `whole` prefix), the bytes folded for the last few; a loop over a column carries `lo`, as C does.
    #[inline]
    pub fn key_of(&self, lo: usize, hi: usize) -> u64 {
        let len = hi.wrapping_sub(lo + 1);
        if len == 0 { 0 }
        else if lo + 8 <= self.blob.len() { self.key_whole(lo, len) }
        else { self.blob[lo..lo + len].iter().fold(0, |w, &b| w << 8 | b as u64) << (8 * (8 - len)) }
    }
    /// the keys of the first `n` symbols, in order, `lo` carried as C's loop does. The caller has seen `packs(n)`: every tag
    /// bit is set, so the starts unbox without a test.
    pub fn keys(&self, n: usize) -> impl Iterator<Item = u64> + '_ {
        let mut lo = if n > 0 { self.offs[0] >> 1 } else { 0 };
        self.offs[..n.saturating_add(1).min(self.offs.len())].windows(2).map(move |w| { let hi = w[1] >> 1; let k = self.key_of(lo, hi); lo = hi; k })
    }
    /// the load of `key_of` where it stays inside the blob and `len` is 1 ..= 8
    #[inline]
    pub fn key_whole(&self, lo: usize, len: usize) -> u64 {
        u64::from_be_bytes(self.blob[lo..lo + 8].try_into().unwrap()) & (!0u64 << (8 * (8 - len)))
    }
    /// sym.h:106 `sym_slices`: the first `n` symbols.
    pub fn slices(&self, n: usize) -> Vec<&'a [u8]> { (0..n).map(|i| self.at(i)).collect() }
    /// sym.h:146 `sym_packs`: every symbol of the first `n` fits the 8-byte key `sym_pack` makes.
    pub fn packs(&self, n: usize) -> bool { {
        let (mut tags, mut wide) = (self.offs[n], false);
        for i in 0..n {
            tags &= self.offs[i]; // a clear tag bit is a bignum, which the blob rules out
            wide |= (self.offs[i + 1] >> 1).wrapping_sub(self.offs[i] >> 1).wrapping_sub(1) > 8;
        }
        tags & 1 != 0 && !wide && self.offs[n] >> 1 <= self.blob.len()
    } }
}
/// sym.h:68 `sym_eq`: length first, then the bytes in overlapping loads (8, 4, 2, 1), so a short symbol is a few
/// compares and never a `bcmp` call (`[u8] ==` is one, and a symbol is two to six bytes).
#[inline]
pub fn sym_eq(a: &[u8], b: &[u8]) -> bool {
    let n = a.len();
    if n != b.len() { return false }
    let w = |s: &[u8], at: usize| u64::from_le_bytes(s[at..at + 8].try_into().unwrap());
    let d = |s: &[u8], at: usize| u32::from_le_bytes(s[at..at + 4].try_into().unwrap());
    let h = |s: &[u8], at: usize| u16::from_le_bytes(s[at..at + 2].try_into().unwrap());
    if n >= 8 {
        let mut i = 0;
        while i + 8 < n { if w(a, i) != w(b, i) { return false } i += 8 }
        w(a, n - 8) == w(b, n - 8)
    } else if n >= 4 { d(a, 0) == d(b, 0) && d(a, n - 4) == d(b, n - 4) }
    else if n >= 2 { h(a, 0) == h(b, 0) && h(a, n - 2) == h(b, n - 2) }
    else { n == 0 || a[0] == b[0] }
}
/// sym.h:77 `sym_cmp`: q's symbol order (bytes unsigned, then length), which is `[u8]`'s.
pub fn sym_cmp(a: &[u8], b: &[u8]) -> Ordering { a.cmp(b) }
/// sym.h:120 `sym_hash`: FNV-1a.
pub fn sym_hash(s: &[u8]) -> u64 { s.iter().fold(0xcbf29ce484222325, |h, &b| (h ^ b as u64).wrapping_mul(0x100000001b3)) }
/// sym.h:89 `sym_msort`: the indices `a` (`v.len()` of them) stably sorted by `v[a[i]]`; `tmp` is scratch, as long.
pub fn sym_msort(v: &[&[u8]], a: &mut [usize], tmp: &mut [usize]) { {
    let n = a.len();
    let mut w = 1;
    while w < n {
        let mut lo = 0;
        while lo < n {
            let (mid, hi) = ((lo + w).min(n), (lo + 2 * w).min(n));
            let (mut i, mut j, mut o) = (lo, mid, lo);
            while i < mid && j < hi {
                if v[a[i]] <= v[a[j]] { tmp[o] = a[i]; i += 1 } else { tmp[o] = a[j]; j += 1 }
                o += 1;
            }
            tmp[o..o + mid - i].copy_from_slice(&a[i..mid]);
            o += mid - i;
            tmp[o..o + hi - j].copy_from_slice(&a[j..hi]);
            lo += 2 * w;
        }
        a.copy_from_slice(&tmp[..n]);
        w <<= 1;
    }
} }

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    /// `offs` for the symbols `ss`, each NUL-terminated in the blob, boxed
    fn col(ss: &[&[u8]]) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (vec![], vec![1]);
        for s in ss { b.extend_from_slice(s); b.push(0); o.push(b.len() << 1 | 1) }
        (b, o)
    }
    #[test] fn order_and_empty() {
        let (b, o) = col(&[b"ab", b"a", b"aa", b"", "\u{e9}".as_bytes(), b"e", b"z"]);
        let s = Syms { blob: &b, offs: &o };
        assert_eq!(s.count(), 7);
        assert_eq!(s.at(3), b"");
        let v = s.slices(7);
        let (mut a, mut t) = ((0..7).collect::<Vec<_>>(), vec![0; 7]);
        sym_msort(&v, &mut a, &mut t);
        assert_eq!(a, [3, 1, 2, 0, 5, 6, 4]);
        assert_eq!(Syms { blob: &[], offs: &[] }.count(), 0);
        assert!(s.packs(7));
        let (b, o) = col(&[b"123456789"]);
        assert!(!Syms { blob: &b, offs: &o }.packs(1));
        assert_eq!(sym_hash(b""), 0xcbf29ce484222325);
    }
}
