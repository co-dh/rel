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
/// sym.h:68 `sym_eq`
pub fn sym_eq(a: &[u8], b: &[u8]) -> bool { a == b }
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
