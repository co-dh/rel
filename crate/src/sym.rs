#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
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
    pub fn off(&self, i: usize) -> usize { unimplemented!("A11: off_at") }
    /// sym.h:40 `sym_at`
    pub fn at(&self, i: usize) -> &'a [u8] { unimplemented!("A11: sym_at") }
    /// sym.h:47 `sym_count`: the symbol count, `offs.len() - 1` (0 for an empty `offs`).
    pub fn count(&self) -> usize { unimplemented!("A11: sym_count") }
    /// sym.h:106 `sym_slices`: the first `n` symbols.
    pub fn slices(&self, n: usize) -> Vec<&'a [u8]> { unimplemented!("A11: sym_slices") }
    /// sym.h:146 `sym_packs`: every symbol of the first `n` fits the 8-byte key `sym_pack` makes.
    pub fn packs(&self, n: usize) -> bool { unimplemented!("A11: sym_packs") }
}
/// sym.h:68 `sym_eq`
pub fn sym_eq(a: &[u8], b: &[u8]) -> bool { unimplemented!("A11: sym_eq") }
/// sym.h:77 `sym_cmp`: q's symbol order.
pub fn sym_cmp(a: &[u8], b: &[u8]) -> Ordering { unimplemented!("A11: sym_cmp") }
/// sym.h:120 `sym_hash`
pub fn sym_hash(s: &[u8]) -> u64 { unimplemented!("A11: sym_hash") }
/// sym.h:89 `sym_msort`: the indices `a` (`v.len()` of them) stably sorted by `v[a[i]]`; `tmp` is scratch, as long.
pub fn sym_msort(v: &[&[u8]], a: &mut [usize], tmp: &mut [usize]) { unimplemented!("A11: sym_msort") }
