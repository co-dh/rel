#![forbid(unsafe_code)]
#![allow(unused_variables, dead_code)] // scaffold: the task that fills this module removes it
//! sort.c:212-334: an encoded column's keys through a window of two blocks, each decoded on first touch, and the
//! column's key range from its metadata. The ALP arm (`kwin.f`, sort.c:2618) is column (a)'s, task A5.
use alloc::boxed::Box;

use crate::BLK;
use crate::coc::Coc;
use crate::key::Keys;

/// `kwin` (sort.c:270): keys `lo .. lo + len` are in `key`.
pub struct Kwin<'a> { kind: u8, c: Coc<'a>, lo: usize, len: usize, key: Box<[u64; 2 * BLK]> }

impl<'a> Kwin<'a> {
    /// `kwin_init`: an empty window.
    pub fn new(kind: u8, c: Coc<'a>) -> Self { unimplemented!() }
}

impl Keys for Kwin<'_> {
    fn at(&mut self, i: usize) -> u64 { unimplemented!() }
    fn fork(&self) -> Self { unimplemented!() }
}

/// sort.c:212: the bit `keys_of` flips at `kind`'s width.
pub fn key_flip(kind: u8) -> u64 { unimplemented!() }

/// `keys_blk_foR` (sort.c:243): block `b`'s `k.len()` keys.
pub fn keys_blk(kind: u8, c: &Coc, b: usize, k: &mut [u64]) { unimplemented!() }

/// `range_foR` (sort.c:320): the least and greatest key, from the frames, the maxima and the patches.
pub fn range(kind: u8, c: &Coc) -> (u64, u64) { unimplemented!() }
