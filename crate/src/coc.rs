#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! The read views of coc.h's `coc`: metadata, patch list, and the whole column.
use crate::pod::Lane;

/// `coc_meta_view`: the 33*mblk + 16 byte buffer.
#[derive(Clone, Copy)]
pub struct Meta<'a> {
    pub base: &'a [i64], pub maxv: &'a [i64], pub off: &'a [u64], pub bsum: &'a [i64], pub width: &'a [u8],
    /// one slot each, read by value
    pub sumnul: i64, pub sumn: u64,
    /// slices are mblk long; nblk <= mblk is what n reaches
    pub n: usize, pub nblk: usize, pub mblk: usize,
}
/// nexc = pos.len()
#[derive(Clone, Copy)]
pub struct Exc<'a> { pub off: &'a [u32], pub pos: &'a [u16], pub raw: &'a [u8], pub esz: usize }
#[derive(Clone, Copy)]
pub struct Coc<'a> { pub meta: Meta<'a>, pub pack: &'a [u8], pub exc: Option<Exc<'a>>, pub fdelta: Option<&'a [u64]> }

impl<'a> Meta<'a> {
    /// coc.h:133; None = misaligned buffer
    pub fn new(m: &'a [u8], n: usize) -> Option<Self> { unimplemented!() }
    /// coc.h:222
    pub fn res_end(&self) -> usize { unimplemented!() }
    /// coc.h:233
    pub fn grid(&self, n: usize) -> bool { unimplemented!() }
}
impl<'a> Coc<'a> {
    /// coc.h:245; None where C aborts
    pub fn attach(meta: Meta<'a>, pack: &'a [u8]) -> Option<Self> { unimplemented!() }
    /// coc.h:234
    pub fn std(&self, n: usize) -> bool { unimplemented!() }
    /// coc.h:155; off stays absolute into pack
    pub fn blocks(&self, b0: usize, b1: usize) -> Coc<'a> { unimplemented!() }
    /// coc.h:217
    pub fn frame(&self, b: usize) -> u64 { unimplemented!() }
    /// coc.h:277: exception `j`'s element, sign-extended; one byte zero-extends.
    pub fn exc(&self, j: usize) -> i64 { unimplemented!() }
    /// coc.h:293
    pub fn blk_nexc(&self, b: usize) -> usize { unimplemented!() }
    /// coc.h:2633: block `b`'s first `nb` elements into `out`, the patches applied.
    pub fn decode_blk<T: Lane>(&self, b: usize, nb: usize, out: &mut [T]) { unimplemented!() }
}

/// coc.h:819: the residuals of a block at a power-of-two width in place, else unpacked into `buf` (`BLK * 8` bytes)
/// with `*w` raised to the lane it now has.
pub fn lanes<'b>(p: &'b [u8], w: &mut u8, nb: usize, buf: &'b mut [u8]) -> &'b [u8] { unimplemented!() }
