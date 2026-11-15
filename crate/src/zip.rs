#![forbid(unsafe_code)]
//! zip.c:141 and the pure parts of zopen (zip.c:185-250).
use crate::why::Why;

/// `dst` = 8 zero bytes + `want`.
pub fn zq(b: &[u8], dst: &mut [u8]) -> Result<(), &'static core::ffi::CStr> { unimplemented!() }
#[repr(C)]
pub struct ZTrailer { pub ulen: u64, pub cend: u64, pub l: u64 }
pub fn trailer(hdr: &[u8; 32], size: u64, nblk: u64, hat: u64, why: &mut Why) -> Option<ZTrailer> { unimplemented!() }
/// Returns maxc; at[0] = 8.
pub fn table(ent: &[u8], at: &mut [u64], algo: &mut [u32]) -> usize { unimplemented!() }
