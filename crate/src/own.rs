#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! own.c:263 and the header checks of own.c:366-394.
use crate::why::Why;

pub const OWN_MAXPARTS: usize = 3;
#[repr(C)]
pub struct OwnHead { pub n: u64, pub hdr: usize, pub np: usize,
                     pub off: [usize; OWN_MAXPARTS], pub len: [usize; OWN_MAXPARTS], pub kind: u8 }

/// `m` = the whole mapping.
pub fn head(m: &[u8], why: &mut Why) -> Option<OwnHead> { unimplemented!() }
pub fn check(kind: u8, n: u64, part: &[&[u8]], why: &mut Why) -> bool { unimplemented!() }
