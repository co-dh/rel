#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), coc.h: one block's residuals as bits — single fields (A2), the scalar pack (A2; the AVX-512 one is
//! `simd::res_pack`), the residual sums (A3, `simd::res_sum8` for 8 bits), the smallest nonzero residual (A4).
//! `p` is always the block's `BLK * w / 8` bytes.

// ---- A2: coc.h:446-518, 678-760 ----
/// coc.h:446 `res_get`: field `j` of width `w`. Per element: C keeps its body while a C caller remains.
pub fn res_get(p: &[u8], w: u8, j: usize) -> u64 { unimplemented!("A2: res_get") }
/// coc.h:460 `res_get_in`: as `res_get`, never reading at or past byte `end`.
pub fn res_get_in(p: &[u8], w: u8, j: usize, end: usize) -> u64 { unimplemented!("A2: res_get_in") }
/// coc.h:470 `res_put`
pub fn res_put(p: &mut [u8], w: u8, j: usize, v: u64) { unimplemented!("A2: res_put") }
/// coc.h:503 `res_pack_scalar`: `nb` values of `v` (BLK long) into `dst` at `w` bits, the rest of the block zero.
pub fn res_pack_scalar(v: &[u64], w: u8, nb: usize, dst: &mut [u8]) { unimplemented!("A2: res_pack_scalar") }

// ---- A3: coc.h:790-856 ----
/// coc.h:802 `res_count_lt8`: of `nb` 8-bit residuals, how many are below `t`.
pub fn res_count_lt8(p: &[u8], nb: usize, t: u64) -> usize { unimplemented!("A3: res_count_lt8") }
/// coc.h:825 `res_sum`: `nb` residuals of width `w` summed.
pub fn res_sum(p: &[u8], nb: usize, w: u8) -> u64 { unimplemented!("A3: res_sum") }

// ---- A4: coc.h:993 ----
/// coc.h:993 `res_min_nonzero`
pub fn res_min_nonzero(p: &[u8], nb: usize, w: u8) -> u64 { unimplemented!("A4: res_min_nonzero") }
