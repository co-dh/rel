#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), coc.c: the threaded passes behind the `qlean_coc_*` entries (A15) and the `qlean_alp_*` ones (A18).
//! The entries themselves unbox and allocate, and stay C (§1); each calls the pass here through its `qrs_*` shim.
use crate::alp::{Cocf, Flt};
use crate::c::Runner;
use crate::coc::Coc;
use crate::pod::Lane;

// ---- A15: coc.c:592-837 ----
/// coc.c:592-594 `qlean_coc_decode_{i16,i32,i64}` past the unboxing: the whole column into `out`, by blocks.
pub fn decode<T: Lane + Send>(run: Runner, c: &Coc, out: &mut [T]) { unimplemented!("A15: coc_decode_run") }
/// coc.c:616 `qlean_coc_block_start`: each block's first element into `out` (`nblk` long).
pub fn block_start(c: &Coc, out: &mut [i64]) { unimplemented!("A15: qlean_coc_block_start") }
/// coc.c:761 `coc_mask_cmp_run` and its entry: `x op v` as a bitmap into `out` (`(n + 7) / 8` bytes).
pub fn mask_cmp(run: Runner, op: u8, v: i64, c: &Coc, out: &mut [u8]) { unimplemented!("A15: coc_mask_cmp_run") }
/// coc.c:766 `coc_cmp2_run`: `a op b` as a bitmap, blocks threaded over `coc_cmp2_res`.
pub fn cmp2(run: Runner, op: i32, a: &Coc, b: &Coc, deep: &[u32], out: &mut [u64]) { unimplemented!("A15: coc_cmp2_run") }
/// coc.c:810 `shift_fill`: the encoder's source for `qlean_coc_shift` when the metadata cannot absorb `k`:
/// elements `i0 .. i0 + buf.len()` of `x + k` (`neg`: `k - x`), nulls `fill`.
pub fn shift_fill(c: &Coc, k: i64, neg: bool, fill: i64, buf: &mut [i64], i0: usize) { unimplemented!("A15: shift_fill") }

// ---- A18: coc.c:1015-1149 ----
/// coc.c:1015 `alp_decode_run` and its entries: the whole ALP column into `out` (`f32`/`f64` bytes).
pub fn alp_decode(run: Runner, f: &Cocf, out: &mut [u8]) { unimplemented!("A18: alp_decode_run") }
/// coc.c:1051-1100 `alp_chunk_run`, `alp_f{32,64}_blk` and the sum entries: the column's sum (`avg`: mean).
pub fn alp_sum<F: Flt>(run: Runner, f: &Cocf, avg: bool) -> f64 { unimplemented!("A18: qlean_alp_sum") }
/// coc.c:1103 `alp_gather_run` and its entry: `f[idx[i]]` into `out`, `fill`'s bits where `idx[i]` is out of range.
pub fn alp_gather(run: Runner, fill: u64, f: &Cocf, idx: &[i64], out: &mut [u8]) { unimplemented!("A18: alp_gather_run") }
