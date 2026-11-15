#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), scan.c:309-505 (A14): the running scans (sums, prds, mins, maxs, fills) over a dense payload and
//! the block skips over an encoded one. `scan_fill` and `scan_any_null` are AVX-512 in C: their vector bodies go
//! into `simd.rs` as `#[target_feature]` fns this module calls.
use crate::alp::Cocf;
use crate::coc::Coc;

/// scan.c:309 `sc_bad_kind`: the abort for a kind the Lean dispatch never sends.
pub fn sc_bad_kind(kind: i32) -> ! { unimplemented!("A14: sc_bad_kind") }
/// scan.c:322 `scan_fill`: `fills` over `n` elements of `p` into `out`; `carry` (one element) is the last non-null
/// seen, read when `resume`.
pub fn scan_fill(kind: i32, p: &[u8], out: &mut [u8], n: usize, carry: &mut [u8], resume: bool) {
    unimplemented!("A14: scan_fill")
}
/// scan.c:346 `scan_any_null`
pub fn scan_any_null(kind: i32, p: &[u8], n: usize) -> bool { unimplemented!("A14: scan_any_null") }
/// scan.c:366 `scan_run`: scan `op` over `n` elements, `carry` the running accumulator.
pub fn scan_run(op: i32, kind: i32, p: &[u8], out: &mut [u8], n: usize, carry: &mut [u8], resume: bool) {
    unimplemented!("A14: scan_run")
}
/// scan.c:411 `sc_out_width`
pub fn sc_out_width(op: i32, kind: i32) -> usize { unimplemented!("A14: sc_out_width") }
/// scan.c:420 `sc_fill_c`: `cnt` copies of `acc` at `w` bytes.
pub fn sc_fill_c(out: &mut [u8], cnt: usize, w: usize, acc: i64) { unimplemented!("A14: sc_fill_c") }
/// scan.c:435 `sc_blk_skip`: block `b` of `c` leaves the accumulator `acc` unchanged under `op`.
pub fn sc_blk_skip(op: i32, kind: i32, c: &Coc, b: usize, cnt: usize, acc: i64) -> bool { unimplemented!("A14: sc_blk_skip") }
/// scan.c:453 `sc_alp_skip`
pub fn sc_alp_skip(op: i32, f: &Cocf, b: usize, cnt: usize, acc: f64) -> bool { unimplemented!("A14: sc_alp_skip") }
