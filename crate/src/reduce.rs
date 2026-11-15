#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), reduce.c: whole-vector reductions of a byte payload (A12; the byte sum is `simd::u8_sum`) and the
//! segmented reductions and bit-row folds (A13).
use crate::c::Runner;

// ---- A12: reduce.c:261-298 ----
/// reduce.c:277 `qlean_over_bytes` past the unboxing: `op` (sum, prd, min, max, ...) of class `cls` over `a`, nulls
/// `nul` skipped.
pub fn over_bytes(op: u8, cls: u8, nul: i64, a: &[u8]) -> i64 { unimplemented!("A12: qlean_over_bytes") }

// ---- A13: reduce.c:488-619 ----
/// reduce.c:488 `seg_at`: segment `k`'s start (`o` the `n` starts; `k == n` answers the end).
pub fn seg_at(o: &[i64], n: usize, k: usize) -> usize { unimplemented!("A13: seg_at") }
/// reduce.c:493 `seg_lower`: the segment holding element `i`.
pub fn seg_lower(o: &[i64], n: usize, ng: usize, i: usize) -> usize { unimplemented!("A13: seg_lower") }
/// reduce.c:516 `over_segments`: elements `from .. to` of `src` (class `cls`) folded by `op` into the
/// segment results `res`, segments `lo .. hi`.
pub fn over_segments(op: u8, cls: u8, nul: i64, lo: i64, hi: i64, ng: usize, n: usize, offs: &[i64], src: &[u8],
                     from: usize, to: usize, res: &mut [i64]) {
    unimplemented!("A13: over_segments")
}
/// reduce.c:537 `qlean_over_segments` past the unboxing: one result per segment into `res` (`ng` long), threaded
/// (`over_segments_pass`).
pub fn segments(run: Runner, op: u8, cls: u8, nul: i64, offs: &[i64], src: &[u8], n: usize, res: &mut [i64]) {
    unimplemented!("A13: qlean_over_segments")
}
/// reduce.c:560 `br_load`: 64 bits of the bit matrix `m` (`nb` bytes) from bit `bit`.
pub fn br_load(m: &[u8], bit: usize) -> u64 { unimplemented!("A13: br_load") }
/// reduce.c:570 `br_store`: the low `nbits` of `v` at bit `bit`.
pub fn br_store(o: &mut [u8], bit: usize, v: u64, nbits: u32) { unimplemented!("A13: br_store") }
/// reduce.c:606 `qlean_bit_rows_over` past the unboxing: per row of `w` bits, the AND (`all`) or OR of the rows
/// `idx[offs[g] .. offs[g + 1]]` of `m`, into `out`; threaded (`bit_rows_pass`).
pub fn bit_rows(run: Runner, all: bool, w: usize, offs: &[i64], idx: &[i64], m: &[u8], out: &mut [u8]) {
    unimplemented!("A13: qlean_bit_rows_over")
}
