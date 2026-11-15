#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), elementwise.c: scalar helpers (A42), the two-operand verbs and comparisons (A43; `ew_val_avx` and
//! `ew_cmp_avx` are `simd::ew_val`/`simd::ew_cmp`), bit verbs and the monadic ones (A44), casts and time (A45),
//! widening (A46a), the fused chain's stage table (A46b; its runner is `c::run_chain`). `op`, `cls`, `shape` are
//! elementwise.c:86-100's `EW_*`. The `qlean_ew_*` entries unbox and allocate and stay C (§1).
use crate::c::Runner;
use crate::coc::Coc;
use crate::sym::Syms;

// ---- A42: elementwise.c:140-299 (per element: C keeps these bodies while a C caller remains) ----
/// elementwise.c:140 `ew_unsupported`: the abort naming the engine, `op` and `cls`.
pub fn ew_unsupported(engine: &str, op: u32, cls: u32) -> ! { unimplemented!("A42: ew_unsupported") }
/// elementwise.c:149 `ew_width`: an element's bytes in class `cls`.
pub fn ew_width(cls: u32) -> usize { unimplemented!("A42: ew_width") }
/// elementwise.c:195 `ew_tol`: q's tolerant float equality.
pub fn ew_tol(x: f64, y: f64) -> bool { unimplemented!("A42: ew_tol") }
/// elementwise.c:203 `ew_ord64`: a double's bits as an order-preserving key.
pub fn ew_ord64(x: u64, y: u64) -> i32 { unimplemented!("A42: ew_ord64") }
/// elementwise.c:207 `ew_ord32`
pub fn ew_ord32(x: u32, y: u32) -> i32 { unimplemented!("A42: ew_ord32") }
/// elementwise.c:240 `ew_outside_long`: `f` has no long.
pub fn ew_outside_long(f: f64) -> bool { unimplemented!("A42: ew_outside_long") }
/// elementwise.c:250 `ew_fdiv`: floor division, q's nulls.
pub fn ew_fdiv(x: i64, y: i64) -> i64 { unimplemented!("A42: ew_fdiv") }
/// elementwise.c:263 `ew_magic`: a divisor's multiply-shift form.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Magic { pub m: i64, pub d: i64, pub sh: u32, pub add: bool }
/// elementwise.c:265 `ew_magic_of`; `None` where C answers 0.
pub fn magic_of(d: i64) -> Option<Magic> { unimplemented!("A42: ew_magic_of") }
/// elementwise.c:293 `ew_fdiv_magic`: `ew_fdiv(x, g.d)` by the magic.
pub fn fdiv_magic(g: &Magic, x: i64) -> i64 { unimplemented!("A42: ew_fdiv_magic") }

// ---- A43: elementwise.c:482-1092 ----
/// elementwise.c:501 `ew_val_run` and its entry: `a op b` of class `cls` (`shape` vector/atom) into `out`, `n` long.
pub fn val(run: Runner, op: u8, cls: u8, shape: u8, nul: i64, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    unimplemented!("A43: ew_val_run")
}
/// elementwise.c:539 `ew_val_foR_run`: two encoded columns, the answer dense.
pub fn val_enc(run: Runner, op: u8, cls: u8, nul: i64, a: &Coc, b: &Coc, out: &mut [u8]) { unimplemented!("A43: ew_val_foR_run") }
/// elementwise.c:562 `ew_val_foR_atom_run`: an encoded column and an atom.
pub fn val_enc_atom(run: Runner, op: u8, cls: u8, shape: u8, nul: i64, c: &Coc, atom: &[u8], out: &mut [u8]) {
    unimplemented!("A43: ew_val_foR_atom_run")
}
/// elementwise.c:820 `ew_cmp_run` and its entry: a byte per comparison.
pub fn cmp(run: Runner, op: u8, cls: u8, shape: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A43: ew_cmp_run") }
/// elementwise.c:867 `ew_low_zero_run`
pub fn low_zero(run: Runner, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A43: ew_low_zero_run") }
/// elementwise.c:888 `ew_low_zero_foR_run`
pub fn low_zero_enc(run: Runner, c: &Coc, atom: &[u8], out: &mut [u8]) { unimplemented!("A43: ew_low_zero_foR_run") }
/// elementwise.c:927 `ew_bitw_run`
pub fn bitw(run: Runner, op: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A43: ew_bitw_run") }
/// elementwise.c:970 `qlean_ew_rank_pair` past the unboxing: each symbol's rank in the merged order of `da`, `db`.
pub fn rank_pair(da: &Syms, db: &Syms, ra: &mut [i32], rb: &mut [i32]) { unimplemented!("A43: qlean_ew_rank_pair") }
/// elementwise.c:1040-1079 `ew_cmp_ids_run`, `ew_eq_ids_run` and their entry: ids at `w` compared through the
/// rank tables `ra`, `rb`; a byte each.
pub fn eq_ids(run: Runner, op: u8, shape: u8, ia: &[u8], ib: &[u8], w: u32, n: usize, ra: &[i32], rb: &[i32], out: &mut [u8]) {
    unimplemented!("A43: ew_eq_ids_run")
}

// ---- A44: elementwise.c:1569-1813 ----
/// elementwise.c:1569 `ew_bit_run` and its entry: bitmap verbs.
pub fn bit(run: Runner, op: u8, shape: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A44: ew_bit_run") }
/// elementwise.c:1665 `ew_mon_run` and its entry: the monadic verbs.
pub fn mon(run: Runner, op: u8, cls: u8, nul: i64, x: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A44: ew_mon_run") }
/// elementwise.c:1708-1765 `ew_mon_foR_run`, `ew_mon_foR_blk`: over an encoded column, the answer dense.
pub fn mon_enc(run: Runner, op: u8, cls: u8, nul: i64, c: &Coc, out: &mut [u8]) { unimplemented!("A44: ew_mon_foR_run") }
/// elementwise.c:1743 `ew_mon_fill`: the encoder source of `qlean_coc_ew_mon_enc`.
pub fn mon_fill(op: u8, cls: u8, nul: i64, c: &Coc, buf: &mut [i64], i0: usize) { unimplemented!("A44: ew_mon_fill") }
/// elementwise.c:1789 `ew_floor_run`
pub fn floor(run: Runner, cls: u8, nul: i64, x: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A44: ew_floor_run") }

// ---- A45: elementwise.c:1843-1981 ----
/// elementwise.c:1843 `ew_cast_clamp`
pub fn cast_clamp(v: i64, lo: i64, hi: i64) -> i64 { unimplemented!("A45: ew_cast_clamp") }
/// elementwise.c:1850 `ew_cast_round`: q's round half away from zero.
pub fn cast_round(x: f64) -> i64 { unimplemented!("A45: ew_cast_round") }
/// elementwise.c:1882 `ew_cast_run` and its entry: class `src` to class `dst`.
pub fn cast(run: Runner, src: u8, dst: u8, nul_in: i64, x: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A45: ew_cast_run") }
/// elementwise.c:1921 `ew_fdiv64`
pub fn fdiv64(a: i64, b: i64) -> i64 { unimplemented!("A45: ew_fdiv64") }
/// elementwise.c:1925 `ew_days_of_first`: days from 2000.01.01 to the first of month `m`.
pub fn days_of_first(m: i64) -> i64 { unimplemented!("A45: ew_days_of_first") }
/// elementwise.c:1935 `ew_month_of_days`
pub fn month_of_days(d: i64) -> i64 { unimplemented!("A45: ew_month_of_days") }
/// elementwise.c:1951 `ew_tick_run`: the time-unit conversions (`op`).
pub fn tick(run: Runner, op: u8, cls: u8, nul: i64, x: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A45: ew_tick_run") }

// ---- A46a: elementwise.c:2007-2150 ----
/// elementwise.c:2007 `ew_widen_run` and its entry: class `src` widened to `dst`, nulls mapped.
pub fn widen(run: Runner, src: u8, dst: u8, nul_in: i64, nul_out: i64, x: &[u8], n: usize, out: &mut [u8]) {
    unimplemented!("A46a: ew_widen_run")
}

// ---- A46b: elementwise.c:2150-2310 (the stage workers stay C until `c::run_chain` calls Rust ones) ----
/// elementwise.c:2242 `ew_stage_bits`: a stage's bits per element of `a`, `b`, `o`; answers the cost.
pub fn stage_bits(engine: u32, op: u32, cls: u32, shape: u32) -> (u32, u16, u16, u16) { unimplemented!("A46b: ew_stage_bits") }
/// elementwise.c:2294 `ew_stage_fixed`: operand `left` of the stage is not re-based per tile.
pub fn stage_fixed(engine: u32, shape: u32, left: bool) -> bool { unimplemented!("A46b: ew_stage_fixed") }
