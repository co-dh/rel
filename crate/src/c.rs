//! The pool as the runner a kernel takes (`pool::run_c`), and the safe calls over the pool.
use alloc::vec::Vec;
use core::ptr::null;

use crate::ffi::CPass;
use crate::pool;

// libm names the crate may leave undefined (listed in rust/BENCH.md, symbols gate); each is declared once here, where `unsafe` is
// allowed, and called through a safe wrapper, so the safe modules need no unsafe block.
unsafe extern "C" { #[link_name = "pow"] fn libm_pow(x: f64, y: f64) -> f64; }
/// libm's `pow`, the one libm call of `ew::val`; both float classes compute it at double width.
#[inline]
pub fn pow(x: f64, y: f64) -> f64 {
    // Safety: `pow` is a pure libm function of two doubles
    unsafe { libm_pow(x, y) }
}

pub type Worker = unsafe extern "C" fn(lo: usize, hi: usize, p: *const CPass);
/// The pool's C entry (`pool::run_c`, exported as `qrs_pool_run`) as a function pointer; F3 deletes the parameter.
pub type Runner = unsafe extern "C" fn(f: Worker, n: usize, cost: u32, wide: usize, p: *const CPass) -> u32;

/// The runner a Rust export hands its kernel: the process's one pool.
pub fn pool() -> Runner { pool::run_c }
/// The unit tests' name for the pool, which they once faked (three slices in turn); under `cargo test` the real pool
/// splits every non-empty pass three ways (`pool::SPLIT_AT`).
#[cfg(test)]
pub use crate::pool::run_c as qlean_run_c;

/// The pool over `units` units of `unit` bytes of `out`: `f(lo, hi, &mut out[lo * unit .. hi * unit])`
/// once per slice, on as many threads as `qlean_run` splits `units` into at `cost` and `wide`; answers that count.
pub fn run_map<F: Fn(usize, usize, &mut [u8]) + Sync>(run: Runner, out: &mut [u8], units: usize, unit: usize, cost: u32,
                                                      wide: usize, f: &F) -> u32 {
    // `k * unit` is ascending, so only the last start needs checking: O(1), where `run_map_at`'s O(units) scan ran
    // serially on the calling thread over every element and cost more wall time than the threaded pass itself
    assert!(units == 0 || (units - 1).checked_mul(unit).is_some_and(|s| s <= out.len()),
            "run_map: {units} units of {unit} bytes do not start inside a {}-byte output", out.len());
    map_at(run, out, units, &|k| k.saturating_mul(unit), cost, wide, f)
}

/// `run_map` whose unit `k` starts at byte `at(k)` of `out` (`at` ascending, `at(units)` the end): slice `[lo, hi)` is
/// `out[at(lo) .. at(hi)]`, so units that are not equally spaced (the deep blocks of a bitmap) still get disjoint slices.
/// Panics unless `at` is non-decreasing over `0 ..= units` and starts every unit inside `out` (the last unit may be
/// short, a ragged final block: its slice ends at `out`); that one check is what makes the `&mut` slices disjoint.
pub fn run_map_at<F: Fn(usize, usize, &mut [u8]) + Sync>(run: Runner, out: &mut [u8], units: usize,
                                                         at: &(dyn Fn(usize) -> usize + Sync), cost: u32, wide: usize, f: &F) -> u32 {
    assert!((0..units).all(|k| at(k) <= at(k + 1)) && (units == 0 || at(units - 1) <= out.len()),
            "run_map_at: {units} units do not start in ascending order inside a {}-byte output", out.len());
    map_at(run, out, units, at, cost, wide, f)
}

/// The pool call behind `run_map` and `run_map_at`, each of which has checked that `at` is non-decreasing over
/// `0 ..= units` and starts every unit inside `out`: that is what makes the `&mut` slices disjoint.
fn map_at<F: Fn(usize, usize, &mut [u8]) + Sync>(_run: Runner, out: &mut [u8], units: usize,
                                                 at: &(dyn Fn(usize) -> usize + Sync), cost: u32, wide: usize, f: &F) -> u32 {
    struct Out(*mut u8);
    // Safety: each slice makes a `&mut` of its own disjoint range only
    unsafe impl Sync for Out {}
    let (o, len) = (Out(out.as_mut_ptr()), out.len());
    pool::run(units, cost, wide, &|_, lo, hi| {
        let e = at(hi).min(len);
        let s = at(lo).min(e);
        // the slices partition [0, units) and `at` is non-decreasing, so these ranges are disjoint; `out` outlives the pass
        f(lo, hi, unsafe { core::slice::from_raw_parts_mut((&o).0.add(s), e - s) })
    })
}

/// `run_map` whose slices each answer one `T` (a private histogram, a partial fold): `(parts, answers)` with the
/// answers `(lo, t)` in slice order (`pool::slices`); a slice the pool leaves empty gives none.
pub fn run_slices<T: Send, F: Fn(usize, usize) -> T + Sync>(_run: Runner, n: usize, cost: u32, wide: usize, f: &F) -> (u32, Vec<(usize, T)>) {
    pool::slices(n, cost, wide, f)
}

#[cfg(test)]
mod tests {
    #[test] fn run_map_cuts_disjoint_slices() {
        let mut out = [0u8; 2 * 7 + 1];
        let parts = super::run_map(super::qlean_run_c, &mut out, 7, 2, crate::QLEAN_COST_ARITH, 8, &|lo, hi, o: &mut [u8]| {
            assert_eq!(o.len(), 2 * (hi - lo));
            for (k, b) in o.iter_mut().enumerate() { *b = (lo * 2 + k) as u8 + 1 }
        });
        assert_eq!(parts, 3);
        assert_eq!(out, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0]);
    }
    // a short last unit (a ragged final block) ends its slice at `out`, not at `units * unit`
    #[test] fn run_map_ends_the_last_slice_at_out() {
        let mut out = [0u8; 2 * 6 + 1];
        super::run_map(super::qlean_run_c, &mut out, 7, 2, crate::QLEAN_COST_ARITH, 8, &|lo, hi, o: &mut [u8]| {
            assert_eq!(o.len(), (2 * hi).min(13) - 2 * lo);
            for (k, b) in o.iter_mut().enumerate() { *b = (lo * 2 + k) as u8 + 1 }
        });
        assert_eq!(out, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]);
    }
    // units that are not equally spaced still get disjoint slices, `at(lo) .. at(hi)`
    #[test] fn run_map_at_cuts_by_the_start_function() {
        let starts = [0usize, 3, 4, 9, 10];
        let mut out = [0u8; 10];
        super::run_map_at(super::qlean_run_c, &mut out, 4, &|k| starts[k], crate::QLEAN_COST_ARITH, 8, &|lo, hi, o: &mut [u8]| {
            assert_eq!(o.len(), starts[hi] - starts[lo]);
            o.fill(lo as u8 + 1)
        });
        assert!(out.iter().all(|&b| b != 0));
    }
    use crate::ffi::{CPass, CStage};
    use std::vec::Vec;
    // stage 0 adds one to a byte column into slot 0, stage 1 doubles that slot into the answer column
    unsafe extern "C" fn inc(lo: usize, hi: usize, p: *const CPass) {
        for i in lo..hi { unsafe { *(*p).o.cast::<u8>().add(i) = (*(*p).a.cast::<u8>().add(i)).wrapping_add(1) } }
    }
    unsafe extern "C" fn dbl(lo: usize, hi: usize, p: *const CPass) {
        for i in lo..hi { unsafe { *(*p).o.cast::<u8>().add(i) = (*(*p).a.cast::<u8>().add(i)).wrapping_mul(2) } }
    }
    fn stage(f: unsafe extern "C" fn(usize, usize, *const CPass), a: *const u8, o: *mut u8, asrc: u8, osrc: u8) -> CStage {
        CStage { f: Some(f), p: CPass { a: a.cast(), b: core::ptr::null(), c: core::ptr::null(), o: o.cast(), n: 0, at: 0, r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 },
                 asrc, bsrc: 255, osrc, abits: 8, bbits: 0, obits: 8, bytewise: 0 }
    }
    #[test] fn chain_runs_every_stage_per_tile_and_one_stage_whole() {
        for n in [1usize, 1023, 1024, 1025, 3000] {
            let x: Vec<u8> = (0..n).map(|i| i as u8).collect();
            let mut o = vec![0u8; n];
            let st = [stage(inc, x.as_ptr(), core::ptr::null_mut(), 254, 0), stage(dbl, core::ptr::null(), o.as_mut_ptr(), 0, 254)];
            super::run_chain(super::qlean_run_c, &st, n, crate::QLEAN_COST_ARITH, 1);
            assert!(o.iter().zip(&x).all(|(&o, &x)| o == x.wrapping_add(1).wrapping_mul(2)), "n = {n}");
            let mut o1 = vec![0u8; n];
            let one = [stage(inc, x.as_ptr(), o1.as_mut_ptr(), 254, 254)];
            super::run_chain(super::qlean_run_c, &one, n, crate::QLEAN_COST_ARITH, 1);
            assert!(o1.iter().zip(&x).all(|(&o, &x)| o == x.wrapping_add(1)), "n = {n}");
        }
    }
}

/// pass.h:488-491: a stage operand's source code at or above `SLOTS` is a column (re-based per tile) or fixed (one pointer).
const SLOTS: usize = 10;
const TILE: usize = 1024;
const COLUMN: u8 = 254;

/// One tile of eight-byte elements per slot, the widest any stage answers, on a cache line.
#[repr(align(64))]
struct Slot([u8; TILE * 8]);

/// pass.h:502 `qlean_chain_run` over the tiles `[lo, hi)`: every stage over a tile before the next tile starts.
/// Safety: `cp.a` is the `[CStage; cp.op]` of `run_chain`, whose `f` are live workers and whose bindings reach `cp.n` elements.
pub unsafe extern "C" fn chain_tiles(lo: usize, hi: usize, cp: *const CPass) {
    let (st, k, n) = unsafe { (core::slice::from_raw_parts((*cp).a.cast::<crate::ffi::CStage>(), (*cp).op as usize), (*cp).op as usize, (*cp).n) };
    // uninitialised like C's: a stage writes a slot before a later stage reads it, and 80 KiB of zeroes a call is a pass
    let mut slot = core::mem::MaybeUninit::<[Slot; SLOTS]>::uninit();
    let sp = slot.as_mut_ptr().cast::<Slot>();
    for t in lo..hi {
        let at = t * TILE;
        let cnt = if at + TILE < n { TILE } else { n - at };
        for s in &st[..k] {
            let mut q = unsafe { core::ptr::read(&s.p) };
            let bind = |src: u8, bits: u16, p: *const core::ffi::c_void| -> *const core::ffi::c_void {
                if (src as usize) < SLOTS { unsafe { (*sp.add(src as usize)).0.as_ptr().cast() } }
                else if src == COLUMN { p.cast::<u8>().wrapping_add(at * bits as usize / 8).cast() } else { p }
            };
            q.a = bind(s.asrc, s.abits, q.a);
            q.b = bind(s.bsrc, s.bbits, q.b);
            q.o = if (s.osrc as usize) < SLOTS { unsafe { (*sp.add(s.osrc as usize)).0.as_mut_ptr().cast() } }
                  else if s.osrc == COLUMN { q.o.cast::<u8>().wrapping_add(at * s.obits as usize / 8).cast() } else { q.o };
            q.n = cnt;
            q.at = at;
            let f = s.f.expect("qlean_chain_run: a stage with no worker");
            unsafe { f(0, if s.bytewise != 0 { (cnt * s.obits as usize).div_ceil(8) } else { cnt }, &q) }
        }
    }
}

/// pass.h:530 `qlean_run_chain`: the stages of `st` over `n` elements on the pool, one thread or several; answers the
/// thread count. `cost` and `wide` are the whole chain's, so the split is decided on the expression, not on one verb.
/// Safety (of the pointers in `st`): the bindings of every stage reach `n` elements, as `qlean_ew_chain` built them.
pub fn run_chain(run: Runner, st: &[crate::ffi::CStage], n: usize, cost: u32, wide: usize) -> u32 {
    assert!(!st.is_empty() && st.len() <= SLOTS, "qlean_run_chain: {} stages, and the driver holds {SLOTS}", st.len());
    if let [s] = st {
        // a chain of one pass is that pass: tiling it fuses nothing and costs a call a tile. A comparison is sliced by
        // output byte, so its widest operand is counted per output bit (pass.h:545)
        let widest = s.abits.max(s.obits).max(s.bbits) as usize;
        let mut one = unsafe { core::ptr::read(&s.p) };
        one.n = n;
        let (units, w) = if s.bytewise != 0 { ((n * s.obits as usize).div_ceil(8), widest / s.obits as usize) } else { (n, widest / 8) };
        return unsafe { run(s.f.expect("qlean_run_chain: a stage with no worker"), units, cost, w, &one) };
    }
    let p = CPass { a: st.as_ptr().cast(), b: null(), c: null(), o: core::ptr::null_mut(), n, at: 0, r#priv: 0, nul: 0,
                    op: st.len() as u8, cls: 0, shape: 0 };
    unsafe { run(chain_tiles, n.div_ceil(TILE), cost, wide * TILE, &p) }
}
