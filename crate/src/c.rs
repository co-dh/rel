//! The runner a kernel takes (the pool, or C's serial one for a stage inside a slice), and the safe calls over it.
use core::ptr::null;

use crate::ffi::CPass;

// libm names the crate may leave undefined (listed in rust/BENCH.md, symbols gate); each is declared once here, where `unsafe` is
// allowed, and called through a safe wrapper, so the safe modules need no unsafe block.
macro_rules! libm {
    ($($f:ident($($a:ident),+);)*) => {
        mod sys { unsafe extern "C" { $(pub fn $f($($a: f64),+) -> f64;)* } }
        $(
            /// libm's own, a safe `#[inline]` wrapper so a loop over it costs the call C's `__builtin_*` costs.
            #[inline]
            pub fn $f($($a: f64),+) -> f64 {
                // Safety: a pure libm function of doubles
                unsafe { sys::$f($($a),+) }
            }
        )*
    };
}
// `pow` (both float classes of `ew::val`, the f32 one computed at double width) and the nine float maps of `ew::mon`.
libm! { pow(x, y); sqrt(x); exp(x); log(x); sin(x); cos(x); tan(x); asin(x); acos(x); atan(x); }


pub type Worker = unsafe extern "C" fn(lo: usize, hi: usize, p: *const CPass);
/// A pass's runner: the pool (`pool::run_c`, `qrs_pool_run` in C) or a serial one C hands a stage already inside a
/// slice (ew.rs `ew_serial`), which is why the kernels take it rather than call the pool; F3 makes it `Par`.
pub type Runner = unsafe extern "C" fn(f: Worker, n: usize, cost: u32, wide: usize, p: *const CPass) -> u32;

/// The runner a Rust export hands its kernel: the process's one pool.
pub fn pool() -> Runner { crate::pool::run_c }
/// The unit tests' name for the pool, which they once faked (three slices in turn); under `cargo test` the real pool
/// splits every non-empty pass three ways (`pool::SPLIT_AT`).
#[cfg(any(test, feature = "std"))]
pub use crate::pool::run_c as qlean_run_c;

pub struct Job<'f, F> { f: &'f F, out: *mut u8, at: &'f (dyn Fn(usize) -> usize + Sync), len: usize }

/// Safety: `p` is the `CPass` `run_map` built, whose `a` is a live `Job<F>`; `[lo, hi)` is a slice of `[0, n)`
/// that no other worker of the same pass is given.
pub unsafe extern "C" fn slice<F: Fn(usize, usize, &mut [u8]) + Sync>(lo: usize, hi: usize, p: *const CPass) {
    let j = unsafe { &*(*p).a.cast::<Job<F>>() };
    let e = (j.at)(hi).min(j.len);
    let s = (j.at)(lo).min(e);
    let o = unsafe { core::slice::from_raw_parts_mut(j.out.add(s), e - s) };
    (j.f)(lo, hi, o)
}

/// The C pool (c.rs) over `units` units of `unit` bytes of `out`: `f(lo, hi, &mut out[lo * unit .. hi * unit])`
/// once per slice, on as many threads as `qlean_run` splits `units` into at `cost` and `wide`; answers that count.
pub fn run_map<F: Fn(usize, usize, &mut [u8]) + Sync>(run: Runner, out: &mut [u8], units: usize, unit: usize, cost: u32,
                                                      wide: usize, f: &F) -> u32 {
    // `k * unit` is ascending, so only the last start needs checking: O(1), where `run_map_at`'s O(units) scan ran
    // serially on the calling thread over every element and cost more wall time than the threaded pass itself
    assert!(units == 0 || (units - 1).checked_mul(unit).is_some_and(|s| s <= out.len()),
            "run_map: {units} units of {unit} bytes do not start inside a {}-byte output", out.len());
    map_at(run, out, units, &|k| k.saturating_mul(unit), cost, wide, f)
}


/// The pool call behind `run_map` and `run_map_at`, each of which has checked that `at` is non-decreasing over
/// `0 ..= units` and starts every unit inside `out`: that is what makes the `&mut` slices disjoint.
pub fn map_at<F: Fn(usize, usize, &mut [u8]) + Sync>(run: Runner, out: &mut [u8], units: usize,
                                                 at: &(dyn Fn(usize) -> usize + Sync), cost: u32, wide: usize, f: &F) -> u32 {
    let o = out.as_mut_ptr();
    let job = Job { f, out: o, at, len: out.len() };
    let p = CPass { a: (&raw const job).cast(), b: null(), c: null(), o: o.cast(), n: units, at: 0,
                    r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 };
    // the slices partition [0, units), so the `&mut` each worker makes are disjoint; `out` outlives the call
    unsafe { run(slice::<F>, units, cost, wide, &p) }
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





