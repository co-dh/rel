//! The one C callback Rust takes, `qlean_run`, as a function pointer C passes in, and the one safe call over it.
use core::ptr::null;

use crate::ffi::CPass;

pub type Worker = unsafe extern "C" fn(lo: usize, hi: usize, p: *const CPass);
/// C's `qlean_run` (pass.h:415) under a symbol; sort.c passes `qlean_run_c`, so this object needs no C symbol of its own.
pub type Runner = unsafe extern "C" fn(f: Worker, n: usize, cost: u32, wide: usize, p: *const CPass) -> u32;

/// Under `cargo test` there is no C pool: three slices, cut as `qlean_slice` (pass.h:243) cuts them, run in turn.
#[cfg(test)]
pub unsafe extern "C" fn qlean_run_c(f: Worker, n: usize, _cost: u32, _wide: usize, p: *const CPass) -> u32 {
    const PARTS: usize = 3;
    for k in 0..PARTS {
        let (lo, hi) = cut(n, PARTS, k);
        if lo < hi { unsafe { f(lo, hi, p) } }
    }
    PARTS as u32
}
#[cfg(test)]
fn cut(n: usize, parts: usize, k: usize) -> (usize, usize) {
    let (q, r) = (n / parts, n % parts);
    let lo = q * k + k.min(r);
    (lo, lo + q + (k < r) as usize)
}

struct Job<'f, F> { f: &'f F, out: *mut u8, unit: usize }

/// Safety: `p` is the `CPass` `run_map` built, whose `a` is a live `Job<F>`; `[lo, hi)` is a slice of `[0, n)`
/// that no other worker of the same pass is given.
unsafe extern "C" fn slice<F: Fn(usize, usize, &mut [u8]) + Sync>(lo: usize, hi: usize, p: *const CPass) {
    let j = unsafe { &*(*p).a.cast::<Job<F>>() };
    let o = unsafe { core::slice::from_raw_parts_mut(j.out.add(lo * j.unit), (hi - lo) * j.unit) };
    (j.f)(lo, hi, o)
}

/// The C pool (pass.h:415) over `units` units of `unit` bytes of `out`: `f(lo, hi, &mut out[lo * unit .. hi * unit])`
/// once per slice, on as many threads as `qlean_run` splits `units` into at `cost` and `wide`; answers that count.
pub fn run_map<F: Fn(usize, usize, &mut [u8]) + Sync>(run: Runner, out: &mut [u8], units: usize, unit: usize, cost: u32,
                                                      wide: usize, f: &F) -> u32 {
    assert!(units.checked_mul(unit).is_some_and(|b| b <= out.len()),
            "run_map: {units} units of {unit} bytes past a {}-byte output", out.len());
    let o = out.as_mut_ptr();
    let job = Job { f, out: o, unit };
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
}

/// A46b: pass.h:502 `qlean_chain_run` -- tiles of `n` elements, every stage of `st` over a tile before the next --
/// on the pool; answers the thread count. Stays here: it calls the stages' C workers.
pub fn run_chain(run: Runner, st: &[crate::ffi::CStage], n: usize, cost: u32, wide: usize) -> u32 {
    let _ = (run, st, n, cost, wide);
    unimplemented!("A46b: qlean_chain_run")
}
