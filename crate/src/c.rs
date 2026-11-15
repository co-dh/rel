//! The C symbols Rust calls, as `unsafe extern "C"` declarations, and the one safe call over each.
use core::ptr::null;

use crate::ffi::CPass;

type Worker = unsafe extern "C" fn(lo: usize, hi: usize, p: *const CPass);

#[cfg(not(test))]
unsafe extern "C" {
    /// sort.c's non-`static` wrapper of pass.h:415 `qlean_run`.
    fn qlean_run_c(f: Worker, n: usize, cost: u32, wide: usize, p: *const CPass) -> u32;
}

/// Under `cargo test` there is no C pool: three slices, cut as `qlean_slice` (pass.h:243) cuts them, run in turn.
#[cfg(test)]
unsafe fn qlean_run_c(f: Worker, n: usize, _cost: u32, _wide: usize, p: *const CPass) -> u32 {
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
pub fn run_map<F: Fn(usize, usize, &mut [u8]) + Sync>(out: &mut [u8], units: usize, unit: usize, cost: u32,
                                                      wide: usize, f: &F) -> u32 {
    assert!(units.checked_mul(unit).is_some_and(|b| b <= out.len()),
            "run_map: {units} units of {unit} bytes past a {}-byte output", out.len());
    let job = Job { f, out: out.as_mut_ptr(), unit };
    let p = CPass { a: (&raw const job).cast(), b: null(), c: null(), o: out.as_mut_ptr().cast(), n: units, at: 0,
                    r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 };
    // the slices partition [0, units), so the `&mut` each worker makes are disjoint; `out` outlives the call
    unsafe { qlean_run_c(slice::<F>, units, cost, wide, &p) }
}

#[cfg(test)]
mod tests {
    #[test] fn run_map_cuts_disjoint_slices() {
        let mut out = [0u8; 2 * 7 + 1];
        let parts = super::run_map(&mut out, 7, 2, 4, 8, &|lo, hi, o: &mut [u8]| {
            assert_eq!(o.len(), 2 * (hi - lo));
            for (k, b) in o.iter_mut().enumerate() { *b = (lo * 2 + k) as u8 + 1 }
        });
        assert_eq!(parts, 3);
        assert_eq!(out, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0]);
    }
}
