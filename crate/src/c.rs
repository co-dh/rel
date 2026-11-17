//! The runner a kernel takes (the pool, or C's serial one for a stage inside a slice), and the safe calls over it.
use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::ptr::null;
use core::sync::atomic::{AtomicBool, Ordering};

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

/// ew.rs `ew_serial`: a runner that runs the whole range on the calling thread and answers one part, for a
/// worker that is already one slice of the pool (a chain tile) and must not enter it again.
pub unsafe extern "C" fn serial(f: Worker, n: usize, _cost: u32, _wide: usize, p: *const CPass) -> u32 {
    unsafe { f(0, n, p) };
    1
}

pub type Worker = unsafe extern "C" fn(lo: usize, hi: usize, p: *const CPass);
/// A pass's runner: the pool (`pool::run_c`, `qrs_pool_run` in C) or a serial one C hands a stage already inside a
/// slice (ew.rs `ew_serial`), which is why the kernels take it rather than call the pool; F3 makes it `Par`.
pub type Runner = unsafe extern "C" fn(f: Worker, n: usize, cost: u32, wide: usize, p: *const CPass) -> u32;

/// The runner a Rust export hands its kernel: the process's one pool.
pub fn pool() -> Runner { crate::pool::run_c }
/// The unit tests' name for the pool, which they once faked (three slices in turn); under `cargo test` the real pool
/// splits every non-empty pass three ways (`pool::SPLIT_AT`).
#[cfg(test)]
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
pub fn map_at<F: Fn(usize, usize, &mut [u8]) + Sync>(run: Runner, out: &mut [u8], units: usize,
                                                 at: &(dyn Fn(usize) -> usize + Sync), cost: u32, wide: usize, f: &F) -> u32 {
    let o = out.as_mut_ptr();
    let job = Job { f, out: o, at, len: out.len() };
    let p = CPass { a: (&raw const job).cast(), b: null(), c: null(), o: o.cast(), n: units, at: 0,
                    r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 };
    // the slices partition [0, units), so the `&mut` each worker makes are disjoint; `out` outlives the call
    unsafe { run(slice::<F>, units, cost, wide, &p) }
}

/// `run_map_at` with a second output `b` of equally spaced units (`unit` bytes, the last may be short): slice `[lo, hi)`
/// is `f(lo, hi, &mut a[at(lo) .. at(hi)], &mut b[lo * unit ..])`, `b` ending at `hi * unit`. For a pass that writes a
/// variable-length blob and a per-element table side by side. Panics unless `at` is non-decreasing over `0 ..= units`
/// and every unit of both starts inside its output, which is what makes the `&mut` slices disjoint.
pub fn run_map2<F: Fn(usize, usize, &mut [u8], &mut [u8]) + Sync>(run: Runner, a: &mut [u8], at: &(dyn Fn(usize) -> usize + Sync),
                                                                  b: &mut [u8], unit: usize, units: usize, cost: u32, wide: usize,
                                                                  f: &F) -> u32 {
    assert!((0..units).all(|k| at(k) <= at(k + 1)) && (units == 0 || at(units - 1) <= a.len()),
            "run_map2: {units} units do not start in ascending order inside a {}-byte output", a.len());
    assert!(units == 0 || (units - 1).checked_mul(unit).is_some_and(|s| s <= b.len()),
            "run_map2: {units} units of {unit} bytes do not start inside a {}-byte output", b.len());
    struct Job2<'f, F> { f: &'f F, a: *mut u8, at: &'f (dyn Fn(usize) -> usize + Sync), la: usize, b: *mut u8, unit: usize, lb: usize }
    /// Safety: `p.a` is a live `Job2<F>` and `[lo, hi)` is a slice of `[0, n)` no other worker is given.
    unsafe extern "C" fn slice2<F: Fn(usize, usize, &mut [u8], &mut [u8]) + Sync>(lo: usize, hi: usize, p: *const CPass) {
        let j = unsafe { &*(*p).a.cast::<Job2<F>>() };
        let (ae, be) = ((j.at)(hi).min(j.la), (hi * j.unit).min(j.lb));
        let (as_, bs) = ((j.at)(lo).min(ae), (lo * j.unit).min(be));
        let (oa, ob) = unsafe { (core::slice::from_raw_parts_mut(j.a.add(as_), ae - as_), core::slice::from_raw_parts_mut(j.b.add(bs), be - bs)) };
        (j.f)(lo, hi, oa, ob)
    }
    let job = Job2 { f, a: a.as_mut_ptr(), at, la: a.len(), b: b.as_mut_ptr(), unit, lb: b.len() };
    let p = CPass { a: (&raw const job).cast(), b: null(), c: null(), o: core::ptr::null_mut(), n: units, at: 0,
                    r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 };
    // the slices partition [0, units), so the `&mut` each worker makes are disjoint in `a` (ascending `at`) and in `b`
    unsafe { run(slice2::<F>, units, cost, wide, &p) }
}

/// `run_map` whose slices each answer one `T` (a private histogram, a partial fold): `(parts, answers)` with the
/// answers `(lo, t)` in slice order. The runner may be C's serial one, which passes no slice index, so a slice is named by its
/// `lo`, which no other slice shares; a slice `qlean_run` leaves empty gives none.
pub fn run_slices<T: Send, F: Fn(usize, usize) -> T + Sync>(run: Runner, n: usize, cost: u32, wide: usize, f: &F) -> (u32, Vec<(usize, T)>) {
    struct Bag<T> { lock: AtomicBool, v: UnsafeCell<Vec<(usize, T)>> }
    // Safety: `v` is touched only with `lock` held
    unsafe impl<T: Send> Sync for Bag<T> {}
    let bag = Bag { lock: AtomicBool::new(false), v: UnsafeCell::new(Vec::new()) };
    let parts = run_map(run, &mut [], n, 0, cost, wide, &|lo, hi, _: &mut [u8]| {
        let t = f(lo, hi);
        let bag = &bag; // the whole bag, not its fields: only the bag is `Sync`
        while bag.lock.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() { core::hint::spin_loop() }
        // Safety: the lock is ours
        unsafe { (*bag.v.get()).push((lo, t)) }
        bag.lock.store(false, Ordering::Release);
    });
    let mut v = bag.v.into_inner();
    v.sort_unstable_by_key(|r| r.0);
    (parts, v)
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

/// c.rs: a stage operand's source code at or above `SLOTS` is a column (re-based per tile) or fixed (one pointer).
pub const SLOTS: usize = 10;
pub const TILE: usize = 1024;
pub const COLUMN: u8 = 254;

/// One tile of eight-byte elements per slot, the widest any stage answers, on a cache line.
#[repr(align(64))]
pub struct Slot([u8; TILE * 8]);

/// c.rs `qlean_chain_run` over the tiles `[lo, hi)`: every stage over a tile before the next tile starts.
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

/// c.rs `qlean_run_chain`: the stages of `st` over `n` elements on the pool, one thread or several; answers the
/// thread count. `cost` and `wide` are the whole chain's, so the split is decided on the expression, not on one verb.
/// Safety (of the pointers in `st`): the bindings of every stage reach `n` elements, as `qlean_ew_chain` built them.
pub fn run_chain(run: Runner, st: &[crate::ffi::CStage], n: usize, cost: u32, wide: usize) -> u32 {
    assert!(!st.is_empty() && st.len() <= SLOTS, "qlean_run_chain: {} stages, and the driver holds {SLOTS}", st.len());
    if let [s] = st {
        // a chain of one pass is that pass: tiling it fuses nothing and costs a call a tile. A comparison is sliced by
        // output byte, so its widest operand is counted per output bit (c.rs)
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

/// The stages of `st` over `n` elements one tile at a time, in order, on the calling thread: for a fold whose lanes are
/// positional, where a split across threads (or one whole-column call of a single stage) would be another sum.
pub fn chain_in_order(st: &[crate::ffi::CStage], n: usize) {
    let p = CPass { a: st.as_ptr().cast(), b: null(), c: null(), o: core::ptr::null_mut(), n, at: 0, r#priv: 0, nul: 0,
                    op: st.len() as u8, cls: 0, shape: 0 };
    // `st` outlives the call and its bindings reach `n` elements, as `chain_tiles` requires
    unsafe { chain_tiles(0, n.div_ceil(TILE), &p) }
}
