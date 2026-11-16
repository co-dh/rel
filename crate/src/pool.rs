//! The thread pool every whole-column pass splits on, C's and Rust's alike (phase-2 §2.3): pass.h's algorithm and
//! constants, each of them measured there, carried over unchanged. The slice index `k` is an argument, not a
//! thread-local: slice `k` is the `k`-th contiguous range of `[0, n)`, so combining per-slice answers in `k` order
//! combines the rows in column order, which a fold whose step is not associative (`+` over floats) needs.
//!
//! The hand-off is two atomic counters, not a mutex and a condition variable: a worker that returns at once cost
//! 360/230/460/490 ns at width 4/8/16/24 against 1510-12190 ns, because a condvar parks every worker every pass. A
//! waiter spins `SPIN` pauses (~12 us) before it parks on a futex: long enough to cover the Lean allocation between
//! two passes of one expression, short enough that a displaced worker gets its CPU back (a 240 us window turned `copy`
//! of a million longs from 37 us into 208 with one other runnable thread). Where a worker runs is left to the
//! scheduler: pinning worker `k` to a die cost up to 3x against the evaluator, whose buffers never sit still.
use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::ffi::{c_int, c_long, c_void};
use core::hint::spin_loop;
use core::ptr::null;
use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering::{Acquire, Relaxed, Release, SeqCst}};

use crate::c::Worker;
use crate::ffi::CPass;

// The three libc names the pool adds to qrs.o's undefined list; futex, sched_getaffinity and sched_yield go through
// `syscall`. `std::thread` would bring `std` (863 KB and libgcc_s); a raw `clone` leaves glibc's thread state unset.
/// cbindgen:ignore
mod sys {
    use core::ffi::{c_int, c_long, c_ulong, c_void};
    unsafe extern "C" {
        pub fn pthread_create(t: *mut c_ulong, attr: *const c_void, f: extern "C" fn(*mut c_void) -> *mut c_void,
                              arg: *mut c_void) -> c_int;
        pub fn pthread_detach(t: c_ulong) -> c_int;
        pub fn syscall(n: c_long, ...) -> c_long;
    }
}
// x86-64 Linux numbers (<sys/syscall.h>, <linux/futex.h>, <unistd.h>)
const SYS_SCHED_YIELD: c_long = 24;
const SYS_FUTEX: c_long = 202;
const SYS_SCHED_GETAFFINITY: c_long = 204;
const FUTEX_WAIT_PRIVATE: c_long = 128;
const FUTEX_WAKE_PRIVATE: c_long = 129;
const SC_NPROCESSORS_ONLN: c_int = 84;

/// Pauses before a waiter parks or yields; a `pause` is 11.8 ns here.
pub const SPIN: u32 = 1024;
/// The widest pool.
pub const MAX_THREADS: u32 = 64;
/// A pass splits when `n * cost * wide` (its work in payload bytes) reaches this: every measured loser was at or
/// below 8M and every winner at or above 9.6M (`xf+xf` 1M 115 us -> 71 split, `xh+xh` 1M 271 -> 454).
pub const SPLIT: usize = 8388608;
// Under `cargo test` every pass of one element or more splits, three ways on the shared pool, so the kernels' unit
// tests run their multi-slice paths on real threads.
const SPLIT_AT: usize = if cfg!(test) { 1 } else { SPLIT };

/// Counter indices of `stat` (Lean `poolStat`): 0-2 are P0's, the bench's `split`/`passes`/`slices` columns.
pub const PASSES: usize = 0;
pub const SPLITS: usize = 1;
pub const SLICES: usize = 2;
/// passes run whole on the entry thread: below `SPLIT`, `wide = 0`, or width 1
pub const DECLINED: usize = 3;
/// passes entered while another was in flight, run as the same slices in turn on their own thread
pub const CONTENDED: usize = 4;
/// `rdtsc` ticks inside the slices of split passes, summed over threads; against `WALL` it is the parallelism had
pub const BUSY: usize = 5;
/// `rdtsc` ticks from the hand-off of each split pass to its join
pub const WALL: usize = 6;

#[derive(Clone, Copy)]
struct Job { call: unsafe fn(*const (), u32, usize, usize), ctx: *const (), n: usize, parts: u32 }

/// `generation` is stored by the entry and spun on by every worker, `left` the reverse: one line each, or the two
/// streams of coherence traffic land on one line. One shared `left`, not a flag a worker: no faster, 25x less steady.
#[repr(align(64))]
struct Line<T>(T);

pub struct Pool {
    /// fixed width (a test's pool) or 0: `QLEAN_THREADS`, else the CPUs this process may run on
    fixed: u32,
    width: AtomicU32,
    started: AtomicBool,
    /// a pass is in flight; also what makes thread creation one-time without a mutex
    busy: AtomicBool,
    /// the slice index the next worker to start takes
    next: AtomicU32,
    job: UnsafeCell<Job>,
    generation: Line<AtomicU32>,
    /// workers asleep on `generation`, so the wake syscall can be skipped
    parked: AtomicU32,
    left: Line<AtomicU32>,
    ctr: Line<[AtomicU64; 7]>,
}
// Safety: `job` is written only by the entry holding `busy`, while every worker is between passes (`left` was 0), and
// read by the workers after the release of `generation` that published it.
unsafe impl Sync for Pool {}

/// Slice `k` of `[0, n)` cut `parts` ways, the remainder spread over the first slices.
pub fn cut(n: usize, parts: u32, k: u32) -> (usize, usize) {
    let (q, r, k) = (n / parts as usize, n % parts as usize, k as usize);
    let lo = q * k + k.min(r);
    (lo, lo + q + (k < r) as usize)
}

#[inline(always)]
fn ticks() -> u64 {
    // Safety: `rdtsc` reads a counter and has no precondition
    unsafe { core::arch::x86_64::_rdtsc() }
}

/// Spins `SPIN` pauses, then sleeps until `*a` is no longer `stale`. `flag` tells the other side the sleep needs a
/// wake; both sides' stores are SeqCst so of "set flag, re-read `a`" and "change `a`, read flag" one sees the other.
fn wait(a: &AtomicU32, stale: u32, flag: &AtomicU32) {
    for _ in 0..SPIN {
        if a.load(Acquire) != stale { return }
        spin_loop()
    }
    loop {
        flag.fetch_add(1, SeqCst);
        if a.load(SeqCst) != stale { flag.fetch_sub(1, SeqCst); return }
        // Safety: FUTEX_WAIT on a live u32 that outlives the call; a stale value returns EAGAIN at once
        unsafe { sys::syscall(SYS_FUTEX, a.as_ptr(), FUTEX_WAIT_PRIVATE, stale as c_long, null::<c_void>(), null::<c_void>(), 0 as c_long) };
        flag.fetch_sub(1, SeqCst);
        if a.load(Acquire) != stale { return }
    }
}

/// The CPUs this process may run on, through `syscall`: glibc declares `sched_getaffinity` only under `_GNU_SOURCE`.
/// The mask starts zeroed because the kernel fills only the bytes its own mask needs.
fn cpu_count() -> i64 {
    let mut m = [0u64; 16];
    // Safety: `m` is 128 writable bytes, the size passed
    if unsafe { sys::syscall(SYS_SCHED_GETAFFINITY, 0 as c_long, size_of_val(&m) as c_long, m.as_mut_ptr()) } <= 0 { return 0 }
    m.iter().map(|w| w.count_ones() as i64).sum()
}

/// `QLEAN_THREADS`'s leading digits (0 when it has none), or None when it is unset.
fn env_threads() -> Option<i64> {
    let s = crate::os::getenv(c"QLEAN_THREADS")?;
    Some(s.iter().take_while(|c| c.is_ascii_digit()).fold(0i64, |a, &c| a.saturating_mul(10).saturating_add((c - b'0') as i64)))
}

extern "C" fn worker(arg: *mut c_void) -> *mut c_void {
    // Safety: `start` passes a `&'static Pool`
    let pool = unsafe { &*(arg as *const Pool) };
    let me = pool.next.fetch_add(1, Relaxed) + 1;
    let mut seen = 0;
    loop {
        wait(&pool.generation.0, seen, &pool.parked);
        seen = pool.generation.0.load(Acquire);
        // Safety: published by the entry's release of `generation`, unchanged until `left` reaches 0
        let job = unsafe { *pool.job.get() };
        if me < job.parts { pool.slice(&job, me) }
        pool.left.0.fetch_sub(1, Release);
    }
}

impl Pool {
    pub const fn new(fixed: u32) -> Pool {
        const Z: AtomicU64 = AtomicU64::new(0);
        Pool { fixed, width: AtomicU32::new(0), started: AtomicBool::new(false), busy: AtomicBool::new(false),
               next: AtomicU32::new(0), job: UnsafeCell::new(Job { call: nop, ctx: null(), n: 0, parts: 0 }),
               generation: Line(AtomicU32::new(0)), parked: AtomicU32::new(0), left: Line(AtomicU32::new(0)),
               ctr: Line([Z; 7]) }
    }

    /// How many threads a pass may use, read once: `getenv` in the hot path would be the measurement. The CPUs
    /// allowed, not online: under `taskset -c 0-5` the online count opened four threads a CPU.
    pub fn width(&self) -> u32 {
        let w = self.width.load(Relaxed);
        if w != 0 { return w }
        let want = if self.fixed != 0 { self.fixed as i64 } else {
            env_threads().unwrap_or_else(|| match cpu_count() {
                c if c < 1 => crate::os::sysconf(SC_NPROCESSORS_ONLN).unwrap_or(1),
                c => c,
            })
        };
        let w = want.clamp(1, MAX_THREADS as i64) as u32;
        self.width.store(w, Relaxed);
        w
    }

    /// Whether a pass of `n` units of `cost`, touching `wide` payload bytes a unit, is worth waking threads for;
    /// `wide = 0` declines outright. Wrapping, as C's `size_t` product was.
    pub fn worth(&self, n: usize, cost: u32, wide: usize) -> bool {
        self.width() > 1 && n.wrapping_mul(cost as usize).wrapping_mul(wide) >= SPLIT_AT
    }

    pub fn stat(&self, k: u8) -> u64 { self.ctr.0.get(k as usize).map_or(0, |c| c.load(Relaxed)) }

    fn add(&self, k: usize, v: u64) { self.ctr.0[k].fetch_add(v, Relaxed); }

    fn slice(&self, job: &Job, k: u32) {
        let (lo, hi) = cut(job.n, job.parts, k);
        if lo < hi {
            let t = ticks();
            // Safety: `enter`'s caller made `call` sound for every slice, concurrently for disjoint ones
            unsafe { (job.call)(job.ctx, k, lo, hi) }
            self.add(BUSY, ticks().wrapping_sub(t));
        }
    }

    /// Makes the workers, by the one entry holding `busy`; a failed create makes the width what was made.
    fn start(&'static self) {
        for i in 1..self.width() {
            let mut t = 0;
            // Safety: `worker` takes the `&'static Pool` passed as its argument
            if unsafe { sys::pthread_create(&mut t, null(), worker, self as *const Pool as *mut c_void) } != 0 {
                self.width.store(i, Relaxed);
                break;
            }
            // Safety: `t` is the thread just made, never joined
            unsafe { sys::pthread_detach(t) };
        }
        self.started.store(true, Relaxed);
    }

    /// Runs `call(ctx, k, lo, hi)` over the slices of `[0, n)`, on one thread or several; answers how many slices
    /// there were, 1 when the split was declined (then `call(ctx, 0, 0, n)` ran, `n = 0` included). Slice 0 is the
    /// caller's. A pass entered while another is in flight (a second Lean thread) runs the same slices in turn here.
    /// Safety: `call(ctx, ..)` is sound on any thread for every slice of `[0, n)`, concurrently for disjoint slices.
    unsafe fn enter(&'static self, n: usize, cost: u32, wide: usize, call: unsafe fn(*const (), u32, usize, usize),
                    ctx: *const ()) -> u32 {
        self.add(PASSES, 1);
        #[cfg(test)] tests::SEEN.with(|s| s.set(s.get().max(n.wrapping_mul(cost as usize).wrapping_mul(wide))));
        if !self.worth(n, cost, wide) {
            self.add(DECLINED, 1);
            unsafe { call(ctx, 0, 0, n) };
            return 1;
        }
        let job = Job { call, ctx, n, parts: self.width() };
        if self.busy.swap(true, Acquire) {
            self.add(CONTENDED, 1);
            for k in 0..job.parts {
                let (lo, hi) = cut(n, job.parts, k);
                if lo < hi { unsafe { call(ctx, k, lo, hi) } }
            }
            return job.parts;
        }
        if !self.started.load(Relaxed) { self.start() }
        let job = Job { parts: self.width(), ..job };
        self.add(SPLITS, 1);
        self.add(SLICES, job.parts as u64);
        let t = ticks();
        // Safety: `busy` is ours and the last pass's workers are done (`left` was 0)
        unsafe { *self.job.get() = job };
        self.left.0.store(job.parts - 1, Relaxed);
        self.generation.0.fetch_add(1, SeqCst); // releases the job, and is the Dekker half of the wake
        if self.parked.load(SeqCst) != 0 {
            // Safety: FUTEX_WAKE on a live u32
            unsafe { sys::syscall(SYS_FUTEX, self.generation.0.as_ptr(), FUTEX_WAKE_PRIVATE, c_int::MAX as c_long, null::<c_void>(), null::<c_void>(), 0 as c_long) };
        }
        self.slice(&job, 0);
        // The entry waits a whole slice, far longer than `SPIN`, so its budget is spent against no progress: every
        // slice that lands resets it, and a worker off the CPU altogether runs it out and gets this CPU back.
        let (mut was, mut spun) = (job.parts, 0);
        loop {
            let left = self.left.0.load(Acquire);
            if left == 0 { break }
            if left < was { was = left; spun = 0 }
            spun += 1;
            if spun > SPIN { unsafe { sys::syscall(SYS_SCHED_YIELD) }; spun = 0 } else { spin_loop() }
        }
        self.add(WALL, ticks().wrapping_sub(t));
        self.busy.store(false, Release);
        job.parts
    }

    /// `f(k, lo, hi)` over the slices of `[0, n)` (see `enter`); answers the slice count.
    pub fn run<F: Fn(u32, usize, usize) + Sync>(&'static self, n: usize, cost: u32, wide: usize, f: &F) -> u32 {
        // Safety: `ctx` is the `&F` below, alive until `enter` returns, which is after every slice
        unsafe fn call<F: Fn(u32, usize, usize) + Sync>(ctx: *const (), k: u32, lo: usize, hi: usize) { unsafe { (*ctx.cast::<F>())(k, lo, hi) } }
        // Safety: `F: Sync`, so calling it from several threads at once is sound
        unsafe { self.enter(n, cost, wide, call::<F>, (f as *const F).cast()) }
    }
}

fn nop(_: *const (), _: u32, _: usize, _: usize) {}

/// The one pool of the process: one, not one per C translation unit (three statics once made 69 threads).
static THE: Pool = Pool::new(if cfg!(test) { 3 } else { 0 });

/// `f(k, lo, hi)` over the slices of `[0, n)` on the pool; answers the slice count (`Pool::enter`).
pub fn run<F: Fn(u32, usize, usize) + Sync>(n: usize, cost: u32, wide: usize, f: &F) -> u32 { THE.run(n, cost, wide, f) }

/// `run` whose slices each answer one `T`: `(parts, answers)`, the answers `(lo, t)` in slice order, none for a slice
/// `cut` leaves empty (the declined pass, `n = 0` included, answers `(0, f(0, n))`).
pub fn slices<T: Send, F: Fn(usize, usize) -> T + Sync>(n: usize, cost: u32, wide: usize, f: &F) -> (u32, Vec<(usize, T)>) {
    struct Slots<T>(*mut Option<(usize, T)>);
    // Safety: slice `k` writes slot `k` only, and `k < MAX_THREADS`
    unsafe impl<T: Send> Sync for Slots<T> {}
    let mut v: Vec<Option<(usize, T)>> = (0..MAX_THREADS).map(|_| None).collect();
    let s = Slots(v.as_mut_ptr());
    let parts = run(n, cost, wide, &|k, lo, hi| {
        let s = &s;
        unsafe { *s.0.add(k as usize) = Some((lo, f(lo, hi))) }
    });
    (parts, v.into_iter().flatten().collect())
}

/// C's `qlean_run`: worker `f` over `p` on the pool (`c::Runner`, and `qrs_pool_run` under its C name).
/// Safety: `f(lo, hi, p)` is sound on any thread for every slice of `[0, n)`, concurrently for disjoint slices.
pub unsafe extern "C" fn run_c(f: Worker, n: usize, cost: u32, wide: usize, p: *const CPass) -> u32 {
    struct Ctx { f: Worker, p: *const CPass }
    unsafe fn call(ctx: *const (), _: u32, lo: usize, hi: usize) {
        let c = unsafe { &*ctx.cast::<Ctx>() };
        unsafe { (c.f)(lo, hi, c.p) }
    }
    let ctx = Ctx { f, p };
    unsafe { THE.enter(n, cost, wide, call, (&ctx as *const Ctx).cast()) }
}

/// Counter `k` of the process's pool (`PASSES` .. `WALL`), 0 for any other.
pub fn stat(k: u8) -> u64 { THE.stat(k) }

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use std::time::{Duration, Instant};
    std::thread_local! {
        /// the largest `n * cost * wide` this thread entered the pool with since `seen`
        pub(crate) static SEEN: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
    }
    /// The largest pass `f` asked the pool for, as `n * cost * wide`.
    pub(crate) fn seen(f: impl FnOnce()) -> usize { SEEN.with(|s| s.set(0)); f(); SEEN.with(|s| s.get()) }

    fn gettid() -> i64 { unsafe { sys::syscall(186 as c_long) as i64 } }

    // A runner that runs its slices in turn never fills the barrier: four slices, each inside at once.
    #[test] fn pool_spreads() {
        let pool: &'static Pool = std::boxed::Box::leak(std::boxed::Box::new(Pool::new(4)));
        let inside = AtomicU32::new(0);
        let tids = std::sync::Mutex::new(std::vec::Vec::new());
        let parts = pool.run(4, 1, SPLIT, &|_, _, _| {
            tids.lock().unwrap().push(gettid());
            inside.fetch_add(1, SeqCst);
            let t = Instant::now();
            while inside.load(SeqCst) < 4 { assert!(t.elapsed() < Duration::from_secs(2), "pool_spreads: slices not concurrent"); spin_loop() }
        });
        assert_eq!(parts, 4);
        let mut t = tids.into_inner().unwrap();
        t.sort();
        t.dedup();
        assert_eq!(t.len(), 4, "four slices on four threads");
    }

    // Many threads entering at once: one splits, the others run the same slices in turn; every answer is whole.
    #[test] fn pool_contended_answers_whole() {
        let pool: &'static Pool = std::boxed::Box::leak(std::boxed::Box::new(Pool::new(8)));
        std::thread::scope(|s| for _ in 0..16 { s.spawn(|| for n in [0usize, 1, 7, 8, 9, 1000, 100_003] {
            let sum = AtomicU64::new(0);
            let parts = pool.run(n, 1, SPLIT, &|_, lo, hi| { sum.fetch_add((lo..hi).map(|i| i as u64).sum(), Relaxed); });
            assert_eq!(sum.load(Relaxed), (n as u64) * (n as u64).saturating_sub(1) / 2);
            assert_eq!(parts, if n == 0 { 1 } else { 8 });
        }); });
        assert_eq!(pool.stat(PASSES as u8), 16 * 7);
        assert_eq!(pool.stat(SPLITS as u8) + pool.stat(CONTENDED as u8) + pool.stat(DECLINED as u8), 16 * 7);
    }

    // A 2^24-element input to each kernel asks for a pass the production threshold splits (at width 4: `worth`'s
    // other half). Kernels whose input needs an encoded column are covered by the bench's `spread` gate instead.
    #[test] fn pool_parts() {
        use crate::c::qlean_run_c as run;
        use std::{vec, vec::Vec};
        const N: usize = 1 << 24;
        let big = |what: &str, s: usize| assert!(s >= SPLIT, "pool_parts: {what} at 2^24 asks for {s} < {SPLIT}: never splits");
        let mut o = vec![0i64; N];
        big("til", seen(|| crate::structural::til(run, &mut o)));
        let (a, b) = (vec![1u8; N / 2], vec![2u8; N / 2]);
        let mut ob = vec![0u8; N];
        big("concat", seen(|| crate::structural::concat(run, &[&a, &b], &mut ob)));
        let src = vec![7u8; 8 * N];
        let idx: Vec<i64> = (0..N as i64).collect();
        let mut o8 = vec![0u8; 8 * N];
        big("gather", seen(|| crate::structural::gather(run, 8, 0, &src, &idx, &mut o8)));
        let x: Vec<u8> = (0..N).flat_map(|i| (i as f64).to_bits().to_le_bytes()).collect();
        let mut o2 = vec![0u8; 2 * N];
        big("cast f64 -> i16", seen(|| crate::ew::cast(run, 5, 1, 0, &x, N, &mut o2)));
        big("floor f64", seen(|| crate::ew::floor(run, 5, &x, N, &mut o8)));
        let w = vec![0x5555_5555_5555_5555u64; N];
        let mut ow = vec![0u64; N];
        big("bitw", seen(|| crate::ew::bitw(run, 0, crate::pod::bytes(&w), crate::pod::bytes(&w), N, crate::pod::bytes_mut(&mut ow))));
    }

    // the threshold: one unit below declines, at it splits; `wide = 0` always declines
    #[test] fn pool_threshold() {
        let pool: &'static Pool = std::boxed::Box::leak(std::boxed::Box::new(Pool::new(2)));
        let w = |n, c, wd| SPLIT_AT <= usize::wrapping_mul(n, c as usize).wrapping_mul(wd) && pool.width() > 1;
        assert_eq!(pool.worth(SPLIT, 1, 1), w(SPLIT, 1, 1));
        assert!(!pool.worth(usize::MAX, 4, 0));
        assert_eq!(cut(10, 3, 0), (0, 4));
        assert_eq!(cut(10, 3, 2), (7, 10));
        assert_eq!(cut(2, 3, 2), (2, 2));
    }
}
