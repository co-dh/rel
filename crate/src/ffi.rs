//! The `#[repr(C)]` column and encoder structs the block encoder and the pool workers share, and the helpers the
//! `ffi/*.rs` exports call. No symbol leaves the object from here: the Lean externs are in `ffi/*.rs`.
use core::alloc::Layout;
use core::ffi::{c_int, c_void};
use core::ptr::null_mut;
use core::slice;
use core::sync::atomic::{AtomicI32, AtomicUsize};


use crate::{c, lean};


use crate::layout::Tail;

use crate::DEFAULT_LG;

use crate::enc::{EncMeta, EncPack, Producer};
use crate::blocks::Grid;
use crate::enc;

/// A column's arrays and counts as raw pointers (`coc` of the C it replaced).
#[repr(C)]
pub struct CCoc {
    pub base: *mut i64, pub maxv: *mut i64, pub width: *mut u8, pub off: *mut u64, pub bsum: *mut i64,
    pub sumnul: *mut i64, pub sumn: *mut u64, pub pack: *mut u8,
    pub n: usize, pub nblk: usize, pub packbytes: usize, pub mblk: usize,
    pub exc_off: *const u32, pub exc_pos: *const u16, pub exc_raw: *const u8, pub fdelta: *mut u64,
    pub nexc: usize, pub exc_esz: usize,
}
impl CCoc {
    /// The block size exponent, read from the metadata trailer the `sumnul` slot points into (two words on). A view with no
    /// trailer has no block size, so there is no default to answer with: it aborts naming the slot.
    #[inline(always)]
    pub fn lg(&self) -> u32 { assert!(!self.sumnul.is_null(), "qlean coc view: no metadata trailer (null sumnul), so no block size lg"); unsafe { *self.sumnul.add(2) as u32 } }
}

/// The context `c::run_map` hands the pool worker (`qlean_pass` of the C it replaced).
#[repr(C)]
pub struct CPass {
    pub a: *const core::ffi::c_void, pub b: *const core::ffi::c_void, pub c: *const core::ffi::c_void,
    pub o: *mut core::ffi::c_void,
    pub n: usize, pub at: usize, pub r#priv: usize,
    pub nul: i64,
    pub op: u8, pub cls: u8, pub shape: u8,
}

pub const _: () = assert!(size_of::<CCoc>() == 144);
pub const _: () = assert!(size_of::<CPass>() == 72);






/// Safety: `p` is null or valid for `n` reads of `T` during `'a`.
pub unsafe fn sl<'a, T>(p: *const T, n: usize) -> &'a [T] {
    if p.is_null() || n == 0 { &[] } else { unsafe { slice::from_raw_parts(p, n) } }
}
/// Safety: `p` is null or valid for `n` writes of `T` during `'a`, and nothing else aliases it.
pub unsafe fn sl_mut<'a, T>(p: *mut T, n: usize) -> &'a mut [T] {
    if p.is_null() || n == 0 { &mut [] } else { unsafe { slice::from_raw_parts_mut(p, n) } }
}





// ---- Column (a) scaffold: the mirrors its shims take, asserted by `QRS_ASSERT_COLA` (structural.rs). ----

/// A source of blocks: callbacks take the struct as `void *`.
#[repr(C)]
pub struct CSrc {
    pub ctx: *mut c_void, pub open: Option<unsafe extern "C" fn(*const c_void) -> *mut c_void>,
    pub at: Option<unsafe extern "C" fn(*const c_void, *mut c_void, usize, usize) -> *const c_void>,
    pub close: Option<unsafe extern "C" fn(*const c_void, *mut c_void)>, pub bad: *mut c_int,
}
/// The encoder's state (the `coc_enc` of the C it replaced). The lean objects are opaque here; `lb` and `over` are plain
/// words, read through `AtomicUsize::from_ptr` by whoever fills A16.
#[repr(C)]
pub struct CEnc {
    pub src: *const CSrc, pub n: usize, pub width: usize,
    pub blk: Option<unsafe extern "C" fn(*mut c_void, usize, *const c_void, usize)>,
    pub c: CCoc, pub meta: *mut c_void, pub pack: *mut c_void,
    pub exc_off: *mut u32, pub exc_heap: *mut u32, pub frm_heap: *mut u64, pub exc_pos: *mut u16,
    pub exc_raw: *mut u8, pub out: *mut u8, pub planned: c_int, pub frm: c_int,
    pub at: usize, pub nexc: usize, pub tail: usize, pub below: usize, pub lb: usize, pub over: c_int,
}
impl CEnc {
    /// Block `b`'s meta-pass view: the slots `coc_enc_open` set up (`c`'s four arrays, `frm_heap` as `c.fdelta`, `exc_off`,
    /// the one a column does not keep is null).
    /// Safety: `self` is an open encoder, `b < c.mblk`, no other view of `b` alive.
    pub unsafe fn meta_blk<'a>(&mut self, b: usize) -> EncMeta<'a> {
        let c = &self.c;
        unsafe { EncMeta { b, base: &mut *c.base.add(b), maxv: &mut *c.maxv.add(b), width: &mut *c.width.add(b), bsum: &mut *c.bsum.add(b),
                           frm: if c.fdelta.is_null() { None } else { Some(&mut *c.fdelta.add(b)) }, nexc: &mut *self.exc_off.add(b + 1),
                           patch: (self.n as u64) < 1 << 32 } }
    }
    /// Block `b`'s pack view after its meta step (`exc_off[b + 1]` still the block's count), its residuals at `res`, its `ne`
    /// patches at `pos` and `raw`: the `nb` elements' `ceil(nb * width / 8)` residual bytes, or with `whole` the full
    /// `blk * width / 8` (`move_pack` copies a whole block). Safety: as `meta_blk`, the three regions large enough.
    unsafe fn pack_at<'a>(&self, b: usize, nb: usize, whole: bool, res: *mut u8, pos: *mut u16, raw: *mut u8, ne: usize) -> EncPack<'a> {
        let c = &self.c;
        unsafe {
            let (base, w) = (*c.base.add(b), *c.width.add(b));
            EncPack { nb, base, frame: (base as u64).wrapping_add(if c.fdelta.is_null() { 0 } else { *c.fdelta.add(b) }), width: w,
                      res: sl_mut(res, (if whole { 1usize << c.lg() } else { nb } * w as usize).div_ceil(8)),
                      pos: sl_mut(pos, ne), raw: sl_mut(raw, ne * self.width) }
        }
    }
    /// Block `b` packed in the meta pass, into `st`: its full residual room (`Meta::offsets`' share, zeroed, as
    /// `coc_enc_layout` zeroes a short last block's) and its patches.
    /// The answer is the `pack` of `move_blk` and `Scatter::write`, which reads the block's width and patch count when it is
    /// called, so it is called after block `b`'s meta step.
    unsafe fn stage<'a>(&'a self, b: usize, nb: usize, st: &'a mut Staged) -> impl FnOnce(bool) -> EncPack<'a> + 'a {
        move |whole| unsafe {
            let (w, ne) = (*self.c.width.add(b), *self.exc_off.add(b + 1) as usize);
            *st = Staged { res: alloc::vec![0; (1usize << self.c.lg()) * w as usize / 8], pos: alloc::vec![0; ne], raw: alloc::vec![0; (ne * self.width).div_ceil(8)] };
            self.pack_at(b, nb, whole, st.res.as_mut_ptr(), st.pos.as_mut_ptr(), st.raw.as_mut_ptr().cast(), ne)
        }
    }
    /// A `Staged` block copied to where `coc_enc_layout` put block `b`. Safety: after `coc_enc_layout`, `st` block `b`'s.
    unsafe fn place(&mut self, b: usize, st: &Staged) {
        unsafe {
            let at = *self.exc_off.add(b) as usize;
            sl_mut(self.c.pack.add(*self.c.off.add(b) as usize), st.res.len()).copy_from_slice(&st.res);
            if !st.pos.is_empty() {
                sl_mut(self.exc_pos.add(at), st.pos.len()).copy_from_slice(&st.pos);
                let raw = &crate::pod::bytes(&st.raw)[..st.pos.len() * self.width];
                sl_mut(self.exc_raw.add(at * self.width), raw.len()).copy_from_slice(raw);
            }
        }
    }
}
/// A block a `Sink`'s meta pass packed, kept until the layout says where it goes, so its producer runs once: its residuals
/// and its patch positions and raw elements (in words, so a float patch list is aligned for its floats).
#[derive(Default)]
pub struct Staged { res: alloc::vec::Vec<u8>, pos: alloc::vec::Vec<u16>, raw: alloc::vec::Vec<u64> }
/// A symbol: its bytes and length.
#[repr(C)]
pub struct CSym { pub p: *const u8, pub len: usize }
/// One pass of a fused chain.
#[repr(C)]
pub struct CStage {
    pub f: Option<unsafe extern "C" fn(usize, usize, *const CPass)>, pub p: CPass, pub asrc: u8, pub bsrc: u8, pub osrc: u8,
    pub abits: u16, pub bbits: u16, pub obits: u16, pub bytewise: u8,
}
pub const _: () = assert!(size_of::<CSrc>() == 40 && size_of::<CEnc>() == 296);
pub const _: () = assert!(size_of::<CSym>() == 16 && size_of::<CStage>() == 96);
impl CPass {
}
impl CStage {
}
impl CCoc {
}


// ---- K10: the chain's stage table and builder (ew.rs `ew_stage_worker`, `ew_chain_build`) and the statistics fold ----

impl CCoc {
}



// ---- K24: coc.rs, 764-816, the one writer of an answer column: `Sink` (coc plan §3) ----
// A sink writes its column a block of its grid at a time on the pool, in the form it was opened in. Its blocks come from
// an `enc::Producer` (a `Blocks` source, a kernel's fill, whole blocks it `take`s) or from a step that writes the block
// itself (`each`). Allocation of the scratch aborts like coc.rs's `coc_alloc`.

/// coc.rs `coc_alloc`: 64-byte aligned, never size 0, abort on failure.
pub unsafe fn coc_alloc(bytes: usize) -> *mut u8 {
    let want = bytes.next_multiple_of(64).max(64);
    let p = unsafe { alloc::alloc::alloc(Layout::from_size_align_unchecked(want, 64)) };
    if p.is_null() {
        crate::os::eprint(format_args!("aligned_alloc {bytes} bytes failed\n")).expect("qlean: stderr");
        crate::os::exit(1)
    }
    p
}
/// Frees what `coc_alloc` or C's `aligned_alloc` gave (the allocator's `dealloc` is `free`, whatever the layout says).
pub unsafe fn coc_free(p: *mut u8) { if !p.is_null() { unsafe { alloc::alloc::dealloc(p, Layout::from_size_align_unchecked(64, 64)) } } }
/// coc.rs `coc_meta_view`: the five sections and the trailer over `metabytes` bytes at `m`, the count cut to what they hold.
pub unsafe fn meta_view(m: *mut u8, metabytes: usize, n: usize) -> CCoc {
    let nblk = metabytes / 33;
    unsafe {
        let lg = *m.add(32 * nblk + 16).cast::<u64>();
        assert!((crate::MIN_LG as u64..=crate::MAX_LG as u64).contains(&lg), "qlean: a column's block size lg {lg} is outside 6 ..= 16");
        let (lg, n) = (lg as u32, n.min(nblk << lg));
        CCoc { base: m.cast(), maxv: m.add(8 * nblk).cast(), off: m.add(16 * nblk).cast(), bsum: m.add(24 * nblk).cast(),
               sumnul: m.add(32 * nblk).cast(), sumn: m.add(32 * nblk + 8).cast(), width: m.add(32 * nblk + 24), pack: null_mut(),
               n, nblk: n.div_ceil(1 << lg), packbytes: 0, mblk: nblk, exc_off: core::ptr::null(), exc_pos: core::ptr::null(),
               exc_raw: core::ptr::null(), fdelta: null_mut(), nexc: 0, exc_esz: 0 }
    }
}

/// coc.rs `coc_enc_open`: the metadata sarray and the heap copies the meta pass fills.
pub unsafe extern "C" fn qrs_coc_enc_open(s: *mut CEnc, n: usize, width: usize) {
    unsafe {
        let (nblk, msz) = (n.div_ceil(1 << DEFAULT_LG), 33 * n.div_ceil(1 << DEFAULT_LG) + 24);
        core::ptr::write_bytes(s, 0, 1);
        (*s).n = n;
        (*s).width = width;
        let meta = lean::alloc_sarray(1, msz, msz);
        // the trailer's block size, which every reader of this metadata (the encoder's own view first) takes its grid from
        lean::sarray_cptr(meta).add(32 * nblk + 16).cast::<u64>().write(DEFAULT_LG as u64);
        (*s).meta = meta.cast();
        (*s).c = meta_view(lean::sarray_cptr(meta), msz, n);
        (*s).frm_heap = coc_alloc(nblk * 8).cast();
        (*s).c.fdelta = (*s).frm_heap;
        (*s).exc_heap = coc_alloc((nblk + 1) * 4).cast();
        (*s).exc_off = (*s).exc_heap;
    }
}
/// coc.rs `coc_enc_plan`: between the two passes, the offsets, the exception prefix sums and the tail's size; answers the
/// encoded column's whole size. Once per encoder.
pub unsafe extern "C" fn qrs_coc_enc_plan(s: *mut CEnc) -> usize {
    unsafe {
        let (nblk, width) = ((*s).c.nblk, (*s).width);
        if (*s).planned == 0 {
            (*s).planned = 1;
            let at = crate::coc::Meta::offsets((*s).c.lg(), sl((*s).c.width, nblk), nblk, sl_mut((*s).c.off, nblk));
            (*s).c.packbytes = at as usize;
            (*s).at = at as usize;
            (*s).nexc = enc::exc_offsets(sl_mut((*s).exc_off, nblk + 1), nblk);
            (*s).frm = sl((*s).frm_heap, nblk).iter().any(|&f| f != 0) as c_int;
            // Frame of Reference's patch list is the pack's tail: `tail` is what follows the residuals
            (*s).tail = enc::tail_bytes((*s).nexc, (*s).frm != 0, width, nblk);
        }
        lean::sarray_size((*s).meta.cast()) + (*s).at + (*s).tail
    }
}
/// coc.rs `coc_enc_layout`: the trailer, then the pack with the patch list as its tail, the heap copies moved in.
pub unsafe extern "C" fn qrs_coc_enc_layout(s: *mut CEnc) {
    use crate::layout::exc_layout;
    unsafe {
        let (nblk, n, width) = ((*s).c.nblk, (*s).n, (*s).width);
        // the trailer is the column's, so it is written here and not inside a block slice
        *(*s).c.sumnul = enc::coc_sumnul(width);
        *(*s).c.sumn = n as u64;
        qrs_coc_enc_plan(s);
        let (at, nexc) = ((*s).at, (*s).nexc);
        let put = |t: *mut u8, tail: usize, w: u64| enc::exc_header(sl_mut(t, tail), nexc, w);
        // Frame of Reference's patch list is the pack's tail, and there is none without an exception
        let frm = (*s).frm != 0;
        let l = if nexc != 0 { exc_layout(nblk, nexc, width, if frm { Tail::Frames } else { Tail::None }) } else { None };
        let tail = l.as_ref().map_or(0, |l| l.size);
        let pack = lean::alloc_sarray(1, at + tail, at + tail);
        (*s).pack = pack.cast();
        (*s).c.pack = lean::sarray_cptr(pack);
        (*s).c.packbytes = at + tail;
        // a short last block reserves a full block's room and packs only `n % blk` residuals into it; the rest is written
        // here, so equal columns are equal bytes
        if n % (1 << (*s).c.lg()) != 0 { core::ptr::write_bytes((*s).c.pack.add(*(*s).c.off.add(nblk - 1) as usize), 0, at - *(*s).c.off.add(nblk - 1) as usize) }
        let o_frm = l.as_ref().map_or(0, |l| l.tail);
        if let Some(l) = l {
            let t = (*s).c.pack.add(at);
            put(t, tail, width as u64 | if frm { 0x100 } else { 0 }); // COC_EXC_FRM
            core::ptr::copy_nonoverlapping((*s).exc_off.cast::<u8>(), t.add(l.off), (nblk + 1) * 4);
            if frm { core::ptr::copy_nonoverlapping((*s).frm_heap.cast::<u8>(), t.add(o_frm), nblk * 8) }
            coc_free((*s).exc_heap.cast());
            (*s).exc_heap = null_mut();
            (*s).exc_off = t.add(l.off).cast();
            (*s).exc_pos = t.add(l.pos).cast();
            (*s).exc_raw = t.add(l.raw);
        }
        // a frame above the minimum leaves an element under it, which is an exception, so a column with no patch list has
        // every frame at base and the null `fdelta` says so
        coc_free((*s).frm_heap.cast());
        (*s).frm_heap = null_mut();
        (*s).c.fdelta = if frm { (*s).c.pack.add(at + o_frm).cast() } else { null_mut() };
    }
}
/// Whatever a failed pass leaves: the heap copies and every part allocated so far.
pub unsafe fn enc_free(s: *mut CEnc) {
    unsafe {
        coc_free((*s).exc_heap.cast());
        coc_free((*s).frm_heap.cast());
        if !(*s).meta.is_null() { lean::dec((*s).meta.cast()) }
        if !(*s).pack.is_null() { lean::dec((*s).pack.cast()) }
    }
}

/// The writer of one answer column (coc plan §3): its grid and the encoder state its passes fill. Dropped
/// unfinished (a size test failed), it frees what it allocated.
pub struct Sink { pub e: CEnc, g: Grid, enc: bool }
/// A pass's step: block `b` (elements `lo .. lo + nb`) of the sink `e`, with the worker's block buffer (`16 << lg` bytes).
pub type Step<'a> = &'a (dyn Fn(*mut CEnc, usize, usize, usize, &mut [u8]) + Sync);
struct Pass<'a> { step: Step<'a>, g: Grid, sized: bool }
/// coc.rs `src_run`: the blocks `[b0, b1)` through the step; a worker writes only what its block owns (its metadata
/// entries, its bytes at off[b], its exceptions at exc_off[b]), so any pass may be split.
unsafe extern "C" fn sink_run(b0: usize, b1: usize, p: *const CPass) {
    use core::sync::atomic::Ordering::SeqCst;
    unsafe {
        let (s, job) = ((*p).o.cast::<CEnc>(), &*(*p).a.cast::<Pass>());
        let (width, lg) = ((*s).width, job.g.lg);
        let mut buf = crate::pod::uninit::<i64>(2 << lg);
        let (lb, over) = (AtomicUsize::from_ptr(&raw mut (*s).lb), AtomicI32::from_ptr(&raw mut (*s).over));
        // the meta pass under a size test stops once the blocks it has sized already reach it: each block's residuals and its
        // exceptions' bytes are a part of the total `qrs_coc_enc_plan` would answer, so their sum is a lower bound
        let mut mine = 0usize;
        for b in b0..b1 {
            let (lo, nb) = job.g.span(b);
            (job.step)(s, b, lo, nb, crate::pod::bytes_mut(&mut buf));
            if !job.sized { continue }
            mine += enc::block_bytes(lg, *(*s).c.width.add(b), *(*s).exc_off.add(b + 1), width);
            if (b - b0) % 16 == 15 {
                if lb.fetch_add(mine, SeqCst) + mine >= (*s).below { over.store(1, SeqCst) }
                mine = 0;
                if over.load(SeqCst) != 0 { break }
            }
        }
        if job.sized { lb.fetch_add(mine, SeqCst); }
    }
}
impl Drop for Sink { fn drop(&mut self) { unsafe { enc_free(&mut self.e) } } }
impl Sink {
    /// `n` elements of `width` bytes: coc.rs `coc_enc_open`.
    pub fn new(n: usize, width: usize) -> Sink {
        let mut s = Sink { e: unsafe { core::mem::zeroed() }, g: Grid { n, lg: DEFAULT_LG }, enc: false };
        unsafe { qrs_coc_enc_open(&mut s.e, n, width) }
        s
    }
    /// `step` over every block on the pool; `sized` makes it the sizing pass of the size test.
    pub fn each(&mut self, sized: bool, cost: u32, step: Step) {
        let job = Pass { step, g: self.g, sized: sized && self.e.below != 0 };
        let p = CPass { a: (&raw const job).cast(), b: core::ptr::null(), c: core::ptr::null(), o: (&raw mut self.e).cast(), n: self.g.n, at: 0,
                        r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 };
        unsafe { c::pool()(sink_run, self.g.nblk(), cost, self.e.width << self.g.lg, &p) };
    }
    /// The column `p` denotes, as the Lean answer (`(meta, pack)`);
    /// with `shrinks`, `None` where the encoded form is not smaller than the `n * width` dense bytes it replaces
    /// (`Enc.shrinks`, `CLAUDE.md`'s "nothing is encoded that the encoding does not shrink").
    pub fn write<P: Producer + ?Sized>(mut self, p: &P, shrinks: bool) -> Option<lean::O> {
        let (w, n) = (self.e.width, self.g.n);
        let below = if shrinks { n * w } else { usize::MAX };
        // what the residuals and exceptions may come to before the size test is already failed, the metadata being fixed
        let msz = unsafe { lean::sarray_size(self.e.meta.cast()) };
        if below != usize::MAX { if below <= msz { return None } self.e.below = below - msz }
        self.staged(crate::QLEAN_COST_ARITH, below, &|s, b, lo, nb, buf, st| unsafe {
            enc::move_blk(p, &mut (*s).meta_blk(b), (*s).stage(b, nb, st), || p.block(b, lo, nb, w, buf), nb, w)
        })?;
        Some(self.finish())
    }
    /// One `Staged` a block of the grid.
    fn staging(&self) -> alloc::vec::Vec<Staged> { (0..self.g.nblk()).map(|_| Staged::default()).collect() }
    /// The one pass of an encoded form: `step` writes block `b`'s metadata and packs it into the `Staged` it is handed, then
    /// `lay`. A block's pack goes at the prefix sum of every earlier block's widths and patch counts, known only after every
    /// meta step, so staging it while its elements are at hand is what spares a second pass computing them again.
    pub fn staged(&mut self, cost: u32, below: usize, step: &(dyn Fn(*mut CEnc, usize, usize, usize, &mut [u8], &mut Staged) + Sync)) -> Option<()> {
        let mut st = self.staging();
        let sp = st.as_mut_ptr() as usize;
        // each block's `Staged` is that block's alone, as its metadata entries are
        self.each(true, cost, &|s, b, lo, nb, buf| step(s, b, lo, nb, buf, unsafe { &mut *(sp as *mut Staged).add(b) }));
        self.lay(&st, below)
    }
    /// The layout of a column whose blocks are staged in `st`, each copied to its place; `None`, and nothing laid out, where
    /// the size test fails (`over`, or a size at or past `below`).
    fn lay(&mut self, st: &[Staged], below: usize) -> Option<()> {
        if self.e.over != 0 || unsafe { qrs_coc_enc_plan(&mut self.e) } >= below { return None }
        unsafe { qrs_coc_enc_layout(&mut self.e) };
        let sp = st.as_ptr() as usize;
        self.each(false, crate::QLEAN_COST_COPY, &|s, b, _, _, _| unsafe { (*s).place(b, &*(sp as *const Staged).add(b)) });
        Some(())
    }
    /// `write` with no size test: the answer of a kernel whose form is decided.
    pub fn answer<P: Producer + ?Sized>(self, p: &P) -> lean::O { self.write(p, false).expect("qlean Sink: a write with no size test has an answer") }
    /// The `u1` Frame of Reference column of `n` booleans, Lean `Coc.encodeAt lgEnc 1 _ false` of their 0/1 bytes, a block
    /// at a time: `f(lo, hi, o)` sets in the zeroed `o` the bits of elements `lo .. hi` that hold. A mixed block's
    /// residuals are its bitmap at width 1; an all-0 or all-1 block is width 0 at base 0 or 1 and stores no residual.
    pub fn bools(mut self, cost: u32, f: &(dyn Fn(usize, usize, &mut [u8]) + Sync)) -> lean::O {
        assert!(self.e.width == 1, "qlean Sink::bools: a sink of {}-byte elements is not a u1 Frame of Reference", self.e.width);
        let blk = self.g.blk();
        self.staged(cost, usize::MAX, &|s, b, lo, nb, _, st| {
            let mut res = alloc::vec![0u8; blk / 8];
            f(lo, lo + nb, &mut res[..nb.div_ceil(8)]);
            if nb & 7 != 0 { res[nb >> 3] &= (1u8 << (nb & 7)) - 1 }
            let pc = res.iter().map(|x| x.count_ones() as usize).sum::<usize>();
            let mixed = pc != 0 && pc != nb;
            let m = unsafe { (*s).meta_blk(b) };
            (*m.base, *m.maxv, *m.bsum, *m.width, *m.nexc) = ((pc == nb) as i64, (pc != 0) as i64, pc as i64, mixed as u8, 0);
            if let Some(fr) = m.frm { *fr = 0 }
            *st = Staged { res: if mixed { res } else { alloc::vec::Vec::new() }, ..Staged::default() };
        }).expect("qlean Sink::bools: a write with no size test has an answer");
        self.finish()
    }
    /// The finished parts as the form's Lean answer, handed over: the writer's scratch freed, nothing left for `drop`.
    fn finish(mut self) -> lean::O {
        let e = &mut self.e;
        unsafe { coc_free(e.exc_heap.cast()) };
        let [m, b] = [&mut e.meta, &mut e.pack].map(|p| core::mem::replace(p, null_mut()));
        e.exc_heap = null_mut();
        let o = |p: *mut c_void| unsafe { lean::O::from_raw(p.cast()) };
        lean::ctor(if self.enc { crate::blocks::tag::FOR as u8 } else { 0 }, [o(m), o(b)], &[])
    }
    /// The sink answering the `Enc` object rather than its `(meta, pack)` parts.
    pub fn enc(mut self) -> Sink { self.enc = true; self }
}



#[cfg(test)]
mod sink_tests {
    use super::Sink;
    use crate::blocks::Blocks;
    use crate::lean::{self, Object};
    use crate::{coc, pod};
    // the Lean runtime's allocation entries, which `cargo test` does not link: `malloc`, and nothing is freed
    unsafe extern "C" { fn malloc(n: usize) -> *mut u8; }
    #[unsafe(no_mangle)] extern "C" fn lean_alloc_object(sz: usize) -> *mut Object { unsafe { malloc(sz).cast() } }
    #[unsafe(no_mangle)] extern "C" fn mi_malloc_small(sz: usize) -> *mut u8 { unsafe { malloc(sz) } }
    #[unsafe(no_mangle)] extern "C" fn lean_dec_ref_cold(_: *mut Object) {}
    #[unsafe(no_mangle)] extern "C" fn lean_inc_heartbeat() {}
    #[unsafe(no_mangle)] extern "C" fn lean_internal_panic_out_of_memory() -> ! { panic!("qlean sink_tests: out of memory") }
    fn pair(o: &lean::O) -> [alloc::vec::Vec<u8>; 2] { [0, 1].map(|i| o.borrow().field(i).bytes().to_vec()) }
    /// `x` with every 97th element far outside its block's range, so the writer leaves patches
    fn col(n: usize) -> alloc::vec::Vec<i64> { (0..n as i64).map(|i| if i % 97 == 5 { i * 1_000_003 } else { 1000 + (i * 7919) % 8000 }).collect() }
    // every producer of a column writes the bytes the dense encoder writes for its elements: a fill narrowed to 2, 4 and
    // 8 bytes, and an encoded column read back as a `Blocks` source
    #[test] fn producers_write_what_the_dense_encoder_writes() {
        for n in [0usize, 1, 1000, 2500] {
            let x = col(n);
            let dense = |v: &[i64], w: usize| {
                let b: alloc::vec::Vec<u8> = v.iter().flat_map(|e| e.to_le_bytes()[..w].to_vec()).collect();
                pair(&Sink::new(n, w).answer(&Blocks::dense(&b, w)))
            };
            let e = Sink::new(n, 8).answer(&Blocks::dense(pod::bytes(&x), 8));
            let [m, p] = pair(&e);
            let c = coc::view(&m, &p, n).unwrap_or_else(|e| panic!("sink_tests: the sink's own column does not view: {e}"));
            for w in [2, 4, 8] {
                let fill = |buf: &mut [i64], i0: usize| buf.copy_from_slice(&x[i0..i0 + buf.len()]);
                assert_eq!(pair(&Sink::new(n, w).answer(&fill)), dense(&x, w), "fill at width {w}, n {n}");
            }
            assert_eq!(pair(&Sink::new(n, 8).answer(&Blocks::from(c))), [m.clone(), p.clone()], "transcode, n {n}");
        }
    }
    // the size test answers exactly where the full encoding is not below the dense bytes
    #[test] fn shrinks() {
        let n = 3000;
        let wide: alloc::vec::Vec<i64> = (0..n as i64).map(|i| i.wrapping_mul(0x1E37_79B9_7F4A_7C15)).collect();
        assert!(Sink::new(n, 8).write(&Blocks::dense(pod::bytes(&wide), 8), true).is_none());
        let x = col(n);
        let s = Sink::new(n, 8).write(&Blocks::dense(pod::bytes(&x), 8), true).expect("sink_tests: a narrow column shrinks");
        assert_eq!(pair(&s), pair(&Sink::new(n, 8).answer(&Blocks::dense(pod::bytes(&x), 8))));
    }
    // `bools` against its rule: a mixed block width 1 with the bitmap as residuals, a uniform block width 0 at base 0 or 1
    // and no residual, the elements decoding back; uniform runs crossing block edges, a short last block, no element
    #[test] fn bools_is_u1_for() {
        for n in [0usize, 5, 1024, 1025, 3000, 5000] {
            let pats: [&(dyn Fn(usize) -> bool + Sync); 4] = [&|_| false, &|_| true, &|i| i % 3 == 0, &|i| (i / 1500) % 2 == 1 || i == 2100];
            for (k, p) in pats.iter().enumerate() {
                let o = Sink::new(n, 1).bools(crate::QLEAN_COST_COPY, &|lo, hi, out| for i in lo..hi { if p(i) { out[(i - lo) >> 3] |= 1 << (i & 7) } });
                let (mv, pv) = (o.borrow().field(0).bytes().to_vec(), o.borrow().field(1).bytes().to_vec());
                let c = crate::coc::view(&mv, &pv, n).unwrap_or_else(|e| panic!("n {n} pattern {k}: {e}"));
                let s = Blocks::from(c);
                let mut res = 0;
                for (b, lo, nb) in s.walk() {
                    let pc = (lo..lo + nb).filter(|&i| p(i)).count();
                    let mixed = pc != 0 && pc != nb;
                    assert_eq!((c.meta.width[b], c.meta.base[b], c.meta.maxv[b], c.meta.bsum[b]), (mixed as u8, (pc == nb) as i64, (pc != 0) as i64, pc as i64), "n {n} pattern {k} block {b}");
                    let mut x = alloc::vec![0u8; nb];
                    s.load(b, nb, &mut x);
                    assert!(x.iter().enumerate().all(|(j, &v)| v == p(lo + j) as u8), "n {n} pattern {k} block {b}");
                    res += mixed as usize * s.blk() / 8;
                }
                assert_eq!(pv.len(), res, "n {n} pattern {k}: the pack is the mixed blocks' bitmaps alone");
            }
        }
    }
}
