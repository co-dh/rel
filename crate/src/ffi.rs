//! The `#[repr(C)]` column and encoder structs the block encoder and the pool workers share, and the helpers the
//! `ffi/*.rs` exports call. No symbol leaves the object from here: the Lean externs are in `ffi/*.rs`.
use core::alloc::Layout;
use core::ffi::{c_int, c_void};
use core::ptr::null_mut;
use core::slice;
use core::sync::atomic::{AtomicI32, AtomicUsize};


use crate::{c, lean};
use crate::coc::{self, Coc};


use crate::layout::Tail;

use crate::DEFAULT_LG;
use crate::alp::Cocf;

use crate::enc::{EncMeta, EncPack, Producer};
use crate::blocks::{Blocks, Grid};
use crate::sym::{self, Syms};
use crate::{enc, ew, structural};

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
    /// The only place raw `coc` pointers become slices. Safety: every pointer is null or valid for the length
    /// coc.rs documents, for `'a`. Inlined so a caller that reads one field (`qrs_coc_block_start`, called per block)
    /// builds only that slice, not the whole 208-byte view out of line.
    #[inline(always)]
    pub unsafe fn view<'a>(&self) -> Coc<'a> {
        let m = self.mblk;
        let meta = coc::Meta {
            base: unsafe { sl(self.base, m) }, maxv: unsafe { sl(self.maxv, m) }, off: unsafe { sl(self.off, m) },
            bsum: unsafe { sl(self.bsum, m) }, width: unsafe { sl(self.width, m) },
            // a null slot is "no sums stored", which coc.rs spells 0
            sumnul: if self.sumnul.is_null() { 0 } else { unsafe { *self.sumnul } },
            sumn: if self.sumn.is_null() { 0 } else { unsafe { *self.sumn } },
            n: self.n, nblk: self.nblk, mblk: m, lg: self.lg(),
        };
        let exc = if self.exc_off.is_null() { None } else {
            Some(coc::Exc { off: unsafe { sl(self.exc_off, m + 1) }, pos: unsafe { sl(self.exc_pos, self.nexc) },
                            // a C view is built per block (`qrs_coc_block_start`), so its order is not scanned; `get` scans
                            asc: false,
                            raw: unsafe { sl(self.exc_raw, self.nexc * self.exc_esz) }, esz: self.exc_esz })
        };
        let fdelta = if self.fdelta.is_null() { None } else { Some(unsafe { sl(self.fdelta.cast_const(), m) }) };
        Coc { meta, pack: unsafe { sl(self.pack.cast_const(), self.packbytes) }, exc, fdelta }
    }
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

/// The ALP column, laid out as C's `cocf`.
#[repr(C)]
pub struct CCocf {
    pub c: CCoc, pub exp: *mut i8, pub exc_off: *mut u32, pub exc_pos: *mut u16, pub exc_raw: *mut c_void,
    pub nexc: usize, pub f32: c_int,
}
impl CCocf {
    /// Safety: as `CCoc::view`, and `exp`/`exc_off` hold `nblk`/`nblk + 1`, `exc_pos`/`exc_raw` `nexc` elements.
    pub unsafe fn view<'a>(&self) -> Cocf<'a> {
        let (nb, esz) = (self.c.mblk, if self.f32 != 0 { 4 } else { 8 });
        Cocf { c: unsafe { self.c.view() }, exp: unsafe { sl(self.exp, nb) }, exc_off: unsafe { sl(self.exc_off, nb + 1) },
               exc_pos: unsafe { sl(self.exc_pos, self.nexc) },
               exc_raw: unsafe { sl(self.exc_raw.cast::<u8>(), self.nexc * esz) }, f32: self.f32 != 0 }
    }
}
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
    pub src: *const CSrc, pub n: usize, pub width: usize, pub alp: c_int,
    pub blk: Option<unsafe extern "C" fn(*mut c_void, usize, *const c_void, usize)>,
    pub c: CCoc, pub meta: *mut c_void, pub pack: *mut c_void, pub blob: *mut c_void,
    pub exp: *mut i8, pub exc_off: *mut u32, pub exc_heap: *mut u32, pub frm_heap: *mut u64, pub exc_pos: *mut u16,
    pub exc_raw: *mut u8, pub out: *mut u8, pub planned: c_int, pub frm: c_int,
    pub at: usize, pub nexc: usize, pub tail: usize, pub below: usize, pub lb: usize, pub over: c_int,
}
impl CEnc {
    /// Block `b`'s meta-pass view: the slots `coc_enc_open` set up (`c`'s four arrays, `frm_heap` as `c.fdelta`, `exc_off`,
    /// `exp`; the two a column does not keep are null).
    /// Safety: `self` is an open encoder, `b < c.mblk`, no other view of `b` alive.
    pub unsafe fn meta_blk<'a>(&mut self, b: usize) -> EncMeta<'a> {
        let c = &self.c;
        unsafe { EncMeta { b, base: &mut *c.base.add(b), maxv: &mut *c.maxv.add(b), width: &mut *c.width.add(b), bsum: &mut *c.bsum.add(b),
                           frm: if c.fdelta.is_null() { None } else { Some(&mut *c.fdelta.add(b)) }, nexc: &mut *self.exc_off.add(b + 1),
                           exp: if self.exp.is_null() { None } else { Some(&mut *self.exp.add(b)) },
                           patch: (self.n as u64) < 1 << 32 } }
    }
    /// Block `b`'s pack view after its meta step (`exc_off[b + 1]` still the block's count), its residuals at `res`, its `ne`
    /// patches at `pos` and `raw`: the `nb` elements' `ceil(nb * width / 8)` residual bytes, or with `whole` the full
    /// `blk * width / 8` (`move_pack` copies a whole block). Safety: as `meta_blk`, the three regions large enough.
    unsafe fn pack_at<'a>(&self, b: usize, nb: usize, whole: bool, res: *mut u8, pos: *mut u16, raw: *mut u8, ne: usize) -> EncPack<'a> {
        let c = &self.c;
        unsafe {
            let (base, w) = (*c.base.add(b), *c.width.add(b));
            EncPack { b, nb, base, frame: (base as u64).wrapping_add(if c.fdelta.is_null() { 0 } else { *c.fdelta.add(b) }), width: w,
                      exp: if self.exp.is_null() { 0 } else { *self.exp.add(b) },
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
pub const _: () = assert!(size_of::<CCocf>() == 192 && size_of::<CSrc>() == 40 && size_of::<CEnc>() == 320);
pub const _: () = assert!(size_of::<CSym>() == 16 && size_of::<CStage>() == 96);
impl CPass {
    /// Every pointer null, every count zero: what a stage is before the builder binds it.
    pub const EMPTY: CPass = CPass { a: core::ptr::null(), b: core::ptr::null(), c: core::ptr::null(), o: null_mut(), n: 0, at: 0,
                                     r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 };
}
impl CStage {
    /// A stage with no worker, for the arrays the chain builder fills in place.
    pub const EMPTY: CStage = CStage { f: None, p: CPass::EMPTY, asrc: 0, bsrc: 0, osrc: 0, abits: 0, bbits: 0, obits: 0, bytewise: 0 };
}
impl CCocf {
    /// A view over nothing, for the arrays the chain builder fills in place.
    pub const EMPTY: CCocf = CCocf {
        c: CCoc { base: null_mut(), maxv: null_mut(), width: null_mut(), off: null_mut(), bsum: null_mut(), sumnul: null_mut(),
                  sumn: null_mut(), pack: null_mut(), n: 0, nblk: 0, packbytes: 0, mblk: 0, exc_off: core::ptr::null(),
                  exc_pos: core::ptr::null(), exc_raw: core::ptr::null(), fdelta: null_mut(), nexc: 0, exc_esz: 0},
        exp: null_mut(), exc_off: null_mut(), exc_pos: null_mut(), exc_raw: null_mut(), nexc: 0, f32: 0 };
}

impl CCoc {
}


// A9: the ALP encoder's per-block steps that need nothing of A7. C reaches them through `coc *` and an exponent array
// the Rust side has no view of (`EncMeta` is A16's), so each is its own entry per element type.
/// The symbol column `blob` and `offs` (an `Array` of boxed starts) names, read where it lies: no copy of the starts, which a
/// per-element kernel would pay as a second pass; a bignum start is refused by `Syms::off` when it is read.
pub fn syms_of<'a>(blob: lean::B<'a>, offs: lean::B<'a>) -> Syms<'a> { Syms { blob: blob.bytes(), offs: offs.words() } }
/// K20: a dictionary or starts object as `sym::Heap` sees it, the lean.rs inlines under the names lean.h gives them.
#[derive(Clone, Copy, PartialEq)]
pub struct Obj(*mut lean::Object);
impl sym::Heap for Obj {
    fn rc(self) -> i32 { unsafe { (*self.0).rc } }
    fn inc(self) { unsafe { lean::inc(self.0) } }
    fn dec(self) { unsafe { lean::dec(self.0) } }
    fn cap(self) -> usize { unsafe { if lean::ptr_tag(self.0) == lean::TAG_ARRAY { lean::array_capacity(self.0) } else { lean::sarray_capacity(self.0) } } }
    fn len(self) -> usize { unsafe { lean::sarray_size(self.0) } }
    fn resize(self, offs: Self, bytes: usize, n: usize) { unsafe { lean::sarray_set_size(self.0, bytes); lean::array_set_size(offs.0, n) } }
    fn alloc(bytes: usize, cap: usize, n: usize, ncap: usize) -> (Self, Self) {
        (Obj(lean::alloc_sarray(1, bytes, cap)), Obj(lean::alloc_array(n, ncap)))
    }
    fn put_bytes(self, at: usize, src: &[u8]) { unsafe { core::ptr::copy(src.as_ptr(), lean::sarray_cptr(self.0).add(at), src.len()) } }
    fn put_starts(self, at: usize, it: impl Iterator<Item = usize>) {
        let p = unsafe { lean::array_cptr(self.0).add(at) };
        for (k, v) in it.enumerate() { unsafe { *p.add(k) = lean::box_(v) } }
    }
}
/// The one cache of kept dictionary hashes. Safety: `SD_LOCK` is held across every call that reaches it.
pub struct Kept(core::cell::UnsafeCell<sym::Cache<Obj>>);
unsafe impl Sync for Kept {}
pub static KEPT: Kept = Kept(core::cell::UnsafeCell::new(sym::Cache::new()));
/// `dict`/`offs` as a part: the bytes and the boxed starts, in place.
pub fn part<'a>(dict: lean::B<'a>, offs: lean::B<'a>) -> sym::Part<'a, Obj> {
    sym::Part { dict: Obj(raw(dict)), offs: Obj(raw(offs)), syms: syms_of(dict, offs) }
}
/// The kept hash of the dictionary `dict`/`offs` at its own count, when the cache holds one: `f` gets its probe, the least id
/// holding the symbol bytes it is given and the symbol count where none does, with `SD_LOCK` held (the lock `sd_concat` takes
/// too); `None`, lock released, where nothing is kept. A lookup does not build one: a scan of `d` entries is a fraction of the
/// hashing.
pub fn sd_kept<R>(dict: lean::B, offs: lean::B, f: impl FnOnce(&dyn Fn(&[u8]) -> usize) -> R) -> Option<R> {
    let p = part(dict, offs);
    let d = p.syms.count();
    SD_LOCK.lock();
    // Safety: `SD_LOCK` is held
    let c = unsafe { &mut *KEPT.0.get() };
    let r = c.find(Obj(raw(dict)), d).map(|i| {
        let t = c.table(i).0.borrow();
        let v = structural::Symview { base: p.syms, d0: d, tb: &[], to: &[] };
        f(&|k| structural::symtab_find(&t.slot, t.mask, &v, d, k))
    });
    SD_LOCK.unlock();
    r
}
/// The lock of the kept dictionary hashes: held by `sd_kept` around its probes and by `sd_concat` around its one call into the cache.
pub static SD_LOCK: crate::pool::Lock = crate::pool::Lock::new();
/// The pointer of a borrowed object: `lean::B` is `repr(transparent)` over one non-null pointer.
pub fn raw(b: lean::B) -> *mut lean::Object {
    // Safety: same size and meaning, as `lean::B` is a pointer
    unsafe { core::mem::transmute(b) }
}
/// Part `i` of `Kernel.hashConcat`'s argument `ps`: `(n, (dict, (offs, ids)))`, `n` a boxed `USize`.
pub struct SdPart<'a> { pub n: usize, pub dict: lean::B<'a>, pub offs: lean::B<'a>, pub ids: lean::B<'a> }
pub fn sd_part<'a>(ps: lean::B<'a>, i: usize) -> SdPart<'a> {
    let e = ps.array()[i];
    let r = e.field(1);
    let r2 = r.field(1);
    // Safety: field 0 is a boxed `USize`, a ctor holding the one word
    SdPart { n: unsafe { lean::unbox_usize(raw(e.field(0))) }, dict: r.field(0), offs: r2.field(0), ids: r2.field(1) }
}
/// structural.rs `take_ids0`: the first part's ids, owned: moved out of `ps` where every object on the way to them is held only
/// there (the slot is left `box(0)`), a reference of their own otherwise.
pub fn take_ids0(ps: &lean::O) -> lean::O {
    let b = ps.borrow();
    let (e, r) = (b.array()[0], b.array()[0].field(1));
    let r2 = r.field(1);
    // Safety: the four objects are borrowed from `ps`, which is alive; the move happens only where nothing else holds them
    unsafe {
        let ids = lean::ctor_get(raw(r2), 1);
        if lean::is_exclusive(raw(b)) && lean::is_exclusive(raw(e)) && lean::is_exclusive(raw(r)) && lean::is_exclusive(raw(r2)) {
            lean::ctor_set(raw(r2), 1, lean::box_(0))
        } else { lean::inc(ids) }
        lean::O::from_raw(ids)
    }
}
/// structural.rs `symdict_concat`'s dictionary half under the cache lock: the joined dictionary and starts (one reference each),
/// its symbol count, and for each part past the first the id every one of its symbols has in it (`None` where they are the
/// base's own); `None` when the base holds a symbol twice or the joined dictionary would not fit 32-bit ids.
pub fn sd_concat(parts: &[(lean::B, lean::B)]) -> Option<(lean::O, lean::O, usize, alloc::vec::Vec<Option<alloc::vec::Vec<usize>>>)> {
    let ps: alloc::vec::Vec<_> = parts.iter().map(|&(d, o)| part(d, o)).collect();
    SD_LOCK.lock();
    // Safety: `SD_LOCK` is held
    let r = unsafe { (&mut *KEPT.0.get()).concat(&ps) };
    SD_LOCK.unlock();
    // Safety: the cache's answer holds one reference to each, which the caller owns
    r.map(|d| unsafe { (lean::O::from_raw(d.dict.0), lean::O::from_raw(d.offs.0), d.cnt, d.maps) })
}
// ---- K10: the chain's stage table and builder (ew.rs `ew_stage_worker`, `ew_chain_build`) and the statistics fold ----
pub type Worker = unsafe extern "C" fn(usize, usize, *const CPass);
/// `p`'s operand at `lo` elements of `w` bytes, `n` of them, unless it is an atom (`one`), which is `w` bytes at its start.
pub unsafe fn tile<'a>(q: *const c_void, lo: usize, n: usize, w: usize, one: bool) -> &'a [u8] {
    unsafe { if one { sl(q.cast::<u8>(), w) } else { sl(q.cast::<u8>().add(lo * w), n * w) } }
}
/// ew.rs `ew_val_run`: the value verbs over one tile, an atom operand its one element; the runner is serial because a
/// chain tile is already one pool slice.
pub unsafe extern "C" fn qrs_ew_val_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, n) = (ew::ew_width(p.cls as u32), hi - lo);
        let (av, va) = (p.shape == ew::k::AV, p.shape == ew::k::VA);
        ew::val(c::serial, p.op, p.cls, p.shape, p.nul, tile(p.a, lo, n, w, av), tile(p.b, lo, n, w, va), n,
                sl_mut(p.o.cast::<u8>().add(lo * w), n * w))
    }
}
/// ew.rs `ew_cmp_stage`: `lo`, `hi` are output bytes, so eight elements each and no two slices share one.
pub unsafe extern "C" fn qrs_ew_cmp_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let w = ew::ew_width(p.cls as u32);
        let (e0, m) = (lo * 8, (hi * 8).min(p.n) - lo * 8);
        let (av, va) = (p.shape == ew::k::AV, p.shape == ew::k::VA);
        ew::cmp(c::serial, p.op, p.cls, p.shape, tile(p.a, e0, m, w, av), tile(p.b, e0, m, w, va), m,
                sl_mut(p.o.cast::<u8>().add(lo), m.div_ceil(8)))
    }
}
/// ew.rs `ew_mon_stage`.
pub unsafe extern "C" fn qrs_ew_mon_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, n) = (ew::ew_width(p.cls as u32), hi - lo);
        ew::mon_lane(p.op, p.cls, p.nul, tile(p.a, lo, n, w, false), sl_mut(p.o.cast::<u8>().add(lo * w), n * w))
    }
}
/// ew.rs `ew_floor_stage`: `n` longs out.
pub unsafe extern "C" fn qrs_ew_floor_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, n) = (ew::ew_width(p.cls as u32), hi - lo);
        ew::floor_lane(p.cls, tile(p.a, lo, n, w, false), sl_mut(p.o.cast::<u8>().add(lo * 8), n * 8))
    }
}
/// ew.rs `ew_bit_stage`: `lo`, `hi` are output bytes, so eight bits each; an atom operand is its one byte.
pub unsafe extern "C" fn qrs_ew_bit_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let m = hi - lo;
        ew::bit(c::serial, p.op, p.shape, tile(p.a, lo, m, 1, p.shape == ew::k::AV), tile(p.b, lo, m, 1, p.shape == ew::k::VA), m * 8,
                sl_mut(p.o.cast::<u8>().add(lo), m))
    }
}
/// ew.rs `ew_cast_stage`: the two classes travel as `cls` and `shape`.
pub unsafe extern "C" fn qrs_ew_cast_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (sw, dw, n) = (ew::ew_width(p.cls as u32), ew::ew_width(p.shape as u32), hi - lo);
        ew::cast_lane(p.cls, p.shape, p.nul, tile(p.a, lo, n, sw, false), sl_mut(p.o.cast::<u8>().add(lo * dw), n * dw))
    }
}
/// ew.rs `ew_tick_stage`: `op` is the source unit's code times 16 plus the target's, `p.c` the target's null; the
/// source is `int`, `double` or else `long`, the target `double`, `int` or else `long`.
pub unsafe extern "C" fn qrs_ew_tick_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (sw, dw, n) = (if p.cls == ew::k::I32 { 4 } else { 8 }, if p.shape == ew::k::I32 { 4 } else { 8 }, hi - lo);
        ew::tick(c::serial, p.op, p.cls, p.shape, p.nul, p.c as isize as i64, tile(p.a, lo, n, sw, false), n,
                 sl_mut(p.o.cast::<u8>().add(lo * dw), n * dw))
    }
}
/// ew.rs `ew_widen_stage`: elements `[lo, hi)` of a tile of `p.n`; a bit source is read from the tile's own bit 0.
pub unsafe extern "C" fn qrs_ew_widen_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let xb = if p.cls == ew::k::BITS { p.n.div_ceil(8) } else { p.n * ew::ew_width(p.cls as u32) };
        ew::widen_stage(p.cls, p.shape, p.nul, p.c as isize as i64, sl(p.a.cast::<u8>(), xb), lo, hi,
                        sl_mut(p.o.cast::<u8>(), p.n * ew::ew_width(p.shape as u32)))
    }
}
/// ew.rs `ew_decode_run`: `Coc.decode` over one tile, the block addressed by its number (`p.at`).
pub unsafe extern "C" fn qrs_ew_decode_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, cnt) = (ew::ew_width(p.cls as u32), hi - lo);
        crate::blocks::Blocks::from((*p.a.cast::<CCoc>()).view()).load_w(p.at >> (*p.a.cast::<CCoc>()).lg(), cnt, w, sl_mut(p.o.cast::<u8>(), cnt * w));
    }
}
/// ew.rs `ew_alp_run`: `Coc.alpDecode` over one tile, the patches the block names applied.
pub unsafe extern "C" fn qrs_ew_alp_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let (p, cnt) = (&*p, hi - lo);
        let f = &*p.a.cast::<CCocf>();
        let w = if f.f32 != 0 { 4 } else { 8 };
        crate::blocks::Blocks::from(f.view()).load_w(p.at >> f.c.lg(), cnt, w, sl_mut(p.o.cast::<u8>(), cnt * w));
    }
}
/// ew.rs `ew_ids_run`: an interned column's ids read where they lie at any lane and written at `cls`.
pub unsafe extern "C" fn qrs_ew_ids_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let w = p.shape as u32;
        ew::ids_stage(p.cls, w, sl(p.a.cast::<u8>(), ew::ids_len(p.n, w)), lo, hi, sl_mut(p.o.cast::<u8>(), p.n * ew::ew_width(p.cls as u32)))
    }
}
/// ew.rs `ew_pack_run`: `qrs_ew_ids_stage`'s inverse; below a byte `lo..hi` are output bytes.
pub unsafe extern "C" fn qrs_ew_pack_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let w = p.shape as u32;
        ew::pack_stage(p.cls, w, sl(p.a.cast::<u8>(), p.n * ew::ew_width(p.cls as u32)), p.n, lo, hi, sl_mut(p.o.cast::<u8>(), ew::ids_len(p.n, w)))
    }
}
/// ew.rs `ew_encmeta_run` and `ew_encpack_run` in one: the writer's Frame of Reference steps over the tile (one block) the
/// chain just computed, `p.o` the `CEnc` and `p.b` its `[Staged]`: the block's metadata, and its pack staged, as `Sink::staged`.
pub unsafe extern "C" fn qrs_ew_enc_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let (s, nb) = ((*p).o.cast::<CEnc>(), hi - lo);
        let (b, w) = ((*p).at >> (*s).c.lg(), (*s).width);
        let x = sl((*p).a.cast::<u8>(), nb * w);
        enc::for_meta(&mut (*s).meta_blk(b), x, w, nb);
        enc::for_pack(&mut (*s).stage(b, nb, &mut *(*p).b.cast::<Staged>().cast_mut().add(b))(false), x, w)
    }
}
/// ew.rs `ew_stage_worker`: the worker of `engine`, chosen once a stage and never per element.
pub fn stage_worker(engine: u32) -> Worker {
    use ew::eng::*;
    match engine {
        ENC => qrs_ew_enc_stage, VAL => qrs_ew_val_stage, CMP => qrs_ew_cmp_stage, MON => qrs_ew_mon_stage,
        WIDEN => qrs_ew_widen_stage, BIT => qrs_ew_bit_stage, FLOOR => qrs_ew_floor_stage, CAST => qrs_ew_cast_stage, DECODE => qrs_ew_decode_stage,
        TICK => qrs_ew_tick_stage, IDS => qrs_ew_ids_stage, PACK => qrs_ew_pack_stage, _ => qrs_ew_alp_stage,
    }
}

impl CCoc {
    /// The `coc` that `coc_meta_view` then `coc_attach` build over metadata `m` (`33 * mblk + 24` bytes) and a pack: the
    /// Rust twins' slices (`Meta::new`, `Coc::attach`) as the raw pointers C reads.
    pub(crate) fn of(c: &Coc, m: *mut u8) -> CCoc {
        let (me, nb) = (&c.meta, c.meta.mblk);
        let (eo, ep, er, esz) = c.exc.map_or((core::ptr::null(), core::ptr::null(), core::ptr::null(), 0), |e| (e.off.as_ptr(), e.pos.as_ptr(), e.raw.as_ptr(), e.esz));
        CCoc {
            base: me.base.as_ptr().cast_mut(), maxv: me.maxv.as_ptr().cast_mut(), width: me.width.as_ptr().cast_mut(),
            off: me.off.as_ptr().cast_mut(), bsum: me.bsum.as_ptr().cast_mut(),
            sumnul: m.wrapping_add(32 * nb).cast(), sumn: m.wrapping_add(32 * nb + 8).cast(),
            pack: c.pack.as_ptr().cast_mut(), n: me.n, nblk: me.nblk, packbytes: c.pack.len(), mblk: nb,
            exc_off: eo, exc_pos: ep, exc_raw: er, fdelta: c.fdelta.map_or(null_mut(), |f| f.as_ptr().cast_mut()),
            nexc: c.exc.map_or(0, |e| e.pos.len()), exc_esz: esz,
        }
    }
}

/// ew.rs `qlean_ew_chain_enc`: `Coc.encode w (Ew.chain prog inputs n)`, the Frame-of-Reference encoder over the chain's
/// answer. Below `qlean_worth_fusing` (the answer's bytes in L3) the chain runs once into a dense buffer that the `Sink`
/// reads; above it the chain is the sink's source, so the dense answer is never built: stage `k` is the sink's meta step,
/// which stages each block's pack as `Sink::staged` does, so the chain runs once here too.
pub fn chain_enc<'a>(prog: &[u8], input: &impl Fn(u8) -> &'a [u8], n: usize, width: usize) -> lean::O {
    let k = ew::stages(prog);
    let mut st = [const { CStage::EMPTY }; ew::SLOTS + 1];
    let mut views = [const { CCocf::EMPTY }; ew::SLOTS];
    let (mut cost, wide) = ew::chain_build(prog, k, input, n, &mut st, &mut views);
    let cls = ew::enc_cls(width, st[k - 1].obits as usize);
    if n * width < 33554432 {
        let mut dense = lean::SArr::new(1, n * width);
        st[k - 1].p.o = dense.bytes_mut().as_mut_ptr().cast();
        st[k - 1].osrc = ew::COLUMN;
        if n != 0 { c::run_chain(c::pool(), &st[..k], n, cost, wide); }
        return Sink::new(n, width, Form::For).answer(&Blocks::dense(dense.bytes_mut(), width));
    }
    let mut s = Sink::new(n, width, Form::For);
    let mut sv = s.staging();
    ew::enc_stage(&mut st, k, cls, (&raw mut s.e).cast(), sv.as_mut_ptr().cast(), &mut cost);
    if n != 0 { c::run_chain(c::pool(), &st[..=k], n, cost, wide); }
    s.lay(&sv, usize::MAX).expect("qlean_ew_chain_enc: a write with no size test is laid out");
    s.finish()
}


// ---- K24: coc.rs, 764-816, the one writer of an answer column: `Sink` (coc plan §3) ----
// A sink writes its column a block of its grid at a time on the pool, in the form it was opened in. Its blocks come from
// an `enc::Producer` (a `Blocks` source, a kernel's fill, whole blocks it `take`s) or from a step that writes the block
// itself (`each`). Allocation of the scratch aborts like coc.rs's `coc_alloc`.

/// A `Sink`'s form: Frame of Reference, ALP, or ids at `lw` bits (a bit column is `Ids(1)`, decision B).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Form { For, Alp, Ids(u32) }
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
pub unsafe extern "C" fn qrs_coc_enc_open(s: *mut CEnc, n: usize, width: usize, alp: c_int) {
    unsafe {
        let (nblk, msz) = (n.div_ceil(1 << DEFAULT_LG), 33 * n.div_ceil(1 << DEFAULT_LG) + 24);
        core::ptr::write_bytes(s, 0, 1);
        (*s).n = n;
        (*s).width = width;
        (*s).alp = alp;
        let meta = lean::alloc_sarray(1, msz, msz);
        // the trailer's block size, which every reader of this metadata (the encoder's own view first) takes its grid from
        lean::sarray_cptr(meta).add(32 * nblk + 16).cast::<u64>().write(DEFAULT_LG as u64);
        (*s).meta = meta.cast();
        (*s).c = meta_view(lean::sarray_cptr(meta), msz, n);
        if alp != 0 { (*s).exp = coc_alloc(nblk).cast() } else { (*s).frm_heap = coc_alloc(nblk * 8).cast(); (*s).c.fdelta = (*s).frm_heap }
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
            (*s).nexc = crate::alp::alp_offsets(sl_mut((*s).exc_off, nblk + 1), nblk);
            let alp = (*s).alp != 0;
            (*s).frm = (!alp && sl((*s).frm_heap, nblk).iter().any(|&f| f != 0)) as c_int;
            // the ALP blob is a part of its own and Frame of Reference's patch list the pack's tail: `tail` is what follows the residuals
            (*s).tail = enc::tail_bytes(alp, (*s).nexc, (*s).frm != 0, width, nblk);
        }
        lean::sarray_size((*s).meta.cast()) + (*s).at + (*s).tail
    }
}
/// coc.rs `coc_enc_layout`: the trailer, then the pack with the patch list as its tail (or ALP's blob), the heap copies moved in.
pub unsafe extern "C" fn qrs_coc_enc_layout(s: *mut CEnc) {
    use crate::layout::exc_layout;
    unsafe {
        let (nblk, n, width, alp) = ((*s).c.nblk, (*s).n, (*s).width, (*s).alp != 0);
        // the trailer is the column's, so it is written here and not inside a block slice
        *(*s).c.sumnul = enc::coc_sumnul(width, alp);
        *(*s).c.sumn = n as u64;
        qrs_coc_enc_plan(s);
        let (at, nexc) = ((*s).at, (*s).nexc);
        let put = |t: *mut u8, tail: usize, w: u64| enc::exc_header(sl_mut(t, tail), nexc, w);
        if alp {
            let l = exc_layout(nblk, nexc, width, Tail::Exps).expect("qlean: the exception layout overflows");
            let blob = lean::alloc_sarray(1, l.size, l.size);
            (*s).blob = blob.cast();
            let a = lean::sarray_cptr(blob);
            put(a, l.size, (width == 4) as u64); // the alignment padding is written, not left undefined
            core::ptr::copy_nonoverlapping((*s).exc_off.cast::<u8>(), a.add(l.off), (nblk + 1) * 4);
            core::ptr::copy_nonoverlapping((*s).exp.cast::<u8>(), a.add(l.tail), nblk);
            coc_free((*s).exp.cast());
            coc_free((*s).exc_heap.cast());
            (*s).exc_heap = null_mut();
            (*s).exp = a.add(l.tail).cast();
            (*s).exc_off = a.add(l.off).cast();
            (*s).exc_pos = a.add(l.pos).cast();
            (*s).exc_raw = a.add(l.raw);
        }
        // Frame of Reference's patch list is the pack's tail, and there is none without an exception
        let frm = (*s).frm != 0;
        let l = if !alp && nexc != 0 { exc_layout(nblk, nexc, width, if frm { Tail::Frames } else { Tail::None }) } else { None };
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
        if (*s).alp != 0 && (*s).blob.is_null() { coc_free((*s).exp.cast()) }
        if !(*s).meta.is_null() { lean::dec((*s).meta.cast()) }
        if !(*s).pack.is_null() { lean::dec((*s).pack.cast()) }
        if !(*s).blob.is_null() { lean::dec((*s).blob.cast()) }
    }
}

/// The writer of one answer column (coc plan §3): its grid, its form, and the encoder state its passes fill. Dropped
/// unfinished (a size test failed), it frees what it allocated.
pub struct Sink { pub e: CEnc, g: Grid, form: Form, enc: bool }
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
    /// `n` elements of `width` bytes in `form`: coc.rs `coc_enc_open` for an encoded form; for ids the payload, its
    /// capacity whole 64-bit words, as a word kernel (`words`) writes them.
    pub fn new(n: usize, width: usize, form: Form) -> Sink {
        let mut s = Sink { e: unsafe { core::mem::zeroed() }, g: Grid { n, lg: DEFAULT_LG }, form, enc: false };
        match form {
            Form::Ids(lw) => {
                let sz = crate::ids::ids_bytes(n, lw);
                let mut a = lean::SArr::with_capacity(1, sz, sz.div_ceil(8) * 8);
                (s.e.n, s.e.width, s.e.out) = (n, width, a.capacity_mut().as_mut_ptr());
                s.e.pack = lean::O::from(a).into_raw().cast();
            }
            _ => unsafe { qrs_coc_enc_open(&mut s.e, n, width, (form == Form::Alp) as c_int) },
        }
        s
    }
    /// `step` over every block on the pool; `sized` makes it the sizing pass of the size test.
    pub fn each(&mut self, sized: bool, cost: u32, step: Step) {
        let job = Pass { step, g: self.g, sized: sized && self.e.below != 0 };
        let p = CPass { a: (&raw const job).cast(), b: core::ptr::null(), c: core::ptr::null(), o: (&raw mut self.e).cast(), n: self.g.n, at: 0,
                        r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 };
        unsafe { c::pool()(sink_run, self.g.nblk(), cost, self.e.width << self.g.lg, &p) };
    }
    /// The column `p` denotes, as the Lean answer of the form (`(meta, pack)`, `(meta, (pack, alp))`, the ids payload);
    /// with `shrinks`, `None` where the encoded form is not smaller than the `n * width` dense bytes it replaces
    /// (`Enc.shrinks`, `CLAUDE.md`'s "nothing is encoded that the encoding does not shrink").
    pub fn write<P: Producer + ?Sized>(mut self, p: &P, shrinks: bool) -> Option<lean::O> {
        let (w, n) = (self.e.width, self.g.n);
        if let Form::Ids(lw) = self.form {
            let out = self.e.out as usize;
            // a block is a multiple of 8 elements, so block `b` starts on a byte and its bytes are its own
            self.each(false, crate::QLEAN_COST_COPY, &|_, b, lo, nb, buf| {
                let o = unsafe { sl_mut((out as *mut u8).add(lo * lw as usize / 8), crate::ids::ids_bytes(nb, lw)) };
                o.fill(0);
                for (k, x) in p.block(b, lo, nb, w, buf).chunks_exact(w).enumerate() {
                    let mut v = [0u8; 8];
                    v[..w.min(8)].copy_from_slice(&x[..w.min(8)]);
                    crate::ids::id_put(o, lw, k, u64::from_le_bytes(v))
                }
            });
            return Some(self.finish());
        }
        let (alp, below) = (self.form == Form::Alp, if shrinks { n * w } else { usize::MAX });
        // what the residuals and exceptions may come to before the size test is already failed, the metadata being fixed
        let msz = unsafe { lean::sarray_size(self.e.meta.cast()) };
        if below != usize::MAX { if below <= msz { return None } self.e.below = below - msz }
        let cost = if alp { crate::QLEAN_COST_MATH } else { crate::QLEAN_COST_ARITH };
        self.staged(cost, below, &|s, b, lo, nb, buf, st| unsafe {
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
    /// The ids answer written whole by the word kernel `f`, which gets the payload's whole 64-bit words, any contents (the
    /// bits past the last id are its to set to 0): a comparison's bitmap.
    pub fn words(self, f: impl FnOnce(&mut [u64])) -> lean::O {
        let Form::Ids(lw) = self.form else { panic!("qlean Sink::words: a {:?} sink has no words", self.form) };
        f(unsafe { sl_mut(self.e.out.cast::<u64>(), crate::ids::ids_bytes(self.g.n, lw).div_ceil(8)) });
        self.finish()
    }
    /// The `u1` Frame of Reference column of `n` booleans, Lean `Coc.encodeAt lgEnc 1 _ false` of their 0/1 bytes, a block
    /// at a time: `f(lo, hi, o)` sets in the zeroed `o` the bits of elements `lo .. hi` that hold. A mixed block's
    /// residuals are its bitmap at width 1; an all-0 or all-1 block is width 0 at base 0 or 1 and stores no residual.
    pub fn bools(mut self, cost: u32, f: &(dyn Fn(usize, usize, &mut [u8]) + Sync)) -> lean::O {
        assert!(self.form == Form::For && self.e.width == 1, "qlean Sink::bools: a {:?} sink of {}-byte elements is not a u1 Frame of Reference", self.form, self.e.width);
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
        let [m, b, a] = [&mut e.meta, &mut e.pack, &mut e.blob].map(|p| core::mem::replace(p, null_mut()));
        (e.exc_heap, e.exp) = (null_mut(), null_mut());
        let o = |p: *mut c_void| unsafe { lean::O::from_raw(p.cast()) };
        match (self.form, self.enc) {
            (Form::For, false) => lean::ctor(0, [o(m), o(b)], &[]),
            (Form::Alp, false) => lean::ctor(0, [o(m), lean::ctor(0, [o(b), o(a)], &[])], &[]),
            (Form::Ids(_), false) => o(b),
            (Form::For, true) => lean::ctor(crate::blocks::tag::FOR as u8, [o(m), o(b)], &[]),
            (Form::Alp, true) => lean::ctor(crate::blocks::tag::ALP as u8, [o(m), o(b), o(a)], &[]),
            // a boolean column is a `u1` `foR` (`Sink::bools`), never ids at width 1
            (Form::Ids(lw), true) => panic!("qlean Sink: ids at {lw} bits are an `Enc` only with a dictionary (`enum`)"),
        }
    }
    /// The sink answering the `Enc` object of its form rather than the form's parts.
    pub fn enc(mut self) -> Sink { self.enc = true; self }
}

/// `Enc.encodeMin`: below it an answer stays dense.
pub const ENCODE_MIN: usize = 64;
/// `Kernel.ofRaw t n` at a fixed-width `t` of the elements `p` produces at `w` bytes, `Enc.answer`'s rule: from
/// `ENCODE_MIN` elements on in `form` (`t`'s encoding; `None` where `Column.encodes`/`alpEncodes` have none) where it
/// shrinks, else the dense payload, written a block at a time on the pool at `cost`.
pub fn of_raw<P: Producer + ?Sized>(n: usize, w: usize, form: Option<Form>, cost: u32, p: &P) -> lean::O {
    if let Some(o) = form.filter(|_| n >= ENCODE_MIN).and_then(|f| Sink::new(n, w, f).enc().write(p, true)) { return o }
    let (g, mut r) = (Grid { n, lg: DEFAULT_LG }, lean::SArr::new(1, n * w));
    c::run_map(c::pool(), r.bytes_mut(), g.nblk(), g.blk() * w, cost, g.blk() * w, &|b0, b1, o| {
        let mut buf = crate::pod::uninit::<i64>(2 << g.lg);
        for b in b0..b1 {
            let (lo, nb) = g.span(b);
            p.block_into(b, lo, nb, w, crate::pod::bytes_mut(&mut buf), &mut o[(lo - g.span(b0).0) * w..][..nb * w]);
        }
    });
    lean::ctor(0, [r.into()], &[])
}

/// `Producer::ints` of a producer whose `ints` answers each exception's bits by address (`structural::Ints`, `f`): the bits
/// copied to `raw`, each alive in a source's patch list or the producer's hole.
pub fn ints_at(f: impl FnOnce(Option<&mut structural::Ints>) -> i32, nb: usize, w: usize, d: &mut [i64], ee: &mut [i8], raw: Option<&mut [u8]>) -> Option<i32> {
    let mut ptrs = alloc::vec![core::ptr::null::<u8>(); nb];
    let e = f(Some(&mut structural::Ints { d: &mut d[..nb], ee: &mut ee[..nb], raw: raw.is_some().then(|| &mut ptrs[..nb]) }));
    if let (Some(raw), true) = (raw, e >= 0) {
        for i in (0..nb).filter(|&i| ee[i] < 0) { raw[i * w..(i + 1) * w].copy_from_slice(unsafe { sl(ptrs[i], w) }) }
    }
    Some(e)
}
/// structural.rs `take_first`: the array `a` back, and its element 0 as an owned reference -- moved out where `a` held the
/// only reference to it (the slot is left `box(0)`), a reference of its own otherwise -- so an append whose first part
/// nothing else holds can write that part in place.
pub fn take_first(a: lean::O) -> (lean::O, lean::O) {
    unsafe {
        let p = a.into_raw();
        let e = lean::array_get_core(p, 0);
        if lean::is_exclusive(p) { lean::array_set_core(p, 0, lean::box_(0)) } else { lean::inc(e) }
        (lean::O::from_raw(p), lean::O::from_raw(e))
    }
}
/// structural.rs `qlean_structural_concat`'s test for growing part 0 in place: `parts` and its element 0 each held by this
/// reference alone, answering that part's capacity. `parts` comes back.
pub fn concat_own(parts: lean::O) -> (lean::O, Option<usize>) {
    unsafe {
        let p = parts.into_raw();
        let cap = (lean::array_size(p) != 0 && lean::is_exclusive(p) && lean::is_exclusive(lean::array_get_core(p, 0)))
            .then(|| lean::sarray_capacity(lean::array_get_core(p, 0)));
        (lean::O::from_raw(p), cap)
    }
}
/// structural.rs `sarray_room`: the owned `ByteArray` `o` at `need` bytes, its first `min(size, need)` kept and the rest
/// unwritten: `o` itself where it holds the only reference and its capacity reaches, a copy otherwise. A copy of an
/// exclusive `o` that outgrew its capacity doubles it, so a loop of one-element appends copies a logarithmic number of
/// times; a shared `o` is copied at size. A mapped part's `rc` is 0 and is never exclusive.
pub fn sarray_room(o: lean::O, need: usize) -> lean::O {
    unsafe {
        let p = o.into_raw();
        let (sz, ex) = (lean::sarray_size(p), lean::is_exclusive(p));
        if ex && lean::sarray_capacity(p) >= need { let mut o = lean::O::from_raw(p); o.set_size(need); return o }
        let r = lean::alloc_sarray(1, need, if ex { 2 * need } else { need });
        core::ptr::copy_nonoverlapping(lean::sarray_cptr(p), lean::sarray_cptr(r), sz.min(need));
        lean::dec(p);
        lean::O::from_raw(r)
    }
}
/// K22: structural.rs `amend_index` past the width check, the answer's three Lean arrays allocated as the kernel asks for them:
/// `Res`, and, when `compact` and no index misses, `Dom` and `Rank` (`None` otherwise). The kernel writes into each while the
/// others are alive, so each is held here by its `SArr` and the slice handed out is of its own payload.
pub fn amend(n: usize, wi: usize, ranked: bool, compact: bool, idx: &[u8]) -> (lean::O, Option<lean::O>, Option<lean::O>) {
    let mut out: [Option<lean::SArr>; 3] = [None, None, None];
    structural::amend_index(c::pool(), n, wi, ranked, compact, idx, &mut |which, words| {
        let mut a = lean::SArr::new(1, words * 8);
        let p = a.bytes_mut().as_mut_ptr().cast::<i64>();
        out[which as usize] = Some(a);
        // Safety: `p` is the payload of the array just stored in `out`, `words` of 8-aligned `Int64`s, which `out` keeps alive
        // until the kernel returns and which nothing else names
        unsafe { sl_mut(p, words) }
    });
    let [dom, rank, res] = out;
    (res.expect("amend_index: the answer is allocated last").into(), dom.map(Into::into), rank.map(Into::into))
}
/// K23: `scatterFoR` (`a` is `None`) and `scatterALP` (`a` the exponents): `(meta, pack)` or `(meta, (pack, alp))`, the sink's
/// answer. The blocks come from `structural::Scatter`, not from a producer, so its step writes each block itself.
#[allow(clippy::too_many_arguments)]
pub fn encode_scatter(w: usize, m: &[u8], pk: &[u8], a: Option<&[u8]>, n: usize, ix: &[u8], vals: &[u8]) -> lean::O {
    let alp = a.is_some();
    let sc = structural::Scatter::new(c::pool(), w, m, pk, a, n, ix, vals);
    let mut s = Sink::new(n, w, if alp { Form::Alp } else { Form::For });
    s.staged(if alp { crate::QLEAN_COST_MATH } else { crate::QLEAN_COST_ARITH }, usize::MAX,
             &|e, b, _, nb, _, st| unsafe { sc.write(&mut (*e).meta_blk(b), (*e).stage(b, nb, st), b) })
        .expect("qlean scatter: a write with no size test is laid out");
    s.finish()
}
/// The stats stage's worker: its fold over the two tiles, `p.o` the `Stats` of the phase running.
pub unsafe extern "C" fn qrs_ew_stats_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let (p, n) = (&*p, hi - lo);
        (*p.o.cast::<ew::Stats>()).run(sl(p.a.cast::<f64>(), n), sl(p.b.cast::<f64>(), n), p.at)
    }
}

#[cfg(test)]
mod sink_tests {
    use super::{Form, Sink};
    use crate::blocks::Blocks;
    use crate::lean::{self, Object};
    use crate::{coc, cocops, ew, ids, pod};
    // the Lean runtime's allocation entries, which `cargo test` does not link: `malloc`, and nothing is freed
    unsafe extern "C" { fn malloc(n: usize) -> *mut u8; }
    #[unsafe(no_mangle)] extern "C" fn lean_alloc_object(sz: usize) -> *mut Object { unsafe { malloc(sz).cast() } }
    #[unsafe(no_mangle)] extern "C" fn mi_malloc_small(sz: usize) -> *mut u8 { unsafe { malloc(sz) } }
    #[unsafe(no_mangle)] extern "C" fn lean_dec_ref_cold(_: *mut Object) {}
    #[unsafe(no_mangle)] extern "C" fn lean_inc_heartbeat() {}
    #[unsafe(no_mangle)] extern "C" fn lean_internal_panic_out_of_memory() -> ! { panic!("qlean sink_tests: out of memory") }
    fn pair(o: &lean::O) -> [Vec<u8>; 2] { [0, 1].map(|i| o.borrow().field(i).bytes().to_vec()) }
    /// `x` with every 97th element far outside its block's range, so the writer leaves patches
    fn col(n: usize) -> Vec<i64> { (0..n as i64).map(|i| if i % 97 == 5 { i * 1_000_003 } else { 1000 + (i * 7919) % 8000 }).collect() }
    // every producer of a column writes the bytes the dense encoder writes for its elements: a fill (`coc_scale`'s,
    // `ew::mon_fill`), a fill narrowed to 2 and 4 bytes, and an encoded column read back as a `Blocks` source
    #[test] fn producers_write_what_the_dense_encoder_writes() {
        for n in [0usize, 1, 1000, 2500] {
            let x = col(n);
            let dense = |v: &[i64], w: usize| {
                let b: Vec<u8> = v.iter().flat_map(|e| e.to_le_bytes()[..w].to_vec()).collect();
                pair(&Sink::new(n, w, Form::For).answer(&Blocks::dense(&b, w)))
            };
            let e = Sink::new(n, 8, Form::For).answer(&Blocks::dense(pod::bytes(&x), 8));
            let [m, p] = pair(&e);
            let c = coc::view(&m, &p, n).unwrap_or_else(|e| panic!("sink_tests: the sink's own column does not view: {e}"));
            for w in [2, 4, 8] {
                let fill = |buf: &mut [i64], i0: usize| buf.copy_from_slice(&x[i0..i0 + buf.len()]);
                assert_eq!(pair(&Sink::new(n, w, Form::For).answer(&fill)), dense(&x, w), "fill at width {w}, n {n}");
            }
            assert_eq!(pair(&Sink::new(n, 8, Form::For).answer(&Blocks::from(c))), [m.clone(), p.clone()], "transcode, n {n}");
            let k3: Vec<i64> = x.iter().map(|v| v * 3).collect();
            assert_eq!(pair(&Sink::new(n, 8, Form::For).answer(&|buf: &mut [i64], i0: usize| cocops::scale_fill(&c, 3, i0, buf))), dense(&k3, 8), "scale, n {n}");
            let mut mon = alloc::vec![0u8; n * 8];
            ew::mon_lane(0, 3, i64::MIN, pod::bytes(&x), &mut mon);
            let map = ew::Map { src: Blocks::from(c), wi: 8, lane: |x: &[u8], o: &mut [u8]| ew::mon_lane(0, 3, i64::MIN, x, o) };
            assert_eq!(pair(&Sink::new(n, 8, Form::For).answer(&map)), pair(&Sink::new(n, 8, Form::For).answer(&Blocks::dense(&mon, 8))), "mon, n {n}");
        }
    }
    // the size test answers exactly where the full encoding is not below the dense bytes, and ALP restores its floats
    #[test] fn shrinks_and_alp() {
        let n = 3000;
        let wide: Vec<i64> = (0..n as i64).map(|i| i.wrapping_mul(0x1E37_79B9_7F4A_7C15)).collect();
        assert!(Sink::new(n, 8, Form::For).write(&Blocks::dense(pod::bytes(&wide), 8), true).is_none());
        let x = col(n);
        let s = Sink::new(n, 8, Form::For).write(&Blocks::dense(pod::bytes(&x), 8), true).expect("sink_tests: a narrow column shrinks");
        assert_eq!(pair(&s), pair(&Sink::new(n, 8, Form::For).answer(&Blocks::dense(pod::bytes(&x), 8))));
        let f: Vec<f64> = (0..n).map(|i| ((i * 7919) % 100000) as f64 / 100.0).collect();
        let a = Sink::new(n, 8, Form::Alp).answer(&Blocks::dense(pod::bytes(&f), 8));
        let (m, rest) = (a.borrow().field(0).bytes(), a.borrow().field(1));
        let cf = crate::alp::Cocf::view(m, rest.field(0).bytes(), rest.field(1).bytes(), n).expect("sink_tests: the sink's ALP column views");
        let mut got = alloc::vec![0u8; n * 8];
        crate::codec::alp_decode(crate::c::pool(), &cf, &mut got);
        assert_eq!(got, pod::bytes(&f));
    }
    // the ids form packs each element at `lw` bits as `id_put` does, a bit column being `Ids(1)`; the bits past the
    // last id are 0
    #[test] fn ids_form() {
        for (n, lw) in [(2500usize, 1u32), (2500, 4), (1030, 8), (7, 2)] {
            let x: Vec<u16> = (0..n).map(|i| ((i * 31 + i / 7) % (1 << lw)) as u16).collect();
            let mut want = alloc::vec![0u8; ids::ids_bytes(n, lw)];
            for (i, &v) in x.iter().enumerate() { ids::id_put(&mut want, lw, i, v as u64) }
            assert_eq!(Sink::new(n, 2, Form::Ids(lw)).answer(&Blocks::dense(pod::bytes(&x), 2)).borrow().bytes(), &want[..], "lw {lw}");
        }
    }
    // `bools` against its rule: a mixed block width 1 with the bitmap as residuals, a uniform block width 0 at base 0 or 1
    // and no residual, the elements decoding back; uniform runs crossing block edges, a short last block, no element
    #[test] fn bools_is_u1_for() {
        for n in [0usize, 5, 1024, 1025, 3000, 5000] {
            let pats: [&(dyn Fn(usize) -> bool + Sync); 4] = [&|_| false, &|_| true, &|i| i % 3 == 0, &|i| (i / 1500) % 2 == 1 || i == 2100];
            for (k, p) in pats.iter().enumerate() {
                let o = Sink::new(n, 1, Form::For).bools(crate::QLEAN_COST_COPY, &|lo, hi, out| for i in lo..hi { if p(i) { out[(i - lo) >> 3] |= 1 << (i & 7) } });
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
    /// `qlean_ew_cmp` at 1M longs against an atom, the bitmap (`ew::cmp`) against the `u1` column (`bools`), per input:
    /// `cargo test --release --features std --lib bools_bench -- --ignored --nocapture`, `QLEAN_THREADS=1 taskset -c 0`
    #[test] #[ignore] fn bools_bench() {
        let n = 1usize << 20;
        let ins: [(&str, alloc::vec::Vec<i64>); 3] = [("random", (0..n as i64).map(|i| i.wrapping_mul(0x9E3779B97F4A7C15u64 as i64) >> 1).collect()),
            ("sorted", (0..n as i64).collect()), ("constant", alloc::vec![7; n])];
        for (name, x) in &ins {
            let (a, b) = (pod::bytes(x), pod::bytes(&[0i64]));
            let best = |f: &dyn Fn() -> usize| (0..20).map(|_| { let t = std::time::Instant::now(); let s = f(); (t.elapsed(), s) }).min().expect("20 runs");
            let (tb, sb) = best(&|| { let mut o = alloc::vec![0u8; n.div_ceil(8)]; crate::ew::cmp(crate::c::pool(), 2, 3, 1, a, b, n, &mut o); o.len() });
            let (tf, sf) = best(&|| { let o = Sink::new(n, 1, Form::For).bools(crate::QLEAN_COST_ARITH, &|lo, hi, out| crate::ew::cmp_slice(2, 3, 1, a, b, n, lo / 8, hi.div_ceil(8), out));
                                       o.borrow().field(0).bytes().len() + o.borrow().field(1).bytes().len() });
            std::println!("{name}: bitmap {:.3} ms {sb} B, u1 FoR {:.3} ms {sf} B", tb.as_secs_f64() * 1e3, tf.as_secs_f64() * 1e3);
        }
    }
}
