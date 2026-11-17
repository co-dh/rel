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

use crate::enc::{EncMeta, EncPack, Moves};
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
    /// The block size exponent, read from the metadata trailer the `sumnul` slot points into (two words on); a column with
    /// no trailer slots is the writer's.
    #[inline(always)]
    pub fn lg(&self) -> u32 { if self.sumnul.is_null() { DEFAULT_LG } else { unsafe { *self.sumnul.add(2) as u32 } } }
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

const _: () = assert!(size_of::<CCoc>() == 144);
const _: () = assert!(size_of::<CPass>() == 72);






/// Safety: `p` is null or valid for `n` reads of `T` during `'a`.
unsafe fn sl<'a, T>(p: *const T, n: usize) -> &'a [T] {
    if p.is_null() || n == 0 { &[] } else { unsafe { slice::from_raw_parts(p, n) } }
}
/// Safety: `p` is null or valid for `n` writes of `T` during `'a`, and nothing else aliases it.
unsafe fn sl_mut<'a, T>(p: *mut T, n: usize) -> &'a mut [T] {
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
                           exp: if self.exp.is_null() { None } else { Some(&mut *self.exp.add(b)) } } }
    }
    /// Block `b`'s pack-pass view, after `coc_enc_layout`: residuals at `off[b]`, patches `exc_off[b]..exc_off[b + 1]`.
    /// The residual region is the `nb` elements' `ceil(nb * width / 8)` bytes, or with `whole` the full `blk * width / 8`
    /// (`move_pack` copies a whole block). Safety: as `meta_blk`.
    pub unsafe fn pack_blk<'a>(&mut self, b: usize, nb: usize, whole: bool) -> EncPack<'a> {
        let c = &self.c;
        unsafe {
            let (base, w, at) = (*c.base.add(b), *c.width.add(b), *self.exc_off.add(b) as usize);
            let ne = *self.exc_off.add(b + 1) as usize - at;
            EncPack { b, nb, base, frame: (base as u64).wrapping_add(if c.fdelta.is_null() { 0 } else { *c.fdelta.add(b) }), width: w,
                      exp: if self.exp.is_null() { 0 } else { *self.exp.add(b) },
                      res: sl_mut(c.pack.add(*c.off.add(b) as usize), (if whole { 1usize << c.lg() } else { nb } * w as usize).div_ceil(8)),
                      pos: sl_mut(self.exc_pos.add(at), ne), raw: sl_mut(self.exc_raw.add(at * self.width), ne * self.width) }
        }
    }
}
/// A symbol: its bytes and length.
#[repr(C)]
pub struct CSym { pub p: *const u8, pub len: usize }
/// One pass of a fused chain.
#[repr(C)]
pub struct CStage {
    pub f: Option<unsafe extern "C" fn(usize, usize, *const CPass)>, pub p: CPass, pub asrc: u8, pub bsrc: u8, pub osrc: u8,
    pub abits: u16, pub bbits: u16, pub obits: u16, pub bytewise: u8,
}
const _: () = assert!(size_of::<CCocf>() == 192 && size_of::<CSrc>() == 40 && size_of::<CEnc>() == 320);
const _: () = assert!(size_of::<CSym>() == 16 && size_of::<CStage>() == 96);
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


/// A16: coc.rs `coc_enc_for_meta`, C's `blk` step.
pub unsafe extern "C" fn qrs_enc_for_meta(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::for_meta(&mut (*s).meta_blk(b), sl(x, nb * w), w, nb) }
}
/// A16: coc.rs `coc_enc_for_pack`.
pub unsafe extern "C" fn qrs_enc_for_pack(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::for_pack(&mut (*s).pack_blk(b, nb, false), sl(x, nb * w), w) }
}
/// A16: coc.rs `src_copy`, a dense block of `bytes` copied to `out`.
pub unsafe extern "C" fn qrs_src_copy(out: *mut u8, x: *const u8, bytes: usize) { unsafe { enc::src_copy(sl_mut(out, bytes), sl(x, bytes)) } }
/// A16: coc.rs `src_bits`, block `b`'s `nb` bytes packed into the `nbytes`-byte bitmap `out`.
pub unsafe extern "C" fn qrs_src_bits(out: *mut u8, nbytes: usize, b: usize, x: *const u8, nb: usize) {
    // a block is a multiple of 8 elements, so block `b` starts on byte `b * blk / 8`; the slice is its own bytes only (disjoint across blocks)
    unsafe { let (o, n) = (b * ((1usize << DEFAULT_LG) / 8), nb.div_ceil(8)); assert!(o + n <= nbytes, "qlean src_bits: block {b} of {nb} bytes past the {nbytes}-byte bitmap"); enc::src_bits(sl_mut(out.add(o), n), sl(x, nb)) }
}
// A9: the ALP encoder's per-block steps that need nothing of A7. C reaches them through `coc *` and an exponent array
// the Rust side has no view of (`EncMeta` is A16's), so each is its own entry per element type.
/// The symbol column `blob` and `offs` (an `Array` of boxed starts) names, read where it lies: no copy of the starts, which a
/// per-element kernel would pay as a second pass. A boxed start is the object word itself; a bignum is an even word, which
/// `Syms::off` refuses when it is read. Lean has no `lean.rs` accessor for an array's words yet.
pub fn syms_of<'a>(blob: lean::B<'a>, offs: lean::B<'a>) -> Syms<'a> {
    let a = offs.array();
    // Safety: `lean::B` is `repr(transparent)` over one non-null pointer, so `a` is `a.len()` consecutive `usize` words
    Syms { blob: blob.bytes(), offs: unsafe { sl(a.as_ptr().cast::<usize>(), a.len()) } }
}
/// K20: a dictionary or starts object as `sym::Heap` sees it, the lean.rs inlines under the names lean.h gives them.
#[derive(Clone, Copy, PartialEq)]
struct Obj(*mut lean::Object);
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
struct Kept(core::cell::UnsafeCell<sym::Cache<Obj>>);
unsafe impl Sync for Kept {}
static KEPT: Kept = Kept(core::cell::UnsafeCell::new(sym::Cache::new()));
/// `dict`/`offs` as a part: the bytes and the boxed starts, in place.
unsafe fn part<'a>(dict: *mut lean::Object, offs: *mut lean::Object) -> sym::Part<'a, Obj> {
    unsafe {
        sym::Part { dict: Obj(dict), offs: Obj(offs),
                    syms: Syms { blob: sl(lean::sarray_cptr(dict), lean::sarray_size(dict)), offs: sl(lean::array_cptr(offs).cast(), lean::array_size(offs)) } }
    }
}
/// The kept hash of the dictionary `dict`/`offs` at its own count, when the cache holds one: `f` gets its probe, the least id
/// holding the symbol bytes it is given and the symbol count where none does, with `SD_LOCK` held (the lock `sd_concat` takes
/// too); `None`, lock released, where nothing is kept. A lookup does not build one: a scan of `d` entries is a fraction of the
/// hashing.
pub fn sd_kept<R>(dict: lean::B, offs: lean::B, f: impl FnOnce(&dyn Fn(&[u8]) -> usize) -> R) -> Option<R> {
    // Safety: the objects are borrowed for the call and the starts are boxed words, as `part` reads them
    let p = unsafe { part(raw(dict), raw(offs)) };
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
static SD_LOCK: crate::pool::Lock = crate::pool::Lock::new();
/// The pointer of a borrowed object: `lean::B` is `repr(transparent)` over one non-null pointer.
fn raw(b: lean::B) -> *mut lean::Object {
    // Safety: same size and meaning, as `syms_of` relies on for an array's elements
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
    // Safety: each part's objects are borrowed for the call and the starts are boxed words, as `part` reads them
    let ps: alloc::vec::Vec<_> = parts.iter().map(|&(d, o)| unsafe { part(raw(d), raw(o)) }).collect();
    SD_LOCK.lock();
    // Safety: `SD_LOCK` is held
    let r = unsafe { (&mut *KEPT.0.get()).concat(&ps) };
    SD_LOCK.unlock();
    // Safety: the cache's answer holds one reference to each, which the caller owns
    r.map(|d| unsafe { (lean::O::from_raw(d.dict.0), lean::O::from_raw(d.offs.0), d.cnt, d.maps) })
}
/// A fresh `Array` of `n` words that `f` writes in place, each already a boxed scalar (`at << 1 | 1`), as the kernels that
/// fill a table of starts write them.
pub fn array_boxed(n: usize, f: impl FnOnce(&mut [usize])) -> lean::O {
    let a = lean::alloc_array(n, n);
    // Safety: `a` is an array of `n` words, uninitialised until `f` writes every one
    unsafe { f(sl_mut(lean::array_cptr(a).cast::<usize>(), n)); lean::O::from_raw(a) }
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
/// K23: `scatterFoR` (`a` is `None`) and `scatterALP` (`a` the exponents): `(meta, pack)` or `(meta, (pack, alp))`, the writer's
/// parts as the Lean declaration types them. The blocks come from `structural::Scatter`, not from a source, so `NoElts`
/// stands in for the element cursor `src_pass` hands each step.
#[allow(clippy::too_many_arguments)]
pub fn encode_scatter(w: usize, m: &[u8], pk: &[u8], a: Option<&[u8]>, n: usize, ix: &[u8], vals: &[u8]) -> lean::O {
    unsafe {
        let alp = a.is_some();
        let sc = structural::Scatter::new(c::pool(), w, m, pk, a, n, ix, vals);
        let mut e: CEnc = core::mem::zeroed();
        let s = &raw mut e;
        qrs_coc_enc_open(s, n, w, alp as c_int);
        src_pass(s, &NoElts, &|s, b, _, _| sc.meta(&mut (*s).meta_blk(b), b), true, if alp { crate::QLEAN_COST_MATH } else { crate::QLEAN_COST_ARITH });
        qrs_coc_enc_layout(s);
        src_pass(s, &NoElts, &|s, b, _, nb| sc.pack(&mut (*s).pack_blk(b, nb, sc.kept(b)), b), false, crate::QLEAN_COST_ARITH);
        if !alp { return lean::O::from_raw(qrs_coc_enc_pair(s).cast()) }
        coc_free((*s).exc_heap.cast());
        lean::O::from_raw(mk_pair((*s).meta, mk_pair((*s).pack, (*s).blob)).cast())
    }
}
/// K23: `encode_scatter` has no elements, only block numbers.
struct NoElts;
impl Source for NoElts {
    unsafe fn open(&self) -> Option<*mut c_void> { Some(null_mut()) }
    unsafe fn at(&self, _: *mut c_void, _: usize, _: usize) -> *const u8 { core::ptr::NonNull::dangling().as_ptr() }
    unsafe fn close(&self, _: *mut c_void) {}
    unsafe fn bad(&self) -> bool { false }
}
// ---- K10: the chain's stage table and builder (ew.rs `ew_stage_worker`, `ew_chain_build`) and the statistics fold ----
pub type Worker = unsafe extern "C" fn(usize, usize, *const CPass);
/// `p`'s operand at `lo` elements of `w` bytes, `n` of them, unless it is an atom (`one`), which is `w` bytes at its start.
unsafe fn tile<'a>(q: *const c_void, lo: usize, n: usize, w: usize, one: bool) -> &'a [u8] {
    unsafe { if one { sl(q.cast::<u8>(), w) } else { sl(q.cast::<u8>().add(lo * w), n * w) } }
}
/// ew.rs `ew_val_run`: the value verbs over one tile, an atom operand its one element; the runner is serial because a
/// chain tile is already one pool slice.
unsafe extern "C" fn qrs_ew_val_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, n) = (ew::ew_width(p.cls as u32), hi - lo);
        let (av, va) = (p.shape == ew::k::AV, p.shape == ew::k::VA);
        ew::val(c::serial, p.op, p.cls, p.shape, p.nul, tile(p.a, lo, n, w, av), tile(p.b, lo, n, w, va), n,
                sl_mut(p.o.cast::<u8>().add(lo * w), n * w))
    }
}
/// ew.rs `ew_cmp_stage`: `lo`, `hi` are output bytes, so eight elements each and no two slices share one.
unsafe extern "C" fn qrs_ew_cmp_stage(lo: usize, hi: usize, p: *const CPass) {
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
unsafe extern "C" fn qrs_ew_mon_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, n) = (ew::ew_width(p.cls as u32), hi - lo);
        ew::mon(c::serial, p.op, p.cls, p.nul, tile(p.a, lo, n, w, false), n, sl_mut(p.o.cast::<u8>().add(lo * w), n * w))
    }
}
/// ew.rs `ew_floor_stage`: `n` longs out.
unsafe extern "C" fn qrs_ew_floor_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, n) = (ew::ew_width(p.cls as u32), hi - lo);
        ew::floor(c::serial, p.cls, tile(p.a, lo, n, w, false), n, sl_mut(p.o.cast::<u8>().add(lo * 8), n * 8))
    }
}
/// ew.rs `ew_bit_stage`: `lo`, `hi` are output bytes, so eight bits each; an atom operand is its one byte.
unsafe extern "C" fn qrs_ew_bit_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let m = hi - lo;
        ew::bit(c::serial, p.op, p.shape, tile(p.a, lo, m, 1, p.shape == ew::k::AV), tile(p.b, lo, m, 1, p.shape == ew::k::VA), m * 8,
                sl_mut(p.o.cast::<u8>().add(lo), m))
    }
}
/// ew.rs `ew_cast_stage`: the two classes travel as `cls` and `shape`.
unsafe extern "C" fn qrs_ew_cast_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (sw, dw, n) = (ew::ew_width(p.cls as u32), ew::ew_width(p.shape as u32), hi - lo);
        ew::cast(c::serial, p.cls, p.shape, p.nul, tile(p.a, lo, n, sw, false), n, sl_mut(p.o.cast::<u8>().add(lo * dw), n * dw))
    }
}
/// ew.rs `ew_tick_stage`: `op` is the source unit's code times 16 plus the target's, `p.c` the target's null; the
/// source is `int`, `double` or else `long`, the target `double`, `int` or else `long`.
unsafe extern "C" fn qrs_ew_tick_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (sw, dw, n) = (if p.cls == ew::k::I32 { 4 } else { 8 }, if p.shape == ew::k::I32 { 4 } else { 8 }, hi - lo);
        ew::tick(c::serial, p.op, p.cls, p.shape, p.nul, p.c as isize as i64, tile(p.a, lo, n, sw, false), n,
                 sl_mut(p.o.cast::<u8>().add(lo * dw), n * dw))
    }
}
/// ew.rs `ew_widen_stage`: elements `[lo, hi)` of a tile of `p.n`; a bit source is read from the tile's own bit 0.
unsafe extern "C" fn qrs_ew_widen_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let xb = if p.cls == ew::k::BITS { p.n.div_ceil(8) } else { p.n * ew::ew_width(p.cls as u32) };
        ew::widen_stage(p.cls, p.shape, p.nul, p.c as isize as i64, sl(p.a.cast::<u8>(), xb), lo, hi,
                        sl_mut(p.o.cast::<u8>(), p.n * ew::ew_width(p.shape as u32)))
    }
}
/// ew.rs `ew_decode_run`: `Coc.decode` over one tile, the block addressed by its number (`p.at`).
unsafe extern "C" fn qrs_ew_decode_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, cnt) = (ew::ew_width(p.cls as u32), hi - lo);
        ew::decode_stage(&(*p.a.cast::<CCoc>()).view(), p.at >> (*p.a.cast::<CCoc>()).lg(), cnt, w, sl_mut(p.o.cast::<u8>(), cnt * w))
    }
}
/// ew.rs `ew_alp_run`: `Coc.alpDecode` over one tile, the patches the block names applied.
unsafe extern "C" fn qrs_ew_alp_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let (p, cnt) = (&*p, hi - lo);
        let f = &*p.a.cast::<CCocf>();
        f.view().load_blk(p.at >> f.c.lg(), cnt, sl_mut(p.o.cast::<u8>(), cnt * if f.f32 != 0 { 4 } else { 8 }))
    }
}
/// ew.rs `ew_ids_run`: an interned column's ids read where they lie at any lane and written at `cls`.
unsafe extern "C" fn qrs_ew_ids_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let w = p.shape as u32;
        ew::ids_stage(p.cls, w, sl(p.a.cast::<u8>(), ew::ids_len(p.n, w)), lo, hi, sl_mut(p.o.cast::<u8>(), p.n * ew::ew_width(p.cls as u32)))
    }
}
/// ew.rs `ew_pack_run`: `qrs_ew_ids_stage`'s inverse; below a byte `lo..hi` are output bytes.
unsafe extern "C" fn qrs_ew_pack_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let w = p.shape as u32;
        ew::pack_stage(p.cls, w, sl(p.a.cast::<u8>(), p.n * ew::ew_width(p.cls as u32)), p.n, lo, hi, sl_mut(p.o.cast::<u8>(), ew::ids_len(p.n, w)))
    }
}
/// ew.rs `ew_encmeta_run`: the writer's meta step over the tile the chain just computed (`p.o` the `coc_enc`).
unsafe extern "C" fn qrs_ew_encmeta_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe { qrs_enc_for_meta((*p).o.cast(), (*p).at >> (*(*p).o.cast::<CEnc>()).c.lg(), (*p).a.cast(), hi - lo) }
}
/// ew.rs `ew_encpack_run`: its pack step over the same tile.
unsafe extern "C" fn qrs_ew_encpack_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe { qrs_enc_for_pack((*p).o.cast(), (*p).at >> (*(*p).o.cast::<CEnc>()).c.lg(), (*p).a.cast(), hi - lo) }
}
/// ew.rs `ew_stage_worker`: the worker of `engine`, chosen once a stage and never per element.
pub fn stage_worker(engine: u32) -> Worker {
    use ew::eng::*;
    match engine {
        ENCMETA => qrs_ew_encmeta_stage, ENCPACK => qrs_ew_encpack_stage, VAL => qrs_ew_val_stage, CMP => qrs_ew_cmp_stage, MON => qrs_ew_mon_stage,
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
/// The stats stage's worker: its fold over the two tiles, `p.o` the `Stats` of the phase running.
pub(crate) unsafe extern "C" fn qrs_ew_stats_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let (p, n) = (&*p, hi - lo);
        (*p.o.cast::<ew::Stats>()).run(sl(p.a.cast::<f64>(), n), sl(p.b.cast::<f64>(), n), p.at)
    }
}

/// ew.rs `qlean_ew_chain_enc`: `Coc.encode w (Ew.chain prog inputs n)`, the Frame-of-Reference encoder over the chain's
/// answer. Below `qlean_worth_fusing` (the answer's bytes in L3) the chain runs once into a dense buffer; above it the chain
/// is the encoder's source and runs twice, the encoder's sizing pass and then its packing pass, so the dense answer is never
/// built. The encoder's meta step and pack step are stages `k` of the chain, writing through the `CEnc` `c`.
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
        let z = encode_dense(dense.bytes_mut(), width, false, usize::MAX).expect("qlean_ew_chain_enc: a dense buffer cannot fail");
        return z.into_pair();
    }
    let mut e: CEnc = unsafe { core::mem::zeroed() };
    let ep: *mut CEnc = &mut e;
    unsafe { qrs_coc_enc_open(ep, n, width, 0) };
    ew::enc_stage(&mut st, k, cls, ep.cast(), false, &mut cost);
    if n != 0 { c::run_chain(c::pool(), &st[..=k], n, cost, wide); }
    unsafe { qrs_coc_enc_layout(ep) };
    ew::enc_stage(&mut st, k, cls, ep.cast(), true, &mut cost);
    if n != 0 { c::run_chain(c::pool(), &st[..=k], n, cost, wide); }
    unsafe { lean::O::from_raw(qrs_coc_enc_pair(ep).cast()) }
}

#[cfg(test)]
mod tests {
    use crate::BLK;
    use super::*;
    // testdata/drv.c (deleted; in git history) encoded a 3000-element column with the C encoder at each element width and dumped the buffers
    // and what coc.rs's accessors answered (`col<esz>.txt`): the header, then `blk b frame nexc` and `exc j value`.
    struct Col { meta: Vec<u64>, pack: Vec<u64>, txt: &'static str }
    fn load(m: &[u8], p: &[u8], txt: &'static str) -> Col {
        let w = |b: &[u8]| { let mut v = vec![0u64; b.len().div_ceil(8)]; v.iter_mut().zip(b.chunks(8)).for_each(|(d, c)| { let mut t = [0u8; 8]; t[..c.len()].copy_from_slice(c); *d = u64::from_ne_bytes(t) }); v };
        Col { meta: w(m), pack: w(p), txt }
    }
    fn cols() -> [Col; 3] {
        [load(include_bytes!("../testdata/col8.meta"), include_bytes!("../testdata/col8.pack"), include_str!("../testdata/col8.txt")),
         load(include_bytes!("../testdata/col4.meta"), include_bytes!("../testdata/col4.pack"), include_str!("../testdata/col4.txt")),
         load(include_bytes!("../testdata/col2.meta"), include_bytes!("../testdata/col2.pack"), include_str!("../testdata/col2.txt"))]
    }
    fn head(c: &Col) -> Vec<i64> { c.txt.lines().next().unwrap().split_whitespace().skip(1).step_by(2).map(|x| x.parse().unwrap()).collect() }
    /// The CCoc coc_view/coc_attach would make: [n nblk mblk packbytes nexc esz exc_off exc_pos exc_raw fdelta]
    fn ccoc(c: &mut Col) -> CCoc {
        let h = head(c);
        let (n, mblk, pb) = (h[0] as usize, h[2] as usize, h[3] as usize);
        let m = c.meta.as_mut_ptr().cast::<u8>();
        let pk = c.pack.as_mut_ptr().cast::<u8>();
        let at = |o: i64| if o < 0 { core::ptr::null() } else { unsafe { pk.add(o as usize) } };
        unsafe { CCoc {
            base: m.cast(), maxv: m.add(8 * mblk).cast(), off: m.add(16 * mblk).cast(), bsum: m.add(24 * mblk).cast(),
            sumnul: m.add(32 * mblk).cast(), sumn: m.add(32 * mblk + 8).cast(), width: m.add(32 * mblk + 24),
            pack: pk, n, nblk: h[1] as usize, packbytes: pb, mblk,
            exc_off: at(h[6]).cast(), exc_pos: at(h[7]).cast(), exc_raw: at(h[8]), fdelta: at(h[9]).cast_mut().cast(),
            nexc: h[4] as usize, exc_esz: h[5] as usize,
        } }
    }
    #[test] fn view_reads_back_what_the_c_accessors_answered() {
        for mut c in cols() {
            let (cc, h) = (ccoc(&mut c), head(&c));
            let v = unsafe { cc.view() };
            assert_eq!((v.meta.base.len(), v.meta.maxv.len(), v.meta.off.len(), v.meta.bsum.len(), v.meta.width.len()),
                       (cc.mblk, cc.mblk, cc.mblk, cc.mblk, cc.mblk));
            let e = v.exc.unwrap();
            assert_eq!((e.off.len(), e.pos.len(), e.raw.len(), e.esz), (cc.mblk + 1, cc.nexc, cc.nexc * cc.exc_esz, cc.exc_esz));
            assert!(h[4] > 0, "the column must have patches");
            let mut seen = 0;
            for l in c.txt.lines().skip(1) {
                let f: Vec<&str> = l.split_whitespace().collect();
                let a: usize = f[1].parse().unwrap();
                match f[0] {
                    "blk" => { assert_eq!(v.frame(a), f[2].parse::<u64>().unwrap(), "frame {a}"); assert_eq!(v.blk_nexc(a), f[3].parse::<usize>().unwrap(), "nexc {a}"); }
                    _ => { assert_eq!(v.exc(a), f[2].parse::<i64>().unwrap(), "exc {a}"); seen += 1 }
                }
            }
            assert_eq!(seen, cc.nexc);
        }
    }
    // decode_blk against the C decoder (testdata/drv.c (deleted; in git history)'s col<esz>.dec), block by block, patches applied
    fn decodes_as_c<T: crate::pod::Lane + PartialEq + core::fmt::Debug>(mut c: Col, dec: &[u8]) {
        let cc = ccoc(&mut c);
        let v = unsafe { cc.view() };
        let e = size_of::<T>();
        let want: Vec<T> = dec.chunks_exact(e).map(|r| { let mut t = [0u8; 8]; t[..e].copy_from_slice(r); T::wrap(u64::from_le_bytes(t)) }).collect();
        let mut got = vec![T::wrap(0x5A); cc.n];
        for b in 0..cc.nblk {
            let lo = b * BLK; let nb = (cc.n - lo).min(BLK);
            v.decode_blk(b, nb, &mut got[lo..lo + nb]);
        }
        assert_eq!(got, want);
    }
    #[test] fn decode_blk_matches_the_c_decoder() {
        decodes_as_c::<i64>(load(include_bytes!("../testdata/col8.meta"), include_bytes!("../testdata/col8.pack"), include_str!("../testdata/col8.txt")), include_bytes!("../testdata/col8.dec"));
        decodes_as_c::<i32>(load(include_bytes!("../testdata/col4.meta"), include_bytes!("../testdata/col4.pack"), include_str!("../testdata/col4.txt")), include_bytes!("../testdata/col4.dec"));
        decodes_as_c::<i16>(load(include_bytes!("../testdata/col2.meta"), include_bytes!("../testdata/col2.pack"), include_str!("../testdata/col2.txt")), include_bytes!("../testdata/col2.dec"));
        decodes_as_c::<u8>(load(include_bytes!("../testdata/col1.meta"), include_bytes!("../testdata/col1.pack"), include_str!("../testdata/col1.txt")), include_bytes!("../testdata/col1.dec"));
    }
    #[test] fn null_patch_list_and_null_frames_are_none() {
        let mut c = load(include_bytes!("../testdata/col8.meta"), include_bytes!("../testdata/col8.pack"), include_str!("../testdata/col8.txt"));
        let mut cc = ccoc(&mut c);
        assert!(unsafe { cc.view() }.fdelta.is_some() || head(&c)[9] < 0);
        cc.fdelta = core::ptr::null_mut();
        assert!(unsafe { cc.view() }.fdelta.is_none());
        let v = unsafe { cc.view() };
        assert_eq!(v.frame(0), v.meta.base[0] as u64, "no fdelta is 0s");
        cc.exc_off = core::ptr::null();
        let v = unsafe { cc.view() };
        assert!(v.exc.is_none());
        assert_eq!(v.blk_nexc(0), 0);
        cc.sumnul = core::ptr::null_mut(); cc.sumn = core::ptr::null_mut();
        assert_eq!((unsafe { cc.view() }.meta.sumnul, unsafe { cc.view() }.meta.sumn), (0, 0));
    }
    // coc.rs's `coc_may_hold64` read off the raw pointers, as the C wrote it
    #[test] fn may_hold64_is_the_c_formula() {
        for mut c in cols() {
            let cc = ccoc(&mut c);
            let nb = cc.n.div_ceil(BLK);
            let sample: Vec<i64> = (0..nb).flat_map(|b| unsafe { [*cc.base.add(b), *cc.maxv.add(b), (*cc.base.add(b)).wrapping_sub(1), (*cc.maxv.add(b)).wrapping_add(1)] })
                .chain([0, 1, -1, i64::MAX, i64::MIN]).collect();
            for v in sample {
                for b0 in (0..nb).step_by(3) {
                    let k = (nb - b0).min(64).min(1 + b0 % 5);
                    let mut m = 0u64;
                    unsafe {
                        for j in 0..k { m |= (((*cc.base.add(b0 + j) <= v) & (v <= *cc.maxv.add(b0 + j))) as u64) << j }
                        let exc = cc.nexc != 0 && *cc.exc_off.add(b0 + k) != *cc.exc_off.add(b0);
                        if exc { for j in 0..k { if m >> j & 1 == 0 && crate::search::coc_exc_within(&cc.view(), b0 + j, v, v) { m |= 1 << j } } }
                        assert_eq!(crate::search::coc_may_hold64(&cc.view(), b0, k, v), m, "block {b0}+{k} for {v}");
                    }
                }
            }
        }
    }
    #[test] fn views_never_exceed_mblk() {
        let mut c = load(include_bytes!("../testdata/col8.meta"), include_bytes!("../testdata/col8.pack"), include_str!("../testdata/col8.txt"));
        let mut cc = ccoc(&mut c);
        cc.nblk = cc.mblk + 5; // a clamped view may hold fewer blocks, never more slices than the metadata has
        let v = unsafe { cc.view() };
        assert_eq!(v.meta.base.len(), cc.mblk);
        assert!(std::panic::catch_unwind(|| v.frame(cc.mblk)).is_err());
    }
}

// ---- K24: coc.rs, 764-816, the one writer of an encoded column ----
// A column's blocks come from a `Source` (a C `coc_src`, a dense buffer, or a producer's `fill` with the three optional
// callbacks that move whole blocks); a pass runs a per-block step over them on the pool, a slice at a time. Allocation of
// the writer's scratch aborts like coc.rs's `coc_alloc`, and its `free`s are the C callers' (`structural.rs` frees `exc_heap`).

/// coc.rs `coc_parts`: the writer's ByteArrays, null where the form has none.
#[repr(C)]
pub struct CParts { pub meta: *mut c_void, pub body: *mut c_void, pub alp: *mut c_void }
const SRC_DENSE: u32 = 0;
const SRC_BITS: u32 = 1;
const SRC_FOR: u32 = 2;
const SRC_ALP: u32 = 3;

/// Where one worker's blocks come from; the encoder's whole difference between a buffer, a file and a producer.
trait Source: Sync {
    /// A private cursor (null when the source needs none); `None` when it cannot open one, and the slice does nothing.
    unsafe fn open(&self) -> Option<*mut c_void>;
    /// The `len` bytes at byte `off` of the element region, good until `cur` is asked again; null stops the slice.
    unsafe fn at(&self, cur: *mut c_void, off: usize, len: usize) -> *const u8;
    unsafe fn close(&self, cur: *mut c_void);
    /// A failed read was recorded: the answer is no column.
    unsafe fn bad(&self) -> bool;
}
/// B4: a `kxzipped` or plain column file as a `Source`; each worker's cursor is a boxed `zip::Cursor`.
struct ZSrc<'a>(&'a crate::zip::File);
impl Source for ZSrc<'_> {
    unsafe fn open(&self) -> Option<*mut c_void> { crate::zip::Cursor::new(self.0).map(|c| alloc::boxed::Box::into_raw(alloc::boxed::Box::new(c)).cast()) }
    unsafe fn at(&self, cur: *mut c_void, off: usize, len: usize) -> *const u8 {
        unsafe { (*cur.cast::<crate::zip::Cursor>()).at(self.0, off, len) }.map_or(core::ptr::null(), <[u8]>::as_ptr)
    }
    unsafe fn close(&self, cur: *mut c_void) { drop(unsafe { alloc::boxed::Box::from_raw(cur.cast::<crate::zip::Cursor>()) }) }
    unsafe fn bad(&self) -> bool { self.0.bad() }
}
struct Dense(*const u8);
// Safety: read only
unsafe impl Sync for Dense {}
impl Source for Dense {
    unsafe fn open(&self) -> Option<*mut c_void> { Some(null_mut()) }
    unsafe fn at(&self, _: *mut c_void, off: usize, _: usize) -> *const u8 { unsafe { self.0.add(off) } }
    unsafe fn close(&self, _: *mut c_void) {}
    unsafe fn bad(&self) -> bool { false }
}
/// coc.rs `coc_alloc`: 64-byte aligned, never size 0, abort on failure.
unsafe fn coc_alloc(bytes: usize) -> *mut u8 {
    let want = bytes.next_multiple_of(64).max(64);
    let p = unsafe { alloc::alloc::alloc(Layout::from_size_align_unchecked(want, 64)) };
    if p.is_null() {
        crate::os::eprint(format_args!("aligned_alloc {bytes} bytes failed\n")).expect("qlean: stderr");
        crate::os::exit(1)
    }
    p
}
/// Frees what `coc_alloc` or C's `aligned_alloc` gave (the allocator's `dealloc` is `free`, whatever the layout says).
unsafe fn coc_free(p: *mut u8) { if !p.is_null() { unsafe { alloc::alloc::dealloc(p, Layout::from_size_align_unchecked(64, 64)) } } }
unsafe fn mk_pair(a: *mut c_void, b: *mut c_void) -> *mut c_void {
    unsafe { let p = lean::alloc_ctor(0, 2, 0); lean::ctor_set(p, 0, a.cast()); lean::ctor_set(p, 1, b.cast()); p.cast() }
}
/// coc.rs `coc_meta_view`: the five sections and the trailer over `metabytes` bytes at `m`, the count cut to what they hold.
unsafe fn meta_view(m: *mut u8, metabytes: usize, n: usize) -> CCoc {
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
unsafe fn enc_free(s: *mut CEnc) {
    unsafe {
        coc_free((*s).exc_heap.cast());
        coc_free((*s).frm_heap.cast());
        if (*s).alp != 0 && (*s).blob.is_null() { coc_free((*s).exp.cast()) }
        lean::dec((*s).meta.cast());
        if !(*s).pack.is_null() { lean::dec((*s).pack.cast()) }
        if !(*s).blob.is_null() { lean::dec((*s).blob.cast()) }
    }
}
/// coc.rs `coc_enc_pair`: the (meta, pack) of a finished Frame of Reference writer.
pub unsafe extern "C" fn qrs_coc_enc_pair(s: *mut CEnc) -> *mut c_void { unsafe { coc_free((*s).exc_heap.cast()); mk_pair((*s).meta, (*s).pack) } }

type Blk<'a> = &'a (dyn Fn(*mut CEnc, usize, *const u8, usize) + Sync);
struct Pass<'a, S> { src: &'a S, blk: Blk<'a>, sized: bool }
/// coc.rs `src_run`: the blocks `[b0, b1)` through the per-block step; a worker writes only what its block owns (its
/// metadata entries, its bytes at off[b], its exceptions at exc_off[b]), so any pass may be split.
unsafe extern "C" fn src_run<S: Source>(b0: usize, b1: usize, p: *const CPass) {
    use core::sync::atomic::Ordering::SeqCst;
    unsafe {
        let (s, job) = ((*p).o.cast::<CEnc>(), &*(*p).a.cast::<Pass<S>>());
        let Some(cur) = job.src.open() else { return };
        let (n, width, sized, lg) = ((*s).n, (*s).width, job.sized, (*s).c.lg());
        let (lb, over) = (AtomicUsize::from_ptr(&raw mut (*s).lb), AtomicI32::from_ptr(&raw mut (*s).over));
        // the meta pass under a size test stops once the blocks it has sized already reach it: each block's residuals and its
        // exceptions' bytes are a part of the total `qrs_coc_enc_plan` would answer, so their sum is a lower bound
        let mut mine = 0usize;
        for b in b0..b1 {
            let (lo, nb) = (b << lg, if (b + 1) << lg < n { 1 << lg } else { n - (b << lg) });
            let x = job.src.at(cur, lo * width, nb * width);
            if x.is_null() { break }
            (job.blk)(s, b, x, nb);
            if !sized { continue }
            mine += enc::block_bytes(lg, *(*s).c.width.add(b), *(*s).exc_off.add(b + 1), width);
            if (b - b0) % 16 == 15 {
                if lb.fetch_add(mine, SeqCst) + mine >= (*s).below { over.store(1, SeqCst) }
                mine = 0;
                if over.load(SeqCst) != 0 { break }
            }
        }
        if sized { lb.fetch_add(mine, SeqCst); }
        job.src.close(cur);
    }
}
/// coc.rs `src_pass`: `blk` over every block of `src` on the pool; `meta` marks the sizing pass. False when the source failed.
unsafe fn src_pass<S: Source>(s: *mut CEnc, src: &S, blk: Blk, meta: bool, cost: u32) -> bool {
    unsafe {
        let job = Pass { src, blk, sized: meta && (*s).below != 0 };
        let (n, w) = ((*s).n, (*s).width);
        let p = CPass { a: (&raw const job).cast(), b: core::ptr::null(), c: core::ptr::null(), o: s.cast(), n, at: 0, r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 };
        c::pool()(src_run::<S>, n.div_ceil(1 << (*s).c.lg()), cost, w << (*s).c.lg(), &p);
        !src.bad()
    }
}
fn meta_step(s: *mut CEnc, b: usize, x: *const u8, nb: usize) { unsafe { let w = (*s).width; enc::meta_step(&mut (*s).meta_blk(b), sl(x, nb * w), w, nb) } }
fn pack_step(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::pack_step(&mut (*s).pack_blk(b, nb, false), sl(x, nb * w), w, (*s).alp != 0) }
}

/// coc.rs `qlean_coc_encode_src`: 1 and the parts, or 0 with nothing allocated when the source failed, or 2 with nothing
/// allocated when the encoded form would be `below` bytes or more (`SIZE_MAX` encodes unconditionally).
unsafe fn encode<S: Source>(src: &S, n: usize, width: usize, kind: u32, out: &mut CParts, below: usize) -> c_int {
    unsafe {
        let mut e: CEnc = core::mem::zeroed();
        let s = &raw mut e;
        *out = CParts { meta: null_mut(), body: null_mut(), alp: null_mut() };
        if kind == SRC_DENSE || kind == SRC_BITS {
            let sz = if kind == SRC_BITS { n.div_ceil(8) } else { n * width };
            let o = lean::alloc_sarray(1, sz, sz);
            (*s).n = n;
            (*s).width = width;
            (*s).out = lean::sarray_cptr(o);
            let bits = kind == SRC_BITS;
            let blk = move |s: *mut CEnc, b: usize, x: *const u8, nb: usize| if bits { qrs_src_bits((*s).out, n.div_ceil(8), b, x, nb) } else { qrs_src_copy((*s).out.add((b << DEFAULT_LG) * width), x, nb * width) };
            if !src_pass(s, src, &blk, false, crate::QLEAN_COST_COPY) { lean::dec(o); return 0 }
            out.body = o.cast();
            return 1;
        }
        if kind != SRC_FOR && kind != SRC_ALP {
            crate::os::eprint(format_args!("qlean_coc_encode_src: form {kind} is not one of rust/src/coc.rs's SRC_*\n")).expect("qlean: stderr");
            crate::os::exit(1)
        }
        let alp = kind == SRC_ALP;
        qrs_coc_enc_open(s, n, width, alp as c_int);
        // what the residuals and exceptions may come to before the size test is already failed, the metadata being fixed;
        // 0 is no test, which `SIZE_MAX` asks for
        let msz = lean::sarray_size((*s).meta.cast());
        if below != usize::MAX {
            if below <= msz { enc_free(s); return 2 }
            (*s).below = below - msz;
        }
        let cost = if alp { crate::QLEAN_COST_MATH } else { crate::QLEAN_COST_ARITH };
        if !src_pass(s, src, &|s, b, x, nb| meta_step(s, b, x, nb), true, cost) { enc_free(s); return 0 }
        if AtomicI32::from_ptr(&raw mut (*s).over).load(core::sync::atomic::Ordering::SeqCst) != 0 { enc_free(s); return 2 }
        // the size is known here, so a form that does not shrink is never packed
        if qrs_coc_enc_plan(s) >= below { enc_free(s); return 2 }
        qrs_coc_enc_layout(s);
        if !src_pass(s, src, &|s, b, x, nb| pack_step(s, b, x, nb), false, crate::QLEAN_COST_ARITH) { enc_free(s); return 0 }
        coc_free((*s).exc_heap.cast());
        *out = CParts { meta: (*s).meta, body: (*s).pack, alp: (*s).blob };
        1
    }
}
/// The three parts of an encoded column (meta, body, alp) as the writer allocated them; dropped, they are released. A
/// part the form has not is empty.
pub struct ZParts(CParts);
impl ZParts {
    /// part `i` (0 meta, 1 body, 2 alp) as the array the writer allocated, handed over without a copy; `None` for a part
    /// the form has not
    fn take(&mut self, i: usize) -> Option<lean::O> {
        let p = core::mem::replace([&mut self.0.meta, &mut self.0.body, &mut self.0.alp][i], null_mut());
        (!p.is_null()).then(|| unsafe { lean::O::from_raw(p.cast()) })
    }
    /// The three parts, a part the form has not being a fresh empty array
    pub fn into_parts(mut self) -> [lean::O; 3] { core::array::from_fn(|i| self.take(i).unwrap_or_else(|| lean::SArr::new(1, 0).into())) }
    /// `(meta, body)`, the answer of the Frame of Reference forms (no alp part)
    pub fn into_pair(mut self) -> lean::O {
        let (m, b) = (self.take(0), self.take(1));
        lean::ctor(0, [m.expect("ZParts::into_pair: no meta part"), b.expect("ZParts::into_pair: no body part")], &[])
    }
    /// `(meta, (body, alp))`, the answer of the ALP form
    pub fn into_triple(self) -> lean::O { let [m, b, a] = self.into_parts(); lean::ctor(0, [m, lean::ctor(0, [b, a], &[])], &[]) }
}
impl Drop for ZParts {
    fn drop(&mut self) { for p in [self.0.meta, self.0.body, self.0.alp] { if !p.is_null() { unsafe { lean::dec(p.cast()) } } } }
}
/// coc.rs `qlean_zip_parts`'s encode: the `n` elements of `width` bytes of `z`'s element region in the form `kind` names,
/// unconditionally (no size test); `None` when `z` failed, the failure being `z.error()`.
pub fn encode_zip(z: &crate::zip::File, n: usize, width: usize, kind: u8) -> Option<ZParts> {
    let mut out = CParts { meta: null_mut(), body: null_mut(), alp: null_mut() };
    (unsafe { encode(&ZSrc(z), n, width, kind as u32, &mut out, usize::MAX) } == 1).then_some(ZParts(out))
}
/// coc.rs `coc_encode_dense`: the parts of the dense `x`'s `x.len() / width` elements of `width` bytes in the Frame of
/// Reference form (`alp` false) or the ALP one, `None` when they would take `below` bytes or more (`usize::MAX`: never).
pub fn encode_dense(x: &[u8], width: usize, alp: bool, below: usize) -> Option<ZParts> {
    let mut out = CParts { meta: null_mut(), body: null_mut(), alp: null_mut() };
    (unsafe { encode(&Dense(x.as_ptr()), x.len() / width, width, if alp { SRC_ALP } else { SRC_FOR }, &mut out, below) } == 1).then_some(ZParts(out))
}

/// A producer written in safe Rust: coc.rs's `coc_fill` and, where the answer holds whole blocks of a column already in
/// the writer's form, `coc_take`; ALP's two hints, `coc_hint` and `coc_ints`, have no answer by default.
pub trait Producer: Sync {
    /// Elements `i0 .. i0 + buf.len()` of the answer into `buf`.
    fn fill(&self, buf: &mut [i64], i0: usize);
    /// Block `pb` of a column in the writer's form that answer block `b` equals, with `pb`.
    fn take(&self, _b: usize) -> Option<(Cocf<'_>, usize)> { None }
    /// A block exponent for answer block `b` and the most exceptions it may leave; -1 is no hint.
    fn hint(&self, _b: usize) -> Option<(i32, u32)> { None }
    /// Answer block `b` as decimals (`out`, none for pass 1 only) and the exponent they are at; -1 = the general path.
    fn ints(&self, _b: usize, _out: Option<&mut structural::Ints>) -> i32 { -1 }
}
/// A closure is a producer with no `take`: the form every kernel that computes an answer a block at a time uses.
impl<F: Fn(&mut [i64], usize) + Sync> Producer for F { fn fill(&self, buf: &mut [i64], i0: usize) { self(buf, i0) } }
/// `P` as the writer's source: the cursor and the blocks it claims, as `FillSrc`'s are for a C producer.
struct ProdSrc<'a, P> { p: &'a P, width: usize, lg: u32 }
impl<P: Producer> Moves for ProdSrc<'_, P> {
    fn take(&self, b: usize) -> Option<(Cocf<'_>, usize)> { self.p.take(b) }
    fn ints(&self, b: usize, nb: usize, d: &mut [i64], ee: &mut [i8], raw: Option<&mut [u8]>) -> Option<i32> {
        let mut ptrs = alloc::vec![core::ptr::null::<u8>(); nb];
        let mut o = structural::Ints { d: &mut d[..nb], ee: &mut ee[..nb], raw: raw.is_some().then(|| &mut ptrs[..nb]) };
        let e = self.p.ints(b, Some(&mut o));
        if let (Some(raw), true) = (raw, e >= 0) {
            let w = self.width;
            // each exception's `w` raw bytes are in the source's patch list or the producer's hole, both alive here
            for i in (0..nb).filter(|&i| ee[i] < 0) { raw[i * w..(i + 1) * w].copy_from_slice(unsafe { sl(ptrs[i], w) }) }
        }
        Some(e)
    }
    fn hint(&self, b: usize) -> Option<(i32, u32)> { self.p.hint(b) }
}
impl<P: Producer> Source for ProdSrc<'_, P> {
    unsafe fn open(&self) -> Option<*mut c_void> { Some(unsafe { coc_alloc(16 << self.lg) }.cast()) }
    unsafe fn at(&self, cur: *mut c_void, off: usize, len: usize) -> *const u8 {
        unsafe {
            let (b, w) = (off / self.width >> self.lg, self.width);
            if self.p.take(b).is_some() || self.p.ints(b, None) >= 0 { return cur.cast() }
            let (v, cnt) = (cur.cast::<i64>(), len / w);
            self.p.fill(sl_mut(v, cnt), off / w);
            enc::narrow(w, sl(v, cnt), sl_mut(v.add(1 << self.lg).cast::<u8>(), cnt * w)).as_ptr()
        }
    }
    unsafe fn close(&self, cur: *mut c_void) { unsafe { coc_free(cur.cast()) } }
    unsafe fn bad(&self) -> bool { false }
}
/// The (meta, pack) of the `n` elements `p` denotes, `width` bytes each: coc.rs `qlean_coc_encode_fill` for a Rust producer.
pub fn encode_fill<P: Producer>(n: usize, width: usize, p: &P) -> lean::O {
    unsafe { lean::O::from_raw(encode_move(n, width, false, &ProdSrc { p, width, lg: DEFAULT_LG }).cast()) }
}
/// `encode_fill` at ALP: `(meta, (pack, alp))` of the `n` floats of `width` bytes `p` denotes (`qlean_coc_encode_move`, alp 1).
pub fn encode_alp<P: Producer>(n: usize, width: usize, p: &P) -> lean::O {
    unsafe { lean::O::from_raw(encode_move(n, width, true, &ProdSrc { p, width, lg: DEFAULT_LG }).cast()) }
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
        if ex && lean::sarray_capacity(p) >= need { lean::sarray_set_size(p, need); return lean::O::from_raw(p) }
        let r = lean::alloc_sarray(1, need, if ex { 2 * need } else { need });
        core::ptr::copy_nonoverlapping(lean::sarray_cptr(p), lean::sarray_cptr(r), sz.min(need));
        lean::dec(p);
        lean::O::from_raw(r)
    }
}
/// `lean_sarray_set_size`: the fresh `ByteArray` `o` (`rc` 1, allocated with room for `size` bytes) counting `size` bytes. `lean.rs`
/// has no size setter, which a kernel writing into the capacity before it knows how much it wrote needs.
pub fn sarray_set_size(o: lean::O, size: usize) -> lean::O {
    unsafe {
        let p = o.into_raw();
        assert!(lean::is_exclusive(p) && size <= lean::sarray_capacity(p), "sarray_set_size: {size} bytes of a shared array or past its capacity {}", lean::sarray_capacity(p));
        lean::sarray_set_size(p, size);
        lean::O::from_raw(p)
    }
}
/// coc.rs `qlean_coc_encode_move` over any source of blocks that also moves them (`alp` answers `(meta, (pack, alp))`).
unsafe fn encode_move<S: Source + Moves>(n: usize, width: usize, alp: bool, fs: &S) -> *mut c_void {
    unsafe {
        let mut e: CEnc = core::mem::zeroed();
        let s = &raw mut e;
        qrs_coc_enc_open(s, n, width, alp as c_int);
        let cost = if alp { crate::QLEAN_COST_MATH } else { crate::QLEAN_COST_ARITH };
        // a fill cannot fail, having no `bad`: a refusal here is the writer's own bug
        let ok = src_pass(s, fs, &|s, b, x, nb| enc::move_meta_blk(fs, &mut (*s).meta_blk(b), || sl(x, nb * width), width, nb), true, cost) && {
            qrs_coc_enc_layout(s);
            src_pass(s, fs, &|s, b, x, nb| enc::move_pack_blk(fs, |whole| (*s).pack_blk(b, nb, whole), || sl(x, nb * width), b, nb, width, alp), false, crate::QLEAN_COST_ARITH)
        };
        if !ok {
            crate::os::eprint(format_args!("qlean_coc_encode_move: the writer refused {n} elements of {width} bytes from a fill\n")).expect("qlean: stderr");
            crate::os::exit(1)
        }
        if !alp { return qrs_coc_enc_pair(s) }
        coc_free((*s).exc_heap.cast());
        mk_pair((*s).meta, mk_pair((*s).pack, (*s).blob))
    }
}
