//! Every symbol that leaves the object, and the `#[repr(C)]` mirrors of C structs. A shim does nothing but turn
//! pointer + length into slices (null or zero length gives an empty slice) and call. c/rs.h is generated from
//! this file by cbindgen (rust/build.sh).
use core::ffi::{c_char, c_int, c_void};
use core::ptr::null_mut;
use core::slice;
use core::sync::atomic::{AtomicI32, AtomicUsize};

use alloc::borrow::Cow;

use crate::c;
use crate::coc::{self, Coc};
use crate::group::{self, Table};
use crate::{key, kwin, own};
use crate::layout::{Tail, exc_ok};
use crate::own::{OwnHead, check, head};
use crate::why::Why;
use crate::zip::{ZTrailer, table, trailer, zq};
use crate::{BLK, ids, simd, unpack};
use crate::alp::Cocf;
use crate::cocops::CocMut;
use crate::enc::{EncMeta, EncPack};
use crate::sym::{self, Syms};
use crate::{codec, enc, ew, reduce, scan, search, sort, structural};

/// Mirror of coc.h:103 `coc`; rs.h asserts every field's offset against it.
#[repr(C)]
pub struct CCoc {
    pub base: *mut i64, pub maxv: *mut i64, pub width: *mut u8, pub off: *mut u64, pub bsum: *mut i64,
    pub sumnul: *mut i64, pub sumn: *mut u64, pub pack: *mut u8,
    pub n: usize, pub nblk: usize, pub packbytes: usize, pub mblk: usize,
    pub exc_off: *const u32, pub exc_pos: *const u16, pub exc_raw: *const u8, pub fdelta: *mut u64,
    pub nexc: usize, pub exc_esz: usize,
}
impl CCoc {
    /// The only place raw `coc` pointers become slices. Safety: every pointer is null or valid for the length
    /// coc.h documents, for `'a`.
    pub unsafe fn view<'a>(&self) -> Coc<'a> {
        let m = self.mblk;
        let meta = coc::Meta {
            base: unsafe { sl(self.base, m) }, maxv: unsafe { sl(self.maxv, m) }, off: unsafe { sl(self.off, m) },
            bsum: unsafe { sl(self.bsum, m) }, width: unsafe { sl(self.width, m) },
            // a null slot is "no sums stored", which coc.h spells 0
            sumnul: if self.sumnul.is_null() { 0 } else { unsafe { *self.sumnul } },
            sumn: if self.sumn.is_null() { 0 } else { unsafe { *self.sumn } },
            n: self.n, nblk: self.nblk, mblk: m,
        };
        let exc = if self.exc_off.is_null() { None } else {
            Some(coc::Exc { off: unsafe { sl(self.exc_off, m + 1) }, pos: unsafe { sl(self.exc_pos, self.nexc) },
                            raw: unsafe { sl(self.exc_raw, self.nexc * self.exc_esz) }, esz: self.exc_esz })
        };
        let fdelta = if self.fdelta.is_null() { None } else { Some(unsafe { sl(self.fdelta.cast_const(), m) }) };
        Coc { meta, pack: unsafe { sl(self.pack.cast_const(), self.packbytes) }, exc, fdelta }
    }
}

/// Mirror of pass.h:74 `qlean_pass`, the context `c::run_map` hands the C pool; rs.h's `QRS_ASSERT_CPASS`, expanded
/// in sort.c beside `qlean_run_c`, asserts every field's offset against it.
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
const _: () = assert!(size_of::<OwnHead>() == 80);
const _: () = assert!(size_of::<ZTrailer>() == 24);

/// Safety: `p` is null or valid for `key::bytes(kind, n)` reads.
unsafe fn keys<'a>(kind: u8, p: *const u8, n: usize) -> Option<&'a [u8]> {
    key::bytes(kind, n).map(|b| unsafe { sl(p, b) })
}

/// `ids` is `bytes` long; `slot` `nd + 1` entries; `first` `min(n, nd + 1)`. Answers the group count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_firsts(ids: *const u8, bytes: usize, n: usize, w: u32, nd: usize, slot: *mut usize,
                                        first: *mut usize) -> usize {
    unsafe { ids::firsts(sl(ids, bytes), n, w, nd, sl_mut(slot, nd + 1), sl_mut(first, n.min(nd + 1))) }
}

/// `ids` is `ids_bytes(n, w)` long, `slot` `nd + 1` entries, `out` `ids_bytes(n, wo)` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_map(ids: *const u8, n: usize, w: u32, nd: usize, slot: *const usize, wo: u32,
                                     out: *mut u8, run: unsafe extern "C" fn()) {
    unsafe { ids::map(core::mem::transmute::<unsafe extern "C" fn(), c::Runner>(run), sl(ids, ids::ids_bytes(n, w)), n, w, nd, sl(slot, nd + 1), wo, sl_mut(out, ids::ids_bytes(n, wo))) }
}

/// `g` holds `n` ids a byte each; packed in place to `w < 8` bits.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_pack(g: *mut u8, n: usize, w: u32) { unsafe { ids::pack_in_place(sl_mut(g, n), w, n) } }

/// 1 and `*mn`, `*mx` filled; 0 for `SK_WIN` or an unknown kind.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_key_range(kind: u8, p: *const u8, n: usize, mn: *mut u64, mx: *mut u64) -> c_int {
    match unsafe { keys(kind, p, n) }.and_then(|b| key::each(kind, b, n, key::Range)) {
        Some((a, b)) => { unsafe { mn.write(a); mx.write(b) }; 1 }
        None => 0,
    }
}

/// `range_foR`: an encoded column's key range.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_key_range_win(kind: u8, c: *const CCoc, mn: *mut u64, mx: *mut u64) {
    let (a, b) = kwin::range(kind, &unsafe { (*c).view() });
    unsafe { mn.write(a); mx.write(b) }
}

/// `ids_run` over `dedup`'s tables: `dtab` (`slots` entries) when not null, else `htab` (`cap` entries) and `gkey`
/// (`ng` entries). `gid` is `n * lane / 8` bytes.  `run` is C's `qlean_run_c`, passed as a `void (*)(void)` and called as `c::Runner`. 1 = written, 0 = refused (a kind outside the enum, `SK_WIN`, a short payload or `gid`, a lane not 8, 16, 32 or 64).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_group_fill(kind: u8, p: *const u8, n: usize, mn: u64, dtab: *const u32, slots: usize,
                                        htab: *const usize, gkey: *const u64, ng: usize, cap: usize, sh: c_int,
                                        gid: *mut u8, lane: u32, run: unsafe extern "C" fn()) -> c_int {
    let Some(b) = (unsafe { keys(kind, p, n) }) else { return 0 };
    let t = if dtab.is_null() {
        Table::Hashed { slot: Cow::Borrowed(unsafe { sl(htab, cap) }), gkey: Cow::Borrowed(unsafe { sl(gkey, ng) }),
                        sh: sh as u32 }
    } else {
        Table::Direct { tab: Cow::Borrowed(unsafe { sl(dtab, slots) }), mn }
    };
    group::fill(unsafe { core::mem::transmute::<unsafe extern "C" fn(), c::Runner>(run) }, kind, b, n, &t, lane, unsafe { sl_mut(gid, n.saturating_mul(lane as usize) / 8) }) as c_int
}

/// `groupIds` of a dense column: `gid` is `gcap` bytes, `first` `n` entries, `run` C's `qlean_run_c` as in `qrs_group_fill`. Answers `ng`, or `SIZE_MAX` for
/// `SK_WIN`, an unknown kind.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_group_ids(kind: u8, p: *const u8, n: usize, mn: u64, mx: u64, gid: *mut u8, gcap: usize,
                                       first: *mut usize, run: unsafe extern "C" fn()) -> usize {
    let Some(b) = (unsafe { keys(kind, p, n) }) else { return usize::MAX };
    group::group_ids(unsafe { core::mem::transmute::<unsafe extern "C" fn(), c::Runner>(run) }, kind, b, n, mn, mx, unsafe { sl_mut(gid, gcap) }, unsafe { sl_mut(first, n) }).unwrap_or(usize::MAX)
}

/// `groupIds` of an encoded column (`qlean_sort_group_ids_foR`): as `qrs_group_ids`, `mn`/`mx` from
/// `qrs_key_range_win`. `SIZE_MAX` = `gid` or `first` too short.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_group_ids_win(kind: u8, c: *const CCoc, n: usize, mn: u64, mx: u64, gid: *mut u8,
                                           gcap: usize, first: *mut usize, run: unsafe extern "C" fn()) -> usize {
    group::group_ids_win(unsafe { core::mem::transmute::<unsafe extern "C" fn(), c::Runner>(run) }, kind, unsafe { (*c).view() }, n, mn, mx, unsafe { sl_mut(gid, gcap) }, unsafe { sl_mut(first, n) }).unwrap_or(usize::MAX)
}

/// `len` and `off` are `np` entries, `head` `hcap` bytes. Answers the header length, or 0 and `why` filled.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_own_write_head(code: u8, attr: u8, kind: u8, count: u64, nl: usize, len: *const usize,
                                            np: usize, head: *mut u8, hcap: usize, off: *mut usize,
                                            w: *mut c_char, cap: usize) -> usize {
    // `len` has `OWN_NPARTS[kind]` entries at most; a larger `np` is refused before a slice over `len` is formed
    if np > own::OWN_NPARTS.into_iter().max().unwrap_or(0) {
        own::refuse_head(kind, np, nl, &mut unsafe { why(w, cap) });
        return 0;
    }
    unsafe { own::write_head(code, attr, kind, count, nl, sl(len, np), sl_mut(head, hcap), sl_mut(off, np),
                             &mut why(w, cap)) }.unwrap_or(0)
}

/// `p` is the block's `BLK * *w / 8` bytes, `buf` `BLK * 8`; answers `p` or `buf`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_lanes(p: *const u8, w: *mut u8, nb: usize, buf: *mut u8) -> *const u8 {
    let w = unsafe { &mut *w };
    unsafe { coc::lanes(sl(p, BLK * *w as usize / 8), w, nb, sl_mut(buf, BLK * 8)) }.as_ptr()
}

/// `decode_blk`: block `b`'s first `nb` elements into `out`. Written out per type, not by a macro: cbindgen
/// does not expand macros, and rs.h needs the prototype.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_decode_blk_u8(c: *const CCoc, b: usize, nb: usize, out: *mut u8) {
    unsafe { (*c).view().decode_blk(b, nb, sl_mut(out, nb)) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_decode_blk_i16(c: *const CCoc, b: usize, nb: usize, out: *mut i16) {
    unsafe { (*c).view().decode_blk(b, nb, sl_mut(out, nb)) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_decode_blk_i32(c: *const CCoc, b: usize, nb: usize, out: *mut i32) {
    unsafe { (*c).view().decode_blk(b, nb, sl_mut(out, nb)) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_decode_blk_i64(c: *const CCoc, b: usize, nb: usize, out: *mut i64) {
    unsafe { (*c).view().decode_blk(b, nb, sl_mut(out, nb)) }
}

/// Safety: `p` is null or valid for `n` reads of `T` during `'a`.
unsafe fn sl<'a, T>(p: *const T, n: usize) -> &'a [T] {
    if p.is_null() || n == 0 { &[] } else { unsafe { slice::from_raw_parts(p, n) } }
}
/// Safety: `p` is null or valid for `n` writes of `T` during `'a`, and nothing else aliases it.
unsafe fn sl_mut<'a, T>(p: *mut T, n: usize) -> &'a mut [T] {
    if p.is_null() || n == 0 { &mut [] } else { unsafe { slice::from_raw_parts_mut(p, n) } }
}
/// Safety: as `sl_mut` for `why`, `cap` bytes.
unsafe fn why<'a>(p: *mut c_char, cap: usize) -> Why<'a> { Why::new(unsafe { sl_mut(p.cast::<u8>(), cap) }) }

/// `alp` 0/1/2 = `Tail::None/Exps/Frames`, as own.c's `exc_ok` numbers them.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_exc_ok(t: *const u8, len: usize, nblk: usize, nexc: u64, esz: usize, part: c_int,
                                    alp: c_int, w: *mut c_char, cap: usize) -> c_int {
    let tail = match alp { 1 => Tail::Exps, 2 => Tail::Frames, _ => Tail::None };
    exc_ok(unsafe { sl(t, len) }, nblk, nexc, esz, part, tail, &mut unsafe { why(w, cap) }) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_max(p: *const u8, bytes: usize, w: u32, n: usize) -> usize {
    ids::ids_max(unsafe { sl(p, bytes) }, w, n)
}

/// 1 and `*h` filled, or 0 and `why` filled.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_own_head(m: *const u8, size: usize, h: *mut OwnHead, w: *mut c_char, cap: usize)
    -> c_int {
    match head(unsafe { sl(m, size) }, &mut unsafe { why(w, cap) }) {
        Some(v) => { unsafe { h.write(v) }; 1 }
        None => 0,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_own_check(kind: u8, n: u64, p: *const *const u8, len: *const usize, np: usize,
                                       w: *mut c_char, cap: usize) -> c_int {
    let (ps, ls) = unsafe { (sl(p, np), sl(len, np)) };
    let parts: alloc::vec::Vec<&[u8]> = ps.iter().zip(ls).map(|(&q, &l)| unsafe { sl(q, l) }).collect();
    check(kind, n, &parts, &mut unsafe { why(w, cap) }) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_std(c: *const CCoc, n: usize) -> c_int {
    unsafe { (*c).view() }.std(n) as c_int
}

/// Null = ok, else the message. `dst` is the pointer C passes, 8 bytes before the block.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_zq(b: *const u8, n: usize, dst: *mut u8, want: usize) -> *const c_char {
    match zq(unsafe { sl(b, n) }, unsafe { sl_mut(dst, 8 + want) }) {
        Ok(()) => core::ptr::null(),
        Err(m) => m.as_ptr(),
    }
}

/// 1 and `*t` filled, or 0 and `why` filled.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ztrailer(hdr: *const u8, size: u64, nblk: u64, hat: u64, t: *mut ZTrailer,
                                      w: *mut c_char, cap: usize) -> c_int {
    let h = unsafe { &*hdr.cast::<[u8; 32]>() };
    match trailer(h, size, nblk, hat, &mut unsafe { why(w, cap) }) {
        Some(v) => { unsafe { t.write(v) }; 1 }
        None => 0,
    }
}

/// `ent` is 8*nblk bytes, `at` nblk+1 entries, `algo` nblk; returns maxc.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ztable(ent: *const u8, nblk: usize, at: *mut u64, algo: *mut u32) -> usize {
    unsafe { table(sl(ent, 8 * nblk), sl_mut(at, nblk + 1), sl_mut(algo, nblk)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_u8_sum(p: *const u8, n: usize) -> i64 { simd::u8_sum(unsafe { sl(p, n) }) }

/// `p` is the block's BLK*w/8 bytes; `out` BLK*8.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_res_unpack_scalar(p: *const u8, w: u8, nb: usize, out: *mut u8) {
    unsafe { unpack::res_unpack_scalar(sl(p, BLK * w as usize / 8), w, nb, sl_mut(out, BLK * 8)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_res_unpack(p: *const u8, w: u8, nb: usize, out: *mut u8) {
    unsafe { simd::res_unpack(sl(p, BLK * w as usize / 8), w, nb, sl_mut(out, BLK * 8)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_res_unpack_add(p: *const u8, w: u8, nb: usize, base: u64, out: *mut u8, tw: u32)
    -> c_int {
    unsafe { simd::res_unpack_add(sl(p, BLK * w as usize / 8), w, nb, base, sl_mut(out, BLK * 8), tw) as c_int }
}

// ---- Column (a) scaffold: the mirrors its shims take, asserted by `QRS_ASSERT_COLA` (structural.c). ----

/// Mirror of coc.h:1443 `cocf`, the ALP column.
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
/// Mirror of coc.h:1925 `coc_src`; Rust only passes it back to C. The callbacks take the struct as `void *`: an
/// anonymous typedef (cbindgen's `style = "type"`) cannot name itself.
#[repr(C)]
pub struct CSrc {
    pub ctx: *mut c_void, pub open: Option<unsafe extern "C" fn(*const c_void) -> *mut c_void>,
    pub at: Option<unsafe extern "C" fn(*const c_void, *mut c_void, usize, usize) -> *const c_void>,
    pub close: Option<unsafe extern "C" fn(*const c_void, *mut c_void)>, pub bad: *mut c_int,
}
/// Mirror of coc.h:1956 `coc_enc`. The lean objects are opaque here; `lb` and `over` are C `_Atomic`, plain
/// words in the mirror so cbindgen can spell them, read through `AtomicUsize::from_ptr` by whoever fills A16.
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
    /// `exp`; the two a column does not keep are null) and the early-decline words, which C reads through its atomics.
    /// Safety: `self` is an open encoder, `b < c.mblk`, no other view of `b` alive.
    pub unsafe fn meta_blk<'a>(&mut self, b: usize) -> EncMeta<'a> {
        let (lb, over) = unsafe { (AtomicUsize::from_ptr(&raw mut self.lb), AtomicI32::from_ptr(&raw mut self.over)) };
        let c = &self.c;
        unsafe { EncMeta { b, base: &mut *c.base.add(b), maxv: &mut *c.maxv.add(b), width: &mut *c.width.add(b), bsum: &mut *c.bsum.add(b),
                           frm: if c.fdelta.is_null() { None } else { Some(&mut *c.fdelta.add(b)) }, nexc: &mut *self.exc_off.add(b + 1),
                           exp: if self.exp.is_null() { None } else { Some(&mut *self.exp.add(b)) },
                           below: self.below, lb, over } }
    }
    /// Block `b`'s pack-pass view, after `coc_enc_layout`: residuals at `off[b]`, patches `exc_off[b]..exc_off[b + 1]`.
    /// Safety: as `meta_blk`.
    pub unsafe fn pack_blk<'a>(&mut self, b: usize, nb: usize) -> EncPack<'a> {
        let c = &self.c;
        unsafe {
            let (base, w, at) = (*c.base.add(b), *c.width.add(b), *self.exc_off.add(b) as usize);
            let ne = *self.exc_off.add(b + 1) as usize - at;
            EncPack { b, nb, base, frame: (base as u64).wrapping_add(if c.fdelta.is_null() { 0 } else { *c.fdelta.add(b) }), width: w,
                      exp: if self.exp.is_null() { 0 } else { *self.exp.add(b) },
                      res: sl_mut(c.pack.add(*c.off.add(b) as usize), (nb * w as usize).div_ceil(8)),
                      pos: sl_mut(self.exc_pos.add(at), ne), raw: sl_mut(self.exc_raw.add(at * self.width), ne * self.width) }
        }
    }
}
/// Mirror of sym.h:22 `sym`.
#[repr(C)]
pub struct CSym { pub p: *const u8, pub len: usize }
/// Mirror of pass.h:492 `qlean_stage`, one pass of a fused chain.
#[repr(C)]
pub struct CStage {
    pub f: Option<unsafe extern "C" fn(usize, usize, *const CPass)>, pub p: CPass, pub asrc: u8, pub bsrc: u8, pub osrc: u8,
    pub abits: u16, pub bbits: u16, pub obits: u16, pub bytewise: u8,
}
/// Mirror of structural.c:2039 `symtab`; `slot` holds `mask + 1` ids.
#[repr(C)]
pub struct CSymtab { pub refs: usize, pub cnt: usize, pub mask: usize, pub stale: usize, pub slot: *mut u32 }
const _: () = assert!(size_of::<CCocf>() == 192 && size_of::<CSrc>() == 40 && size_of::<CEnc>() == 320);
const _: () = assert!(size_of::<CSym>() == 16 && size_of::<CStage>() == 96 && size_of::<CSymtab>() == 40);

impl CCoc {
    /// The writable view the in-place verbs (A3 `sums_drop`, A6 `shift`) take. Safety: as `view`, and no other
    /// view of `self` is alive for `'a`.
    pub unsafe fn view_mut<'a>(&mut self) -> CocMut<'a> {
        let m = self.mblk;
        CocMut { base: unsafe { sl_mut(self.base, m) }, maxv: unsafe { sl_mut(self.maxv, m) },
                 off: unsafe { sl_mut(self.off, m) }, bsum: unsafe { sl_mut(self.bsum, m) },
                 width: unsafe { sl_mut(self.width, m) },
                 sumnul: unsafe { self.sumnul.as_mut() }, sumn: unsafe { self.sumn.as_mut() },
                 pack: unsafe { sl_mut(self.pack, self.packbytes) }, n: self.n, nblk: self.nblk, mblk: m }
    }
}

/// C's `qlean_run_c` as the Rust `Runner`, the one cast every column (a) shim makes.
unsafe fn rn(run: unsafe extern "C" fn()) -> c::Runner { unsafe { core::mem::transmute::<unsafe extern "C" fn(), c::Runner>(run) } }
/// `n` symbols: `blob` and C's boxed `lean_array_cptr(offs)`, unboxed by `Syms`.
unsafe fn syms<'a>(blob: *const u8, bytes: usize, offs: *const usize, n: usize) -> Syms<'a> {
    Syms { blob: unsafe { sl(blob, bytes) }, offs: unsafe { sl(offs, n + 1) } }
}

/// A2: coc.h:690 `res_pack`: the vector pack where the build has it, the scalar one elsewhere.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_res_pack(v: *const u64, w: u8, nb: usize, dst: *mut u8) {
    // the C callers pass a block of the pack, `BLK * w / 8` bytes, not `BLK * 8`; the pack writes `⌈nb * w / 8⌉` of them
    unsafe { simd::res_pack(sl(v, BLK), w, nb, sl_mut(dst, (nb * w as usize).div_ceil(8))) }
}
/// A7: coc.h:2191 `pack_block`, per element type (cbindgen does not expand macros). `dst` is the block's ⌈nb*w/8⌉ bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pack_block_u8(dst: *mut u8, src: *const u8, nb: usize, base: i64, w: u8) {
    unsafe { enc::pack_block(sl_mut(dst, (nb * w as usize).div_ceil(8)), sl(src, nb), nb, base, w) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pack_block_i16(dst: *mut u8, src: *const i16, nb: usize, base: i64, w: u8) {
    unsafe { enc::pack_block(sl_mut(dst, (nb * w as usize).div_ceil(8)), sl(src, nb), nb, base, w) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pack_block_i32(dst: *mut u8, src: *const i32, nb: usize, base: i64, w: u8) {
    unsafe { enc::pack_block(sl_mut(dst, (nb * w as usize).div_ceil(8)), sl(src, nb), nb, base, w) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pack_block_i64(dst: *mut u8, src: *const i64, nb: usize, base: i64, w: u8) {
    unsafe { enc::pack_block(sl_mut(dst, (nb * w as usize).div_ceil(8)), sl(src, nb), nb, base, w) }
}
/// Block `b`'s meta view over `c`'s four arrays and its frames (`fdelta`, null = none). `exp` is an ALP column's exponent
/// array (null = none), `nexc` the patch-count slot, `lb`/`over` the early-decline words; none declines here.
/// Safety: `b < c.mblk`, the arrays valid, no other view of `b` alive.
unsafe fn ccoc_meta<'a>(c: &CCoc, b: usize, exp: *mut i8, nexc: &'a mut u32, lb: &'a AtomicUsize, over: &'a AtomicI32)
    -> EncMeta<'a> {
    unsafe {
        EncMeta { b, base: &mut *c.base.add(b), maxv: &mut *c.maxv.add(b), width: &mut *c.width.add(b), bsum: &mut *c.bsum.add(b),
                  frm: if c.fdelta.is_null() { None } else { Some(&mut *c.fdelta.add(b)) }, nexc,
                  exp: if exp.is_null() { None } else { Some(&mut *exp.add(b)) }, below: 0, lb, over }
    }
}
/// `encode_meta_blk` writes block `b`'s `base`, `maxv`, `width`, `bsum` of `c`; the patch and early-decline slots of
/// `EncMeta` have no C counterpart here and are scratch. Safety: `b < c.mblk`, the four arrays valid, no other view of `b`.
unsafe fn meta_blk<T: enc::Elt>(c: *mut CCoc, b: usize, x: *const T, nb: usize) {
    let (lb, over, mut nexc) = (AtomicUsize::new(0), AtomicI32::new(0), 0u32);
    enc::encode_meta_blk(&mut unsafe { ccoc_meta(&*c, b, null_mut(), &mut nexc, &lb, &over) }, unsafe { sl(x, nb) }, nb)
}
/// A7: coc.h:2240 `encode_meta_blk`, per element type.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_blk_u8(c: *mut CCoc, b: usize, x: *const u8, nb: usize) { unsafe { meta_blk(c, b, x, nb) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_blk_i16(c: *mut CCoc, b: usize, x: *const i16, nb: usize) { unsafe { meta_blk(c, b, x, nb) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_blk_i32(c: *mut CCoc, b: usize, x: *const i32, nb: usize) { unsafe { meta_blk(c, b, x, nb) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_blk_i64(c: *mut CCoc, b: usize, x: *const i64, nb: usize) { unsafe { meta_blk(c, b, x, nb) } }
/// `frame_pick` for C: 1 with `fo`, `wo`, `neo` written when a frame beats `cost`, else 0. `smp` is `k` samples.
unsafe fn pick<T: enc::Elt>(smp: *mut i64, k: usize, nb: usize, nnul: usize, cost: usize, mn: i64, x: *const T,
                            fo: *mut i64, wo: *mut u8, neo: *mut u32) -> c_int {
    match enc::frame_pick(unsafe { sl_mut(smp, k) }, nb, nnul, cost, mn, unsafe { sl(x, nb) }) {
        Some(f) => { unsafe { *fo = f.fo; *wo = f.wo; *neo = f.neo } 1 }
        None => 0,
    }
}
/// A7: coc.h:2275 `frame_pick`, per element type.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_frame_pick_u8(smp: *mut i64, k: usize, nb: usize, nnul: usize, cost: usize, mn: i64, x: *const u8,
                                           fo: *mut i64, wo: *mut u8, neo: *mut u32) -> c_int { unsafe { pick(smp, k, nb, nnul, cost, mn, x, fo, wo, neo) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_frame_pick_i16(smp: *mut i64, k: usize, nb: usize, nnul: usize, cost: usize, mn: i64, x: *const i16,
                                            fo: *mut i64, wo: *mut u8, neo: *mut u32) -> c_int { unsafe { pick(smp, k, nb, nnul, cost, mn, x, fo, wo, neo) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_frame_pick_i32(smp: *mut i64, k: usize, nb: usize, nnul: usize, cost: usize, mn: i64, x: *const i32,
                                            fo: *mut i64, wo: *mut u8, neo: *mut u32) -> c_int { unsafe { pick(smp, k, nb, nnul, cost, mn, x, fo, wo, neo) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_frame_pick_i64(smp: *mut i64, k: usize, nb: usize, nnul: usize, cost: usize, mn: i64, x: *const i64,
                                            fo: *mut i64, wo: *mut u8, neo: *mut u32) -> c_int { unsafe { pick(smp, k, nb, nnul, cost, mn, x, fo, wo, neo) } }
/// `encode_meta_exc_blk` for C: block `b` of `c`'s four meta arrays and `fdelta`; answers the patch count.
/// Safety: as `meta_blk`, and `c.fdelta` is valid for `b`.
unsafe fn meta_exc_blk<T: enc::Elt>(c: *mut CCoc, b: usize, x: *const T, nb: usize) -> u32 {
    let (lb, over, mut nexc) = (AtomicUsize::new(0), AtomicI32::new(0), 0u32);
    enc::encode_meta_exc_blk(&mut unsafe { ccoc_meta(&*c, b, null_mut(), &mut nexc, &lb, &over) }, unsafe { sl(x, nb) }, nb)
}
/// `pack_exc_blk` for C: block `b`'s residuals at `off[b]`, its `ne` patches at `pos` and `raw`.
/// Safety: `c` has its pack and layout set, `pos`/`raw` hold `ne` slots of `u16` / `T`.
unsafe fn pack_exc<T: enc::Elt>(c: *const CCoc, b: usize, x: *const T, nb: usize, ne: u32, pos: *mut u16, raw: *mut u8) {
    let c = unsafe { &*c };
    let w = unsafe { *c.width.add(b) };
    let frame = unsafe { (*c.base.add(b) as u64).wrapping_add(if c.fdelta.is_null() { 0 } else { *c.fdelta.add(b) }) };
    let mut p = enc::EncPack { b, nb, base: unsafe { *c.base.add(b) }, frame, width: w, exp: 0,
                               res: unsafe { sl_mut(c.pack.add(*c.off.add(b) as usize), (nb * w as usize).div_ceil(8)) },
                               pos: unsafe { sl_mut(pos, ne as usize) }, raw: unsafe { sl_mut(raw, ne as usize * size_of::<T>()) } };
    enc::pack_exc_blk(&mut p, unsafe { sl(x, nb) }, ne)
}
/// A8: coc.h:2226 `encode_meta_exc_blk`, per element type.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_exc_blk_u8(c: *mut CCoc, b: usize, x: *const u8, nb: usize) -> u32 { unsafe { meta_exc_blk(c, b, x, nb) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_exc_blk_i16(c: *mut CCoc, b: usize, x: *const i16, nb: usize) -> u32 { unsafe { meta_exc_blk(c, b, x, nb) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_exc_blk_i32(c: *mut CCoc, b: usize, x: *const i32, nb: usize) -> u32 { unsafe { meta_exc_blk(c, b, x, nb) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_exc_blk_i64(c: *mut CCoc, b: usize, x: *const i64, nb: usize) -> u32 { unsafe { meta_exc_blk(c, b, x, nb) } }
/// A8: coc.h:2263 `pack_exc_blk`, per element type.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pack_exc_blk_u8(c: *const CCoc, b: usize, x: *const u8, nb: usize, ne: u32, pos: *mut u16, raw: *mut u8) { unsafe { pack_exc(c, b, x, nb, ne, pos, raw) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pack_exc_blk_i16(c: *const CCoc, b: usize, x: *const i16, nb: usize, ne: u32, pos: *mut u16, raw: *mut u8) { unsafe { pack_exc(c, b, x, nb, ne, pos, raw) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pack_exc_blk_i32(c: *const CCoc, b: usize, x: *const i32, nb: usize, ne: u32, pos: *mut u16, raw: *mut u8) { unsafe { pack_exc(c, b, x, nb, ne, pos, raw) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pack_exc_blk_i64(c: *const CCoc, b: usize, x: *const i64, nb: usize, ne: u32, pos: *mut u16, raw: *mut u8) { unsafe { pack_exc(c, b, x, nb, ne, pos, raw) } }
/// A8: coc.h:2320 `decode`, per element type: the whole column, `c->n` elements, into `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_decode_u8(c: *const CCoc, out: *mut u8) { unsafe { enc::decode(&(*c).view(), sl_mut(out, (*c).n)) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_decode_i16(c: *const CCoc, out: *mut i16) { unsafe { enc::decode(&(*c).view(), sl_mut(out, (*c).n)) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_decode_i32(c: *const CCoc, out: *mut i32) { unsafe { enc::decode(&(*c).view(), sl_mut(out, (*c).n)) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_decode_i64(c: *const CCoc, out: *mut i64) { unsafe { enc::decode(&(*c).view(), sl_mut(out, (*c).n)) } }
/// A3: coc.h:860 `coc_sum`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_sum(c: *const CCoc, nul: i64) -> u64 { unsafe { (*c).view() }.sum(nul) }
/// A3: coc.h:858 `coc_sum_blk`, which the float layer's block sums still call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_sum_blk(c: *const CCoc, b: usize, nb: usize) -> u64 { unsafe { (*c).view() }.sum_blk(b, nb) }
/// A3: coc.h:893 `coc_sums_ok`, which `coc_shift` still calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_sums_ok(c: *const CCoc, nul: i64) -> c_int { unsafe { (*c).view() }.sums_ok(nul) as c_int }
/// A3: coc.h:901 `coc_sums_drop`, which `coc_shift` and the float layer's shift still call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_sums_drop(c: *mut CCoc) { unsafe { (*c).view_mut() }.sums_drop() }
/// A3: coc.h:802 `res_count_lt8`, which `res_count_lt` still calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_res_count_lt8(p: *const u8, nb: usize, t: u64) -> usize { crate::res::res_count_lt8(unsafe { sl(p, nb) }, nb, t) }
/// A4: coc.h:934 `coc_prd`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_prd(c: *const CCoc, nul: i64) -> u64 { unsafe { (*c).view() }.prd(nul) }
/// A4: coc.h:964 `coc_any`, which `qlean_coc_over` calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_any(c: *const CCoc) -> c_int { unsafe { (*c).view() }.any() as c_int }
/// A4: coc.h:970 `coc_all`, which `qlean_coc_over` calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_all(c: *const CCoc) -> c_int { unsafe { (*c).view() }.all() as c_int }
/// A4: coc.h:1007 `coc_min`, which `qlean_coc_over` calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_min(c: *const CCoc, nul: i64) -> i64 { unsafe { (*c).view() }.min(nul) }
/// A4: coc.h:1031 `coc_max`, which `qlean_coc_over` calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_max(c: *const CCoc, nul: i64) -> i64 { unsafe { (*c).view() }.max(nul) }
/// A5: coc.h:1554 `cocf_decode`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cocf_decode(f: *const CCocf, b0: usize, b1: usize, out: *mut u8, bytes: usize) {
    unsafe { (*f).view().decode(b0, b1, sl_mut(out, bytes)) }
}
/// A6: coc.h:1304 `coc_shift`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_shift(c: *mut CCoc, k: i64, neg: c_int) { unsafe { (*c).view_mut() }.shift(k, neg != 0) }
/// A10: ids.h:281 `ids_runs`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_runs(p: *const u8, n: usize, w: u32, nd: usize, most: usize, out: *mut i64) -> usize {
    unsafe { ids::runs(sl(p, ids::ids_bytes(n, w)), n, w, nd, most, sl_mut(out, most)) }
}
/// A11: sym.h `sym_msort` over `n` symbols.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sym_msort(v: *const CSym, n: usize, a: *mut usize, tmp: *mut usize) {
    let s: alloc::vec::Vec<&[u8]> = unsafe { sl(v, n) }.iter().map(|x| unsafe { sl(x.p, x.len) }).collect();
    unsafe { sym::sym_msort(&s, sl_mut(a, n), sl_mut(tmp, n)) }
}
/// A12: reduce.c `qlean_over_bytes` past the unboxing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_over_bytes(op: u8, cls: u8, nul: i64, a: *const u8, bytes: usize) -> i64 {
    reduce::over_bytes(op, cls, nul, unsafe { sl(a, bytes) })
}
/// A13: reduce.c `qlean_over_segments`' threaded pass.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_segments(run: unsafe extern "C" fn(), op: u8, cls: u8, nul: i64, offs: *const i64, ng: usize,
                                      src: *const u8, bytes: usize, n: usize, res: *mut i64) {
    unsafe { reduce::segments(rn(run), op, cls, nul, sl(offs, ng + 1), sl(src, bytes), n, sl_mut(res, 2 * ng)) }
}
/// A13: reduce.c `bit_rows_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_bit_rows(run: unsafe extern "C" fn(), all: c_int, w: usize, offs: *const i64, ng: usize,
                                      idx: *const i64, ni: usize, m: *const u8, mbytes: usize, out: *mut u8) {
    unsafe { reduce::bit_rows(rn(run), all != 0, w, sl(offs, ng + 1), sl(idx, ni), sl(m, mbytes), sl_mut(out, (ng * w).div_ceil(8))) }
}
/// A14: scan.c `scan_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_run(op: c_int, kind: c_int, p: *const u8, out: *mut u8, bytes: usize, n: usize,
                                      carry: *mut u8, resume: c_int) {
    // `bytes` is the input's (scan.c:490 `lean_sarray_size(a)`); the answer is `n * sc_out_width` bytes (scan.c:496), and
    // `carry` is `&acc`, an `int64_t` or `uint64_t` (scan.c:517, 570), or null
    unsafe { scan::scan_run(op, kind, sl(p, bytes), sl_mut(out, n * scan::sc_out_width(op, kind)), n, sl_mut(carry, 8), resume != 0) }
}
/// A15: coc.c `coc_decode_run`, 8-byte lanes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_decode(run: unsafe extern "C" fn(), c: *const CCoc, out: *mut i64) {
    unsafe { codec::decode(rn(run), &(*c).view(), sl_mut(out, (*c).n)) }
}
/// A15: coc.c `coc_mask_cmp_run`: a bit per element.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_mask_cmp(run: unsafe extern "C" fn(), op: u8, v: i64, c: *const CCoc, out: *mut u8) {
    unsafe { codec::mask_cmp(rn(run), op, v, &(*c).view(), sl_mut(out, (*c).n.div_ceil(8))) }
}
/// A16: coc.c `coc_enc_for_meta`, C's `blk` step.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_for_meta(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::for_meta(&mut (*s).meta_blk(b), sl(x, nb * w), w, nb) }
}
/// A16: coc.c `coc_enc_for_pack`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_for_pack(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::for_pack(&mut (*s).pack_blk(b, nb), sl(x, nb * w), w) }
}
/// A16: coc.c `coc_enc_alp_meta`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_alp_meta(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::alp_meta(&mut (*s).meta_blk(b), sl(x, nb * w), w, nb) }
}
/// A16: coc.c `coc_enc_alp_pack`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_alp_pack(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::alp_pack(&mut (*s).pack_blk(b, nb), sl(x, nb * w), w) }
}
/// A16: coc.c `src_copy`, a dense block of `bytes` copied to `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_src_copy(out: *mut u8, x: *const u8, bytes: usize) { unsafe { enc::src_copy(sl_mut(out, bytes), sl(x, bytes)) } }
/// A16: coc.c `src_bits`, block `b`'s `nb` bytes packed into the `nbytes`-byte bitmap `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_src_bits(out: *mut u8, nbytes: usize, b: usize, x: *const u8, nb: usize) {
    unsafe { enc::src_bits(sl_mut(out, nbytes), b, sl(x, nb)) }
}
/// A16: coc.h `coc_sumnul`.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_coc_sumnul(width: usize, alp: c_int) -> i64 { enc::coc_sumnul(width, alp != 0) }
/// A17: coc.c `coc_enc_blk_meta` over one block's values.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_blk_meta(s: *mut CEnc, b: usize, v: *const i64, nb: usize) -> u32 {
    unsafe { let w = (*s).width; enc::blk_meta(&mut (*s).meta_blk(b), sl(v, nb), w) }
}
/// A17: coc.c `coc_narrow`; answers `v` itself at eight bytes, else `out` holding the `cnt` narrowed elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_narrow(width: usize, v: *const i64, cnt: usize, out: *mut u8) -> *const u8 {
    unsafe { enc::narrow(width, sl(v, cnt), sl_mut(out, cnt * width)).as_ptr() }
}
/// A17: coc.c `coc_enc_blk_meta` for a caller that holds a `coc` and no encoder (structural.c's append); `c.fdelta` is
/// valid for `b`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_blk_meta_coc(c: *mut CCoc, b: usize, v: *const i64, nb: usize, width: usize) -> u32 {
    let (lb, over, mut nexc) = (AtomicUsize::new(0), AtomicI32::new(0), 0u32);
    unsafe { enc::blk_meta(&mut ccoc_meta(&*c, b, null_mut(), &mut nexc, &lb, &over), sl(v, nb), width) }
}
/// The column `take` answered, as the encoder's form reads it: a Frame of Reference part has only `c` set, its ALP fields
/// (`exp`, `nexc`, ...) being whatever the caller's allocation held.
unsafe fn taken<'a>(f: *const CCocf, alp: bool) -> Cocf<'a> {
    unsafe { if alp { (*f).view() } else { Cocf { c: (*f).c.view(), exp: &[], exc_off: &[], exc_pos: &[], exc_raw: &[], f32: false } } }
}
/// A17: coc.c `move_meta`'s branch for a block `take` claimed (block `pb` of `f`); writes `exc_off[b + 1]`.
// needs A16: `CEnc::meta_blk(b)` is this view
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_move_meta(s: *mut CEnc, b: usize, f: *const CCocf, pb: usize) {
    let (lb, over) = (AtomicUsize::new(0), AtomicI32::new(0));
    unsafe { let s = &*s; enc::move_meta(&mut ccoc_meta(&s.c, b, s.exp, &mut *s.exc_off.add(b + 1), &lb, &over), &taken(f, s.alp != 0), pb); }
}
/// A17: coc.c `move_pack`'s branch for a block `take` claimed. The residual region is the whole `BLK * width / 8`
/// bytes, not the `nb` elements' share: the moved block's pack is copied whole, zero padded.
// needs A16: `CEnc::pack_blk(b, nb)` is this view, with a region of `ceil(nb * width / 8)` bytes
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_move_pack(s: *mut CEnc, b: usize, nb: usize, f: *const CCocf, pb: usize) {
    unsafe {
        let (s, w) = (&*s, *(*s).c.width.add(b));
        let (base, at) = (*s.c.base.add(b), *s.exc_off.add(b) as usize);
        let ne = *s.exc_off.add(b + 1) as usize - at;
        let mut p = enc::EncPack { b, nb, base, frame: (base as u64).wrapping_add(if s.c.fdelta.is_null() { 0 } else { *s.c.fdelta.add(b) }),
                                   width: w, exp: if s.exp.is_null() { 0 } else { *s.exp.add(b) },
                                   res: sl_mut(s.c.pack.add(*s.c.off.add(b) as usize), BLK * w as usize / 8),
                                   pos: sl_mut(s.exc_pos.add(at), ne), raw: sl_mut(s.exc_raw.add(at * s.width), ne * s.width) };
        enc::move_pack(&mut p, &taken(f, s.alp != 0), pb, s.alp != 0, s.width)
    }
}
/// A9: coc.h `alp_patch_blk_f32`; answers the exponent the search would raise the block to, or -1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_patch_blk_f32(o: *const CCocf, b: usize, nb: usize, ix: *const u64, v: *const f32, m: usize,
                                               d: *mut i64, ee: *mut i8) -> c_int {
    unsafe { crate::alp::alp_patch_blk(&(*o).view(), b, nb, sl(ix, m), sl(v, m), sl_mut(d, nb), sl_mut(ee, nb)) }
}
/// A9: coc.h `alp_patch_blk_f64`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_patch_blk_f64(o: *const CCocf, b: usize, nb: usize, ix: *const u64, v: *const f64, m: usize,
                                               d: *mut i64, ee: *mut i8) -> c_int {
    unsafe { crate::alp::alp_patch_blk(&(*o).view(), b, nb, sl(ix, m), sl(v, m), sl_mut(d, nb), sl_mut(ee, nb)) }
}
/// A18: coc.c `alp_decode_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_decode(run: unsafe extern "C" fn(), f: *const CCocf, out: *mut u8, bytes: usize) {
    unsafe { codec::alp_decode(rn(run), &(*f).view(), sl_mut(out, bytes)) }
}
/// A18: coc.c `alp_gather_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_gather(run: unsafe extern "C" fn(), fill: u64, f: *const CCocf, idx: *const i64, n: usize,
                                        out: *mut u8) {
    unsafe { let e = if (*f).f32 != 0 { 4 } else { 8 }; codec::alp_gather(rn(run), fill, &(*f).view(), sl(idx, n), sl_mut(out, n * e)) }
}
// A9: the ALP encoder's per-block steps that need nothing of A7. C reaches them through `coc *` and an exponent array
// the Rust side has no view of (`EncMeta` is A16's), so each is its own entry per element type.
/// A9: coc.h `dat_blk_f32`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_dat_blk_f32(x: *const f32, nb: usize, e: c_int, d: *mut i64, ok: *mut u8) {
    unsafe { crate::alp::dat_blk(sl(x, nb), e, sl_mut(d, nb), sl_mut(ok, nb)) }
}
/// A9: coc.h `dat_blk_f64`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_dat_blk_f64(x: *const f64, nb: usize, e: c_int, d: *mut i64, ok: *mut u8) {
    unsafe { crate::alp::dat_blk(sl(x, nb), e, sl_mut(d, nb), sl_mut(ok, nb)) }
}
/// A9: coc.h `alp_meta_blk_f32`'s exponent search; answers the block exponent.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_exps_f32(x: *const f32, nb: usize, ee: *mut i8) -> c_int {
    unsafe { crate::alp::alp_exps(sl(x, nb), nb, sl_mut(ee, nb)) }
}
/// A9: coc.h `alp_meta_blk_f64`'s exponent search; answers the block exponent.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_exps_f64(x: *const f64, nb: usize, ee: *mut i8) -> c_int {
    unsafe { crate::alp::alp_exps(sl(x, nb), nb, sl_mut(ee, nb)) }
}
/// A9: coc.h `alp_exc_at_f32`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_exc_at_f32(x: *const f32, nb: usize, be: c_int, lim: u32) -> u32 {
    unsafe { crate::alp::alp_exc_at(sl(x, nb), be, lim) }
}
/// A9: coc.h `alp_exc_at_f64`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_exc_at_f64(x: *const f64, nb: usize, be: c_int, lim: u32) -> u32 {
    unsafe { crate::alp::alp_exc_at(sl(x, nb), be, lim) }
}
/// A20: sort.c `grade_keys`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_grade_keys(run: unsafe extern "C" fn(), k: *const u64, n: usize, desc: c_int, mn: u64, mx: u64,
                                        out: *mut i64) {
    unsafe { sort::grade_keys(rn(run), sl(k, n), desc != 0, mn, mx, sl_mut(out, n)) }
}
/// A21: sort.c `grade_narrow`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_grade_narrow(run: unsafe extern "C" fn(), kind: u8, p: *const u8, bytes: usize, n: usize,
                                          desc: c_int, rank: c_int, out: *mut i64) {
    unsafe { sort::grade_narrow(rn(run), kind, sl(p, bytes), n, desc != 0, rank != 0, sl_mut(out, n)) }
}
/// A22: sort.c `order`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_order(run: unsafe extern "C" fn(), kind: u8, desc: c_int, rank: c_int, p: *const u8,
                                   bytes: usize, n: usize, out: *mut i64) {
    unsafe { sort::order(rn(run), kind, desc != 0, rank != 0, sl(p, bytes), n, sl_mut(out, n)) }
}
/// A22: sort.c `order_foR`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_order_enc(run: unsafe extern "C" fn(), kind: u8, desc: c_int, rank: c_int, c: *const CCoc,
                                       out: *mut i64) {
    unsafe { sort::order_enc(rn(run), kind, desc != 0, rank != 0, &(*c).view(), sl_mut(out, (*c).n)) }
}
/// A23: sort.c:3386 `pair_ids_narrow`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pair_ids_narrow(run: unsafe extern "C" fn(), wa: u32, wb: u32, m: usize, pa: *const u8,
                                             pb: *const u8, gid: *mut u8, gbytes: usize, first: *mut usize) -> usize {
    unsafe { sort::pair_ids_narrow(rn(run), wa, wb, m, sl(pa, ids::ids_bytes(m, wa)), sl(pb, ids::ids_bytes(m, wb)),
                                   // sort.c:3386-3391: `first` is `ids_slots(1 << wc, m)`'s `min(m, (1 << wc) + 1)`
                                   sl_mut(gid, gbytes), sl_mut(first, m.min((1usize << ids::id_width(1 << (wa + wb))) + 1))) }
}
/// A24: sort.c `qlean_sort_rank_slices` past the unboxing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_rank_slices(w: usize, v: *const u8, bytes: usize, o: *const i64, ng: usize, out: *mut i64) {
    // sort.c:2487: the answer is one id per group, `g * 8` bytes with `g = ng`
    unsafe { sort::rank_slices(w, sl(v, bytes), sl(o, ng + 1), sl_mut(out, ng)) }
}
/// A25: sort.c `qlean_sort_grade_syms` past the unboxing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_grade_syms(run: unsafe extern "C" fn(), desc: c_int, blob: *const u8, bytes: usize,
                                        offs: *const usize, n: usize, out: *mut i64) {
    unsafe { sort::grade_syms(rn(run), desc != 0, &syms(blob, bytes, offs, n), sl_mut(out, n)) }
}
/// A26: sort.c `qlean_sort_grade_ids` past the unboxing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_grade_ids(run: unsafe extern "C" fn(), desc: c_int, n: usize, blob: *const u8, bytes: usize,
                                       offs: *const usize, nd: usize, p: *const u8, w: u32, out: *mut i64) {
    unsafe { sort::grade_ids(rn(run), desc != 0, n, &syms0(blob, bytes, offs, nd), sl(p, ids::ids_bytes(n, w)), w, sl_mut(out, n)) }
}
/// A26: sort.c `qlean_sort_intern_syms` past the unboxing; answers the distinct count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_intern_syms(blob: *const u8, bytes: usize, offs: *const usize, n: usize, w: u32, out: *mut u8,
                                         first: *mut usize) -> usize {
    unsafe { sort::intern_syms(&syms(blob, bytes, offs, n), w, sl_mut(out, ids::ids_bytes(n, w)), sl_mut(first, n)) }
}
/// A26: sort.c `qlean_sort_distinct_syms` past the unboxing: `first` holds `n` entries; answers the distinct count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_distinct_syms(blob: *const u8, bytes: usize, offs: *const usize, n: usize, first: *mut usize) -> usize {
    unsafe { sort::distinct_syms(&syms(blob, bytes, offs, n), sl_mut(first, n)) }
}
/// A26: sort.c `sym_group` for `qlean_sort_group_syms`: `want` 2 fills `gid`, `cnt` and `first` (`n` entries each);
/// answers the group count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sym_group(blob: *const u8, bytes: usize, offs: *const usize, n: usize, want: c_int, gid: *mut u32,
                                       cnt: *mut u32, first: *mut usize) -> usize {
    let g = unsafe { sort::sym_group(&syms(blob, bytes, offs, n), n, want) };
    unsafe { sl_mut(gid, g.gid.len()).copy_from_slice(&g.gid); sl_mut(cnt, g.cnt.len()).copy_from_slice(&g.cnt) };
    unsafe { sl_mut(first, g.ng).copy_from_slice(&g.first) };
    g.ng
}
/// A26: sort.c `sym_heads`: the symbol at each of the `ng` indices `first`, into `out`; `offs` holds `nd + 1` entries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sym_heads(blob: *const u8, bytes: usize, offs: *const usize, nd: usize, first: *const usize, ng: usize,
                                       out: *mut CSym) {
    let h = unsafe { sort::sym_heads(&syms0(blob, bytes, offs, nd), sl(first, ng)) };
    for (o, s) in unsafe { sl_mut(out, ng) }.iter_mut().zip(h) { *o = CSym { p: s.as_ptr(), len: s.len() } }
}
/// A26: sort.c `ids_heads`: the dictionary symbol of each of the `ng` first rows `first`, into `out`; `nids` ids at `w`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_heads(blob: *const u8, bytes: usize, offs: *const usize, nd: usize, ids: *const u8, nids: usize,
                                       w: u32, first: *const usize, ng: usize, out: *mut CSym) {
    let h = unsafe { sort::ids_heads(&syms0(blob, bytes, offs, nd), sl(ids, ids::ids_bytes(nids, w)), w, sl(first, ng)) };
    for (o, s) in unsafe { sl_mut(out, ng) }.iter_mut().zip(h) { *o = CSym { p: s.as_ptr(), len: s.len() } }
}
/// A26: sort.c `qlean_sort_sorted_ids` past the unboxing: `out` is `ids_bytes(n, w)` zeroed bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sorted_ids(run: unsafe extern "C" fn(), desc: c_int, n: usize, blob: *const u8, bytes: usize,
                                        offs: *const usize, nd: usize, p: *const u8, w: u32, out: *mut u8) {
    unsafe { sort::sorted_ids(rn(run), desc != 0, n, &syms0(blob, bytes, offs, nd), sl(p, ids::ids_bytes(n, w)), w,
                              sl_mut(out, ids::ids_bytes(n, w))) }
}
/// A26: sort.c `ids_group`: `gid` (null for none) is `4n` bytes, `cnt` `nd + 1` entries, `first` `min(n, nd + 1)`;
/// answers the group count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_group(ids: *const u8, n: usize, w: u32, nd: usize, gid: *mut u8, cnt: *mut u32, first: *mut usize) -> usize {
    let g = unsafe { sort::ids_group(sl(ids, ids::ids_bytes(n, w)), n, w, nd, if gid.is_null() { None } else { Some(sl_mut(gid, 4 * n)) },
                                     sl_mut(cnt, nd + 1)) };
    unsafe { sl_mut(first, g.len()).copy_from_slice(&g) };
    g.len()
}
/// A26: sort.c `qlean_sort_parted_ids` past the clamp of `n` to the ids present; `d` is the dictionary size.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_parted_ids(strict: c_int, d: usize, n: usize, w: u32, ids: *const u8) -> c_int {
    unsafe { sort::parted_ids(strict != 0, d, n, w, sl(ids, ids::ids_bytes(n, w))) as c_int }
}
/// A27: sort.c `qlean_sort_grade_guid`: 16-byte elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_grade_guid(run: unsafe extern "C" fn(), desc: c_int, p: *const u8, n: usize, out: *mut i64) {
    unsafe { sort::grade_guid(rn(run), desc != 0, sl(p, 16 * n), sl_mut(out, n)) }
}
/// A28: search.c `coc_srange`: an encoded column's signed range, written to `lo`, `hi`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_srange(c: *const CCoc, lo: *mut i64, hi: *mut i64) {
    unsafe { (*lo, *hi) = search::coc_srange(&(*c).view()) }
}
/// A31: search.c `sym_scan`: the first of `n` symbols equal to `k`, or `n`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sym_scan(blob: *const u8, bytes: usize, offs: *const usize, n: usize, k: *const u8, klen: usize)
    -> usize {
    unsafe { search::sym_scan(&syms(blob, bytes, offs, n), n, sl(k, klen)) }
}
/// A32: search.c `bin` over a dense haystack and dense keys.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_bin(run: unsafe extern "C" fn(), w: usize, is_float: c_int, is_signed: c_int, right: c_int,
                                 hay: *const u8, n: i64, keys: *const u8, m: usize, out: *mut i64) {
    unsafe { search::bin(rn(run), w, is_float != 0, is_signed != 0, right != 0, sl(hay, w * n.max(0) as usize), None, n,
                         sl(keys, w * m), None, m, sl_mut(out, m)) }
}
/// A34: structural.c `reverse_foR_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_reverse_enc(run: unsafe extern "C" fn(), c: *const CCoc, pack: *mut u8) {
    // structural.c:254-257: the answer's pack is the residuals only, `Σ BLK * width / 8`; the source's `packbytes` may
    // be longer (a patch list) or shorter
    unsafe { let v = (*c).view(); structural::reverse_enc(rn(run), &v, sl_mut(pack, v.meta.width.iter().map(|&w| BLK * w as usize / 8).sum())) }
}
/// A35: structural.c `unpack_run`: elements `lo .. lo + cnt` of block `s` (reversed when `rev`) into `dst`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_unpack_run(dst: *mut i64, c: *const CCoc, s: usize, lo: usize, cnt: usize, rev: c_int) {
    unsafe { structural::unpack_run(sl_mut(dst, cnt), &(*c).view(), s, lo, rev != 0) }
}
/// A35: the parts of a concat. `parts` is C's `cocf` array; a part that is not ALP holds only its `c`, the rest of the
/// struct is not set, so it is not read.
unsafe fn cat_parts<'a>(parts: *const CCocf, alp: bool) -> impl Fn(usize) -> Cocf<'a> {
    move |p| unsafe { let f = &*parts.add(p); if alp { f.view() } else { structural::plain(&f.c.view()) } }
}
/// A35: C's `coc_ints` outputs for a block of `cnt` elements; `d` null is pass 1 only.
unsafe fn ints_out<'a>(d: *mut i64, ee: *mut i8, raw: *mut *const c_void, cnt: usize) -> Option<structural::Ints<'a>> {
    if d.is_null() { return None }
    Some(structural::Ints { d: unsafe { sl_mut(d, cnt) }, ee: unsafe { sl_mut(ee, cnt) },
                            raw: if raw.is_null() { None } else { Some(unsafe { sl_mut(raw.cast::<*const u8>(), cnt) }) } })
}
/// A35: structural.c `rev_fill`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_rev_fill(c: *const CCoc, buf: *mut i64, i0: usize, cnt: usize) {
    unsafe { structural::rev_fill(&(*c).view(), sl_mut(buf, cnt), i0) }
}
/// A35: structural.c `cycle_fill`; `off` is below the source's count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cycle_fill(c: *const CCoc, off: usize, m: usize, buf: *mut i64, i0: usize, cnt: usize) {
    unsafe { structural::cycle_fill(&(*c).view(), off, m, sl_mut(buf, cnt), i0) }
}
/// A35: structural.c `shift_fill`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_shift_fill(c: *const CCoc, k: i64, fill: i64, buf: *mut i64, i0: usize, cnt: usize) {
    unsafe { structural::shift_fill(&(*c).view(), k, fill, sl_mut(buf, cnt), i0) }
}
/// A35: structural.c `cat_fill` over the `k` parts (`start` holds `k + 1`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cat_fill(parts: *const CCocf, start: *const usize, k: usize, w: usize, buf: *mut i64, i0: usize,
                                      cnt: usize) {
    unsafe { structural::cat_fill(&cat_parts(parts, false), sl(start, k + 1), w, false, sl_mut(buf, cnt), i0) }
}
/// A35: structural.c `cat_fill_alp`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cat_fill_alp(parts: *const CCocf, start: *const usize, k: usize, w: usize, buf: *mut i64,
                                          i0: usize, cnt: usize) {
    unsafe { structural::cat_fill_alp(&cat_parts(parts, true), sl(start, k + 1), w, sl_mut(buf, cnt), i0) }
}
/// A35: structural.c `rev_fill_alp`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_rev_fill_alp(f: *const CCocf, buf: *mut i64, i0: usize, cnt: usize) {
    unsafe { structural::rev_fill_alp(&(*f).view(), sl_mut(buf, cnt), i0) }
}
/// A35: structural.c `cycle_fill_alp`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cycle_fill_alp(f: *const CCocf, off: usize, m: usize, buf: *mut i64, i0: usize, cnt: usize) {
    unsafe { structural::cycle_fill_alp(&(*f).view(), off, m, sl_mut(buf, cnt), i0) }
}
/// A35: structural.c `shift_fill_alp`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_shift_fill_alp(f: *const CCocf, k: i64, fill: i64, buf: *mut i64, i0: usize, cnt: usize) {
    unsafe { structural::shift_fill_alp(&(*f).view(), k, fill, sl_mut(buf, cnt), i0) }
}
/// A35: structural.c `cat_hint`; -1 is no hint.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cat_hint(parts: *const CCocf, start: *const usize, k: usize, b: usize, lim: *mut u32) -> c_int {
    unsafe { structural::cat_hint(&cat_parts(parts, true), sl(start, k + 1), b, &mut *lim) }
}
/// A35: structural.c `rev_hint`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_rev_hint(f: *const CCocf, b: usize, lim: *mut u32) -> c_int {
    unsafe { structural::rev_hint(&(*f).view(), b, &mut *lim) }
}
/// A35: structural.c `cycle_hint`; `m` is the answer's count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cycle_hint(f: *const CCocf, off: usize, m: usize, b: usize, lim: *mut u32) -> c_int {
    unsafe { structural::cycle_hint(&(*f).view(), off, m, b, &mut *lim) }
}
/// A35: structural.c `shift_hint`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_shift_hint(f: *const CCocf, k: i64, b: usize, lim: *mut u32) -> c_int {
    unsafe { structural::shift_hint(&(*f).view(), k, b, &mut *lim) }
}
/// A35: structural.c `cat_ints`: `d` null is pass 1 only.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cat_ints(parts: *const CCocf, start: *const usize, k: usize, b: usize, d: *mut i64, ee: *mut i8,
                                      raw: *mut *const c_void) -> c_int {
    unsafe {
        let n = *start.add(k);
        let mut o = ints_out(d, ee, raw, (n - b * BLK).min(BLK));
        structural::cat_ints(&cat_parts(parts, true), sl(start, k + 1), b, o.as_mut())
    }
}
/// A35: structural.c `rev_ints`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_rev_ints(f: *const CCocf, b: usize, d: *mut i64, ee: *mut i8, raw: *mut *const c_void) -> c_int {
    unsafe {
        let v = (*f).view();
        let mut o = ints_out(d, ee, raw, structural::blk_count(v.c.meta.n, b));
        structural::rev_ints(&v, b, o.as_mut())
    }
}
/// A35: structural.c `cycle_ints`; `m` is the answer's count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cycle_ints(f: *const CCocf, off: usize, m: usize, b: usize, d: *mut i64, ee: *mut i8,
                                        raw: *mut *const c_void) -> c_int {
    unsafe {
        let mut o = ints_out(d, ee, raw, structural::blk_count(m, b));
        structural::cycle_ints(&(*f).view(), off, m, b, o.as_mut())
    }
}
/// A35: structural.c `shift_ints`' pass 1, the exponent every source block holds; -1 = the general path.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_shift_exp(f: *const CCocf, k: i64, b: usize) -> c_int {
    unsafe { structural::shift_exp(&(*f).view(), k, b) }
}
/// A35: structural.c `shift_ints`' pass 2; a hole is the integer `hd`, `ee` `hx` and the bits at `fill`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_shift_ints(f: *const CCocf, k: i64, b: usize, fill: *const i64, hd: i64, hx: i8, d: *mut i64,
                                        ee: *mut i8, raw: *mut *const c_void) {
    unsafe {
        let v = (*f).view();
        if let Some(mut o) = ints_out(d, ee, raw, structural::blk_count(v.c.meta.n, b)) {
            structural::shift_ints(&v, k, b, (hd, hx, fill.cast::<u8>()), &mut o)
        }
    }
}
/// A36: structural.c `put_res`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_put_res(p: *mut u8, w: u8, lo: usize, v: *const i64, n: usize, base: u64) {
    // structural.c:760 passes block `b` of a pack: `BLK * w / 8` bytes, not `BLK * 8`
    unsafe { structural::put_res(sl_mut(p, BLK * w as usize / 8), w, lo, sl(v, n), base) }
}
/// A36: structural.c `trailer_ok`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_trailer_ok(c: *const CCoc, n: usize, w: usize, alp: c_int) -> c_int {
    unsafe { structural::trailer_ok(&(*c).view(), n, w, alp != 0) as c_int }
}
/// A36: structural.c `cat_take` over the `k` parts: the part that holds answer block `b` whole, its block there in
/// `*pb`, or null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cat_take(parts: *const CCocf, start: *const usize, k: usize, w: usize, alp: c_int, b: usize,
                                      pb: *mut usize) -> *const CCocf {
    unsafe {
        let Some((p, j)) = structural::cat_take(sl(start, k + 1), b) else { return core::ptr::null() };
        if !structural::cat_part_ok(&(*parts.add(p)).c.view(), w, alp != 0) { return core::ptr::null() }
        *pb = j;
        parts.add(p)
    }
}
/// A37: structural.c `gather_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_gather(run: unsafe extern "C" fn(), w: usize, fill: u64, src: *const u8, ns: usize,
                                    idx: *const i64, n: usize, out: *mut u8) {
    unsafe { structural::gather(rn(run), w, fill, sl(src, w * ns), sl(idx, n), sl_mut(out, w * n)) }
}
/// A37: structural.c `gather_foR_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_gather_enc(run: unsafe extern "C" fn(), w: usize, fill: u64, c: *const CCoc, idx: *const i64,
                                        n: usize, out: *mut u8) {
    unsafe { structural::gather_enc(rn(run), w, fill, &(*c).view(), sl(idx, n), sl_mut(out, w * n)) }
}
/// A38: structural.c `expand_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_expand(run: unsafe extern "C" fn(), w: usize, fill: u64, src: *const u8, ns: usize,
                                    wv: *const i64, k: usize, n: usize, out: *mut u8) {
    // `wv` holds `k = size / 8` widths (structural.c `qlean_structural_expand`), which is not `ns` = the source length
    unsafe { structural::expand(rn(run), w, fill, sl(src, w * ns), sl(wv, k), sl_mut(out, w * n)) }
}
/// A38: structural.c `gather_ids_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_gather_ids(run: unsafe extern "C" fn(), w: u32, wout: u32, fill: u64, src: *const u8,
                                        ns: usize, idx: *const i64, n: usize, out: *mut u8) {
    unsafe { structural::gather_ids(rn(run), w, wout, fill, sl(src, ids::ids_bytes(ns, w)), ns, sl(idx, n),
                                    sl_mut(out, ids::ids_bytes(n, wout))) }
}
/// A38: structural.c `gather_ids_foR_run`; `out` is `ids_bytes(c.n, wout)` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_gather_ids_enc(run: unsafe extern "C" fn(), w: u32, wout: u32, fill: u64, src: *const u8,
                                            ns: usize, c: *const CCoc, out: *mut u8) {
    unsafe {
        let v = (*c).view();
        structural::gather_ids_enc(rn(run), w, wout, fill, sl(src, ids::ids_bytes(ns, w)), ns, &v, v.meta.n,
                                   sl_mut(out, ids::ids_bytes(v.meta.n, wout)))
    }
}
/// A38: structural.c `qlean_structural_cycle_ids`: `ids` is `bytes` long, `out` the zeroed `ids_bytes(m, w)`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cycle_ids(n: usize, off: usize, m: usize, w: u32, ids: *const u8, bytes: usize, out: *mut u8) {
    unsafe { structural::cycle_ids(n, off, m, w, sl(ids, bytes), sl_mut(out, ids::ids_bytes(m, w))) }
}
/// A38: structural.c `qlean_structural_rows_of`: `n` longs of `b` as the boxed words `out` holds.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_rows_of(b: *const u8, n: usize, out: *mut i64) {
    unsafe { structural::rows_of(sl(b, n * 8), sl_mut(out, n)); }
}
/// A38: structural.c `qlean_structural_gather_syms`, the blob length: `n` symbols, `m` indices.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_gather_syms_len(blob: *const u8, bytes: usize, offs: *const usize, n: usize,
                                             idx: *const i64, m: usize) -> usize {
    unsafe { structural::gather_syms_len(&syms0(blob, bytes, offs, n), sl(idx, m)) }
}
/// A38: structural.c `qlean_structural_gather_syms`: `total` is `qrs_gather_syms_len`, `no` holds `m + 1` boxed starts.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_gather_syms(blob: *const u8, bytes: usize, offs: *const usize, n: usize, idx: *const i64,
                                         m: usize, nb: *mut u8, total: usize, no: *mut usize) {
    unsafe { structural::gather_syms(&syms0(blob, bytes, offs, n), sl(idx, m), sl_mut(nb, total), sl_mut(no, m + 1)) }
}
/// A39: structural.c `concat_run` over `np` parts.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_concat(run: unsafe extern "C" fn(), p: *const *const u8, len: *const usize, np: usize,
                                    out: *mut u8, bytes: usize) {
    let (ps, ls) = unsafe { (sl(p, np), sl(len, np)) };
    let parts: alloc::vec::Vec<&[u8]> = ps.iter().zip(ls).map(|(&q, &l)| unsafe { sl(q, l) }).collect();
    unsafe { structural::concat(rn(run), &parts, sl_mut(out, bytes)) }
}
/// `n` symbols as `syms`, but an empty dictionary may come with no starts at all (`sym_count`'s case).
unsafe fn syms0<'a>(blob: *const u8, bytes: usize, offs: *const usize, n: usize) -> Syms<'a> {
    if n == 0 { Syms { blob: &[], offs: &[] } } else { unsafe { syms(blob, bytes, offs, n) } }
}
/// A40: structural.c `symtab_fit`'s rehash over the whole symview: the base's `d0` symbols, then the table's
/// `cnt - d0` new ones in `tb` at the starts `to`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_symtab_fill(t: *mut CSymtab, blob: *const u8, bytes: usize, offs: *const usize, d0: usize,
                                         tb: *const u8, to: *const usize) {
    unsafe {
        let t = &mut *t;
        let to = sl(to, if t.cnt > d0 { t.cnt - d0 + 1 } else { 0 });
        let tb = sl(tb, to.last().copied().unwrap_or(0));
        let mut s = structural::Symtab { cnt: t.cnt, mask: t.mask, stale: t.stale, slot: sl_mut(t.slot, t.mask + 1) };
        s.fill(&structural::Symview { base: syms0(blob, bytes, offs, d0), d0, tb, to });
        (t.cnt, t.stale) = (s.cnt, s.stale);
    }
}
/// A40: structural.c `symtab_fork` after the allocation: `t`'s `slot` is `s_mask + 1` ids, filled from `s`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_symtab_fork(t: *mut CSymtab, s: *const u32, s_mask: usize, d: usize) {
    unsafe {
        let t = &mut *t;
        let mut f = structural::Symtab { cnt: t.cnt, mask: t.mask, stale: t.stale, slot: sl_mut(t.slot, s_mask + 1) };
        f.fork(sl(s, s_mask + 1), d);
        (t.cnt, t.mask, t.stale) = (f.cnt, f.mask, f.stale);
    }
}
/// A41a: structural.c `symdict_concat`'s per-part interning; `tb`/`to` are the new-symbol area's `tbn`/`ton`
/// capacity. Answers the index it stopped at (`symtab_fit` is due) or `di`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_symdict_intern(t: *mut CSymtab, blob: *const u8, bytes: usize, offs: *const usize, d0: usize,
                                            tb: *mut u8, tbn: usize, to: *mut usize, ton: usize, pblob: *const u8,
                                            pbytes: usize, poffs: *const usize, di: usize, map: *mut usize,
                                            from: usize) -> usize {
    unsafe {
        let t = &mut *t;
        let mut s = structural::Symtab { cnt: t.cnt, mask: t.mask, stale: t.stale, slot: sl_mut(t.slot, t.mask + 1) };
        let j = structural::symdict_intern(&mut s, &syms0(blob, bytes, offs, d0), d0, sl_mut(tb, tbn), sl_mut(to, ton),
                                           &syms0(pblob, pbytes, poffs, di), sl_mut(map, di), from);
        (t.cnt, t.stale) = (s.cnt, s.stale);
        j
    }
}
/// A41b: structural.c `symtab_find` over the plain dictionary of `d` symbols (`blob`, `offs`): the id of `k` in it,
/// or `d`. `t` is `symdict_probe`'s const table.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_symtab_find(t: *const CSymtab, blob: *const u8, bytes: usize, offs: *const usize, d: usize,
                                         k: *const u8, klen: usize) -> usize {
    unsafe {
        let t = &*t;
        let v = structural::Symview { base: syms0(blob, bytes, offs, d), d0: d, tb: &[], to: &[] };
        structural::symtab_find(sl(t.slot, t.mask + 1), t.mask, &v, d, sl(k, klen))
    }
}
/// A41b: structural.c `symtab_build`'s loop over the plain dictionary of `d` symbols once `t`'s slots are
/// allocated and empty; sets `t->cnt`. 0 when one symbol repeats an earlier one.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_symtab_build(t: *mut CSymtab, blob: *const u8, bytes: usize, offs: *const usize,
                                          d: usize) -> c_int {
    unsafe {
        let t = &mut *t;
        let mut s = structural::Symtab { cnt: t.cnt, mask: t.mask, stale: t.stale, slot: sl_mut(t.slot, t.mask + 1) };
        let v = structural::Symview { base: syms0(blob, bytes, offs, d), d0: d, tb: &[], to: &[] };
        let ok = structural::symtab_build(&mut s, &v, d);
        t.cnt = s.cnt;
        ok as c_int
    }
}
/// A41b: structural.c `til_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_til(run: unsafe extern "C" fn(), out: *mut i64, n: usize) {
    unsafe { structural::til(rn(run), sl_mut(out, n)) }
}
/// A41b: structural.c `scatter`; 0 when an index is out of range.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scatter(wb: usize, dst: *mut u8, nd: usize, idx: *const i64, n: usize, src: *const u8,
                                     soff: usize, bcast: c_int) -> c_int {
    // `wb` is in BYTES here: structural.c calls with `w = wb / 8` from its own bit width; the source holds `soff` + 1 or n
    let ns = soff + if bcast != 0 { 1 } else { n };
    unsafe { structural::scatter(wb, sl_mut(dst, wb * nd), sl(idx, n), sl(src, wb * ns), soff, bcast != 0) as c_int }
}
/// A43: elementwise.c `ew_val_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_val(run: unsafe extern "C" fn(), op: u8, cls: u8, shape: u8, nul: i64, a: *const u8,
                                    abytes: usize, b: *const u8, bbytes: usize, n: usize, out: *mut u8, obytes: usize) {
    unsafe { ew::val(rn(run), op, cls, shape, nul, sl(a, abytes), sl(b, bbytes), n, sl_mut(out, obytes)) }
}
/// A43: elementwise.c `ew_cmp_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_cmp(run: unsafe extern "C" fn(), op: u8, cls: u8, shape: u8, a: *const u8, abytes: usize,
                                    b: *const u8, bbytes: usize, n: usize, out: *mut u8) {
    // elementwise.c:857: the answer is a bit vector, `⌈n / 8⌉` bytes
    unsafe { ew::cmp(rn(run), op, cls, shape, sl(a, abytes), sl(b, bbytes), n, sl_mut(out, n.div_ceil(8))) }
}
/// A44: elementwise.c `ew_mon_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_mon(run: unsafe extern "C" fn(), op: u8, cls: u8, nul: i64, x: *const u8, xbytes: usize,
                                    n: usize, out: *mut u8, obytes: usize) {
    unsafe { ew::mon(rn(run), op, cls, nul, sl(x, xbytes), n, sl_mut(out, obytes)) }
}
/// A44: elementwise.c `qlean_ew_bit`; `n` bits, so `⌈n / 8⌉` answer bytes. An atom operand is `abytes`/`bbytes` = 1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_bit(run: unsafe extern "C" fn(), op: u8, shape: u8, a: *const u8, abytes: usize,
                                    b: *const u8, bbytes: usize, n: usize, out: *mut u8) {
    unsafe { ew::bit(rn(run), op, shape, sl(a, abytes), sl(b, bbytes), n, sl_mut(out, n.div_ceil(8))) }
}
/// A44: elementwise.c `qlean_ew_floor`; the answer is `n` longs.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_floor(run: unsafe extern "C" fn(), cls: u8, nul: i64, x: *const u8, xbytes: usize,
                                      n: usize, out: *mut u8) {
    unsafe { ew::floor(rn(run), cls, nul, sl(x, xbytes), n, sl_mut(out, n * 8)) }
}
/// A44: elementwise.c `qlean_coc_ew_mon`: `neg`/`abs` over an encoded column `c`, the answer dense in `obytes`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_mon_enc(run: unsafe extern "C" fn(), op: u8, cls: u8, nul: i64, c: *const CCoc,
                                        out: *mut u8, obytes: usize) {
    unsafe { ew::mon_enc(rn(run), op, cls, nul, &(*c).view(), sl_mut(out, obytes)) }
}
/// A44: elementwise.c `ew_mon_fill`, the encoder source of `qlean_coc_ew_mon_enc`: the `nb` elements of block
/// `i0 / BLK` of `c`, mapped and widened to `buf`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_mon_fill(op: u8, cls: u8, nul: i64, c: *const CCoc, buf: *mut i64, nb: usize,
                                         i0: usize) {
    unsafe { ew::mon_fill(op, cls, nul, &(*c).view(), sl_mut(buf, nb), i0) }
}
/// A45: elementwise.c `ew_cast_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_cast(run: unsafe extern "C" fn(), src: u8, dst: u8, nul: i64, x: *const u8, xbytes: usize,
                                     n: usize, out: *mut u8, obytes: usize) {
    unsafe { ew::cast(rn(run), src, dst, nul, sl(x, xbytes), n, sl_mut(out, obytes)) }
}
/// A46a: elementwise.c `ew_widen_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_widen(run: unsafe extern "C" fn(), src: u8, dst: u8, nul_in: i64, nul_out: i64,
                                      x: *const u8, xbytes: usize, n: usize, out: *mut u8, obytes: usize) {
    unsafe { ew::widen(rn(run), src, dst, nul_in, nul_out, sl(x, xbytes), n, sl_mut(out, obytes)) }
}
/// A46b: pass.h:502 `qlean_chain_run`'s driver over `k` stages and `n` elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_run_chain(run: unsafe extern "C" fn(), st: *const CStage, k: usize, n: usize, cost: u32,
                                       wide: usize) -> u32 {
    unsafe { c::run_chain(rn(run), sl(st, k), n, cost, wide) }
}
/// A46b: the tiles `[lo, hi)` of a chain on the calling thread, `cp` as `qlean_chain_run` read it (`a` the stages, `op`
/// their count, `n` the elements); `ew_stats_pass` runs its fold chain through it.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_chain_run(lo: usize, hi: usize, cp: *const CPass) { unsafe { c::chain_tiles(lo, hi, cp) } }
/// A46b: elementwise.c `ew_stage_bits`: writes a stage's bits per element of `a`, `b`, `o`; answers its cost.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_stage_bits(engine: u32, op: u32, cls: u32, shape: u32, ab: *mut u16, bb: *mut u16,
                                           ob: *mut u16) -> u32 {
    let (cost, a, b, o) = ew::stage_bits(engine, op, cls, shape);
    unsafe { (*ab, *bb, *ob) = (a, b, o) };
    cost
}
/// A46b: elementwise.c `ew_stage_fixed`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_stage_fixed(engine: u32, shape: u32, left: c_int) -> c_int {
    ew::stage_fixed(engine, shape, left != 0) as c_int
}

#[cfg(test)]
mod tests {
    use super::*;
    // testdata/drv.c encoded a 3000-element column with the C encoder at each element width and dumped the buffers
    // and what coc.h's accessors answered (`col<esz>.txt`): the header, then `blk b frame nexc` and `exc j value`.
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
            sumnul: m.add(32 * mblk).cast(), sumn: m.add(32 * mblk + 8).cast(), width: m.add(32 * mblk + 16),
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
    // decode_blk against the C decoder (testdata/drv.c's col<esz>.dec), block by block, patches applied
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
    #[test] fn views_never_exceed_mblk() {
        let mut c = load(include_bytes!("../testdata/col8.meta"), include_bytes!("../testdata/col8.pack"), include_str!("../testdata/col8.txt"));
        let mut cc = ccoc(&mut c);
        cc.nblk = cc.mblk + 5; // a clamped view may hold fewer blocks, never more slices than the metadata has
        let v = unsafe { cc.view() };
        assert_eq!(v.meta.base.len(), cc.mblk);
        assert!(std::panic::catch_unwind(|| v.frame(cc.mblk)).is_err());
    }
}
