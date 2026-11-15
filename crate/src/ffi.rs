//! Every symbol that leaves the object, and the `#[repr(C)]` mirrors of C structs. A shim does nothing but turn
//! pointer + length into slices (null or zero length gives an empty slice) and call. c/rs.h is generated from
//! this file by cbindgen (rust/build.sh).
use core::ffi::{c_char, c_int, c_void};
use core::slice;

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
    /// Block `b`'s meta-pass view. Safety: `self` is an open encoder, `b < c.mblk`, no other view of `b` alive.
    pub unsafe fn meta_blk<'a>(&mut self, b: usize) -> EncMeta<'a> { let _ = b; unimplemented!("A16: coc_enc meta view") }
    /// Block `b`'s pack-pass view, after `coc_enc_layout`. Safety: as `meta_blk`.
    pub unsafe fn pack_blk<'a>(&mut self, b: usize, nb: usize) -> EncPack<'a> { let _ = (b, nb); unimplemented!("A16: coc_enc pack view") }
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
    unsafe { simd::res_pack(sl(v, BLK), w, nb, sl_mut(dst, BLK * 8)) }
}
/// A3: coc.h:860 `coc_sum`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_sum(c: *const CCoc, nul: i64) -> u64 { unsafe { (*c).view() }.sum(nul) }
/// A4: coc.h:934 `coc_prd`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_prd(c: *const CCoc, nul: i64) -> u64 { unsafe { (*c).view() }.prd(nul) }
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
    unsafe { reduce::segments(rn(run), op, cls, nul, sl(offs, ng + 1), sl(src, bytes), n, sl_mut(res, ng)) }
}
/// A13: reduce.c `bit_rows_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_bit_rows(run: unsafe extern "C" fn(), all: c_int, w: usize, offs: *const i64, ng: usize,
                                      idx: *const i64, ni: usize, m: *const u8, mbytes: usize, out: *mut u8) {
    unsafe { reduce::bit_rows(rn(run), all != 0, w, sl(offs, ng + 1), sl(idx, ni), sl(m, mbytes), sl_mut(out, ng.div_ceil(8))) }
}
/// A14: scan.c `scan_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_run(op: c_int, kind: c_int, p: *const u8, out: *mut u8, bytes: usize, n: usize,
                                      carry: *mut u8, resume: c_int) {
    unsafe { scan::scan_run(op, kind, sl(p, bytes), sl_mut(out, bytes), n, sl_mut(carry, 16), resume != 0) }
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
/// A17: coc.c `coc_enc_blk_meta` over one block's values.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_blk_meta(s: *mut CEnc, b: usize, v: *const i64, nb: usize) -> u32 {
    unsafe { let w = (*s).width; enc::blk_meta(&mut (*s).meta_blk(b), sl(v, nb), w) }
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
                                   sl_mut(gid, gbytes), sl_mut(first, m)) }
}
/// A24: sort.c `qlean_sort_rank_slices` past the unboxing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_rank_slices(w: usize, v: *const u8, bytes: usize, o: *const i64, ng: usize, out: *mut i64) {
    unsafe { sort::rank_slices(w, sl(v, bytes), sl(o, ng + 1), sl_mut(out, bytes / w.max(1))) }
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
    unsafe { sort::grade_ids(rn(run), desc != 0, n, &syms(blob, bytes, offs, nd), sl(p, ids::ids_bytes(n, w)), w, sl_mut(out, n)) }
}
/// A26: sort.c `qlean_sort_intern_syms` past the unboxing; answers the distinct count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_intern_syms(blob: *const u8, bytes: usize, offs: *const usize, n: usize, w: u32, out: *mut u8,
                                         first: *mut usize) -> usize {
    unsafe { sort::intern_syms(&syms(blob, bytes, offs, n), w, sl_mut(out, ids::ids_bytes(n, w)), sl_mut(first, n)) }
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
    unsafe { structural::reverse_enc(rn(run), &(*c).view(), sl_mut(pack, (*c).packbytes)) }
}
/// A36: structural.c `put_res`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_put_res(p: *mut u8, w: u8, lo: usize, v: *const i64, n: usize, base: u64) {
    unsafe { structural::put_res(sl_mut(p, BLK * 8), w, lo, sl(v, n), base) }
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
                                    wv: *const i64, n: usize, out: *mut u8) {
    unsafe { structural::expand(rn(run), w, fill, sl(src, w * ns), sl(wv, ns), sl_mut(out, w * n)) }
}
/// A38: structural.c `gather_ids_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_gather_ids(run: unsafe extern "C" fn(), w: u32, wout: u32, fill: u64, src: *const u8,
                                        ns: usize, idx: *const i64, n: usize, out: *mut u8) {
    unsafe { structural::gather_ids(rn(run), w, wout, fill, sl(src, ids::ids_bytes(ns, w)), ns, sl(idx, n),
                                    sl_mut(out, ids::ids_bytes(n, wout))) }
}
/// A39: structural.c `concat_run` over `np` parts.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_concat(run: unsafe extern "C" fn(), p: *const *const u8, len: *const usize, np: usize,
                                    out: *mut u8, bytes: usize) {
    let (ps, ls) = unsafe { (sl(p, np), sl(len, np)) };
    let parts: alloc::vec::Vec<&[u8]> = ps.iter().zip(ls).map(|(&q, &l)| unsafe { sl(q, l) }).collect();
    unsafe { structural::concat(rn(run), &parts, sl_mut(out, bytes)) }
}
/// A40: structural.c `symtab_fit` over a plain dictionary of `n` symbols.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_symtab_fill(t: *mut CSymtab, blob: *const u8, bytes: usize, offs: *const usize, n: usize) {
    unsafe {
        let t = &mut *t;
        let mut s = structural::Symtab { cnt: t.cnt, mask: t.mask, stale: t.stale, slot: sl_mut(t.slot, t.mask + 1) };
        s.fill(&structural::Symview { base: syms(blob, bytes, offs, n), d0: n, tb: &[], to: &[] }, n);
        (t.cnt, t.stale) = (s.cnt, s.stale);
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
    let ns = if bcast != 0 { 1 } else { soff + n };
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
    unsafe { ew::cmp(rn(run), op, cls, shape, sl(a, abytes), sl(b, bbytes), n, sl_mut(out, n)) }
}
/// A44: elementwise.c `ew_mon_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_mon(run: unsafe extern "C" fn(), op: u8, cls: u8, nul: i64, x: *const u8, xbytes: usize,
                                    n: usize, out: *mut u8, obytes: usize) {
    unsafe { ew::mon(rn(run), op, cls, nul, sl(x, xbytes), n, sl_mut(out, obytes)) }
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
