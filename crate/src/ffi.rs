//! Every symbol that leaves the object, and the `#[repr(C)]` mirrors of C structs. A shim does nothing but turn
//! pointer + length into slices (null or zero length gives an empty slice) and call. c/rs.h is generated from
//! this file by cbindgen (rust/build.sh).
use core::ffi::{c_char, c_int};
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
    pub unsafe fn view<'a>(&self) -> Coc<'a> { unimplemented!() }
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
                                     out: *mut u8) {
    unsafe { ids::map(sl(ids, ids::ids_bytes(n, w)), n, w, nd, sl(slot, nd + 1), wo, sl_mut(out, ids::ids_bytes(n, wo))) }
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
/// `qrs_key_range_win`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_group_ids_win(kind: u8, c: *const CCoc, n: usize, mn: u64, mx: u64, gid: *mut u8,
                                           gcap: usize, first: *mut usize) -> usize {
    group::group_ids_win(kind, unsafe { (*c).view() }, n, mn, mx, unsafe { sl_mut(gid, gcap) }, unsafe { sl_mut(first, n) })
}

/// `len` and `off` are `np` entries, `head` `hcap` bytes. Answers the header length, or 0 and `why` filled.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_own_write_head(code: u8, attr: u8, kind: u8, count: u64, nl: usize, len: *const usize,
                                            np: usize, head: *mut u8, hcap: usize, off: *mut usize,
                                            w: *mut c_char, cap: usize) -> usize {
    unsafe { own::write_head(code, attr, kind, count, nl, sl(len, np), sl_mut(head, hcap), sl_mut(off, np),
                             &mut why(w, cap)) }.unwrap_or(0)
}

/// `p` is the block's `BLK * *w / 8` bytes, `buf` `BLK * 8`; answers `p` or `buf`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_lanes(p: *const u8, w: *mut u8, nb: usize, buf: *mut u8) -> *const u8 {
    let w = unsafe { &mut *w };
    unsafe { coc::lanes(sl(p, BLK * *w as usize / 8), w, nb, sl_mut(buf, BLK * 8)) }.as_ptr()
}

macro_rules! decode_blk {
    ($($name:ident: $t:ty),*) => {$(
        /// `decode_blk`: block `b`'s first `nb` elements into `out`.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(c: *const CCoc, b: usize, nb: usize, out: *mut $t) {
            unsafe { (*c).view().decode_blk(b, nb, sl_mut(out, nb)) }
        }
    )*};
}
decode_blk!(qrs_decode_blk_u8: u8, qrs_decode_blk_i16: i16, qrs_decode_blk_i32: i32, qrs_decode_blk_i64: i64);

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
