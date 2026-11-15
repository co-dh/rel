//! Every symbol that leaves the object, and the `#[repr(C)]` mirrors of C structs. A shim does nothing but turn
//! pointer + length into slices (null or zero length gives an empty slice) and call. c/rs.h is generated from
//! this file by cbindgen (rust/build.sh).
use core::ffi::{c_char, c_int};
use core::slice;

use crate::coc::Coc;
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

const _: () = assert!(size_of::<CCoc>() == 144);
const _: () = assert!(size_of::<OwnHead>() == 80);
const _: () = assert!(size_of::<ZTrailer>() == 24);

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
