//! Every symbol that leaves the object, and the `#[repr(C)]` mirrors of C structs. A shim does nothing but turn
//! pointer + length into slices (null or zero length gives an empty slice) and call. c/rs.h is generated from
//! this file by cbindgen (rust/build.sh).
use core::alloc::Layout;
use core::ffi::{c_char, c_int, c_void};
use core::ptr::null_mut;
use core::slice;
use core::sync::atomic::{AtomicI32, AtomicUsize};

use alloc::borrow::Cow;

use crate::{c, lean};
use crate::coc::{self, Coc};
use crate::group::{self, Table};
use crate::{key, kwin, own};
use crate::layout::{Tail, exc_ok};
use crate::own::{OwnHead, head};
use crate::why::Why;
use crate::{BLK, ids, simd};
use crate::alp::Cocf;
use crate::cocops::CocMut;
use crate::enc::{EncMeta, EncPack, Moves};
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
    /// coc.h documents, for `'a`. Inlined so a caller that reads one field (`qrs_coc_block_start`, called per block)
    /// builds only that slice, not the whole 208-byte view out of line.
    #[inline(always)]
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
/// in sort.c, asserts every field's offset against it.
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

/// Safety: `p` is null or valid for `key::bytes(kind, n)` reads.
unsafe fn keys<'a>(kind: u8, p: *const u8, n: usize) -> Option<&'a [u8]> {
    key::bytes(kind, n).map(|b| unsafe { sl(p, b) })
}

/// `ids` is `bytes` long; `slot` `nd + 1` entries, filled empty here; `first` `min(n, nd + 1)`. Answers the group count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_firsts(ids: *const u8, bytes: usize, n: usize, w: u32, nd: usize, slot: *mut usize,
                                        first: *mut usize) -> usize {
    let slot = unsafe { sl_mut(slot, nd + 1) };
    slot.fill(usize::MAX); // C's `ids_slots` did this memset
    unsafe { ids::firsts(sl(ids, bytes), n, w, nd, slot, sl_mut(first, n.min(nd + 1))) }
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

/// `range_foR`: the key range of C's `kwin` window over `c` (`f` its ALP column, else null).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_kwin_range(kind: u8, c: *const CCoc, f: *const CCocf, mn: *mut u64, mx: *mut u64) {
    let (a, b) = kwin::win_range(kind, &unsafe { (*c).view() }, !f.is_null());
    unsafe { mn.write(a); mx.write(b) }
}

/// `kwin_blk`'s decode: block `b` of `c` as keys into `k` (`BLK` long), through `f` when it is not null
/// (`keys_blk_alp`), else `keys_blk_foR`. Answers the block's key count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_kwin_blk(kind: u8, c: *const CCoc, f: *const CCocf, b: usize, k: *mut u64) -> usize {
    let cv = unsafe { (*c).view() };
    let cnt = (cv.meta.n - b * BLK).min(BLK);
    let k = unsafe { sl_mut(k, BLK) };
    if f.is_null() { kwin::keys_blk(kind, &cv, b, &mut k[..cnt]) } else { kwin::keys_blk_alp(&unsafe { (*f).view() }, b, &mut k[..cnt]) }
    cnt
}

/// `keys_of`: the `n` keys of the dense payload `p` into `k`, and their range into `*mn`, `*mx` (`0, 0` for none).
/// 1 = written, 0 = `kind` is not one of the eight element kinds.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_keys_of(kind: u8, p: *const u8, n: usize, k: *mut u64, mn: *mut u64, mx: *mut u64) -> c_int {
    if kind >= key::SK_KINDS_N { return 0 }
    let (a, b) = sort::keys_of(kind, unsafe { sl(p, key::bytes(kind, n).unwrap_or(0)) }, n, unsafe { sl_mut(k, n) });
    unsafe { mn.write(a); mx.write(b) };
    1
}

/// `ksrc_blk`: block `b` of `n` keys of a `ksrc` (`c` an encoded column, else `p` a dense payload of `kind`) into `k`,
/// `BLK` long. Answers the block's key count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ksrc_blk(kind: u8, p: *const u8, c: *const CCoc, n: usize, b: usize, k: *mut u64) -> usize {
    let s = unsafe { ksrc(kind, p, c, n) };
    s.blk(b, unsafe { sl_mut(k, BLK) })
}

/// `ksrc_range`: the key range of a `ksrc`, `u64::MAX, 0` for none.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ksrc_range(kind: u8, p: *const u8, c: *const CCoc, n: usize, mn: *mut u64, mx: *mut u64) {
    let (a, b) = unsafe { ksrc(kind, p, c, n) }.range();
    unsafe { mn.write(a); mx.write(b) }
}

/// Safety: `c` is null or a live `coc`; else `p` is null or valid for `key::bytes(kind, n)` reads.
unsafe fn ksrc<'a>(kind: u8, p: *const u8, c: *const CCoc, n: usize) -> sort::Ksrc<'a> {
    let c = if c.is_null() { None } else { Some(unsafe { (*c).view() }) };
    sort::Ksrc { kind, p: unsafe { sl(p, if c.is_some() { 0 } else { key::bytes(kind, n).unwrap_or(0) }) }, c, n }
}

/// `ids_run` over `dedup`'s tables: `dtab` (`slots` entries) when not null, else `htab` (`cap` entries) and `gkey`
/// (`ng` entries). `gid` is `n * lane / 8` bytes.  `run` is the pool (`qrs_pool_run`), passed as a `void (*)(void)` and called as `c::Runner`. 1 = written, 0 = refused (a kind outside the enum, `SK_WIN`, a short payload or `gid`, a lane not 8, 16, 32 or 64).
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

/// `groupIds` of a dense column: `gid` is `gcap` bytes, `first` `n` entries, `run` the pool (`qrs_pool_run`) as in `qrs_group_fill`. Answers `ng`, or `SIZE_MAX` for
/// `SK_WIN`, an unknown kind.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_group_ids(kind: u8, p: *const u8, n: usize, mn: u64, mx: u64, gid: *mut u8, gcap: usize,
                                       first: *mut usize, run: unsafe extern "C" fn()) -> usize {
    let Some(b) = (unsafe { keys(kind, p, n) }) else { return usize::MAX };
    group::group_ids(unsafe { core::mem::transmute::<unsafe extern "C" fn(), c::Runner>(run) }, kind, b, n, mn, mx, unsafe { sl_mut(gid, gcap) }, unsafe { sl_mut(first, n) }).unwrap_or(usize::MAX)
}

/// `groupIds` of an encoded column (`qlean_sort_group_ids_foR`): as `qrs_group_ids`, `mn`/`mx` from
/// `qrs_kwin_range`. `SIZE_MAX` = `gid` or `first` too short.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_group_ids_win(kind: u8, c: *const CCoc, n: usize, mn: u64, mx: u64, gid: *mut u8,
                                           gcap: usize, first: *mut usize, run: unsafe extern "C" fn()) -> usize {
    group::group_ids_win(unsafe { core::mem::transmute::<unsafe extern "C" fn(), c::Runner>(run) }, kind, unsafe { (*c).view() }, n, mn, mx, unsafe { sl_mut(gid, gcap) }, unsafe { sl_mut(first, n) }).unwrap_or(usize::MAX)
}

/// K14: sort.c `dedup` for `distinct` (`gid` null) and `group` (`gid` and `cnt` `n` entries each): `first[..ng]` the
/// first occurrence of each distinct key in order of first occurrence, answers `ng`. `c` null: a dense column, `kind`
/// and `p`; else an encoded one read through a window, and `f` its ALP column when not null. `mn`, `mx` the key range.
/// `SIZE_MAX` = an unknown kind or a misaligned `p`, which C never produces.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_dedup(kind: u8, p: *const u8, c: *const CCoc, f: *const CCocf, n: usize, mn: u64, mx: u64,
                                   gid: *mut u32, cnt: *mut u32, first: *mut usize) -> usize {
    let d = group::Dedup { mn, mx, first: unsafe { sl_mut(first, n) },
                           bucket: if gid.is_null() { None } else { Some((unsafe { sl_mut(gid, n) }, unsafe { sl_mut(cnt, n) })) } };
    if c.is_null() {
        let Some(b) = (unsafe { keys(kind, p, n) }) else { return usize::MAX };
        return key::each(kind, b, n, d).unwrap_or(usize::MAX);
    }
    let cv = unsafe { (*c).view() };
    use key::Pass;
    if f.is_null() { d.run(kwin::Kwin::new(kind, cv), n) } else { d.run(kwin::Kwin::with_alp(kind, unsafe { (*f).view() }), n) }
}

/// K14: sort.c `gather`: the `ng` elements of the dense column `p` (`n` of kind `kind`) at `first`, written at their own
/// width into `out` (`ng` bytes of a bit or one-byte kind, else `ng` times its width). 0 = an unknown kind, a short
/// `p`, or an index past `n`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sort_gather(kind: u8, p: *const u8, n: usize, first: *const usize, ng: usize, out: *mut u8) -> c_int {
    let w = if kind == key::SK_BIT { Some(ng) } else { key::bytes(kind, ng) };
    let (Some(b), Some(w)) = (unsafe { keys(kind, p, n) }, w) else { return 0 };
    group::gather(kind, b, unsafe { sl(first, ng) }, unsafe { sl_mut(out, w) }).is_some() as c_int
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
pub unsafe extern "C" fn qrs_coc_std(c: *const CCoc, n: usize) -> c_int {
    unsafe { (*c).view() }.std(n) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_u8_sum(p: *const u8, n: usize) -> i64 { simd::u8_sum(unsafe { sl(p, n) }) }

/// coc.h `res_unpack_agrees`, the self-check `qlean_coc_unpack_agrees` exports.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_res_unpack_agrees(w: u8, nb: usize) -> c_int { crate::res::res_unpack_agrees(w, nb) as c_int }

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
    /// The residual region is the `nb` elements' `ceil(nb * width / 8)` bytes, or with `whole` the full `BLK * width / 8`
    /// (`move_pack` copies a whole block). Safety: as `meta_blk`.
    pub unsafe fn pack_blk<'a>(&mut self, b: usize, nb: usize, whole: bool) -> EncPack<'a> {
        let c = &self.c;
        unsafe {
            let (base, w, at) = (*c.base.add(b), *c.width.add(b), *self.exc_off.add(b) as usize);
            let ne = *self.exc_off.add(b + 1) as usize - at;
            EncPack { b, nb, base, frame: (base as u64).wrapping_add(if c.fdelta.is_null() { 0 } else { *c.fdelta.add(b) }), width: w,
                      exp: if self.exp.is_null() { 0 } else { *self.exp.add(b) },
                      res: sl_mut(c.pack.add(*c.off.add(b) as usize), (if whole { BLK } else { nb } * w as usize).div_ceil(8)),
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
const _: () = assert!(size_of::<CCocf>() == 192 && size_of::<CSrc>() == 40 && size_of::<CEnc>() == 320);
const _: () = assert!(size_of::<CSym>() == 16 && size_of::<CStage>() == 96);

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

/// the pool (`qrs_pool_run`) as the Rust `Runner`, the one cast every column (a) shim makes.
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
/// A8: coc.h:2226 `encode_meta_exc_blk`, per element type.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_exc_blk_u8(c: *mut CCoc, b: usize, x: *const u8, nb: usize) -> u32 { unsafe { meta_exc_blk(c, b, x, nb) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_exc_blk_i16(c: *mut CCoc, b: usize, x: *const i16, nb: usize) -> u32 { unsafe { meta_exc_blk(c, b, x, nb) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_exc_blk_i32(c: *mut CCoc, b: usize, x: *const i32, nb: usize) -> u32 { unsafe { meta_exc_blk(c, b, x, nb) } }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_encode_meta_exc_blk_i64(c: *mut CCoc, b: usize, x: *const i64, nb: usize) -> u32 { unsafe { meta_exc_blk(c, b, x, nb) } }
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
/// K25: coc.h `coc_count_lt`, which `qlean_coc_count_lt` and tools/coc/coc.c call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_count_lt(c: *const CCoc, v: i64) -> usize { unsafe { (*c).view() }.count_lt(v) }
/// K25: coc.h `coc_any_null`, which `qlean_coc_any_null` calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_any_null(c: *const CCoc, nul: i64) -> c_int { unsafe { (*c).view() }.any_null(nul) as c_int }
/// K25: coc.h `cocf_min`, `cocf_max`, `cocf_count_lt` (tools/coc/coc.c's) and `cocf_mask_lt`; `out` is `ceil(n / 64)` words.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cocf_min(f: *const CCocf) -> f64 { unsafe { (*f).view() }.min() }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cocf_max(f: *const CCocf) -> f64 { unsafe { (*f).view() }.max() }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cocf_count_lt(f: *const CCocf, v: f64) -> usize { unsafe { (*f).view() }.count_lt(v) }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cocf_mask_lt(f: *const CCocf, v: f64, out: *mut u64) {
    unsafe { (*f).view().mask_lt(v, sl_mut(out, (*f).c.n.div_ceil(64))) }
}
/// K25: coc.h `cocf_load_blk`: block `b`'s first `nb` elements into `out` (`nb` of the column's element), patches applied.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cocf_load_blk(f: *const CCocf, b: usize, nb: usize, out: *mut u8) {
    unsafe { let f = (*f).view(); f.load_blk(b, nb, sl_mut(out, nb * if f.f32 { 4 } else { 8 })) }
}
/// K25: coc.h `cocf_load_range`: elements `i0 .. i1` of block `b` into `out` at their own places, from the lanes `p`
/// (`cocf_lanes`' answer at lane width `w`) which are read up to element `i1`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cocf_load_range(f: *const CCocf, b: usize, p: *const u8, w: u8, i0: usize, i1: usize, out: *mut u8) {
    unsafe { let f = (*f).view(); f.load_range(b, sl(p, (i1 * w as usize).div_ceil(8)), w, i0, i1, sl_mut(out, i1 * if f.f32 { 4 } else { 8 })) }
}
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
/// A6: coc.h:952 `coc_shift_ok`, which `qlean_coc_shift` calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_shift_ok(c: *const CCoc, k: i64, neg: c_int) -> c_int { unsafe { (*c).view() }.shift_ok(k, neg != 0) }
/// A6: coc.h:1023 `coc_shift`, which `qlean_coc_shift` calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_shift(c: *mut CCoc, k: i64, neg: c_int) { unsafe { (*c).view_mut() }.shift(k, neg != 0) }
/// A11: sym.h `sym_msort` over `n` symbols.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sym_msort(v: *const CSym, n: usize, a: *mut usize, tmp: *mut usize) {
    let s: alloc::vec::Vec<&[u8]> = unsafe { sl(v, n) }.iter().map(|x| unsafe { sl(x.p, x.len) }).collect();
    unsafe { sym::sym_msort(&s, sl_mut(a, n), sl_mut(tmp, n)) }
}
/// K2: reduce.c `qlean_group_cells` past its width check: `n` cells of `ow` bytes (`w`, or 8 for the two averages) at
/// `out`, from the `2 * ng` slots at `m` gathered by the `n` ids at `ord`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_group_cells(kind: u8, w: usize, ow: usize, ng: usize, m: *const i64, ord: *const u64,
                                         n: usize, out: *mut u8) {
    unsafe { reduce::group_cells(kind, w, ng, sl(m, 2 * ng), sl(ord, n), sl_mut(out, n * ow)) }
}
/// Safety: `p` is null or valid for a write of a `usize`.
unsafe fn opt<'a>(p: *mut usize) -> Option<&'a mut usize> { unsafe { p.as_mut() } }
/// A column read through C's block callback `at(src, b, nb, buf)`: a pointer to block `b`'s `nb` elements.
struct CBlocks<T> {
    src: *const c_void,
    at: unsafe extern "C" fn(*const c_void, usize, usize, *mut T) -> *const T,
}
impl<T> reduce::Blocks<T> for CBlocks<T> {
    fn at<'a>(&'a mut self, b: usize, nb: usize, buf: &'a mut [T]) -> &'a [T] {
        // SAFETY: the callback answers a pointer valid for `nb` elements until the next call, as C's callers do
        unsafe { sl((self.at)(self.src, b, nb, buf.as_mut_ptr()), nb) }
    }
}
/// K2: reduce.c `qlean_f32_sum_src`; `live` null or a `size_t`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_f32_sum_src(src: *const c_void,
                                         at: unsafe extern "C" fn(*const c_void, usize, usize, *mut f32) -> *const f32,
                                         n: usize, blk: usize, live: *mut usize) -> f64 {
    reduce::with_buf(blk, |buf| reduce::f32_sum(&mut CBlocks { src, at }, n, blk, buf, unsafe { opt(live) }))
}
/// K2: reduce.c `qlean_f64_sum_src`; `live` null or a `size_t`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_f64_sum_src(src: *const c_void,
                                         at: unsafe extern "C" fn(*const c_void, usize, usize, *mut f64) -> *const f64,
                                         n: usize, blk: usize, live: *mut usize, avg: c_int) -> f64 {
    reduce::with_buf(blk, |buf| reduce::f64_sum(&mut CBlocks { src, at }, n, blk, buf, unsafe { opt(live) }, avg != 0))
}
/// K2: reduce.c `qlean_over_f32_sum` over the `n` floats at `p`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_over_f32_sum(p: *const f32, n: usize, live: *mut usize) -> f64 {
    unsafe { reduce::over_f32_sum(sl(p, n), opt(live)) }
}
/// K2: reduce.c `qlean_over_f64_sum` over the `n` doubles at `p`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_over_f64_sum(p: *const f64, n: usize, live: *mut usize) -> f64 {
    unsafe { reduce::over_f64_sum(sl(p, n), opt(live)) }
}
/// K2: reduce.c `over_f32` (`qlean_over_f32` past the unboxing) over the `n` floats at `p`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_over_f32(op: u8, p: *const f32, n: usize, live: *mut usize) -> f32 {
    unsafe { reduce::over_f32(op, sl(p, n), opt(live)) }
}
/// K2: reduce.c `over_f64` (`qlean_over_f64` past the unboxing) over the `n` doubles at `p`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_over_f64(op: u8, p: *const f64, n: usize, live: *mut usize) -> f64 {
    unsafe { reduce::over_f64(op, sl(p, n), opt(live)) }
}
/// A14: scan.c `scan_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_run(op: c_int, kind: c_int, p: *const u8, out: *mut u8, bytes: usize, n: usize,
                                      carry: *mut u8, resume: c_int) {
    // `bytes` is the input's (scan.c:490 `lean_sarray_size(a)`); the answer is `n * sc_out_width` bytes (scan.c:496), and
    // `carry` is `&acc`, an `int64_t` or `uint64_t` (scan.c:517, 570), or null
    unsafe { scan::scan_run(op, kind, sl(p, bytes), sl_mut(out, n * scan::sc_out_width(op, kind)), n, sl_mut(carry, 8), resume != 0) }
}
/// A14: scan.c `scan_any_null` over the first `n` elements of a payload of `bytes` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_any_null(kind: c_int, p: *const u8, bytes: usize, n: usize) -> c_int {
    unsafe { scan::scan_any_null(kind, sl(p, bytes), n) as c_int }
}
/// A14: scan.c `sc_out_width`: the bytes of one element of the answer of verb `op` at `kind`.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_scan_out_width(op: c_int, kind: c_int) -> usize { scan::sc_out_width(op, kind) }
/// A14: scan.c `sc_fill_const`: `cnt` copies of the low `w` bytes of `acc` at `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_fill_c(out: *mut u8, cnt: usize, w: usize, acc: i64) {
    unsafe { scan::sc_fill_c(sl_mut(out, cnt * w), cnt, w, acc) }
}
/// A14: scan.c `sc_blk_skip` over block `b` of the view `c`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_blk_skip(op: c_int, kind: c_int, c: *const CCoc, b: usize, cnt: usize, acc: i64) -> c_int {
    unsafe { scan::sc_blk_skip(op, kind, &(*c).view(), b, cnt, acc) as c_int }
}
/// A14: scan.c `sc_bad_kind`: the abort for a kind the dispatch never sends; never returns.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_scan_bad_kind(kind: c_int) -> c_int { scan::sc_bad_kind(kind) }
/// A14: scan.c `sc_alp_skip` over block `b` of the ALP column `f`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_alp_skip(op: c_int, f: *const CCocf, b: usize, cnt: usize, acc: f64) -> c_int {
    unsafe { scan::sc_alp_skip(op, &(*f).view(), b, cnt, acc) as c_int }
}
/// K3: scan.c `sc_bits_run` over `nb` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_bits_run(out: *mut u8, p: *const u8, nb: usize, inv: u64) {
    scan::bits_run(unsafe { sl_mut(out, nb) }, unsafe { sl(p, nb) }, inv)
}
/// K3: scan.c `qlean_scan_ema`'s recurrence over the `n` doubles `y`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_ema(abits: u64, y: *const u8, out: *mut u8, n: usize) {
    scan::ema(abits, unsafe { sl(y, 8 * n) }, unsafe { sl_mut(out, 8 * n) })
}
/// K3: scan.c `qlean_scan_ema_v`'s recurrence over the `n` doubles `xy` and `co`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan_ema_v(xy: *const u8, co: *const u8, seedbits: u64, out: *mut u8, n: usize) {
    scan::ema_v(unsafe { sl(xy, 8 * n) }, unsafe { sl(co, 8 * n) }, seedbits, unsafe { sl_mut(out, 8 * n) })
}
/// K3: scan.c `mw_out_width`: the bytes of one element of the answer of window verb `op` at `kind`.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_mw_out_width(op: c_int, kind: c_int) -> usize { scan::mw_out_width(op, kind) }

/// Mirror of scan.c's `mwin`, the state of the window engine that `mw_run` (C until K4) runs on; the rings are
/// allocated by `qrs_mw_open` and freed by `qrs_mw_close`, and C's `typedef CMwin mwin` is the one definition.
#[repr(C)]
pub struct CMwin {
    /// the window, clamped to n + 1 -- past that no lookback ever lands
    pub w: usize,
    /// history cursor: the slot the accumulator after element i lands in
    pub cu: usize,
    /// the history's capacity `w + tl`
    pub cap: usize,
    /// `tl`, the longest chunk a pass runs
    pub tl: usize,
    /// offset inside the current van Herk phase
    pub t: usize,
    /// `+\y` at an integral layout, wrapping the way q's `+` does
    pub isum: u64,
    /// `+\0.0^"f"$y` for the two means, `+\y` with the null skipped for `msum`
    pub fsum: f64,
    /// `+\0.0^"f"$y*y`
    pub fsq: f64,
    /// `+\~^y`
    pub cnt: i64,
    pub ri: *mut u64,
    pub rf: *mut f64,
    pub rq: *mut f64,
    pub rc: *mut i64,
    pub phase: *mut c_void,
    pub sufx: *mut c_void,
    /// the phase's prefix extreme, at the element's own width
    pub extbits: u64,
    /// the extreme of no elements, as bits (`mw_sent`): what a phase's opening `ex` holds again after each close
    pub sent: u64,
    /// the answer's width in bytes, which is the width of `phase` and `sufx`; `qrs_mw_close` sizes them by it
    pub ew: usize,
}
/// `calloc(n, size)` as the C tree's `xcalloc`: a zeroed block, or the run stops saying which buffer and how big.
/// no_std has no `exit`, so the panic handler prints the text and aborts.
unsafe fn zalloc<T>(n: usize, size: usize, what: &str) -> *mut T {
    let p = n.checked_mul(size).and_then(|b| Layout::from_size_align(b, 8).ok()).map_or(null_mut(), |l| unsafe { alloc::alloc::alloc_zeroed(l) });
    if p.is_null() { panic!("qlean: calloc of {n} x {size} bytes for {what} failed") }
    p.cast()
}
unsafe fn zfree<T>(p: *mut T, n: usize, size: usize) {
    if !p.is_null() { unsafe { alloc::alloc::dealloc(p.cast(), Layout::from_size_align_unchecked(n * size, 8)) } }
}
/// K3: scan.c `mw_open`: `st` is zeroed, sized for window `w` over `n` elements, and given the rings `op` reads and
/// nothing more, so a window wider than the column costs one array and not six.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_mw_open(st: *mut CMwin, op: c_int, kind: c_int, w: usize, n: usize) {
    let d = scan::mw_dims(op, kind, w, n);
    let mut s = CMwin { w: d.w, cu: 0, cap: d.cap, tl: d.tl, t: 0, isum: 0, fsum: 0.0, fsq: 0.0, cnt: 0, ri: null_mut(),
                        rf: null_mut(), rq: null_mut(), rc: null_mut(), phase: null_mut(), sufx: null_mut(), extbits: 0,
                        sent: 0, ew: d.ew };
    let f = kind == key::SK_F32 as c_int || kind == key::SK_F64 as c_int;
    unsafe {
        match op {
            scan::MW_MSUM if f => s.rf = zalloc(d.cap, 8, "a msum ring"),
            scan::MW_MSUM => s.ri = zalloc(d.cap, 8, "a msum ring"),
            scan::MW_MCOUNT => s.rc = zalloc(d.cap, 8, "a mcount ring"),
            scan::MW_MAVG => { s.rf = zalloc(d.cap, 8, "a mavg ring"); s.rc = zalloc(d.cap, 8, "a mavg null count") }
            scan::MW_MDEV => {
                s.rf = zalloc(d.cap, 8, "a mdev ring");
                s.rq = zalloc(d.cap, 8, "a mdev square ring");
                s.rc = zalloc(d.cap, 8, "a mdev null count");
            }
            _ => {
                s.phase = zalloc(d.w, d.ew, "a window extreme's phase");
                s.sufx = zalloc(d.w + 1, d.ew, "a window extreme's suffix");
                s.extbits = scan::mw_prime(slice::from_raw_parts_mut(s.sufx.cast::<u8>(), (d.w + 1) * d.ew), op, kind, d.ew);
                s.sent = s.extbits;
            }
        }
        st.write(s);
    }
}
/// K4: scan.c `mw_run`: the window verb `op` over `n` elements of `p` at `kind` into `o`, on the state `st` that
/// `qrs_mw_open` made; the scalars of `st` are written back so the next piece resumes. `p` holds `n` elements at
/// `kind` (a boolean's is the bitmap from element 0 of the piece).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_mw_run(st: *mut CMwin, op: c_int, kind: c_int, p: *const u8, o: *mut u8, n: usize) {
    let s = unsafe { &mut *st };
    let mut m = scan::Mw {
        w: s.w, cu: s.cu, cap: s.cap, tl: s.tl, t: s.t, isum: s.isum, fsum: s.fsum, fsq: s.fsq, cnt: s.cnt, extbits: s.extbits,
        sent: s.sent, ri: unsafe { sl_mut(s.ri, s.cap) }, rf: unsafe { sl_mut(s.rf, s.cap) }, rq: unsafe { sl_mut(s.rq, s.cap) },
        rc: unsafe { sl_mut(s.rc, s.cap) }, phase: unsafe { sl_mut(s.phase.cast::<u8>(), s.w * s.ew) },
        sufx: unsafe { sl_mut(s.sufx.cast::<u8>(), (s.w + 1) * s.ew) },
    };
    scan::mw_run(&mut m, op, kind, unsafe { sl(p, scan::mw_in_bytes(kind, n)) }, unsafe { sl_mut(o, n * scan::mw_out_width(op, kind)) }, n);
    (s.cu, s.t, s.isum, s.fsum, s.fsq, s.cnt, s.extbits) = (m.cu, m.t, m.isum, m.fsum, m.fsq, m.cnt, m.extbits);
}
/// K3: scan.c `mw_close`: frees what `qrs_mw_open` allocated.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_mw_close(st: *mut CMwin) {
    let s = unsafe { &*st };
    unsafe {
        zfree(s.ri, s.cap, 8); zfree(s.rf, s.cap, 8); zfree(s.rq, s.cap, 8); zfree(s.rc, s.cap, 8);
        zfree(s.phase, s.w, s.ew); zfree(s.sufx, s.w + 1, s.ew);
    }
}
/// A15: coc.c `coc_decode_run`, 8-byte lanes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_decode(run: unsafe extern "C" fn(), c: *const CCoc, out: *mut i64) {
    unsafe { codec::decode(rn(run), &(*c).view(), sl_mut(out, (*c).n)) }
}
/// A15: `qrs_coc_decode` at 2-byte lanes (coc.c `qlean_coc_decode_i16`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_decode_i16(run: unsafe extern "C" fn(), c: *const CCoc, out: *mut i16) {
    unsafe { codec::decode(rn(run), &(*c).view(), sl_mut(out, (*c).n)) }
}
/// A15: `qrs_coc_decode` at 4-byte lanes (coc.c `qlean_coc_decode_i32`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_decode_i32(run: unsafe extern "C" fn(), c: *const CCoc, out: *mut i32) {
    unsafe { codec::decode(rn(run), &(*c).view(), sl_mut(out, (*c).n)) }
}
/// A15: coc.c `qlean_coc_block_start` past the unboxing; `c` is a metadata-only view.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_block_start(c: *const CCoc, b: usize) -> usize { unsafe { codec::block_start(&(*c).view().meta, b) } }
/// A15: coc.c `coc_cmp2_run`: the `nd` deep blocks `deep` of `a op b` into the bitmap `out` (`a.n.div_ceil(64)` words).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_cmp2(run: unsafe extern "C" fn(), op: c_int, a: *const CCoc, b: *const CCoc, deep: *const u32, nd: usize, out: *mut u64) {
    unsafe { codec::cmp2(rn(run), op, &(*a).view(), &(*b).view(), sl(deep, nd), sl_mut(out, (*a).n.div_ceil(64))) }
}
/// A15: coc.c `shift_fill` (the encoder's per-block source of `k + x`, `k - x` when `neg`), `cnt` elements from `i0`, nulls
/// staying the null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_shift_fill(c: *const CCoc, k: i64, neg: c_int, buf: *mut i64, i0: usize, cnt: usize) {
    unsafe { codec::shift_fill(&(*c).view(), k, neg != 0, i64::MIN, sl_mut(buf, cnt), i0) }
}
/// A15b: `x <op> v` of a column as a bitmap, a bit per element LSB-first, the whole job (the metadata pass, then the deep
/// blocks threaded on `run`, the pool (`qrs_pool_run`)). `out` is `ceil(n / 64)` words, any contents.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_mask_cmp(run: unsafe extern "C" fn(), op: u8, v: i64, c: *const CCoc, out: *mut u64) {
    unsafe { codec::mask_cmp(rn(run), op, v, &(*c).view(), sl_mut(out, (*c).n.div_ceil(64))) }
}
/// A15b: the metadata pass of `a <op> b` (`b` null: the atom form, `v` the other side): the bitmap `out` (`ceil(n / 64)`
/// words) wherever a block's range settles it, and in `deep` (`nblk` entries) the numbers of the blocks it does not;
/// answers how many.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_cmp_meta(op: c_int, a: *const CCoc, b: *const CCoc, v: i64, deep: *mut u32, out: *mut u64) -> usize {
    unsafe {
        let b = b.as_ref().map(|b| b.view());
        codec::cmp_meta(&(*a).view(), b.as_ref(), op, v, sl_mut(out, (*a).n.div_ceil(64)), sl_mut(deep, (*a).nblk))
    }
}
/// A15b: coc.h `cocf_mask_lt`'s block loop: block `b` of `x <op> ts[b]` into the zeroed bitmap `out`, serial. `ts` is `nblk`
/// thresholds.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_mask_blks(c: *const CCoc, op: c_int, ts: *const i64, out: *mut u64) {
    unsafe { codec::mask_blks(&(*c).view(), op, sl(ts, (*c).nblk), sl_mut(out, (*c).n.div_ceil(64))) }
}
/// A16: coc.c `coc_enc_for_meta`, C's `blk` step.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_for_meta(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::for_meta(&mut (*s).meta_blk(b), sl(x, nb * w), w, nb) }
}
/// A16: coc.c `coc_enc_for_pack`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_for_pack(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::for_pack(&mut (*s).pack_blk(b, nb, false), sl(x, nb * w), w) }
}
/// A16: coc.c `coc_enc_alp_meta`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_alp_meta(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::alp_meta(&mut (*s).meta_blk(b), sl(x, nb * w), w, nb) }
}
/// A16: coc.c `coc_enc_alp_pack`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_enc_alp_pack(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::alp_pack(&mut (*s).pack_blk(b, nb, false), sl(x, nb * w), w) }
}
/// A16: coc.c `src_copy`, a dense block of `bytes` copied to `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_src_copy(out: *mut u8, x: *const u8, bytes: usize) { unsafe { enc::src_copy(sl_mut(out, bytes), sl(x, bytes)) } }
/// A16: coc.c `src_bits`, block `b`'s `nb` bytes packed into the `nbytes`-byte bitmap `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_src_bits(out: *mut u8, nbytes: usize, b: usize, x: *const u8, nb: usize) {
    // BLK is a multiple of 8, so block `b` starts on byte `b * BLK / 8`; the slice is its own bytes only (disjoint across blocks)
    unsafe { let (o, n) = (b * (BLK / 8), nb.div_ceil(8)); assert!(o + n <= nbytes, "qlean src_bits: block {b} of {nb} bytes past the {nbytes}-byte bitmap"); enc::src_bits(sl_mut(out.add(o), n), sl(x, nb)) }
}
/// A16: coc.h `coc_sumnul`.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_coc_sumnul(width: usize, alp: c_int) -> i64 { enc::coc_sumnul(width, alp != 0) }
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
/// A18: coc.c `alp_chunk_run`, blocks `b0 .. b1` of an `f64` column into `buf` (`(b1 - b0) * BLK` doubles).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_chunk(run: unsafe extern "C" fn(), f: *const CCocf, b0: usize, b1: usize, buf: *mut u8) {
    unsafe { codec::alp_chunk(rn(run), &(*f).view(), b0, b1, sl_mut(buf, (b1 - b0) * crate::BLK * 8)) }
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
/// K26: coc.h `coc_popcount`: the set bits among the first `nbits` of `bits`, which holds `nbits.div_ceil(8)` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_popcount(bits: *const u64, nbits: usize) -> usize {
    crate::bits::popcount(unsafe { sl(bits.cast::<u8>(), nbits.div_ceil(8)) }, nbits)
}
/// K26: coc.h `coc_vv_ok`: whether `a op b` (`b` read from `i - s`, `fill` off its ends) rides the encoded forms.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_vv_ok(a: *const CCoc, b: *const CCoc, op: c_int, s: i64, fill: i64) -> c_int {
    unsafe { (*a).view().vv_ok(&(*b).view(), op, s, fill) as c_int }
}
/// K26: coc.h `coc_scale_ok`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_scale_ok(c: *const CCoc, k: i64) -> c_int { unsafe { (*c).view() }.scale_ok(k) as c_int }
/// K26: own.c `own_check`: `p` and `len` are `OWN_MAXPARTS` parts, those past the kind's null/0. 1, or 0 and `why` filled.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_own_check(kind: u8, n: u64, p: *const *const u8, len: *const usize, w: *mut c_char, cap: usize) -> c_int {
    let (p, len) = unsafe { (sl(p, own::OWN_MAXPARTS), sl(len, own::OWN_MAXPARTS)) };
    own::check(kind, n, core::array::from_fn(|k| unsafe { sl(p[k], len[k]) }), &mut unsafe { why(w, cap) }) as c_int
}
/// K26: sym.h `sym_slices`: the first `n` symbols of `blob` (`bytes` long) and the boxed `offs` into `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sym_slices(blob: *const u8, bytes: usize, offs: *const usize, n: usize, out: *mut CSym) {
    let s = unsafe { syms0(blob, bytes, offs, n) };
    for (i, o) in unsafe { sl_mut(out, n) }.iter_mut().enumerate() { let v = s.at(i); *o = CSym { p: v.as_ptr(), len: v.len() } }
}
/// K26: coc.h `alp_offsets`: the per-block patch counts in `exc_off[1..=nblk]` into prefix sums; answers the total.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_offsets(exc_off: *mut u32, nblk: usize) -> usize {
    crate::alp::alp_offsets(unsafe { sl_mut(exc_off, nblk + 1) }, nblk)
}
/// K26: block `b`'s meta view over `c` with the ALP exponent slot `exp`; `body` gets it and the patch count it answers.
unsafe fn alp_meta<R>(c: *mut CCoc, exp: *mut i8, b: usize, body: impl FnOnce(&mut EncMeta) -> R) -> R {
    let (lb, over, mut nexc) = (AtomicUsize::new(0), AtomicI32::new(0), 0u32);
    body(&mut unsafe { ccoc_meta(&*c, b, exp, &mut nexc, &lb, &over) })
}
/// K26: coc.h `alp_fin_blk`: block `b`'s decimals `d` (exponents `ee`) at the block exponent `be` into the integer metadata
/// and `exp[b]`; answers the patch count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_fin_blk(c: *mut CCoc, exp: *mut i8, b: usize, be: c_int, d: *mut i64, ee: *const i8, nb: usize) -> u32 {
    unsafe { alp_meta(c, exp, b, |m| crate::alp::alp_fin_blk(m, be, sl_mut(d, nb), sl(ee, nb), nb)) }
}
/// K26: coc.h `alp_meta_blk_f32`: block `b`'s exponent search and metadata; answers the patch count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_meta_blk_f32(c: *mut CCoc, exp: *mut i8, b: usize, x: *const f32, nb: usize) -> u32 {
    unsafe { alp_meta(c, exp, b, |m| crate::alp::alp_meta_blk(m, sl(x, nb), nb)) }
}
/// K26: coc.h `alp_meta_blk_f64`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_meta_blk_f64(c: *mut CCoc, exp: *mut i8, b: usize, x: *const f64, nb: usize) -> u32 {
    unsafe { alp_meta(c, exp, b, |m| crate::alp::alp_meta_blk(m, sl(x, nb), nb)) }
}
/// K26: coc.h `alp_meta_exp_f32`: block `b`'s metadata at the given exponent `be`, no search.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_meta_exp_f32(c: *mut CCoc, exp: *mut i8, b: usize, x: *const f32, nb: usize, be: c_int) -> u32 {
    unsafe { alp_meta(c, exp, b, |m| crate::alp::alp_meta_exp(m, sl(x, nb), nb, be)) }
}
/// K26: coc.h `alp_meta_exp_f64`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_alp_meta_exp_f64(c: *mut CCoc, exp: *mut i8, b: usize, x: *const f64, nb: usize, be: c_int) -> u32 {
    unsafe { alp_meta(c, exp, b, |m| crate::alp::alp_meta_exp(m, sl(x, nb), nb, be)) }
}
/// A20: sort.c `grade_keys`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_grade_keys(k: *const u64, n: usize, desc: c_int, mn: u64, mx: u64,
                                        out: *mut i64) {
    unsafe { sort::grade_keys(sl(k, n), desc != 0, mn, mx, sl_mut(out, n)) }
}
/// K13: sort.c `sort_values`: the `m` elements of `kind` in `p` (`bytes` long) sorted into `out` (`m` elements of the kind's
/// write width); `m` already clamped to what `p` holds.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sort_values(kind: u8, desc: c_int, m: usize, p: *const u8, bytes: usize, out: *mut u8) {
    let w = if kind == key::SK_BIT { 1 } else { key::bytes(kind, 1).unwrap_or(0) };
    unsafe { sort::sort_values(kind, desc != 0, m, sl(p, bytes), sl_mut(out, m * w)) }
}
/// K12: sort.c `hist_find`: the bucket of the `nb` counts in `cnt` that rank `*r` falls in; `*r` becomes relative to it.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_hist_find(cnt: *const usize, nb: usize, r: *mut usize) -> usize {
    let mut q = unsafe { r.read() };
    let b = sort::hist_find(unsafe { sl(cnt, nb) }, &mut q);
    unsafe { r.write(q) };
    b
}
/// K12: sort.c `select_keys`: the keys at ranks `r1 <= r2 <= r1 + 1` of a `ksrc` into `*k1`, `*k2`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_select_keys(kind: u8, p: *const u8, c: *const CCoc, n: usize, r1: usize, r2: usize,
                                         k1: *mut u64, k2: *mut u64) {
    let (a, b) = sort::select_keys(&unsafe { ksrc(kind, p, c, n) }, r1, r2);
    unsafe { k1.write(a); k2.write(b) }
}
/// K12: sort.c `xrank_src`: `floor(rank * t)` of each of the `n` keys of a `ksrc`, into `out` (`n` entries).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_xrank_src(kind: u8, p: *const u8, c: *const CCoc, n: usize, t: f64, out: *mut i64) {
    sort::xrank_src(&unsafe { ksrc(kind, p, c, n) }, t, unsafe { sl_mut(out, n) })
}
/// A21: sort.c `hist_narrow`: the counts of the `n` keys of a one-byte (`SK_U8`) or two-byte (`SK_I16`) payload into
/// `out`, which holds `SK_NARROW_NB(kind)` of them (256 or 65536).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_hist_narrow(run: unsafe extern "C" fn(), kind: u8, p: *const u8, bytes: usize, n: usize,
                                         out: *mut usize) {
    let h = unsafe { sort::hist_narrow(rn(run), kind, sl(p, bytes), n) };
    unsafe { sl_mut(out, h.len()) }.copy_from_slice(&h)
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
/// A22: sort.c `qlean_sort_ascending`: 1 = ordered, 0 = not. `bytes` is the payload's size, `n` the Lean count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ascending(kind: u8, desc: c_int, strict: c_int, p: *const u8, bytes: usize, n: usize) -> c_int {
    unsafe { sort::ascending(kind, desc != 0, strict != 0, sl(p, bytes), n) as c_int }
}
/// A22: sort.c `qlean_sort_ascending_foR`; `kind` is one of `SK_I16`, `SK_I32`, `SK_I64`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ascending_enc(run: unsafe extern "C" fn(), kind: u8, desc: c_int, strict: c_int, c: *const CCoc) -> c_int {
    unsafe { sort::ascending_enc(rn(run), kind, desc != 0, strict != 0, &(*c).view()) as c_int }
}
/// A22: sort.c `qlean_sort_invert`: `out` is `m` entries, `p` is the `m` of the permutation.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_invert(p: *const i64, m: usize, out: *mut i64) {
    unsafe { sort::invert(sl(p, m), sl_mut(out, m)) }
}
/// A22: sort.c `qlean_sort_grade_lane`: `n` ids at `w` bits in `ids` (`bytes` long), `n` already clamped.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_grade_lane(run: unsafe extern "C" fn(), desc: c_int, w: u32, ids: *const u8, bytes: usize,
                                        n: usize, out: *mut i64) {
    unsafe { sort::grade_lane(rn(run), desc != 0, w, sl(ids, bytes), n, sl_mut(out, n)) }
}
/// A23: sort.c `group_bound`: aborts when `n` rows cannot be numbered in `u32`; for the C callers with no Rust callee.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_group_bound(n: usize) { sort::group_bound(n) }
/// A23: sort.c `ids_keys`: `m` ids at `w` bits as keys into `k` (`m` entries); `*mn`, `*mx` the range.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_keys(v: *const u8, w: u32, m: usize, k: *mut u64, mn: *mut u64, mx: *mut u64) {
    let (a, b) = sort::ids_keys(unsafe { sl(v, ids::ids_bytes(m, w)) }, w, m, unsafe { sl_mut(k, m) });
    unsafe { mn.write(a); mx.write(b) }
}
/// A23: sort.c `pair_ids`: the group of each pair `(x[i], y[i])`, `m` of them, into `gid` (`gbytes` bytes) at
/// `max(8, id_width(ng))` bits; `first` holds `m` entries. Answers `ng`. `x` and `y` are the caller's scratch: both
/// are overwritten (a side narrowed, then the combined key).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pair_ids(run: unsafe extern "C" fn(), x: *mut u64, y: *mut u64, m: usize, mnx: u64, sx: u64,
                                      mny: u64, sy: u64, gid: *mut u8, gbytes: usize, first: *mut usize) -> usize {
    unsafe { sort::pair_ids(rn(run), sl_mut(x, m), sl_mut(y, m), mnx, sx, mny, sy, sl_mut(gid, gbytes), sl_mut(first, m)) }
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
/// A24: sort.c `qlean_sort_group_sizes`: `n` is already clamped to what `gid` holds, `out` is `ng` long.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_group_sizes(ng: usize, w: u32, n: usize, gid: *const u8, out: *mut i64) {
    unsafe { sort::group_sizes(ng, w, n, sl(gid, ids::ids_bytes(n, w)), sl_mut(out, ng)) }
}
/// A24: sort.c `qlean_sort_group_lasts`, as `qrs_group_sizes`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_group_lasts(ng: usize, w: u32, n: usize, gid: *const u8, out: *mut i64) {
    unsafe { sort::group_lasts(ng, w, n, sl(gid, ids::ids_bytes(n, w)), sl_mut(out, ng)) }
}
/// A24: sort.c `qlean_sort_id_longs`: `n` is already clamped to what `ids` holds, `out` is `n` long.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_id_longs(n: usize, w: u32, ids: *const u8, out: *mut i64) {
    unsafe { sort::id_longs(n, w, sl(ids, ids::ids_bytes(n, w)), sl_mut(out, n)) }
}
/// A25: sort.c `qlean_sort_grade_syms` past the unboxing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_grade_syms(desc: c_int, blob: *const u8, bytes: usize,
                                        offs: *const usize, n: usize, out: *mut i64) {
    unsafe { sort::grade_syms(desc != 0, &syms(blob, bytes, offs, n), sl_mut(out, n)) }
}
/// A26: sort.c `qlean_sort_grade_ids` past the unboxing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_grade_ids(desc: c_int, n: usize, blob: *const u8, bytes: usize,
                                       offs: *const usize, nd: usize, p: *const u8, w: u32, out: *mut i64) {
    unsafe { sort::grade_ids(desc != 0, n, &syms0(blob, bytes, offs, nd), sl(p, ids::ids_bytes(n, w)), w, sl_mut(out, n)) }
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
pub unsafe extern "C" fn qrs_sorted_ids(desc: c_int, n: usize, blob: *const u8, bytes: usize,
                                        offs: *const usize, nd: usize, p: *const u8, w: u32, out: *mut u8) {
    unsafe { sort::sorted_ids(desc != 0, n, &syms0(blob, bytes, offs, nd), sl(p, ids::ids_bytes(n, w)), w,
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
pub unsafe extern "C" fn qrs_grade_guid(desc: c_int, p: *const u8, n: usize, out: *mut i64) {
    unsafe { sort::grade_guid(desc != 0, sl(p, 16 * n), sl_mut(out, n)) }
}
/// K16: sort.c `qlean_sort_ascending_syms` past the unboxing: `n` symbols.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ascending_syms(desc: c_int, strict: c_int, blob: *const u8, bytes: usize, offs: *const usize,
                                            n: usize) -> c_int {
    unsafe { sort::ascending_syms(desc != 0, strict != 0, &syms0(blob, bytes, offs, n), n) as c_int }
}
/// K16: sort.c `qlean_sort_ascending_ids` past the clamp of `n`: the dictionary has `nd` symbols, the ids are at `w`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ascending_ids(desc: c_int, strict: c_int, blob: *const u8, bytes: usize, offs: *const usize,
                                           nd: usize, ids: *const u8, w: u32, n: usize) -> c_int {
    unsafe { sort::ascending_ids(desc != 0, strict != 0, &syms0(blob, bytes, offs, nd), sl(ids, ids::ids_bytes(n, w)), w, n) as c_int }
}
/// K16: sort.c `qlean_sort_ascending_guid`: `n` 16-byte guids.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ascending_guid(desc: c_int, strict: c_int, p: *const u8, n: usize) -> c_int {
    unsafe { sort::ascending_guid(desc != 0, strict != 0, sl(p, 16 * n), n) as c_int }
}
/// The bytes of the `ng` symbols `v`.
unsafe fn sym_iter<'a>(v: *const CSym, ng: usize) -> impl Iterator<Item = &'a [u8]> {
    unsafe { sl(v, ng) }.iter().map(|s| unsafe { sl(s.p, s.len) })
}
/// K16: sort.c `syms_at`'s size: the bytes of the `ng` symbols `v`, each with its NUL.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_syms_len(v: *const CSym, ng: usize) -> usize { unsafe { sort::syms_len(sym_iter(v, ng)) } }
/// K16: sort.c `syms_at`: `out` is `qrs_syms_len` bytes, `offs` `ng + 1` words (the data of an `Array Nat`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_syms_at(v: *const CSym, ng: usize, out: *mut u8, offs: *mut usize) {
    unsafe { sort::syms_at(sym_iter(v, ng), sl_mut(out, sort::syms_len(sym_iter(v, ng))), sl_mut(offs, ng + 1)) }
}
/// K16: sort.c `qlean_sort_thin_sweep`: `k` columns `cols` (pointer and byte size), the `nb` boxed `Bool`s `big`, the
/// `ob` bytes of segment offsets `o`, and `mask` of `ceil(n / 8)` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_thin_sweep(cols: *const CSym, k: usize, big: *const usize, nb: usize, o: *const u8, ob: usize, n: usize,
                                        mask: *mut u8) {
    let big: alloc::vec::Vec<bool> = unsafe { sl(big, nb) }.iter().map(|w| w >> 1 != 0).collect();
    let cols: alloc::vec::Vec<&[u8]> = unsafe { sym_iter(cols, k) }.collect();
    unsafe { sort::thin_sweep(&cols, &big, sl(o, ob), n, sl_mut(mask, n.div_ceil(8))) }
}
/// A28: search.c `coc_exc_within`: whether a patch of block `b` lies in `lo ..= hi`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_exc_within(c: *const CCoc, b: usize, lo: i64, hi: i64) -> c_int {
    unsafe { search::coc_exc_within(&(*c).view(), b, lo, hi) as c_int }
}
/// A28: search.c `ids_top`.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_ids_top(lw: u32) -> u64 { search::ids_top(lw) }
/// A28: search.c `opnd_blk` over C's `opnd`: payload `d` (`enc` 0 and 2) or the column `c` (`enc` 1), `n` elements; block
/// `b` at key width `w`. Answers the block, a pointer into `d` or `buf` (BLK * w bytes), and its length in `cnt`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_opnd_blk(d: *const u8, c: *const CCoc, n: usize, enc: c_int, lw: u32, b: usize, w: usize,
                                      buf: *mut u8, cnt: *mut usize) -> *const u8 {
    let r = unsafe { opnd(d, c, n, enc, lw, w) }.blk(b, w, unsafe { sl_mut(buf, crate::BLK * w) });
    unsafe { *cnt = r.len() / w };
    r.as_ptr()
}
/// search.c `opnd` as C holds it: payload `d` (`enc` 0 at key width `w`, `enc` 2 at `lw` bits) or the column `c` (`enc` 1).
/// Safety: as `sl`, for the payload `n` elements need.
unsafe fn opnd<'a>(d: *const u8, c: *const CCoc, n: usize, enc: c_int, lw: u32, w: usize) -> search::Opnd<'a> {
    let src = match enc {
        1 => search::Src::Enc(unsafe { (*c).view() }),
        2 => search::Src::Ids(unsafe { sl(d, ids::ids_bytes(n, lw)) }, lw),
        _ => search::Src::Dense(unsafe { sl(d, n * w) }),
    };
    search::Opnd { src, n }
}
/// A29: search.c `scan_*`: the first index in the dense haystack `h` of `n` keys of each of the `m` needles `x`, or `n`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scan(kind: c_int, h: *const u8, n: usize, x: *const u8, m: usize, out: *mut i64) {
    let kd = search::KINDS[kind as usize];
    let (h, x) = unsafe { (opnd(h, null_mut(), n, 0, 0, kd.width()), opnd(x, null_mut(), m, 0, 0, kd.width())) };
    search::scan_kind(kd, &h, &x, unsafe { sl_mut(out, m) })
}
/// A30: search.c `search`: `x ? h` (`member` 0, `8 * xn` bytes of `Int64`s) or `x in h` (`member` 1, `ceil(xn / 8)` bytes,
/// bit `i` for needle `i`) into `out`, the whole job on `run` (the pool (`qrs_pool_run`)) with no further call back into C.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_search(run: unsafe extern "C" fn(), kind: c_int, hd: *const u8, hc: *const CCoc, hn: usize, henc: c_int,
                                    hlw: u32, xd: *const u8, xc: *const CCoc, xn: usize, xenc: c_int, xlw: u32, member: c_int,
                                    out: *mut u8) {
    let kd = search::KINDS[kind as usize];
    let (h, x) = unsafe { (opnd(hd, hc, hn, henc, hlw, kd.width()), opnd(xd, xc, xn, xenc, xlw, kd.width())) };
    let bytes = if member != 0 { xn.div_ceil(8) } else { xn * 8 };
    search::search(unsafe { rn(run) }, kd, &h, &x, member != 0, unsafe { sl_mut(out, bytes) })
}
/// A30: search.c `ids_key_width`: bytes an id key takes where one side is at `a` bits and the other at `b`.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_ids_key_width(a: usize, b: usize) -> usize { search::ids_key_width(a, b) }
/// A28: search.c `kind_of`: the `kind` enum's number; `who` names the caller in the abort text (null reads as `?`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_kind_of(w: usize, is_float: u8, who: *const c_char) -> c_int {
    let who = if who.is_null() { "?" } else { unsafe { core::ffi::CStr::from_ptr(who) }.to_str().unwrap_or("?") };
    search::kind_of(w, is_float != 0, who) as c_int
}
/// A28: search.c `kind_width` of the `kind` number `k`; a number past the enum answers 8, as the C's `switch` falls out.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_kind_width(k: c_int) -> usize {
    search::KINDS.get(k as usize).map_or(8, |k| k.width())
}
/// A31: search.c `sym_scan`: the first of `n` symbols equal to `k`, or `n`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sym_scan(blob: *const u8, bytes: usize, offs: *const usize, n: usize, k: *const u8, klen: usize)
    -> usize {
    unsafe { search::sym_scan(&syms0(blob, bytes, offs, n), n, sl(k, klen)) }
}
/// `lean_array_size` boxed offsets (`n + 1` for `n` symbols, none for an empty dictionary) as a column.
unsafe fn symcol<'a>(blob: *const u8, bytes: usize, offs: *const usize, noffs: usize) -> Syms<'a> {
    Syms { blob: unsafe { sl(blob, bytes) }, offs: unsafe { sl(offs, noffs) } }
}
/// A31: search.c `sym_search` past the kept hash: the needle column `nb`/`no` (`nno` offsets) against the haystack `hb`/`ho`
/// (`nho` offsets), `bits` 0: `out` is `8 * m` bytes of `Int64`s; `bits` 1: `ceil(m / 8)` zeroed bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sym_search(bits: c_int, nb: *const u8, nbytes: usize, no: *const usize, nno: usize, hb: *const u8,
                                        hbytes: usize, ho: *const usize, nho: usize, out: *mut u8) {
    let (nd, h) = unsafe { (symcol(nb, nbytes, no, nno), symcol(hb, hbytes, ho, nho)) };
    let m = nd.count();
    unsafe { search::sym_search(bits != 0, &nd, &h, sl_mut(out, if bits != 0 { m.div_ceil(8) } else { m * 8 })) }
}
/// A31: search.c `qlean_search_match_ids`' translation: for each of the `na` entries of `a`, its index among the `nb` of `b`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sym_translate(ab: *const u8, abytes: usize, ao: *const usize, na: usize, bb: *const u8,
                                           bbytes: usize, bo: *const usize, nb: usize, tr: *mut usize) {
    unsafe { search::sym_translate(&syms0(ab, abytes, ao, na), na, &syms0(bb, bbytes, bo, nb), nb, sl_mut(tr, na)) }
}
/// K17: search.c `coc_may_hold64`: the blocks `[b0, b0 + k)`, `k <= 64`, of `c` that may hold `v`, as a bit mask.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_may_hold64(c: *const CCoc, b0: usize, k: usize, v: i64) -> u64 {
    search::coc_may_hold64(&unsafe { (*c).view() }, b0, k, v)
}
/// K17: search.c `qlean_search_remap_ids`: `n` ids of `ids` (`idbytes` long, `w` bits) renamed by `map` (`mapbytes` long,
/// `wout` bits), into `out` (`ids_bytes(n, wout)` bytes).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_remap_ids(ids: *const u8, idbytes: usize, n: usize, w: u32, map: *const u8, mapbytes: usize,
                                       wout: u32, out: *mut u8, run: unsafe extern "C" fn()) {
    unsafe {
        search::remap_ids(core::mem::transmute::<unsafe extern "C" fn(), c::Runner>(run), sl(ids, idbytes), n, w, sl(map, mapbytes),
                          wout, sl_mut(out, ids::ids_bytes(n, wout)))
    }
}
/// K17: search.c `ix_alloc`'s size: the bytes of a table for `distinct` keys.
#[unsafe(no_mangle)]
pub extern "C" fn qrs_ix_bytes(distinct: usize) -> usize { search::ix_bytes(distinct) }
/// A table of the index: `bytes` of slots and the rows word, 8-aligned (a Lean scalar array's payload).
/// Safety: as `sl_mut`, for `bytes / 8` words.
unsafe fn ix<'a>(t: *mut u8, bytes: usize) -> &'a mut [u64] { unsafe { sl_mut(t.cast::<u64>(), bytes / 8) } }
/// K17: search.c `ix_alloc`'s fill: every slot empty, no rows hashed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_init(t: *mut u8, bytes: usize) { search::ix_init(unsafe { ix(t, bytes) }) }
/// K17: search.c `qlean_index_hash_build`: how many runs of equal neighbours `n` ids at `w` bits make.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_distinct(p: *const u8, pbytes: usize, w: u32, n: usize) -> usize {
    search::ix_distinct(unsafe { sl(p, pbytes) }, w, n)
}
/// K17: search.c `qlean_index_hash_build`'s fill of the initialised table `t`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_build(t: *mut u8, tbytes: usize, p: *const u8, pbytes: usize, w: u32, n: usize) {
    unsafe { search::ix_build(ix(t, tbytes), sl(p, pbytes), w, n) }
}
/// K17: search.c `qlean_index_hash_find`: `m` needles at `w` bits against the table `t`, `m` answers in `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_find(t: *const u8, tbytes: usize, p: *const u8, pbytes: usize, w: u32, miss: usize, out: *mut i64,
                                     m: usize) {
    unsafe { search::ix_find(sl(t.cast::<u64>(), tbytes / 8), sl(p, pbytes), w, miss, sl_mut(out, m)) }
}
/// K17: search.c `qlean_index_hash_extend`: the `m` keys at `w` bits added as rows `base` on.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_extend(t: *mut u8, tbytes: usize, p: *const u8, pbytes: usize, w: u32, base: usize, m: usize) {
    unsafe { search::ix_extend(ix(t, tbytes), sl(p, pbytes), w, base, m) }
}
/// K17: search.c `ix_room`: 1 when the table `t` (owned, hashing `base` rows) is large enough for `keys` and now hashes
/// them, claimed by compare-and-swap of the rows word -- every value sharing it reads only its own rows, so the claim is
/// all that is needed; 0 when the caller copies it.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_claim(t: *mut u8, tbytes: usize, base: usize, keys: usize) -> c_int {
    let cap = tbytes / 16;
    if cap < 16 || cap < keys + keys / 2 { return 0 }
    let rows = unsafe { core::sync::atomic::AtomicU64::from_ptr(t.add(cap * 16).cast::<u64>()) };
    use core::sync::atomic::Ordering::{AcqRel, Acquire};
    rows.compare_exchange(base as u64, keys as u64, AcqRel, Acquire).is_ok() as c_int
}
/// K17: search.c `ix_room`'s copy of the slots of `src` below `base` into the initialised `dst`, which then hashes `keys`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_rehash(dst: *mut u8, dbytes: usize, src: *const u8, sbytes: usize, base: usize, keys: usize) {
    unsafe { search::ix_rehash(ix(dst, dbytes), sl(src.cast::<u64>(), sbytes / 8), base, keys) }
}
/// A symbol column as the index reads it (search.c `ixsyms`): the blob and its `noffs` offsets, the `idbytes` of ids at `w`
/// bits when `interned`.
/// Safety: as `symcol` and `sl`.
unsafe fn ixsyms<'a>(blob: *const u8, bytes: usize, offs: *const usize, noffs: usize, ids: *const u8, idbytes: usize, w: u32,
                     interned: u8) -> search::IxSyms<'a> {
    search::IxSyms { s: unsafe { symcol(blob, bytes, offs, noffs) }, ids: unsafe { sl(ids, idbytes) }, w, interned: interned != 0 }
}
/// K17: search.c `qlean_index_hash_build_syms`: how many runs of equal neighbouring symbols the first `n` make.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_distinct_syms(blob: *const u8, bytes: usize, offs: *const usize, noffs: usize, ids: *const u8,
                                              idbytes: usize, w: u32, interned: u8, n: usize) -> usize {
    search::ix_distinct_syms(&unsafe { ixsyms(blob, bytes, offs, noffs, ids, idbytes, w, interned) }, n)
}
/// K17: search.c `qlean_index_hash_build_syms`' fill of the initialised table `t`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_build_syms(t: *mut u8, tbytes: usize, blob: *const u8, bytes: usize, offs: *const usize,
                                           noffs: usize, ids: *const u8, idbytes: usize, w: u32, interned: u8, n: usize) {
    unsafe { search::ix_build_syms(ix(t, tbytes), &ixsyms(blob, bytes, offs, noffs, ids, idbytes, w, interned), n) }
}
/// K17: search.c `qlean_index_hash_extend_syms`: rows `base..n` of the column added to `t`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_extend_syms(t: *mut u8, tbytes: usize, blob: *const u8, bytes: usize, offs: *const usize,
                                            noffs: usize, ids: *const u8, idbytes: usize, w: u32, interned: u8, base: usize,
                                            n: usize) {
    unsafe { search::ix_extend_syms(ix(t, tbytes), &ixsyms(blob, bytes, offs, noffs, ids, idbytes, w, interned), base, n) }
}
/// K17: search.c `qlean_index_hash_find_syms`: each of the `nno - 1` symbols of the needle blob `nb`/`no` against `t`, which
/// hashes the column `blob`/`offs`/`ids`; `out` holds them.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ix_find_syms(t: *const u8, tbytes: usize, blob: *const u8, bytes: usize, offs: *const usize,
                                          noffs: usize, ids: *const u8, idbytes: usize, w: u32, interned: u8, nb: *const u8,
                                          nbytes: usize, no: *const usize, nno: usize, miss: usize, out: *mut i64) {
    unsafe {
        let nd = symcol(nb, nbytes, no, nno);
        search::ix_find_syms(sl(t.cast::<u64>(), tbytes / 8), &ixsyms(blob, bytes, offs, noffs, ids, idbytes, w, interned), &nd, miss,
                             sl_mut(out, nd.count()))
    }
}
/// A31: search.c `find_bit` over a payload of `size` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_find_bit(b: *const u8, size: usize, n: usize, needle: u8) -> usize {
    search::find_bit(unsafe { sl(b, size) }, n, needle)
}
/// A31: search.c `qlean_search_find_bit_vec`; `out` holds `m` entries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_find_bit_vec(n: usize, hay: *const u8, hs: usize, ndl: *const u8, ns: usize, m: usize, out: *mut i64) {
    unsafe { search::find_bit_vec(n, sl(hay, hs), sl(ndl, ns), m, sl_mut(out, m)) }
}
/// A31: search.c `qlean_search_bin_bits`; `out` holds `m` entries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_bin_bits(n: usize, hay: *const u8, hs: usize, ndl: *const u8, ns: usize, m: usize, right: u8, out: *mut i64) {
    unsafe { search::bin_bits(n, sl(hay, hs), sl(ndl, ns), m, right != 0, sl_mut(out, m)) }
}
/// A31: search.c `qlean_search_member_bits`; `out` holds `ceil(m / 8)` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_member_bits(m: usize, xs: *const u8, xsz: usize, n: usize, hay: *const u8, hsz: usize, out: *mut u8) {
    unsafe { search::member_bits(m, sl(xs, xsz), n, sl(hay, hsz), sl_mut(out, m.div_ceil(8))) }
}
/// A31: search.c `qlean_search_where_bits`, the count: how many of the first `n` bits of the `size`-byte payload are set.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_where_count(n: usize, bits: *const u8, size: usize) -> usize { search::where_count(n, unsafe { sl(bits, size) }) }
/// A31: search.c `qlean_search_where_bits`, the indices; `out` holds `qrs_where_count` entries. Answers that count.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_where_bits(n: usize, bits: *const u8, size: usize, k: usize, out: *mut i64) -> usize {
    unsafe { search::where_bits(n, sl(bits, size), sl_mut(out, k)) }
}
/// A32: search.c `bin` over a dense haystack and dense keys.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_bin(run: unsafe extern "C" fn(), w: usize, is_float: c_int, is_signed: c_int, right: c_int,
                                 hay: *const u8, n: i64, keys: *const u8, m: usize, out: *mut i64) {
    unsafe { search::bin(rn(run), w, is_float != 0, is_signed != 0, right != 0, sl(hay, w * n.max(0) as usize), None, n,
                         sl(keys, w * m), None, m, sl_mut(out, m)) }
}
/// A32: `qrs_bin` where either side may be an encoded column (`qlean_bin_operands`, `qlean_coc_bin`): `hc` or `kc` non-null
/// is that side's column, and its dense pointer is not read.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_bin_enc(run: unsafe extern "C" fn(), w: usize, is_float: c_int, is_signed: c_int, right: c_int,
                                     hay: *const u8, hc: *const CCoc, n: i64, keys: *const u8, kc: *const CCoc, m: usize,
                                     out: *mut i64) {
    unsafe {
        let (h, k) = (hc.as_ref().map(|c| c.view()), kc.as_ref().map(|c| c.view()));
        search::bin(rn(run), w, is_float != 0, is_signed != 0, right != 0, sl(hay, if h.is_some() { 0 } else { w * n.max(0) as usize }),
                    h.as_ref(), n, sl(keys, if k.is_some() { 0 } else { w * m }), k.as_ref(), m, sl_mut(out, m))
    }
}
/// A33: search.c `find_sorted_run`: `find_sorted` over a dense or encoded (`hc` non-null) haystack of `n` and dense keys.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_find_sorted(run: unsafe extern "C" fn(), w: usize, is_float: c_int, is_signed: c_int, hay: *const u8,
                                         hc: *const CCoc, n: i64, keys: *const u8, m: usize, out: *mut i64) {
    unsafe {
        let h = hc.as_ref().map(|c| c.view());
        search::find_sorted(rn(run), w, is_float != 0, is_signed != 0, sl(hay, if h.is_some() { 0 } else { w * n.max(0) as usize }),
                            h.as_ref(), n, sl(keys, w * m), m, sl_mut(out, m))
    }
}
/// A33: search.c `member_sorted_run`: the bitmap (`m.div_ceil(8)` bytes) of `qrs_find_sorted`'s answers below `n`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_member_sorted(run: unsafe extern "C" fn(), w: usize, is_float: c_int, is_signed: c_int, hay: *const u8,
                                           hc: *const CCoc, n: i64, keys: *const u8, m: usize, out: *mut u8) {
    unsafe {
        let h = hc.as_ref().map(|c| c.view());
        search::member_sorted(rn(run), w, is_float != 0, is_signed != 0, sl(hay, if h.is_some() { 0 } else { w * n.max(0) as usize }),
                              h.as_ref(), n, sl(keys, w * m), m, sl_mut(out, m.div_ceil(8)))
    }
}
/// A33: search.c `qlean_search_bin_ids`: `vals` is `vbytes` long, `ids` holds `n` ids at `w` bits, `keys` and `out` `m` each.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_bin_ids(right: c_int, vals: *const u8, vbytes: usize, n: usize, w: u32, ids: *const u8, keys: *const u8,
                                     m: usize, out: *mut i64) {
    unsafe { search::bin_ids(right != 0, sl(vals, vbytes), n, w, sl(ids, ids::ids_bytes(n, w)), sl(keys, 8 * m), sl_mut(out, m)) }
}
/// A33: search.c `bin_rows`: the haystack is `hay` (`hbytes` long) or the column `hc`; `order` is `obytes` long (0: none),
/// `bounds` `nb` and `gids` `ng` words; `keys` and `out` `m` each.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_bin_rows(run: unsafe extern "C" fn(), w: usize, is_float: c_int, is_signed: c_int, right: c_int,
                                      hay: *const u8, hbytes: usize, hc: *const CCoc, keys: *const u8, order: *const u8, obytes: usize,
                                      bounds: *const i64, nb: usize, gids: *const i64, ng: usize, miss: i64, m: usize, out: *mut i64) {
    unsafe {
        let h = hc.as_ref().map(|c| c.view());
        search::bin_rows(rn(run), w, is_float != 0, is_signed != 0, right != 0, sl(hay, if h.is_some() { 0 } else { hbytes }), h.as_ref(),
                         sl(keys, w * m), sl(order, obytes), sl(bounds, nb), sl(gids, ng), miss, m, sl_mut(out, m))
    }
}
/// A33: search.c `run_starts` over C's `opnd`; `out` holds `n + 1`. Answers the count with the terminator.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_run_starts(d: *const u8, c: *const CCoc, n: usize, enc: c_int, lw: u32, w: usize, is_float: c_int,
                                        out: *mut i64) -> usize {
    unsafe { search::run_starts(&opnd(d, c, n, enc, lw, w), w, is_float != 0, sl_mut(out, n + 1)) }
}
/// A33: search.c `qlean_search_run_starts_ids`; `out` holds `n + 1`. Answers the count with the terminator.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_run_starts_ids(n: usize, w: u32, ids: *const u8, out: *mut i64) -> usize {
    unsafe { search::run_starts_ids(n, w, sl(ids, ids::ids_bytes(n, w)), sl_mut(out, n + 1)) }
}
/// A33: search.c `qlean_search_run_starts_syms` over `n` symbols; `out` holds `n + 1`. Answers the count with the terminator.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_run_starts_syms(blob: *const u8, bytes: usize, offs: *const usize, n: usize, out: *mut i64) -> usize {
    unsafe { search::run_starts_syms(&syms0(blob, bytes, offs, n), sl_mut(out, n + 1)) }
}
/// A33: search.c `qlean_search_run_starts_bits`: `size` bytes of bits for `n` booleans; `out` holds `n + 1`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_run_starts_bits(n: usize, bits: *const u8, size: usize, out: *mut i64) -> usize {
    unsafe { search::run_starts_bits(n, sl(bits, size), sl_mut(out, n + 1)) }
}
/// A34: structural.c `reverse_foR_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_reverse_enc(run: unsafe extern "C" fn(), c: *const CCoc, pack: *mut u8) {
    // structural.c:254-257: the answer's pack is the residuals only, `Σ BLK * width / 8`; the source's `packbytes` may
    // be longer (a patch list) or shorter
    unsafe { let v = (*c).view(); structural::reverse_enc(rn(run), &v, sl_mut(pack, v.meta.width.iter().map(|&w| BLK * w as usize / 8).sum())) }
}
/// A34: structural.c `reverse_foR_move`'s metadata into `out` (`msz` = `33 * c.mblk + 16` bytes); answers the pack's length.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_reverse_meta(c: *const CCoc, out: *mut u8, msz: usize) -> usize {
    unsafe { structural::reverse_meta(&(*c).view(), sl_mut(out, msz)) }
}
/// A34: structural.c `concat_foR_move`: `p` holds the `k` metadata pointers then the `k` pack pointers, `sz` their sizes;
/// `mo`/`po` are the answer's `mosz`/`posz` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_concat_move(p: *const *const u8, sz: *const usize, k: usize, n: usize, w: usize,
                                         mo: *mut u8, mosz: usize, po: *mut u8, posz: usize) {
    unsafe {
        let (p, sz) = (sl(p, 2 * k), sl(sz, 2 * k));
        let v = |r: core::ops::Range<usize>| -> alloc::vec::Vec<&[u8]> { r.map(|i| sl(p[i], sz[i])).collect() };
        structural::concat_move(&v(0..k), &v(k..2 * k), n, w, sl_mut(mo, mosz), sl_mut(po, posz))
    }
}
/// A34: structural.c `concat_foR`'s test over the `k` parts (`ns` their counts); a part that is not ALP holds only its `c`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cat_aligned(part: *const CCocf, k: usize, ns: *const u64, w: usize) -> c_int {
    unsafe { structural::cat_aligned(k, sl(ns, k), w, |i| (*part.add(i)).c.view()) as c_int }
}
/// A34: structural.c `copy_bits`: bits `[from, from + len)` of `b` (`size` bytes) or-ed into `out` (`bytes`) at bit `at`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_copy_bits(out: *mut u8, bytes: usize, at: usize, b: *const u8, size: usize, from: usize, len: usize) {
    unsafe { structural::copy_bits(sl_mut(out, bytes), at, sl(b, size), from, len) }
}
/// A39: structural.c `qlean_structural_cycle_bits`: `out` is the zeroed `bytes = (m + 7) / 8` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_cycle_bits(n: usize, off: usize, m: usize, b: *const u8, size: usize, out: *mut u8, bytes: usize) {
    unsafe { structural::cycle_bits(n, off, m, sl(b, size), sl_mut(out, bytes)) }
}
/// A39: structural.c `qlean_structural_reverse_bits`: `out` is the zeroed `bytes = (n + 7) / 8` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_reverse_bits(n: usize, b: *const u8, size: usize, out: *mut u8, bytes: usize) {
    unsafe { structural::reverse_bits(n, sl(b, size), sl_mut(out, bytes)) }
}
/// A39: structural.c `qlean_structural_shift_bits`: `out` is the zeroed `bytes = (n + 7) / 8` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_shift_bits(n: usize, fill: u64, k: i64, b: *const u8, size: usize, out: *mut u8, bytes: usize) {
    unsafe { structural::shift_bits(n, fill, k, sl(b, size), sl_mut(out, bytes)) }
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
/// A37: structural.c `qlean_structural_all_below` over the `m` indices; 1 when every one, unsigned, is below `n`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_all_below(n: usize, idx: *const i64, m: usize) -> u8 { unsafe { structural::all_below(n, sl(idx, m)) as u8 } }
/// A37: structural.c `gather_foR_idx_run`; `ic` is the encoded index (`ic.n` of them), `out` is `w * ic.n` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_gather_enc_idx(run: unsafe extern "C" fn(), w: usize, fill: u64, c: *const CCoc, ic: *const CCoc,
                                            out: *mut u8) {
    unsafe {
        let (v, iv) = ((*c).view(), (*ic).view());
        structural::gather_enc_idx(rn(run), w, fill, &v, &iv, sl_mut(out, w * iv.meta.n))
    }
}
/// A37: structural.c `gather_bits_run`: `n` is the source's bit count, `bits` its `bytes` bytes, `out` the zeroed
/// `ceil(m / 8)` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_gather_bits(run: unsafe extern "C" fn(), n: usize, bits: *const u8, bytes: usize,
                                         idx: *const i64, m: usize, out: *mut u8) {
    unsafe { structural::gather_bits(rn(run), n, sl(bits, bytes), sl(idx, m), sl_mut(out, m.div_ceil(8))) }
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
        structural::gather_ids_enc(rn(run), w, wout, fill, sl(src, ids::ids_bytes(ns, w)), ns, &v,
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
/// K19: structural.c `qlean_structural_split`'s first pass over delimiter `d` and payload `b`: the cuts.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_split_cuts(d: *const u8, dn: usize, b: *const u8, bn: usize) -> usize {
    unsafe { structural::split_cuts(sl(d, dn), sl(b, bn)) }
}
/// K19: its second pass: `total` payload bytes, `cuts + 2` boxed starts in `offs`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_split(d: *const u8, dn: usize, b: *const u8, bn: usize, out: *mut u8, total: usize,
                                   cuts: usize, offs: *mut usize) {
    unsafe { structural::split(sl(d, dn), sl(b, bn), sl_mut(out, total), sl_mut(offs, cuts + 2)) }
}
/// K19: structural.c `reverse_run`: `n` elements of `w` bytes reversed into `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_reverse(run: unsafe extern "C" fn(), w: usize, src: *const u8, n: usize, out: *mut u8) {
    unsafe { structural::reverse(rn(run), w, sl(src, n * w), n, sl_mut(out, n * w)) }
}
/// K19: structural.c `shift_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_shift(run: unsafe extern "C" fn(), w: usize, fill: u64, k: i64, src: *const u8, n: usize,
                                   out: *mut u8) {
    unsafe { structural::shift(rn(run), w, fill, k, sl(src, n * w), n, sl_mut(out, n * w)) }
}
/// K19: structural.c `translate_run`: `n` bytes through the `tn`-byte table `tab`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_translate(run: unsafe extern "C" fn(), tab: *const u8, tn: usize, src: *const u8, n: usize,
                                       out: *mut u8) {
    unsafe { structural::translate(rn(run), sl(tab, tn), sl(src, n), sl_mut(out, n)) }
}
/// K19: structural.c `ids_place`; `tab` null reads each id as itself, either way an id at or past `nm` reads `0`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ids_place(out: *mut u8, bytes: usize, at: usize, wout: u32, cn: usize, w: u32, pp: *const u8,
                                       ppn: usize, tab: *const usize, nm: usize) {
    unsafe {
        let t = if tab.is_null() { None } else { Some(sl(tab, nm + 1)) };
        structural::ids_place(sl_mut(out, bytes), at, wout, cn, w, sl(pp, ppn), t, nm)
    }
}
/// K19: structural.c `qlean_structural_concat_ids` past the unboxing: `k` parts, their `counts`, `widths`, part and map
/// payloads (`ppn[i]`, `mpn[i]` bytes; a map the array does not reach is null).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_concat_ids(wout: u32, k: usize, counts: *const usize, widths: *const u32, pp: *const *const u8,
                                        ppn: *const usize, mp: *const *const u8, mpn: *const usize, out: *mut u8, bytes: usize) {
    unsafe {
        let rows = |p: *const *const u8, n: *const usize| -> alloc::vec::Vec<&[u8]> {
            sl(p, k).iter().zip(sl(n, k)).map(|(&q, &l)| sl(q, l)).collect()
        };
        structural::concat_ids(wout, sl(counts, k), sl(widths, k), &rows(mp, mpn), &rows(pp, ppn), sl_mut(out, bytes))
    }
}
/// `n` symbols as `syms`, but an empty dictionary may come with no starts at all (`sym_count`'s case).
unsafe fn syms0<'a>(blob: *const u8, bytes: usize, offs: *const usize, n: usize) -> Syms<'a> {
    if n == 0 { Syms { blob: &[], offs: &[] } } else { unsafe { syms(blob, bytes, offs, n) } }
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
/// The one cache of kept dictionary hashes. Safety: structural.c's `sd_mu` is held across every call that reaches it.
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
/// K20: structural.c `symdict_hold`'s find, `sd_mu` held by the caller: the kept table of the dictionary `dict`/`offs`
/// at its own count, or null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sd_find(dict: *mut lean::Object, offs: *mut lean::Object) -> *const sym::Tab {
    unsafe {
        let (c, d) = (&mut *KEPT.0.get(), part(dict, offs).syms.count());
        c.find(Obj(dict), d).map_or(core::ptr::null(), |i| c.table(i))
    }
}
/// K20: structural.c `symdict_probe`: the id of `k` in the plain dictionary `dict`/`offs` through the table `t`, or its
/// symbol count. `sd_mu` is held since `qrs_sd_find` answered `t`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sd_probe(t: *const sym::Tab, dict: *mut lean::Object, offs: *mut lean::Object, k: *const u8,
                                      klen: usize) -> usize {
    unsafe {
        let (t, p) = ((*t).0.borrow(), part(dict, offs));
        let d = p.syms.count();
        structural::symtab_find(&t.slot, t.mask, &structural::Symview { base: p.syms, d0: d, tb: &[], to: &[] }, d, sl(k, klen))
    }
}
/// One part of `qrs_sd_concat`'s input.
#[repr(C)]
pub struct CPart { pub dict: *mut lean::Object, pub offs: *mut lean::Object }
/// What `qrs_sd_concat` answers past the dictionary: the id map of each part (`qrs_sd_map`).
pub struct Plan(sym::Dicts<Obj>);
/// K20: structural.c `symdict_concat`'s dictionary half under `sd_mu`, held by the caller. Null declines; else the
/// joined dictionary and starts (one reference each, the caller's) and its symbol count are written to
/// `dict`/`offs`/`cnt`, and the answer is the plan whose maps `qrs_sd_map` reads, until `qrs_sd_plan_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sd_concat(parts: *const CPart, k: usize, dict: *mut *mut lean::Object,
                                       offs: *mut *mut lean::Object, cnt: *mut usize) -> *mut Plan {
    unsafe {
        let ps: alloc::vec::Vec<_> = sl(parts, k).iter().map(|p| part(p.dict, p.offs)).collect();
        match (&mut *KEPT.0.get()).concat(&ps) {
            None => null_mut(),
            Some(d) => {
                (*dict, *offs, *cnt) = (d.dict.0, d.offs.0, d.cnt);
                alloc::boxed::Box::into_raw(alloc::boxed::Box::new(Plan(d)))
            }
        }
    }
}
/// K20: part `i`'s id map (a 0 past its last), or null for a part whose symbols are the base's own.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sd_map(p: *const Plan, i: usize) -> *const usize {
    unsafe { (&*p).0.maps[i].as_ref().map_or(core::ptr::null(), |m| m.as_ptr()) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_sd_plan_free(p: *mut Plan) { drop(unsafe { alloc::boxed::Box::from_raw(p) }) }
/// K22: structural.c `amend_index` past the width check; `alloc(ctx, which, words)` makes the Lean array `which` (`AmOut`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_amend_index(run: unsafe extern "C" fn(), n: usize, wi: usize, ranked: u8, compact: c_int, idx: *const u8,
                                         bytes: usize, alloc: unsafe extern "C" fn(*mut c_void, c_int, usize) -> *mut i64, ctx: *mut c_void) {
    structural::amend_index(unsafe { rn(run) }, n, wi, ranked != 0, compact != 0, unsafe { sl(idx, bytes) },
                            &mut |o, w| unsafe { sl_mut(alloc(ctx, o as c_int, w), w) })
}
/// A41b: structural.c `scatter`; 0 when an index is out of range.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_scatter(wb: usize, dst: *mut u8, nd: usize, idx: *const i64, n: usize, src: *const u8,
                                     soff: usize, bcast: c_int) -> c_int {
    // `wb` is in BYTES here: structural.c calls with `w = wb / 8` from its own bit width; the source holds `soff` + 1 or n
    let ns = soff + if bcast != 0 { 1 } else { n };
    unsafe { structural::scatter(wb, sl_mut(dst, wb * nd), sl(idx, n), sl(src, wb * ns), soff, bcast != 0) as c_int }
}
/// K21: structural.c `til_fill`, the encoder's block producer for `til`: `buf[j] = i0 + j`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_til_fill(buf: *mut i64, i0: usize, cnt: usize, _ctx: *const c_void) { unsafe { structural::til_fill(sl_mut(buf, cnt), i0) } }
/// K21: structural.c `qlean_structural_string_digits`' count pass over `n` integers of `w` (2, 4 or 8) bytes; `at` has
/// `ceil(n / 4096) + 1` words, the first of which answer where each block's spellings start and the last the blob's length, returned.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_str_count(w: usize, src: *const u8, n: usize, at: *mut usize) -> usize {
    unsafe { structural::str_count(c::pool(), w, sl(src, n * w), n, sl_mut(at, n.div_ceil(structural::STR_BLK) + 1)) }
}
/// K21: the write pass: `blob` is the `at[ceil(n / 4096)]` bytes `qrs_str_count` counted, `offs` `n + 1` boxed offsets.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_str_write(w: usize, src: *const u8, n: usize, at: *const usize, blob: *mut u8, offs: *mut usize) {
    unsafe {
        let at = sl(at, n.div_ceil(structural::STR_BLK) + 1);
        structural::str_write(c::pool(), w, sl(src, n * w), n, at, sl_mut(blob, at[at.len() - 1]), sl_mut(offs, n + 1))
    }
}
/// K21: structural.c `qlean_structural_mmu`'s products: `a` the `n` rows of `m` doubles, `b` the `m` rows of `p`, `out` room for
/// `ceil(n / 4) * 4` rows of `p`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_mmu(a: *const *const u8, n: usize, b: *const *const u8, m: usize, p: usize, out: *mut f64) {
    unsafe {
        let rows = |r: *const *const u8, k: usize, len: usize| sl(r, k).iter().map(|&x| sl(x.cast::<f64>(), len)).collect::<alloc::vec::Vec<_>>();
        structural::mmu(&rows(a, n, m), &rows(b, m, p), p, sl_mut(out, n.div_ceil(4) * 4 * p))
    }
}
/// K21: structural.c `qlean_structural_transpose`'s copy: `cols` the `k` columns of `n` cells of `w` bytes, `out` `n * k * w` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_transpose(w: usize, n: usize, cols: *const *const u8, k: usize, out: *mut u8) {
    unsafe { structural::transpose(w, n, &sl(cols, k).iter().map(|&c| sl(c, n * w)).collect::<alloc::vec::Vec<_>>(), sl_mut(out, n * k * w)) }
}
/// K21: structural.c `qlean_structural_untranspose`'s copy: `src` the `n` rows of `k` cells of `w` bytes into `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_untranspose(w: usize, n: usize, k: usize, src: *const u8, out: *mut u8) {
    unsafe { structural::untranspose(w, n, k, sl(src, n * k * w), sl_mut(out, n * k * w)) }
}
/// K23: structural.c `qlean_structural_scatter_for` / `_alp` past the unboxing (`a` null = Frame of Reference): the writer's
/// parts as the Lean declaration types them, `(meta, pack)` or `(meta, (pack, alp))`. The blocks come from `structural::Scatter`,
/// not from a source, so `NoElts` stands in for the element cursor `src_pass` hands each step.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_structural_scatter(w: usize, m: *const u8, msz: usize, pk: *const u8, pksz: usize, a: *const u8, asz: usize,
                                                n: usize, ix: *const u8, ixsz: usize, vals: *const u8, vsz: usize) -> *mut c_void {
    unsafe {
        let alp = !a.is_null();
        let sc = structural::Scatter::new(c::pool(), w, sl(m, msz), sl(pk, pksz), alp.then(|| sl(a, asz)), n, sl(ix, ixsz), sl(vals, vsz));
        let mut e: CEnc = core::mem::zeroed();
        let s = &raw mut e;
        qrs_coc_enc_open(s, n, w, alp as c_int);
        src_pass(s, &NoElts, &|s, b, _, _| sc.meta(&mut (*s).meta_blk(b), b), true, if alp { crate::QLEAN_COST_MATH } else { crate::QLEAN_COST_ARITH });
        qrs_coc_enc_layout(s);
        src_pass(s, &NoElts, &|s, b, _, nb| sc.pack(&mut (*s).pack_blk(b, nb, sc.kept(b)), b), false, crate::QLEAN_COST_ARITH);
        if !alp { return qrs_coc_enc_pair(s) }
        coc_free((*s).exc_heap.cast());
        mk_pair((*s).meta, mk_pair((*s).pack, (*s).blob))
    }
}
/// K23: `qrs_structural_scatter` has no elements, only block numbers.
struct NoElts;
impl Source for NoElts {
    unsafe fn open(&self) -> Option<*mut c_void> { Some(null_mut()) }
    unsafe fn at(&self, _: *mut c_void, _: usize, _: usize) -> *const u8 { core::ptr::NonNull::dangling().as_ptr() }
    unsafe fn close(&self, _: *mut c_void) {}
    unsafe fn bad(&self) -> bool { false }
}
/// A43: elementwise.c `ew_val_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_val(run: unsafe extern "C" fn(), op: u8, cls: u8, shape: u8, nul: i64, a: *const u8,
                                    abytes: usize, b: *const u8, bbytes: usize, n: usize, out: *mut u8, obytes: usize) {
    unsafe { ew::val(rn(run), op, cls, shape, nul, sl(a, abytes), sl(b, bbytes), n, sl_mut(out, obytes)) }
}
/// K6: elementwise.c `qlean_coc_ew_val`: `op` over two encoded columns of `n` elements, the answer dense in `obytes`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_val_enc(run: unsafe extern "C" fn(), op: u8, cls: u8, nul: i64, a: *const CCoc,
                                        b: *const CCoc, out: *mut u8, obytes: usize) {
    unsafe { ew::val_enc(rn(run), op, cls, nul, &(*a).view(), &(*b).view(), sl_mut(out, obytes)) }
}
/// K6: elementwise.c `qlean_coc_ew_val_atom`: an encoded column and the one-element `atom` (`ew_width(cls)` bytes).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_val_enc_atom(run: unsafe extern "C" fn(), op: u8, cls: u8, shape: u8, nul: i64,
                                             c: *const CCoc, atom: *const u8, out: *mut u8, obytes: usize) {
    unsafe { ew::val_enc_atom(rn(run), op, cls, shape, nul, &(*c).view(), sl(atom, ew::ew_width(cls as u32)), sl_mut(out, obytes)) }
}
/// K6: elementwise.c `qlean_ew_low_zero`: `a` is `n` longs, `b` one; the answer is `⌈n / 8⌉` bytes of bits.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_low_zero(run: unsafe extern "C" fn(), a: *const u8, b: *const u8, n: usize, out: *mut u8) {
    unsafe { ew::low_zero(rn(run), sl(a, n * 8), sl(b, 8), n, sl_mut(out, n.div_ceil(8))) }
}
/// K6: elementwise.c `qlean_coc_low_zero`: as `qrs_ew_low_zero` over an encoded column of `n` longs.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_low_zero_enc(run: unsafe extern "C" fn(), c: *const CCoc, atom: *const u8, n: usize,
                                             out: *mut u8) {
    unsafe { ew::low_zero_enc(rn(run), &(*c).view(), sl(atom, 8), sl_mut(out, n.div_ceil(8))) }
}
/// K6: elementwise.c `qlean_ew_bitw`: `op` 0 and, 1 or, 2 and-not (any other reads as and) over `n` longs.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_bitw(run: unsafe extern "C" fn(), op: u8, a: *const u8, b: *const u8, n: usize, out: *mut u8) {
    unsafe { ew::bitw(rn(run), op, sl(a, n * 8), sl(b, n * 8), n, sl_mut(out, n * 8)) }
}
/// A43: elementwise.c `ew_cmp_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_cmp(run: unsafe extern "C" fn(), op: u8, cls: u8, shape: u8, a: *const u8, abytes: usize,
                                    b: *const u8, bbytes: usize, n: usize, out: *mut u8) {
    // elementwise.c:857: the answer is a bit vector, `⌈n / 8⌉` bytes
    unsafe { ew::cmp(rn(run), op, cls, shape, sl(a, abytes), sl(b, bbytes), n, sl_mut(out, n.div_ceil(8))) }
}
/// K8: elementwise.c `ew_cmp_syms_run`: the symbol columns `ba`/`oa` and `bb`/`ob` (`noa`, `nob` boxed offsets), `out` `⌈n / 8⌉` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_cmp_syms(run: unsafe extern "C" fn(), op: u8, shape: u8, ba: *const u8, bab: usize, oa: *const usize,
                                         noa: usize, bb: *const u8, bbb: usize, ob: *const usize, nob: usize, n: usize, out: *mut u8) {
    unsafe { ew::cmp_syms(rn(run), op, shape, &symcol(ba, bab, oa, noa), &symcol(bb, bbb, ob, nob), n, sl_mut(out, n.div_ceil(8))) }
}
/// K8: elementwise.c `like_*` over a symbol column; 0 (nothing written) where `parsePat` refuses; `out` is `⌈count / 8⌉` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_like_syms(pat: *const u8, pn: usize, blob: *const u8, bytes: usize, offs: *const usize, noffs: usize,
                                          out: *mut u8) -> c_int {
    let s = unsafe { symcol(blob, bytes, offs, noffs) };
    unsafe { ew::like_syms(sl(pat, pn), &s, sl_mut(out, s.count().div_ceil(8))) as c_int }
}
/// K8: elementwise.c `fixed_items` + `fixed_width`: the pattern's width, 0 for each of the three refusals.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_fixed_width(atom: u8, pat: *const u8, pn: usize) -> usize { unsafe { ew::fixed_width(atom != 0, sl(pat, pn)) } }
/// K8: elementwise.c `fixed_scan`: the match starts into `h` (`n / w + 1` entries, `w` the width above); answers how many.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_fixed_scan(atom: u8, pat: *const u8, pn: usize, b: *const u8, n: usize, h: *mut i64, hcap: usize) -> usize {
    unsafe { ew::fixed_scan(atom != 0, sl(pat, pn), sl(b, n), sl_mut(h, hcap)) }
}
/// K8: elementwise.c `qlean_ew_ssr`'s copy loop: `o` is `total + 16` bytes (the answer and 16 of slack).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_ssr_fill(o: *mut u8, olen: usize, b: *const u8, n: usize, h: *const i64, hits: usize, w: usize,
                                         t: *const u8, tn: usize) {
    unsafe { ew::ssr_fill(sl_mut(o, olen), sl(b, n), sl(h, hits), w, sl(t, tn)) }
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
pub unsafe extern "C" fn qrs_ew_floor(run: unsafe extern "C" fn(), cls: u8, x: *const u8, xbytes: usize,
                                      n: usize, out: *mut u8) {
    unsafe { ew::floor(rn(run), cls, sl(x, xbytes), n, sl_mut(out, n * 8)) }
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
/// A45: elementwise.c `ew_tick_run`, the chain's time-unit stage: `op` is the source unit's code times 16 plus the
/// target's, `src`/`dst` the two classes, `nul_in`/`nul_out` the two nulls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_tick(run: unsafe extern "C" fn(), op: u8, src: u8, dst: u8, nul_in: i64, nul_out: i64,
                                     x: *const u8, xbytes: usize, n: usize, out: *mut u8, obytes: usize) {
    unsafe { ew::tick(rn(run), op, src, dst, nul_in, nul_out, sl(x, xbytes), n, sl_mut(out, obytes)) }
}
/// K7: elementwise.c `ew_eq_ids_run`; `out` is `⌈n / 8⌉` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_eq_ids(run: unsafe extern "C" fn(), op: u8, shape: u8, ia: *const u8, iabytes: usize,
                                       ib: *const u8, ibbytes: usize, w: u32, n: usize, out: *mut u8) {
    unsafe { ew::eq_ids(rn(run), op, shape, sl(ia, iabytes), sl(ib, ibbytes), w, n, sl_mut(out, n.div_ceil(8))) }
}
/// K7: elementwise.c `ew_cmp_ids_run`; `ra`, `rb` hold `nra`, `nrb` ranks.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_cmp_ids(run: unsafe extern "C" fn(), op: u8, shape: u8, ra: *const i32, nra: usize,
                                        ia: *const u8, iabytes: usize, wa: u32, rb: *const i32, nrb: usize,
                                        ib: *const u8, ibbytes: usize, wb: u32, n: usize, out: *mut u8) {
    unsafe {
        ew::cmp_ids(rn(run), op, shape, sl(ra, nra), sl(ia, iabytes), wa, sl(rb, nrb), sl(ib, ibbytes), wb, n,
                    sl_mut(out, n.div_ceil(8)))
    }
}
/// K7: elementwise.c `ew_cmp_key_run`; `tab` is `d + 1` verdict bytes, or null where the verb is `=`/`<>`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_cmp_ids_key(run: unsafe extern "C" fn(), op: u8, ids: *const u8, idbytes: usize, w: u32,
                                            n: usize, na: usize, e: usize, d: usize, past: c_int, tab: *const u8,
                                            out: *mut u8) {
    let tab = if tab.is_null() { None } else { Some(unsafe { sl(tab, d + 1) }) };
    unsafe { ew::cmp_key(rn(run), op, sl(ids, idbytes), w, n, na, e, d, past != 0, tab, sl_mut(out, n.div_ceil(8))) }
}
/// A46a: elementwise.c `ew_widen_run`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_widen(run: unsafe extern "C" fn(), src: u8, dst: u8, nul_in: i64, nul_out: i64,
                                      x: *const u8, xbytes: usize, n: usize, out: *mut u8, obytes: usize) {
    unsafe { ew::widen(rn(run), src, dst, nul_in, nul_out, sl(x, xbytes), n, sl_mut(out, obytes)) }
}
/// P1: pass.h's `qlean_run`, worker `f` (a `qlean_worker`) over its `qlean_pass` `p` on the pool (`pool::run_c`);
/// answers the slice count. `f` and `p` are untyped so pass.h, which comes before `CPass`, declares this prototype.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_pool_run(f: unsafe extern "C" fn(), n: usize, cost: u32, wide: usize, p: *const c_void) -> u32 {
    unsafe { crate::pool::run_c(core::mem::transmute::<unsafe extern "C" fn(), c::Worker>(f), n, cost, wide, p.cast()) }
}
/// K9: elementwise.c `ew_serial`, the runner of every stage worker (`c::serial` with the worker's type erased).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_serial(f: unsafe extern "C" fn(), n: usize, cost: u32, wide: usize, p: *const CPass) -> u32 {
    // Safety: `f` is a `qlean_worker`, which every caller of a runner passes
    unsafe { c::serial(core::mem::transmute::<unsafe extern "C" fn(), c::Worker>(f), n, cost, wide, p) }
}
/// A46b: pass.h:502 `qlean_chain_run`'s driver over `k` stages and `n` elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_run_chain(run: unsafe extern "C" fn(), st: *const CStage, k: usize, n: usize, cost: u32,
                                       wide: usize) -> u32 {
    unsafe { c::run_chain(rn(run), sl(st, k), n, cost, wide) }
}

// ---- K10: the chain's stage table and builder (elementwise.c `ew_stage_worker`, `ew_chain_build`) and the statistics fold ----
type Worker = unsafe extern "C" fn(usize, usize, *const CPass);
#[cfg(not(test))]
unsafe extern "C" {
    /// elementwise.c: the value verbs of one tile; C keeps it for the two Frame-of-Reference runs that call it too.
    fn ew_val_run(lo: usize, hi: usize, p: *const CPass);
}
/// Under `cargo test` there is no C: the stage table needs a name for it, and no test runs a value stage.
#[cfg(test)]
unsafe extern "C" fn ew_val_run(_lo: usize, _hi: usize, _p: *const CPass) { unreachable!("ew_val_run is C's") }

/// `p`'s operand at `lo` elements of `w` bytes, `n` of them, unless it is an atom (`one`), which is `w` bytes at its start.
unsafe fn tile<'a>(q: *const c_void, lo: usize, n: usize, w: usize, one: bool) -> &'a [u8] {
    unsafe { if one { sl(q.cast::<u8>(), w) } else { sl(q.cast::<u8>().add(lo * w), n * w) } }
}
/// elementwise.c `ew_cmp_stage`: `lo`, `hi` are output bytes, so eight elements each and no two slices share one.
#[unsafe(no_mangle)]
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
/// elementwise.c `ew_mon_stage`.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_mon_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, n) = (ew::ew_width(p.cls as u32), hi - lo);
        ew::mon(c::serial, p.op, p.cls, p.nul, tile(p.a, lo, n, w, false), n, sl_mut(p.o.cast::<u8>().add(lo * w), n * w))
    }
}
/// elementwise.c `ew_floor_stage`: `n` longs out.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_floor_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, n) = (ew::ew_width(p.cls as u32), hi - lo);
        ew::floor(c::serial, p.cls, tile(p.a, lo, n, w, false), n, sl_mut(p.o.cast::<u8>().add(lo * 8), n * 8))
    }
}
/// elementwise.c `ew_bit_stage`: `lo`, `hi` are output bytes, so eight bits each; an atom operand is its one byte.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_bit_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let m = hi - lo;
        ew::bit(c::serial, p.op, p.shape, tile(p.a, lo, m, 1, p.shape == ew::k::AV), tile(p.b, lo, m, 1, p.shape == ew::k::VA), m * 8,
                sl_mut(p.o.cast::<u8>().add(lo), m))
    }
}
/// elementwise.c `ew_cast_stage`: the two classes travel as `cls` and `shape`.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_cast_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (sw, dw, n) = (ew::ew_width(p.cls as u32), ew::ew_width(p.shape as u32), hi - lo);
        ew::cast(c::serial, p.cls, p.shape, p.nul, tile(p.a, lo, n, sw, false), n, sl_mut(p.o.cast::<u8>().add(lo * dw), n * dw))
    }
}
/// elementwise.c `ew_tick_stage`: `op` is the source unit's code times 16 plus the target's, `p.c` the target's null; the
/// source is `int`, `double` or else `long`, the target `double`, `int` or else `long`.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_tick_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (sw, dw, n) = (if p.cls == ew::k::I32 { 4 } else { 8 }, if p.shape == ew::k::I32 { 4 } else { 8 }, hi - lo);
        ew::tick(c::serial, p.op, p.cls, p.shape, p.nul, p.c as isize as i64, tile(p.a, lo, n, sw, false), n,
                 sl_mut(p.o.cast::<u8>().add(lo * dw), n * dw))
    }
}
/// elementwise.c `ew_widen_stage`: elements `[lo, hi)` of a tile of `p.n`; a bit source is read from the tile's own bit 0.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_widen_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let xb = if p.cls == ew::k::BITS { p.n.div_ceil(8) } else { p.n * ew::ew_width(p.cls as u32) };
        ew::widen_stage(p.cls, p.shape, p.nul, p.c as isize as i64, sl(p.a.cast::<u8>(), xb), lo, hi,
                        sl_mut(p.o.cast::<u8>(), p.n * ew::ew_width(p.shape as u32)))
    }
}
/// elementwise.c `ew_decode_run`: `Coc.decode` over one tile, the block addressed by its number (`p.at`).
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_decode_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let (w, cnt) = (ew::ew_width(p.cls as u32), hi - lo);
        ew::decode_stage(&(*p.a.cast::<CCoc>()).view(), p.at / BLK, cnt, w, sl_mut(p.o.cast::<u8>(), cnt * w))
    }
}
/// elementwise.c `ew_alp_run`: `Coc.alpDecode` over one tile, the patches the block names applied.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_alp_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let (p, cnt) = (&*p, hi - lo);
        let f = &*p.a.cast::<CCocf>();
        f.view().load_blk(p.at / BLK, cnt, sl_mut(p.o.cast::<u8>(), cnt * if f.f32 != 0 { 4 } else { 8 }))
    }
}
/// elementwise.c `ew_ids_run`: an interned column's ids read where they lie at any lane and written at `cls`.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_ids_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let w = p.shape as u32;
        ew::ids_stage(p.cls, w, sl(p.a.cast::<u8>(), ew::ids_len(p.n, w)), lo, hi, sl_mut(p.o.cast::<u8>(), p.n * ew::ew_width(p.cls as u32)))
    }
}
/// elementwise.c `ew_pack_run`: `qrs_ew_ids_stage`'s inverse; below a byte `lo..hi` are output bytes.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_pack_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let p = &*p;
        let w = p.shape as u32;
        ew::pack_stage(p.cls, w, sl(p.a.cast::<u8>(), p.n * ew::ew_width(p.cls as u32)), p.n, lo, hi, sl_mut(p.o.cast::<u8>(), ew::ids_len(p.n, w)))
    }
}
/// elementwise.c `ew_encmeta_run`: the writer's meta step over the tile the chain just computed (`p.o` the `coc_enc`).
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_encmeta_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe { qrs_enc_for_meta((*p).o.cast(), (*p).at / BLK, (*p).a.cast(), hi - lo) }
}
/// elementwise.c `ew_encpack_run`: its pack step over the same tile.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_encpack_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe { qrs_enc_for_pack((*p).o.cast(), (*p).at / BLK, (*p).a.cast(), hi - lo) }
}
/// elementwise.c `ew_stage_worker`: the worker of `engine`, chosen once a stage and never per element.
fn stage_worker(engine: u32) -> Worker {
    use ew::eng::*;
    match engine {
        ENCMETA => qrs_ew_encmeta_stage, ENCPACK => qrs_ew_encpack_stage, VAL => ew_val_run, CMP => qrs_ew_cmp_stage, MON => qrs_ew_mon_stage,
        WIDEN => qrs_ew_widen_stage, BIT => qrs_ew_bit_stage, FLOOR => qrs_ew_floor_stage, CAST => qrs_ew_cast_stage, DECODE => qrs_ew_decode_stage,
        TICK => qrs_ew_tick_stage, IDS => qrs_ew_ids_stage, PACK => qrs_ew_pack_stage, _ => qrs_ew_alp_stage,
    }
}

impl CCoc {
    /// The `coc` that `coc_meta_view` then `coc_attach` build over metadata `m` (`33 * mblk + 16` bytes) and a pack: the
    /// Rust twins' slices (`Meta::new`, `Coc::attach`) as the raw pointers C reads.
    fn of(c: &Coc, m: *mut u8) -> CCoc {
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
/// A decode or ALP stage's view: metadata `m`, pack `pk`, and for ALP the float sections `a`. Where C's `coc_attach` aborts
/// or a buffer is misaligned or short, the stage names it.
unsafe fn stage_view(i: usize, alp: bool, m: (*mut u8, usize), pk: (*mut u8, usize), a: (*mut u8, usize), n: usize) -> CCocf {
    unsafe {
        let ms = sl(m.0.cast_const(), m.1);
        let me = coc::Meta::new(ms, n).unwrap_or_else(|| panic!("qlean_ew_chain: stage {i}'s metadata is misaligned or short"));
        let cocf = if alp { Some(Cocf::meta_view(ms, sl(a.0.cast_const(), a.1), n).unwrap_or_else(|| panic!("qlean_ew_chain: stage {i}'s ALP sections are misaligned or short"))) } else { None };
        let c = Coc::attach(cocf.as_ref().map_or(me, |f| f.c.meta), sl(pk.0.cast_const(), pk.1)).unwrap_or_else(|| {
            panic!("qlean: a Frame of Reference pack of {} bytes whose residuals end at {} holds no patch list of {} blocks after them", pk.1, me.res_end(), me.mblk)
        });
        let cc = CCoc::of(&c, m.0);
        match cocf {
            Some(f) => CCocf { c: cc, exp: f.exp.as_ptr().cast_mut(), exc_off: f.exc_off.as_ptr().cast_mut(), exc_pos: f.exc_pos.as_ptr().cast_mut(),
                               exc_raw: f.exc_raw.as_ptr().cast_mut().cast(), nexc: f.exc_pos.len(), f32: f.f32 as c_int },
            None => CCocf { c: cc, exp: null_mut(), exc_off: null_mut(), exc_pos: null_mut(), exc_raw: null_mut(), nexc: 0, f32: 0 },
        }
    }
}

/// pass.h's `QLEAN_SLOTS`, `QLEAN_COLUMN`, `QLEAN_FIXED`, and elementwise.c's `EW_SLOT0`, `EW_STAGE_BYTES`.
const SLOTS: usize = 10;
const COLUMN: u8 = 254;
const FIXED: u8 = 255;
const SLOT0: u8 = 128;
const STAGE_BYTES: usize = 24;
/// elementwise.c `ew_chain_build`: the `st[]` the `k`-record program `prog` describes, every stage writing its own slot, the
/// caller re-binding the last one's output. `views` is the caller's array because a decode stage's `p.a` points into it (a
/// `cocf` serves both decode engines: its first member is the integral view). `cost` and `wide` come back as the whole chain's.
/// Safety: `prog` is `k` records, `inputs` the payloads they name (sarrays), `st` and `views` `SLOTS` entries of room.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_chain_build(prog: *const u8, k: usize, inputs: *const *mut c_void, n: usize, st: *mut CStage,
                                            views: *mut CCocf, costp: *mut u32, widep: *mut usize) {
    use ew::eng::*;
    assert!(k != 0 && k <= SLOTS, "qlean_ew_chain: {k} stages, and the driver holds {SLOTS}. The chain is built in QLean/Kernel/Elementwise.lean and every one of them is shorter than that; a longer one needs QLEAN_SLOTS in c/pass.h raised with it.");
    let (mut cost, mut wide) = (0u32, 1usize);
    let input = |i: u8| unsafe { (*inputs.add(i as usize)).cast::<lean::Object>() };
    for i in 0..k {
        unsafe {
            let rec = sl(prog.add(i * STAGE_BYTES), STAGE_BYTES);
            let (engine, op, cls, shape) = (rec[0] as u32, rec[1], rec[2], rec[3]);
            let nul = i64::from_ne_bytes(rec[8..16].try_into().unwrap());
            let nul_out = i64::from_ne_bytes(rec[16..24].try_into().unwrap());
            let (c, ab, bb, ob) = ew::stage_bits(engine, op as u32, cls as u32, shape as u32);
            let mut s = CStage {
                f: Some(stage_worker(engine)),
                p: CPass { a: core::ptr::null(), b: core::ptr::null(), c: nul_out as isize as *const c_void, o: null_mut(), n: 0, at: 0, r#priv: 0, nul, op, cls, shape },
                asrc: 0, bsrc: 0, osrc: i as u8, abits: ab, bbits: bb, obits: ob,
                bytewise: (engine == CMP || engine == BIT || (engine == PACK && shape != 0 && shape < 8)) as u8,
            };
            cost += c;
            wide = wide.max(ab as usize / 8).max(ob as usize / 8);
            // an operand names either a slot, the answer of the stage that many places along (already tile-local), or one
            // of the payloads handed in
            for side in 0..2 {
                let code = rec[4 + side];
                let (bind, src) = if side == 0 { (&mut s.p.a, &mut s.asrc) } else { (&mut s.p.b, &mut s.bsrc) };
                // a monadic engine has no right operand, which is where `bbits` is zero
                if side == 1 && bb == 0 && engine != DECODE && engine != ALP { *bind = core::ptr::null(); *src = FIXED; continue }
                if code >= SLOT0 { *src = code - SLOT0; continue }
                *bind = lean::sarray_cptr(input(code)).cast();
                *src = if ew::stage_fixed(engine, shape as u32, side == 0) { FIXED } else { COLUMN };
            }
            if engine == DECODE || engine == ALP {
                // the metadata and the pack become one view for the run, with an ALP column's float sections read out of the
                // third payload beside them
                let (mo, po) = (input(rec[4]), input(rec[5]));
                let alp = engine == ALP;
                let ao = if alp { input(rec[6]) } else { null_mut() };
                let a = if alp { (lean::sarray_cptr(ao), lean::sarray_size(ao)) } else { (null_mut(), 0) };
                let v = views.add(i);
                v.write(stage_view(i, alp, (lean::sarray_cptr(mo), lean::sarray_size(mo)), (lean::sarray_cptr(po), lean::sarray_size(po)), a, n));
                s.p.a = if alp { v.cast_const().cast() } else { (&raw const (*v).c).cast() };
                s.p.b = core::ptr::null();
            }
            st.add(i).write(s);
        }
    }
    unsafe { (*costp, *widep) = (cost, wide) }
}

/// elementwise.c `qlean_ew_chain_enc`'s appended stage: stage `k` is the encoder's meta step (`pack` 0) or pack step over the
/// tile stage `k - 1` wrote, `c` the `coc_enc` it writes through, at class `cls`. It answers no slot (`osrc` fixed), and its cost
/// is added to `*cost`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_enc_stage(st: *mut CStage, k: usize, cls: u32, c: *mut CEnc, pack: c_int, cost: *mut u32) {
    use ew::eng::*;
    let (cs, ab, bb, ob) = ew::stage_bits(ENCMETA, 0, cls, 0);
    unsafe {
        st.add(k).write(CStage {
            f: Some(stage_worker(if pack != 0 { ENCPACK } else { ENCMETA })),
            p: CPass { a: core::ptr::null(), b: core::ptr::null(), c: core::ptr::null(), o: c.cast(), n: 0, at: 0, r#priv: 0, nul: 0, op: 0, cls: cls as u8, shape: 0 },
            asrc: (k - 1) as u8, bsrc: FIXED, osrc: FIXED, abits: ab, bbits: bb, obits: ob, bytewise: 0,
        });
        if pack == 0 { *cost += cs }
    }
}

/// The stats stage's worker: its fold over the two tiles, `p.o` the `Stats` of the phase running.
#[unsafe(no_mangle)]
unsafe extern "C" fn qrs_ew_stats_stage(lo: usize, hi: usize, p: *const CPass) {
    unsafe {
        let (p, n) = (&*p, hi - lo);
        (*p.o.cast::<ew::Stats>()).run(sl(p.a.cast::<f64>(), n), sl(p.b.cast::<f64>(), n), p.at)
    }
}
/// elementwise.c `qlean_stats_chain`'s body after `ew_chain_build`: `Kernel.moments` (`mode` 0) or `Kernel.dots` (1, and 2 on
/// `real` lanes) over the two payloads source codes `sa`, `sb` name, the fold as the chain's last stage `st[k]` (`k` stages
/// built, none when 0). Writes the answer's 48 bytes: five doubles and the pairs kept as a long.
/// Safety: as `qrs_ew_chain_build`, with `st` holding `k + 1` entries and `out` 48 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_ew_stats_chain(mode: u8, st: *mut CStage, k: usize, inputs: *const *mut c_void, n: usize, sa: u8, sb: u8,
                                            out: *mut u8) {
    let mut st0 = ew::Stats::new();
    let sp: *mut ew::Stats = &mut st0;
    let s = || unsafe { &mut *sp };
    let mut fold = CStage { f: Some(qrs_ew_stats_stage), p: CPass { a: core::ptr::null(), b: core::ptr::null(), c: core::ptr::null(), o: sp.cast(),
                            n: 0, at: 0, r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 }, asrc: 0, bsrc: 0, osrc: FIXED, abits: 64, bbits: 64, obits: 0, bytewise: 0 };
    for (side, code) in [sa, sb].into_iter().enumerate() {
        let slot = code >= SLOT0;
        let at = if slot { (code - SLOT0) as usize } else { code as usize };
        let col = if slot { null_mut() } else { unsafe { (*inputs.add(at)).cast::<lean::Object>() } };
        if if slot { at >= k || unsafe { (*st.add(at)).obits } != 64 } else { (unsafe { lean::sarray_size(col) }) < n * 8 } {
            panic!("qlean_stats_chain: operand {side}, source code {code} of a {k}-stage chain, is not {n} doubles. `Kernel.statsColumns` brings both operands to `Ew.f64` through `operandSource`, so this means that builder named another class.");
        }
        let (bind, src) = if slot { (core::ptr::null(), at as u8) } else { (unsafe { lean::sarray_cptr(col) }.cast_const().cast(), COLUMN) };
        if side == 1 { fold.p.b = bind; fold.bsrc = src } else { fold.p.a = bind; fold.asrc = src }
    }
    unsafe { st.add(k).write(fold) };
    let cp = CPass { a: st.cast_const().cast(), b: core::ptr::null(), c: core::ptr::null(), o: null_mut(), n, at: 0, r#priv: 0, nul: 0,
                     op: (k + 1) as u8, cls: 0, shape: 0 };
    // one phase over the whole column, on the calling thread and in order: the lanes are positional, so a split across
    // threads would be another sum
    let pass = |phase: u8| {
        s().begin(phase, n);
        if n != 0 { unsafe { c::chain_tiles(0, n.div_ceil(crate::BLK), &cp) } }
    };
    let mut o = [0f64; 5];
    let cnt;
    if mode == 0 {
        pass(ew::st::SUMS);
        (o[3], o[4]) = (s().sum(0), s().sum(1));
        cnt = s().cnt;
        (s().mx, s().my) = (o[3] / cnt as f64, o[4] / cnt as f64);
        pass(ew::st::CENTRED);
        (o[0], o[1], o[2]) = (s().sum(0), s().sum(1), s().sum(2));
    } else {
        pass(if mode >= 2 { ew::st::DOTS32 } else { ew::st::DOTS });
        // a null anywhere and q's sum is one accumulator over the live pairs; under `real` lanes an integral left operand's
        // null (mode 3) is a zero weight instead, and only a null right operand is that accumulator: any inside the lanes,
        // and past them one under a live left
        if if mode == 3 { s().bad != 0 } else { s().cnt != n } { pass(ew::st::SERIAL) }
        (o[0], o[3]) = (s().sum(0), s().sum(1));
        cnt = s().cnt;
    }
    let r = unsafe { sl_mut(out, 48) };
    for (d, v) in r.chunks_exact_mut(8).zip(o.iter().map(|v| v.to_ne_bytes()).chain([(cnt as i64).to_ne_bytes()])) { d.copy_from_slice(&v) }
}

#[cfg(test)]
mod tests {
    use super::*;
    // the C's `kind_of` always had a string; a null `who` reads as `?`. A `kind` number past the enum answers 8 as the C's switch falls out
    #[test] fn kind_of_and_width_take_null_and_out_of_range() {
        unsafe {
            assert_eq!(qrs_kind_of(4, 1, core::ptr::null()), search::Kind::F32 as c_int);
            assert_eq!(qrs_kind_of(1, 0, c"who".as_ptr()), search::Kind::U8 as c_int);
        }
        assert_eq!((qrs_kind_width(0), qrs_kind_width(6), qrs_kind_width(-1), qrs_kind_width(99)), (1, 16, 8, 8));
    }
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
    // coc.h's `coc_may_hold64` read off the raw pointers, as the C wrote it
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
                        if exc { for j in 0..k { if m >> j & 1 == 0 && qrs_coc_exc_within(&cc, b0 + j, v, v) != 0 { m |= 1 << j } } }
                        assert_eq!(qrs_coc_may_hold64(&cc, b0, k, v), m, "block {b0}+{k} for {v}");
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

// ---- K24: coc.c:134-448, 764-816, the one writer of an encoded column ----
// A column's blocks come from a `Source` (a C `coc_src`, a dense buffer, or a producer's `fill` with the three optional
// callbacks that move whole blocks); a pass runs a per-block step over them on the pool, a slice at a time. Allocation of
// the writer's scratch aborts like coc.h's `coc_alloc`, and its `free`s are the C callers' (`structural.c` frees `exc_heap`).

/// coc.h `coc_parts`: the writer's ByteArrays, null where the form has none.
#[repr(C)]
pub struct CParts { pub meta: *mut c_void, pub body: *mut c_void, pub alp: *mut c_void }
type FillFn = unsafe extern "C" fn(*mut i64, usize, usize, *const c_void);
type TakeFn = Option<unsafe extern "C" fn(usize, *mut usize, *const c_void) -> *const CCocf>;
type HintFn = Option<unsafe extern "C" fn(usize, *mut u32, *const c_void) -> c_int>;
type IntsFn = Option<unsafe extern "C" fn(usize, *mut i64, *mut i8, *mut *const c_void, *const c_void) -> c_int>;
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
/// A producer's `coc_fill`: each worker's cursor is a block of `i64` and its narrowed copy. A block `take` claims is not
/// filled -- the cursor itself stands in for its elements, which the two move steps never read -- and neither is a block
/// `ints` answers.
struct FillSrc { fill: FillFn, take: TakeFn, hint: HintFn, ints: IntsFn, ctx: *const c_void, width: usize, alp: bool }
// Safety: the producer's callbacks are called from every worker, as C's were
unsafe impl Sync for FillSrc {}
impl Moves for FillSrc {
    fn take(&self, b: usize) -> Option<(Cocf<'_>, usize)> {
        unsafe {
            let mut pb = 0usize;
            let f = self.take.map_or(core::ptr::null(), |t| t(b, &mut pb, self.ctx));
            // a Frame of Reference part has only `c` set, its ALP fields being whatever the caller's allocation held
            (!f.is_null()).then(|| (if self.alp { (*f).view() } else { Cocf { c: (*f).c.view(), exp: &[], exc_off: &[], exc_pos: &[], exc_raw: &[], f32: false } }, pb))
        }
    }
    fn ints(&self, b: usize, nb: usize, d: &mut [i64], ee: &mut [i8], raw: Option<&mut [u8]>) -> Option<i32> {
        let f = self.ints?;
        unsafe {
            let mut ptrs = core::mem::MaybeUninit::<[*const c_void; BLK]>::uninit();
            let e = f(b, d.as_mut_ptr(), ee.as_mut_ptr(), if raw.is_some() { ptrs.as_mut_ptr().cast() } else { null_mut() }, self.ctx);
            if let (Some(raw), true) = (raw, e >= 0) {
                let (ptrs, w) = (sl(ptrs.as_ptr().cast::<*const c_void>(), nb), self.width);
                for i in (0..nb).filter(|&i| ee[i] < 0) { raw[i * w..(i + 1) * w].copy_from_slice(sl(ptrs[i].cast::<u8>(), w)) }
            }
            Some(e)
        }
    }
    fn hint(&self, b: usize) -> Option<(i32, u32)> {
        let h = self.hint?;
        let mut lim = 0u32;
        Some((unsafe { h(b, &mut lim, self.ctx) }, lim))
    }
}
impl Source for FillSrc {
    unsafe fn open(&self) -> Option<*mut c_void> { Some(unsafe { coc_alloc(BLK * 16) }.cast()) }
    unsafe fn at(&self, cur: *mut c_void, off: usize, len: usize) -> *const u8 {
        unsafe {
            let (b, w) = (off / self.width / BLK, self.width);
            if self.take(b).is_some() || self.ints.is_some_and(|i| i(b, null_mut(), null_mut(), null_mut(), self.ctx) >= 0) { return cur.cast() }
            let (v, cnt) = (cur.cast::<i64>(), len / w);
            (self.fill)(v, off / w, cnt, self.ctx);
            // the producers compute in i64, the writer's block steps read the column's own element type
            enc::narrow(w, sl(v, cnt), sl_mut(v.add(BLK).cast::<u8>(), cnt * w)).as_ptr()
        }
    }
    unsafe fn close(&self, cur: *mut c_void) { unsafe { coc_free(cur.cast()) } }
    unsafe fn bad(&self) -> bool { false }
}

/// coc.h `coc_alloc`: 64-byte aligned, never size 0, abort on failure.
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
/// coc.h `coc_meta_view`: the five sections and the trailer over `metabytes` bytes at `m`, the count cut to what they hold.
unsafe fn meta_view(m: *mut u8, metabytes: usize, n: usize) -> CCoc {
    let nblk = metabytes / 33;
    let n = n.min(nblk * BLK);
    unsafe {
        CCoc { base: m.cast(), maxv: m.add(8 * nblk).cast(), off: m.add(16 * nblk).cast(), bsum: m.add(24 * nblk).cast(),
               sumnul: m.add(32 * nblk).cast(), sumn: m.add(32 * nblk + 8).cast(), width: m.add(32 * nblk + 16), pack: null_mut(),
               n, nblk: n.div_ceil(BLK), packbytes: 0, mblk: nblk, exc_off: core::ptr::null(), exc_pos: core::ptr::null(),
               exc_raw: core::ptr::null(), fdelta: null_mut(), nexc: 0, exc_esz: 0 }
    }
}

/// coc.c `coc_enc_open`: the metadata sarray and the heap copies the meta pass fills.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_enc_open(s: *mut CEnc, n: usize, width: usize, alp: c_int) {
    unsafe {
        let (nblk, msz) = (n.div_ceil(BLK), 33 * n.div_ceil(BLK) + 16);
        core::ptr::write_bytes(s, 0, 1);
        (*s).n = n;
        (*s).width = width;
        (*s).alp = alp;
        let meta = lean::alloc_sarray(1, msz, msz);
        (*s).meta = meta.cast();
        (*s).c = meta_view(lean::sarray_cptr(meta), msz, n);
        if alp != 0 { (*s).exp = coc_alloc(nblk).cast() } else { (*s).frm_heap = coc_alloc(nblk * 8).cast(); (*s).c.fdelta = (*s).frm_heap }
        (*s).exc_heap = coc_alloc((nblk + 1) * 4).cast();
        (*s).exc_off = (*s).exc_heap;
    }
}
/// coc.c `coc_enc_plan`: between the two passes, the offsets, the exception prefix sums and the tail's size; answers the
/// encoded column's whole size. Once per encoder.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_enc_plan(s: *mut CEnc) -> usize {
    unsafe {
        let (nblk, width) = ((*s).c.nblk, (*s).width);
        if (*s).planned == 0 {
            (*s).planned = 1;
            let at = crate::coc::Meta::offsets(sl((*s).c.width, nblk), nblk, sl_mut((*s).c.off, nblk));
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
/// coc.c `coc_enc_layout`: the trailer, then the pack with the patch list as its tail (or ALP's blob), the heap copies moved in.
#[unsafe(no_mangle)]
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
        // a short last block reserves a full block's room and packs only `n % 1024` residuals into it; the rest is written
        // here, so equal columns are equal bytes
        if n % BLK != 0 { core::ptr::write_bytes((*s).c.pack.add(*(*s).c.off.add(nblk - 1) as usize), 0, at - *(*s).c.off.add(nblk - 1) as usize) }
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
/// coc.c `coc_enc_pair`: the (meta, pack) of a finished Frame of Reference writer.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_enc_pair(s: *mut CEnc) -> *mut c_void { unsafe { coc_free((*s).exc_heap.cast()); mk_pair((*s).meta, (*s).pack) } }

type Blk<'a> = &'a (dyn Fn(*mut CEnc, usize, *const u8, usize) + Sync);
struct Pass<'a, S> { src: &'a S, blk: Blk<'a>, sized: bool }
/// coc.c `src_run`: the blocks `[b0, b1)` through the per-block step; a worker writes only what its block owns (its
/// metadata entries, its bytes at off[b], its exceptions at exc_off[b]), so any pass may be split.
unsafe extern "C" fn src_run<S: Source>(b0: usize, b1: usize, p: *const CPass) {
    use core::sync::atomic::Ordering::SeqCst;
    unsafe {
        let (s, job) = ((*p).o.cast::<CEnc>(), &*(*p).a.cast::<Pass<S>>());
        let Some(cur) = job.src.open() else { return };
        let (n, width, sized) = ((*s).n, (*s).width, job.sized);
        let (lb, over) = (AtomicUsize::from_ptr(&raw mut (*s).lb), AtomicI32::from_ptr(&raw mut (*s).over));
        // the meta pass under a size test stops once the blocks it has sized already reach it: each block's residuals and its
        // exceptions' bytes are a part of the total `qrs_coc_enc_plan` would answer, so their sum is a lower bound
        let mut mine = 0usize;
        for b in b0..b1 {
            let (lo, nb) = (b * BLK, if b * BLK + BLK < n { BLK } else { n - b * BLK });
            let x = job.src.at(cur, lo * width, nb * width);
            if x.is_null() { break }
            (job.blk)(s, b, x, nb);
            if !sized { continue }
            mine += enc::block_bytes(*(*s).c.width.add(b), *(*s).exc_off.add(b + 1), width);
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
/// coc.c `src_pass`: `blk` over every block of `src` on the pool; `meta` marks the sizing pass. False when the source failed.
unsafe fn src_pass<S: Source>(s: *mut CEnc, src: &S, blk: Blk, meta: bool, cost: u32) -> bool {
    unsafe {
        let job = Pass { src, blk, sized: meta && (*s).below != 0 };
        let (n, w) = ((*s).n, (*s).width);
        let p = CPass { a: (&raw const job).cast(), b: core::ptr::null(), c: core::ptr::null(), o: s.cast(), n, at: 0, r#priv: 0, nul: 0, op: 0, cls: 0, shape: 0 };
        c::pool()(src_run::<S>, n.div_ceil(BLK), cost, BLK * w, &p);
        !src.bad()
    }
}
fn meta_step(s: *mut CEnc, b: usize, x: *const u8, nb: usize) { unsafe { let w = (*s).width; enc::meta_step(&mut (*s).meta_blk(b), sl(x, nb * w), w, nb) } }
fn pack_step(s: *mut CEnc, b: usize, x: *const u8, nb: usize) {
    unsafe { let w = (*s).width; enc::pack_step(&mut (*s).pack_blk(b, nb, false), sl(x, nb * w), w, (*s).alp != 0) }
}

/// coc.c `qlean_coc_encode_src`: 1 and the parts, or 0 with nothing allocated when the source failed, or 2 with nothing
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
            let blk = move |s: *mut CEnc, b: usize, x: *const u8, nb: usize| if bits { qrs_src_bits((*s).out, n.div_ceil(8), b, x, nb) } else { qrs_src_copy((*s).out.add(b * BLK * width), x, nb * width) };
            if !src_pass(s, src, &blk, false, crate::QLEAN_COST_COPY) { lean::dec(o); return 0 }
            out.body = o.cast();
            return 1;
        }
        if kind != SRC_FOR && kind != SRC_ALP {
            crate::os::eprint(format_args!("qlean_coc_encode_src: form {kind} is not one of c/coc.h's SRC_*\n")).expect("qlean: stderr");
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
    /// part `i` (0 meta, 1 body, 2 alp) as bytes
    pub fn part(&self, i: usize) -> &[u8] {
        let p = [self.0.meta, self.0.body, self.0.alp][i].cast::<lean::Object>();
        if p.is_null() { &[] } else { unsafe { sl(lean::sarray_cptr(p), lean::sarray_size(p)) } }
    }
}
impl Drop for ZParts {
    fn drop(&mut self) { for p in [self.0.meta, self.0.body, self.0.alp] { if !p.is_null() { unsafe { lean::dec(p.cast()) } } } }
}
/// coc.c `qlean_zip_parts`'s encode: the `n` elements of `width` bytes of `z`'s element region in the form `kind` names,
/// unconditionally (no size test); `None` when `z` failed, the failure being `z.error()`.
pub fn encode_zip(z: &crate::zip::File, n: usize, width: usize, kind: u8) -> Option<ZParts> {
    let mut out = CParts { meta: null_mut(), body: null_mut(), alp: null_mut() };
    (unsafe { encode(&ZSrc(z), n, width, kind as u32, &mut out, usize::MAX) } == 1).then_some(ZParts(out))
}
/// coc.c `coc_encode_dense`: the parts of the `n` elements of `width` bytes at `x`, 1 unless they would be `below` bytes or more.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_encode_dense(x: *const u8, n: usize, width: usize, kind: u32, below: usize, r: *mut CParts) -> c_int {
    unsafe { (encode(&Dense(x), n, width, kind, &mut *r, below) == 1) as c_int }
}
/// coc.c `qlean_coc_encode_raw`: the (meta, pack) of a whole dense column, the one place that says how one is encoded.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_encode_raw(src: *const u8, n: usize, width: usize) -> *mut c_void {
    unsafe {
        let mut r = CParts { meta: null_mut(), body: null_mut(), alp: null_mut() };
        assert!(encode(&Dense(src), n, width, SRC_FOR, &mut r, usize::MAX) == 1, "qlean_coc_encode_raw: a dense buffer cannot fail");
        mk_pair(r.meta, r.body)
    }
}

/// coc.c `qlean_coc_encode_move`: the writer where some answer blocks already exist in the writer's form (`take`), with
/// ALP's two hints (`hint`, `ints`); null callbacks fill the block. `alp` answers `(meta, (pack, alp))`, else `(meta, pack)`.
/// `take`, `hint` and `ints` are coc.h's `coc_take`, `coc_hint`, `coc_ints`; null is none.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_encode_move(n: usize, width: usize, alp: c_int, fill: FillFn, take: TakeFn, hint: HintFn,
                                             ints: IntsFn, ctx: *const c_void) -> *mut c_void {
    unsafe {
        let fs = FillSrc { fill, take, hint, ints, ctx, width, alp: alp != 0 };
        let mut e: CEnc = core::mem::zeroed();
        let s = &raw mut e;
        qrs_coc_enc_open(s, n, width, alp);
        let cost = if alp != 0 { crate::QLEAN_COST_MATH } else { crate::QLEAN_COST_ARITH };
        // a fill cannot fail, having no `bad`: a refusal here is the writer's own bug
        let ok = src_pass(s, &fs, &|s, b, x, nb| enc::move_meta_blk(&fs, &mut (*s).meta_blk(b), || sl(x, nb * width), width, nb), true, cost) && {
            qrs_coc_enc_layout(s);
            src_pass(s, &fs, &|s, b, x, nb| enc::move_pack_blk(&fs, |whole| (*s).pack_blk(b, nb, whole), || sl(x, nb * width), b, nb, width, alp != 0), false, crate::QLEAN_COST_ARITH)
        };
        if !ok {
            crate::os::eprint(format_args!("qlean_coc_encode_move: the writer refused {n} elements of {width} bytes from a fill\n")).expect("qlean: stderr");
            crate::os::exit(1)
        }
        if alp == 0 { return qrs_coc_enc_pair(s) }
        coc_free((*s).exc_heap.cast());
        mk_pair((*s).meta, mk_pair((*s).pack, (*s).blob))
    }
}
/// coc.c `qlean_coc_encode_fill`: the (meta, pack) of the `n` elements `fill` denotes, how every kernel that computes a
/// Frame of Reference answer hands it to the writer.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_encode_fill(n: usize, width: usize, fill: FillFn, ctx: *const c_void) -> *mut c_void {
    unsafe { qrs_coc_encode_move(n, width, 0, fill, None, None, None, ctx) }
}

/// coc.c `coc_fill_ctx`, the context of the shift, vv and scale producers.
#[repr(C)]
pub struct CFillCtx { pub a: *const CCoc, pub b: *const CCoc, pub op: c_int, pub s: i64, pub fill: i64, pub k: i64 }
/// coc.c `vv_fill`, `cocops::vv_fill` over the producer's context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_vv_fill(buf: *mut i64, i0: usize, nb: usize, ctx: *const c_void) {
    unsafe { let x = &*ctx.cast::<CFillCtx>(); crate::cocops::vv_fill(&(*x.a).view(), &(*x.b).view(), x.op, x.s, x.fill, i0, sl_mut(buf, nb)) }
}
/// coc.c `scale_fill`, `cocops::scale_fill` over the producer's context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qrs_coc_scale_fill(buf: *mut i64, i0: usize, nb: usize, ctx: *const c_void) {
    unsafe { let x = &*ctx.cast::<CFillCtx>(); crate::cocops::scale_fill(&(*x.a).view(), x.k, i0, sl_mut(buf, nb)) }
}
