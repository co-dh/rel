//! Lean 4.28's object layout and the `lean.h` inlines an export needs, the one module that names an object field, so
//! a toolchain bump is re-verified here and nowhere else. `c/abi.c` asserts every mirror and constant against `lean.h`
//! (the build stops on a mismatch); `test/abi.c` runs each `lean.h` inline beside its twin here (feature `abi`).
//! The build is `LEAN_MIMALLOC` (`config.h:10`); out-of-line runtime functions are called by symbol, never rewritten.
//! Export files (`ffi/*.rs`) see only the safe types `B`, `O`, `SArr` and the macro `export!`.
#![allow(unsafe_code)]
use core::marker::PhantomData;
use core::ptr::NonNull;

/// `lean_object`: `int m_rc; unsigned m_cs_sz:16, m_other:8, m_tag:8` -- three bit-fields in one little-endian
/// 32-bit unit, so the fields are the bytes 4-5, 6 and 7 (test/abi.c compares the header bytes).
#[repr(C)]
pub struct Object { pub rc: i32, pub cs_sz: u16, pub other: u8, pub tag: u8 }
/// `lean_ctor_object`
#[repr(C)]
pub struct Ctor { pub hdr: Object, pub objs: [*mut Object; 0] }
/// `lean_array_object`
#[repr(C)]
pub struct Array { pub hdr: Object, pub size: usize, pub capacity: usize, pub data: [*mut Object; 0] }
/// `lean_sarray_object`
#[repr(C)]
pub struct SArray { pub hdr: Object, pub size: usize, pub capacity: usize, pub data: [u8; 0] }
/// `lean_string_object`; `size` counts the trailing NUL, `length` is in code points
#[repr(C)]
pub struct Str { pub hdr: Object, pub size: usize, pub capacity: usize, pub length: usize, pub data: [u8; 0] }
/// `lean_external_class`
#[repr(C)]
pub struct ExternalClass { pub finalize: Option<unsafe extern "C" fn(*mut u8)>,
                           pub foreach: Option<unsafe extern "C" fn(*mut u8, *mut Object)> }
/// `lean_external_object`
#[repr(C)]
pub struct External { pub hdr: Object, pub class: *mut ExternalClass, pub data: *mut u8 }

// lean.h's tags and limits, each asserted equal to its C name in c/abi.c
pub const TAG_MAX_CTOR: u8 = 243;
pub const TAG_PROMISE: u8 = 244;
pub const TAG_CLOSURE: u8 = 245;
pub const TAG_ARRAY: u8 = 246;
pub const TAG_STRUCT_ARRAY: u8 = 247;
pub const TAG_SCALAR_ARRAY: u8 = 248;
pub const TAG_STRING: u8 = 249;
pub const TAG_MPZ: u8 = 250;
pub const TAG_THUNK: u8 = 251;
pub const TAG_TASK: u8 = 252;
pub const TAG_REF: u8 = 253;
pub const TAG_EXTERNAL: u8 = 254;
pub const TAG_RESERVED: u8 = 255;
pub const OBJECT_SIZE_DELTA: usize = 8;
pub const MAX_SMALL_OBJECT_SIZE: usize = 4096;
pub const MAX_CTOR_FIELDS: usize = 256;
pub const MAX_CTOR_SCALARS_SIZE: usize = 1024;
pub const CLOSURE_MAX_ARGS: usize = 16;

// The out-of-line runtime: c/rt.c defines each for a program linked without Lean, and the Rel gate checks that every
// `lean_*`/`mi_*` name this object leaves undefined is one rt.c defines. A module so cbindgen skips the declarations.
/// cbindgen:ignore
mod sys {
    use super::Object;
    unsafe extern "C" {
        pub fn lean_alloc_object(sz: usize) -> *mut Object;
        pub fn mi_malloc_small(sz: usize) -> *mut u8;
        pub fn lean_inc_heartbeat();
        pub fn lean_internal_panic_out_of_memory() -> !;
        pub fn lean_dec_ref_cold(o: *mut Object);
    }
}
use sys::*;

// ---------------------------------------------------------------- lean.h's inlines, one twin each, same name less `lean_`

#[inline(always)] pub fn is_scalar(o: *const Object) -> bool { o as usize & 1 == 1 }
#[inline(always)] pub fn box_(n: usize) -> *mut Object { ((n << 1) | 1) as *mut Object }
#[inline(always)] pub fn unbox(o: *const Object) -> usize { o as usize >> 1 }
#[inline(always)] pub fn align(v: usize, a: usize) -> usize { v.div_ceil(a) * a }

/// Safety, for every `unsafe fn` below: `o` points at a live object of the kind the `lean.h` original asserts.
#[inline(always)] pub unsafe fn ptr_tag(o: *const Object) -> u8 { unsafe { (*o).tag } }
#[inline(always)] pub unsafe fn ptr_other(o: *const Object) -> u8 { unsafe { (*o).other } }
/// `lean_obj_tag` answers `unsigned`, so a scalar past 2^32 is truncated as in C
#[inline(always)] pub unsafe fn obj_tag(o: *const Object) -> u32 {
    if is_scalar(o) { unbox(o) as u32 } else { unsafe { ptr_tag(o) as u32 } }
}
#[inline(always)] pub unsafe fn is_mt(o: *const Object) -> bool { unsafe { (*o).rc < 0 } }
#[inline(always)] pub unsafe fn is_st(o: *const Object) -> bool { unsafe { (*o).rc > 0 } }
#[inline(always)] pub unsafe fn is_persistent(o: *const Object) -> bool { unsafe { (*o).rc == 0 } }
#[inline(always)] pub unsafe fn is_exclusive(o: *const Object) -> bool { unsafe { (*o).rc == 1 } }
#[inline(always)] pub unsafe fn is_shared(o: *const Object) -> bool { unsafe { (*o).rc > 1 } }
#[inline(always)] pub unsafe fn is_ctor(o: *const Object) -> bool { unsafe { ptr_tag(o) <= TAG_MAX_CTOR } }

/// `lean_get_rc_mt_addr`: a negative `rc` is shared between threads and only moved atomically
#[inline(always)] unsafe fn rc_atomic<'a>(o: *mut Object) -> &'a core::sync::atomic::AtomicI32 {
    unsafe { core::sync::atomic::AtomicI32::from_ptr(&raw mut (*o).rc) }
}
/// `lean_inc_ref_n`: single-threaded counts up, multi-threaded counts down atomically, persistent (0) not at all.
/// C adds `n` as `int` (truncating), so the twin does the same.
#[inline(always)] pub unsafe fn inc_ref_n(o: *mut Object, n: usize) {
    unsafe {
        if is_st(o) { (*o).rc = (*o).rc.wrapping_add(n as i32) }
        else if (*o).rc != 0 { rc_atomic(o).fetch_sub(n as i32, core::sync::atomic::Ordering::Relaxed); }
    }
}
#[inline(always)] pub unsafe fn inc_ref(o: *mut Object) { unsafe { inc_ref_n(o, 1) } }
/// `lean_dec_ref`: above 1 a plain decrement; 1 or negative is the runtime's (it frees, or counts atomically)
#[inline(always)] pub unsafe fn dec_ref(o: *mut Object) {
    unsafe { if (*o).rc > 1 { (*o).rc -= 1 } else if (*o).rc != 0 { lean_dec_ref_cold(o) } }
}
#[inline(always)] pub unsafe fn inc(o: *mut Object) { if !is_scalar(o) { unsafe { inc_ref(o) } } }
#[inline(always)] pub unsafe fn inc_n(o: *mut Object, n: usize) { if !is_scalar(o) { unsafe { inc_ref_n(o, n) } } }
#[inline(always)] pub unsafe fn dec(o: *mut Object) { if !is_scalar(o) { unsafe { dec_ref(o) } } }

/// `lean_set_st_header`; under mimalloc `cs_sz` was set by the allocation and is left alone
#[inline(always)] pub unsafe fn set_st_header(o: *mut Object, tag: u8, other: u8) {
    unsafe { (*o).rc = 1; (*o).tag = tag; (*o).other = other }
}
/// `lean_set_non_heap_header`: `rc` 0, and `cs_sz` holds the size (1 for a big object)
#[inline(always)] pub unsafe fn set_non_heap_header(o: *mut Object, sz: usize, tag: u8, other: u8) {
    debug_assert!(sz > 0 && sz < 1 << 16);
    unsafe { (*o).rc = 0; (*o).tag = tag; (*o).other = other; (*o).cs_sz = sz as u16 }
}

/// `lean_alloc_small_object`, mimalloc branch (`lean.h:355-363`)
#[inline(always)] pub fn alloc_small_object(sz: u32) -> *mut Object {
    let sz = align(sz as usize, OBJECT_SIZE_DELTA);
    unsafe {
        lean_inc_heartbeat();
        let m = mi_malloc_small(sz);
        if m.is_null() { lean_internal_panic_out_of_memory() }
        let o = m.cast::<Object>();
        (*o).cs_sz = sz as u16;
        o
    }
}
/// `lean_alloc_ctor_memory`, mimalloc branch: the last word zeroed when `sz` was rounded up, so padding is defined
#[inline(always)] pub fn alloc_ctor_memory(sz: u32) -> *mut Object {
    let sz1 = align(sz as usize, OBJECT_SIZE_DELTA);
    let r = alloc_small_object(sz);
    if sz1 > sz as usize { unsafe { r.cast::<u8>().add(sz1).cast::<usize>().sub(1).write(0) } }
    r
}
/// `lean_alloc_ctor`
#[inline(always)] pub fn alloc_ctor(tag: u8, num_objs: u32, scalar_sz: u32) -> *mut Object {
    debug_assert!(tag <= TAG_MAX_CTOR && (num_objs as usize) < MAX_CTOR_FIELDS && (scalar_sz as usize) < MAX_CTOR_SCALARS_SIZE);
    let o = alloc_ctor_memory((size_of::<Ctor>() + size_of::<usize>() * num_objs as usize) as u32 + scalar_sz);
    unsafe { set_st_header(o, tag, num_objs as u8) }
    o
}
#[inline(always)] pub unsafe fn ctor_num_objs(o: *const Object) -> u32 { unsafe { ptr_other(o) as u32 } }
#[inline(always)] pub unsafe fn ctor_obj_cptr(o: *mut Object) -> *mut *mut Object { unsafe { (&raw mut (*o.cast::<Ctor>()).objs).cast() } }
#[inline(always)] pub unsafe fn ctor_scalar_cptr(o: *mut Object) -> *mut u8 {
    unsafe { ctor_obj_cptr(o).add(ctor_num_objs(o) as usize).cast() }
}
#[inline(always)] pub unsafe fn ctor_get(o: *mut Object, i: u32) -> *mut Object { unsafe { *ctor_obj_cptr(o).add(i as usize) } }
#[inline(always)] pub unsafe fn ctor_set(o: *mut Object, i: u32, v: *mut Object) { unsafe { *ctor_obj_cptr(o).add(i as usize) = v } }
#[inline(always)] pub unsafe fn ctor_set_tag(o: *mut Object, tag: u8) { unsafe { (*o).tag = tag } }
/// `lean_ctor_release`: field `i` dropped and replaced by `box(0)`
#[inline(always)] pub unsafe fn ctor_release(o: *mut Object, i: u32) {
    unsafe { let f = ctor_obj_cptr(o).add(i as usize); dec(*f); *f = box_(0) }
}
/// `lean_ctor_get_usize`/`set_usize`: `i` counts words from the first field, so it is at least `num_objs`
#[inline(always)] pub unsafe fn ctor_get_usize(o: *mut Object, i: u32) -> usize { unsafe { *ctor_obj_cptr(o).add(i as usize).cast() } }
#[inline(always)] pub unsafe fn ctor_set_usize(o: *mut Object, i: u32, v: usize) { unsafe { *ctor_obj_cptr(o).add(i as usize).cast() = v } }
/// `lean_ctor_get_uint8` .. `float32`: `off` is a byte offset from the first field, past the object fields
#[inline(always)] pub unsafe fn ctor_get_scalar<T: Copy>(o: *mut Object, off: u32) -> T { unsafe { ctor_obj_cptr(o).cast::<u8>().add(off as usize).cast::<T>().read_unaligned() } }
#[inline(always)] pub unsafe fn ctor_set_scalar<T: Copy>(o: *mut Object, off: u32, v: T) { unsafe { ctor_obj_cptr(o).cast::<u8>().add(off as usize).cast::<T>().write_unaligned(v) } }

/// `lean_alloc_array`: always `lean_alloc_object`, which sets `cs_sz` itself
#[inline(always)] pub fn alloc_array(size: usize, capacity: usize) -> *mut Object {
    unsafe {
        let o = lean_alloc_object(size_of::<Array>() + size_of::<usize>() * capacity);
        set_st_header(o, TAG_ARRAY, 0);
        let a = o.cast::<Array>();
        (*a).size = size;
        (*a).capacity = capacity;
        o
    }
}
#[inline(always)] pub unsafe fn array_size(o: *const Object) -> usize { unsafe { (*o.cast::<Array>()).size } }
#[inline(always)] pub unsafe fn array_capacity(o: *const Object) -> usize { unsafe { (*o.cast::<Array>()).capacity } }
#[inline(always)] pub unsafe fn array_cptr(o: *mut Object) -> *mut *mut Object { unsafe { (&raw mut (*o.cast::<Array>()).data).cast() } }
#[inline(always)] pub unsafe fn array_set_size(o: *mut Object, n: usize) { unsafe { (*o.cast::<Array>()).size = n } }
#[inline(always)] pub unsafe fn array_get_core(o: *mut Object, i: usize) -> *mut Object { unsafe { *array_cptr(o).add(i) } }
#[inline(always)] pub unsafe fn array_set_core(o: *mut Object, i: usize, v: *mut Object) { unsafe { *array_cptr(o).add(i) = v } }

/// `lean_alloc_sarray`: `elem_size` goes in `other`
#[inline(always)] pub fn alloc_sarray(elem_size: u32, size: usize, capacity: usize) -> *mut Object {
    unsafe {
        let o = lean_alloc_object(size_of::<SArray>() + elem_size as usize * capacity);
        set_st_header(o, TAG_SCALAR_ARRAY, elem_size as u8);
        let a = o.cast::<SArray>();
        (*a).size = size;
        (*a).capacity = capacity;
        o
    }
}
#[inline(always)] pub unsafe fn sarray_elem_size(o: *const Object) -> u32 { unsafe { ptr_other(o) as u32 } }
#[inline(always)] pub unsafe fn sarray_size(o: *const Object) -> usize { unsafe { (*o.cast::<SArray>()).size } }
#[inline(always)] pub unsafe fn sarray_capacity(o: *const Object) -> usize { unsafe { (*o.cast::<SArray>()).capacity } }
#[inline(always)] pub unsafe fn sarray_set_size(o: *mut Object, n: usize) { unsafe { (*o.cast::<SArray>()).size = n } }
#[inline(always)] pub unsafe fn sarray_cptr(o: *mut Object) -> *mut u8 { unsafe { (&raw mut (*o.cast::<SArray>()).data).cast() } }

/// `lean_box_uint32` on a 64-bit machine is `lean_box`; the 64-bit scalars go in a ctor of no fields
#[inline(always)] pub fn box_uint32(v: u32) -> *mut Object { box_(v as usize) }
#[inline(always)] pub fn unbox_uint32(o: *const Object) -> u32 { unbox(o) as u32 }
#[inline(always)] fn box_scalar<T: Copy>(v: T) -> *mut Object {
    let r = alloc_ctor(0, 0, size_of::<T>() as u32);
    unsafe { ctor_set_scalar(r, 0, v) }
    r
}
#[inline(always)] pub fn box_uint64(v: u64) -> *mut Object { box_scalar(v) }
#[inline(always)] pub fn box_usize(v: usize) -> *mut Object { box_scalar(v) }
#[inline(always)] pub fn box_float(v: f64) -> *mut Object { box_scalar(v) }
#[inline(always)] pub fn box_float32(v: f32) -> *mut Object { box_scalar(v) }
#[inline(always)] pub unsafe fn unbox_uint64(o: *mut Object) -> u64 { unsafe { ctor_get_scalar(o, 0) } }
#[inline(always)] pub unsafe fn unbox_usize(o: *mut Object) -> usize { unsafe { ctor_get_scalar(o, 0) } }
#[inline(always)] pub unsafe fn unbox_float(o: *mut Object) -> f64 { unsafe { ctor_get_scalar(o, 0) } }
#[inline(always)] pub unsafe fn unbox_float32(o: *mut Object) -> f32 { unsafe { ctor_get_scalar(o, 0) } }

// ---------------------------------------------------------------- the safe types an export is written in

/// A borrowed argument (`@&`, `b_lean_obj_arg`): Lean holds the reference for the whole call, so `'a` is the call.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct B<'a>(NonNull<Object>, PhantomData<&'a Object>);
/// An owned object (an argument Lean hands over, or a result): dropping it is `lean_dec`.
#[repr(transparent)]
pub struct O(NonNull<Object>);

impl Drop for O { fn drop(&mut self) { unsafe { dec(self.0.as_ptr()) } } }
impl O {
    /// Safety: `p` is a reference the caller owns and gives up
    unsafe fn own(p: *mut Object) -> O { O(unsafe { NonNull::new_unchecked(p) }) }
    pub fn borrow(&self) -> B<'_> { B(self.0, PhantomData) }
    pub fn into_raw(self) -> *mut Object { let p = self.0.as_ptr(); core::mem::forget(self); p }
}
/// `lean_box(n)`: a scalar, `n < 2^63`
pub fn boxed(n: usize) -> O { unsafe { O::own(box_(n)) } }
impl<'a> B<'a> {
    fn p(self) -> *mut Object { self.0.as_ptr() }
    /// `lean_inc`: a reference of its own
    pub fn to_owned(self) -> O { unsafe { inc(self.p()); O::own(self.p()) } }
    pub fn is_scalar(self) -> bool { is_scalar(self.p()) }
    pub fn unbox(self) -> usize { unbox(self.p()) }
    /// `lean_obj_tag`: the ctor tag of a heap object, the value of a scalar
    pub fn tag(self) -> u32 { unsafe { obj_tag(self.p()) } }
    /// field `i` of a ctor; panics on anything else or an index past its fields
    pub fn field(self, i: u32) -> B<'a> {
        assert!(!self.is_scalar() && unsafe { is_ctor(self.p()) && i < ctor_num_objs(self.p()) }, "lean::B::field {i}: not a field");
        B(unsafe { NonNull::new_unchecked(ctor_get(self.p(), i)) }, PhantomData)
    }
    /// the elements of an `Array`
    pub fn array(self) -> &'a [B<'a>] {
        assert!(!self.is_scalar() && unsafe { ptr_tag(self.p()) } == TAG_ARRAY, "lean::B::array: not an Array");
        unsafe { core::slice::from_raw_parts(array_cptr(self.p()).cast(), array_size(self.p())) }
    }
    /// the bytes of a scalar array (`ByteArray`, `FloatArray`): `size · elem_size` of them
    pub fn bytes(self) -> &'a [u8] {
        assert!(!self.is_scalar() && unsafe { ptr_tag(self.p()) } == TAG_SCALAR_ARRAY, "lean::B::bytes: not a scalar array");
        unsafe { core::slice::from_raw_parts(sarray_cptr(self.p()), sarray_size(self.p()) * sarray_elem_size(self.p()) as usize) }
    }
}

/// A fresh scalar array, `rc` 1, filled through `bytes_mut` before it becomes an `O`.
pub struct SArr(O);
impl SArr {
    /// `n` elements of `elem` bytes, size = capacity = `n`; the contents are undefined until written
    pub fn new(elem: u32, n: usize) -> SArr { SArr(unsafe { O::own(alloc_sarray(elem, n, n)) }) }
    pub fn bytes_mut(&mut self) -> &mut [u8] {
        let p = self.0.0.as_ptr();
        unsafe { core::slice::from_raw_parts_mut(sarray_cptr(p), sarray_size(p) * sarray_elem_size(p) as usize) }
    }
}
impl From<SArr> for O { fn from(a: SArr) -> O { a.0 } }

/// `lean_alloc_ctor(tag, N, scalars.len())` with `objs` as its fields and `scalars` copied after them
pub fn ctor<const N: usize>(tag: u8, objs: [O; N], scalars: &[u8]) -> O {
    let o = alloc_ctor(tag, N as u32, scalars.len() as u32);
    for (i, f) in objs.into_iter().enumerate() { unsafe { ctor_set(o, i as u32, f.into_raw()) } }
    unsafe { core::ptr::copy_nonoverlapping(scalars.as_ptr(), ctor_scalar_cptr(o), scalars.len()); O::own(o) }
}
/// An `Array` of `items`, size = capacity = their count
pub fn arr<I: ExactSizeIterator<Item = O>>(items: I) -> O {
    let n = items.len();
    let o = alloc_array(n, n);
    let mut k = 0;
    for f in items { assert!(k < n, "lean::arr: more items than len()"); unsafe { array_set_core(o, k, f.into_raw()) }; k += 1 }
    assert!(k == n, "lean::arr: {k} items, len() said {n}");
    unsafe { O::own(o) }
}
pub fn box_u64(v: u64) -> O { unsafe { O::own(box_uint64(v)) } }
pub fn box_f64(v: f64) -> O { unsafe { O::own(box_float(v)) } }

/// A Lean extern under its `@[extern]` name, in an export file that denies `unsafe_code`: the item gets the one
/// attribute that needs `unsafe`, so the export files hold no `unsafe` token (`forbid` would reject even the macro's
/// `allow`).
#[cfg_attr(test, allow(unused_macros))] // the export files are not built under `cargo test`
macro_rules! export {
    ($($(#[$m:meta])* fn $name:ident($($a:ident: $t:ty),* $(,)?) $(-> $r:ty)? $body:block)*) => {$(
        $(#[$m])* #[allow(unsafe_code)] #[unsafe(no_mangle)] pub extern "C" fn $name($($a: $t),*) $(-> $r)? $body
    )*};
}
#[cfg_attr(test, allow(unused_imports))]
pub(crate) use export;

/// The twins `test/abi.c` calls beside the `lean.h` originals, in the separate object `build.sh` makes with feature `abi`.
#[cfg(feature = "abi")]
pub mod abi {
    use super::*;
    macro_rules! twin {
        ($($sym:ident = $f:ident($($a:ident: $t:ty),*) $(-> $r:ty)?;)*) => {$(
            #[unsafe(no_mangle)] pub unsafe extern "C" fn $sym($($a: $t),*) $(-> $r)? { #[allow(unused_unsafe)] unsafe { $f($($a),*) } }
        )*};
    }
    twin! {
        qrs_abi_is_scalar = is_scalar(o: *const Object) -> bool;
        qrs_abi_box = box_(n: usize) -> *mut Object;
        qrs_abi_unbox = unbox(o: *const Object) -> usize;
        qrs_abi_align = align(v: usize, a: usize) -> usize;
        qrs_abi_ptr_tag = ptr_tag(o: *const Object) -> u8;
        qrs_abi_ptr_other = ptr_other(o: *const Object) -> u8;
        qrs_abi_obj_tag = obj_tag(o: *const Object) -> u32;
        qrs_abi_is_mt = is_mt(o: *const Object) -> bool;
        qrs_abi_is_st = is_st(o: *const Object) -> bool;
        qrs_abi_is_persistent = is_persistent(o: *const Object) -> bool;
        qrs_abi_is_exclusive = is_exclusive(o: *const Object) -> bool;
        qrs_abi_is_shared = is_shared(o: *const Object) -> bool;
        qrs_abi_is_ctor = is_ctor(o: *const Object) -> bool;
        qrs_abi_inc_ref_n = inc_ref_n(o: *mut Object, n: usize);
        qrs_abi_inc_ref = inc_ref(o: *mut Object);
        qrs_abi_dec_ref = dec_ref(o: *mut Object);
        qrs_abi_inc = inc(o: *mut Object);
        qrs_abi_inc_n = inc_n(o: *mut Object, n: usize);
        qrs_abi_dec = dec(o: *mut Object);
        qrs_abi_set_st_header = set_st_header(o: *mut Object, tag: u8, other: u8);
        qrs_abi_set_non_heap_header = set_non_heap_header(o: *mut Object, sz: usize, tag: u8, other: u8);
        qrs_abi_alloc_small_object = alloc_small_object(sz: u32) -> *mut Object;
        qrs_abi_alloc_ctor_memory = alloc_ctor_memory(sz: u32) -> *mut Object;
        qrs_abi_alloc_ctor = alloc_ctor(tag: u8, num_objs: u32, scalar_sz: u32) -> *mut Object;
        qrs_abi_ctor_num_objs = ctor_num_objs(o: *const Object) -> u32;
        qrs_abi_ctor_obj_cptr = ctor_obj_cptr(o: *mut Object) -> *mut *mut Object;
        qrs_abi_ctor_scalar_cptr = ctor_scalar_cptr(o: *mut Object) -> *mut u8;
        qrs_abi_ctor_get = ctor_get(o: *mut Object, i: u32) -> *mut Object;
        qrs_abi_ctor_set = ctor_set(o: *mut Object, i: u32, v: *mut Object);
        qrs_abi_ctor_set_tag = ctor_set_tag(o: *mut Object, tag: u8);
        qrs_abi_ctor_release = ctor_release(o: *mut Object, i: u32);
        qrs_abi_ctor_get_usize = ctor_get_usize(o: *mut Object, i: u32) -> usize;
        qrs_abi_ctor_set_usize = ctor_set_usize(o: *mut Object, i: u32, v: usize);
        qrs_abi_alloc_array = alloc_array(size: usize, capacity: usize) -> *mut Object;
        qrs_abi_array_size = array_size(o: *const Object) -> usize;
        qrs_abi_array_capacity = array_capacity(o: *const Object) -> usize;
        qrs_abi_array_cptr = array_cptr(o: *mut Object) -> *mut *mut Object;
        qrs_abi_array_set_size = array_set_size(o: *mut Object, n: usize);
        qrs_abi_array_get_core = array_get_core(o: *mut Object, i: usize) -> *mut Object;
        qrs_abi_array_set_core = array_set_core(o: *mut Object, i: usize, v: *mut Object);
        qrs_abi_alloc_sarray = alloc_sarray(elem_size: u32, size: usize, capacity: usize) -> *mut Object;
        qrs_abi_sarray_elem_size = sarray_elem_size(o: *const Object) -> u32;
        qrs_abi_sarray_size = sarray_size(o: *const Object) -> usize;
        qrs_abi_sarray_capacity = sarray_capacity(o: *const Object) -> usize;
        qrs_abi_sarray_set_size = sarray_set_size(o: *mut Object, n: usize);
        qrs_abi_sarray_cptr = sarray_cptr(o: *mut Object) -> *mut u8;
        qrs_abi_box_uint32 = box_uint32(v: u32) -> *mut Object;
        qrs_abi_unbox_uint32 = unbox_uint32(o: *const Object) -> u32;
        qrs_abi_box_uint64 = box_uint64(v: u64) -> *mut Object;
        qrs_abi_box_usize = box_usize(v: usize) -> *mut Object;
        qrs_abi_box_float = box_float(v: f64) -> *mut Object;
        qrs_abi_box_float32 = box_float32(v: f32) -> *mut Object;
        qrs_abi_unbox_uint64 = unbox_uint64(o: *mut Object) -> u64;
        qrs_abi_unbox_usize = unbox_usize(o: *mut Object) -> usize;
        qrs_abi_unbox_float = unbox_float(o: *mut Object) -> f64;
        qrs_abi_unbox_float32 = unbox_float32(o: *mut Object) -> f32;
    }
    /// The scalar accessors are one generic twin; C calls them per width.
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_get_uint8(o: *mut Object, off: u32) -> u8 { unsafe { ctor_get_scalar(o, off) } }
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_get_uint16(o: *mut Object, off: u32) -> u16 { unsafe { ctor_get_scalar(o, off) } }
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_get_uint32(o: *mut Object, off: u32) -> u32 { unsafe { ctor_get_scalar(o, off) } }
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_get_uint64(o: *mut Object, off: u32) -> u64 { unsafe { ctor_get_scalar(o, off) } }
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_get_float(o: *mut Object, off: u32) -> f64 { unsafe { ctor_get_scalar(o, off) } }
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_set_uint8(o: *mut Object, off: u32, v: u8) { unsafe { ctor_set_scalar(o, off, v) } }
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_set_uint16(o: *mut Object, off: u32, v: u16) { unsafe { ctor_set_scalar(o, off, v) } }
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_set_uint32(o: *mut Object, off: u32, v: u32) { unsafe { ctor_set_scalar(o, off, v) } }
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_set_uint64(o: *mut Object, off: u32, v: u64) { unsafe { ctor_set_scalar(o, off, v) } }
    #[unsafe(no_mangle)] pub unsafe extern "C" fn qrs_abi_ctor_set_float(o: *mut Object, off: u32, v: f64) { unsafe { ctor_set_scalar(o, off, v) } }
}
