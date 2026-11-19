//! The Lean runtime symbols `libqleankernel.a` calls, for a program linked WITHOUT the Lean runtime: the Rel native
//! backend, whose generated C calls the kernels directly. `lean.rs` (the one object layout, shared with qrs by path)
//! supplies the inlines; this crate is the out-of-line rest, replacing `c/rt.c`.
//!
//! Never part of `libqleankernel.a`: a Lean-linked build has the real definitions, and these would clash with them.
//! Every object here is `malloc`ed whole, so freeing one is `free`. A path the native backend cannot reach (calling
//! back into Lean, an index cell with an attribute vector, a `Nat` past 2^63) aborts with a message naming it.
#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(unsafe_code)]
extern crate alloc;

// lean.rs declares the symbols below as `extern` for qrs; here they are defined, which the linker resolves
#[allow(dead_code, unused_macros, unused_imports, clashing_extern_declarations)]
#[path = "../../src/lean.rs"]
mod lean;
#[path = "../../src/rt.rs"]
mod rt;

use core::ffi::{CStr, c_char, c_int};
use core::fmt::Write;
use lean::*;

unsafe extern "C" {
    fn malloc(n: usize) -> *mut u8;
    fn free(p: *mut u8);
    fn abort() -> !;
    fn exit(code: c_int) -> !;
    fn write(fd: c_int, p: *const u8, n: usize) -> isize;
    fn strlen(s: *const c_char) -> usize;
    fn strerror(e: c_int) -> *const c_char;
    fn snprintf(buf: *mut c_char, n: usize, fmt: *const c_char, ...) -> c_int;
}

struct Err;
impl Write for Err {
    fn write_str(&mut self, s: &str) -> core::fmt::Result { unsafe { write(2, s.as_ptr(), s.len()) }; Ok(()) }
}
fn cs<'a>(s: *const c_char) -> &'a CStr { unsafe { CStr::from_ptr(s) } }
/// `qlean rt: <what>` on stderr, then abort
fn die(what: core::fmt::Arguments) -> ! {
    let _ = Err.write_fmt(format_args!("qlean rt: {what}\n"));
    unsafe { abort() }
}

// ---------------------------------------------------------------------------------- allocation

/// `lean_alloc_small_object` checks for NULL
#[unsafe(no_mangle)] pub extern "C" fn mi_malloc_small(sz: usize) -> *mut u8 { unsafe { malloc(sz) } }

#[unsafe(no_mangle)] pub extern "C" fn lean_alloc_object(sz: usize) -> *mut Object {
    let m = unsafe { malloc(sz) };
    if m.is_null() { lean_internal_panic_out_of_memory() }
    m.cast()
}

#[unsafe(no_mangle)] pub extern "C" fn lean_internal_panic_out_of_memory() -> ! { die(format_args!("out of memory")) }

/// heartbeats bound Lean elaboration; a native run has no budget to count them against
#[unsafe(no_mangle)] pub extern "C" fn lean_inc_heartbeat() {}

#[unsafe(no_mangle)] pub extern "C" fn lean_notify_assert(file: *const c_char, line: c_int, cond: *const c_char) {
    die(format_args!("{}:{line}: assertion failed: {}", cs(file).to_string_lossy(), cs(cond).to_string_lossy()))
}

/// `o` and the references it holds: the object kinds a kernel builds (constructors, arrays, scalar arrays,
/// strings); any other kind is one this runtime never makes.
unsafe fn rt_free(o: *mut Object) {
    unsafe {
        if is_ctor(o) {
            for i in 0..ctor_num_objs(o) as usize { dec(*ctor_obj_cptr(o).add(i)) }
        } else {
            match ptr_tag(o) {
                TAG_ARRAY => for i in 0..array_size(o) { dec(array_get_core(o, i)) },
                TAG_SCALAR_ARRAY | TAG_STRING => {}
                t => die(format_args!("freeing an object of tag {t}, which this runtime never allocates")),
            }
        }
        free(o.cast())
    }
}

/// `lean_dec_ref` calls this at a count of 1, or at a negative one: a multi-threaded object counting up to 0
#[unsafe(no_mangle)] pub unsafe extern "C" fn lean_dec_ref_cold(o: *mut Object) {
    unsafe {
        let rc = core::sync::atomic::AtomicI32::from_ptr(&raw mut (*o).rc);
        if (*o).rc == 1 || rc.fetch_add(1, core::sync::atomic::Ordering::AcqRel).wrapping_add(1) == 0 { rt_free(o) }
    }
}

/// the copy a non-exclusive `ByteArray` update makes; it consumes `a`, as Lean's does
#[unsafe(no_mangle)] pub unsafe extern "C" fn lean_copy_byte_array(a: *mut Object) -> *mut Object {
    unsafe {
        let n = sarray_size(a);
        let r = alloc_sarray(1, n, sarray_capacity(a));
        core::ptr::copy_nonoverlapping(sarray_cptr(a), sarray_cptr(r), n);
        dec(a);
        r
    }
}

/// `Array.push`, consuming `a` and `v`: in place when `a` is exclusive with room, else into a copy of twice the
/// capacity that holds its own reference to each element (a plan's literal `parts` is persistent, never exclusive)
#[unsafe(no_mangle)] pub unsafe extern "C" fn lean_array_push(a: *mut Object, v: *mut Object) -> *mut Object {
    unsafe {
        let n = array_size(a);
        let r = if is_exclusive(a) && n < array_capacity(a) { a } else {
            let r = alloc_array(n, 2 * n + 1);
            for i in 0..n { let e = array_get_core(a, i); inc(e); array_set_core(r, i, e) }
            dec(a);
            r
        };
        array_set_core(r, n, v);
        array_set_size(r, n + 1);
        r
    }
}

// ---------------------------------------------------------------------------------- strings and IO errors

#[unsafe(no_mangle)] pub unsafe extern "C" fn lean_mk_string(s: *const c_char) -> *mut Object {
    unsafe {
        let sz = strlen(s);
        let len = (0..sz).filter(|&i| *s.add(i) as u8 & 0xc0 != 0x80).count();
        let o = lean_alloc_object(size_of::<Str>() + sz + 1);
        set_st_header(o, TAG_STRING, 0);
        let p = o.cast::<Str>();
        (*p).size = sz + 1;
        (*p).capacity = sz + 1;
        (*p).length = len;
        core::ptr::copy_nonoverlapping(s.cast::<u8>(), (&raw mut (*p).data).cast(), sz + 1);
        o
    }
}

/// An IO error is a constructor holding its message: this file makes every one and `qlean_rt_io` reads them, so
/// Lean's `IO.Error` constructors are not needed.
#[unsafe(no_mangle)] pub unsafe extern "C" fn lean_mk_io_user_error(s: *mut Object) -> *mut Object {
    unsafe {
        let e = alloc_ctor(0, 1, 0);
        *ctor_obj_cptr(e) = s;
        e
    }
}

#[unsafe(no_mangle)] pub unsafe extern "C" fn lean_decode_io_error(errnum: c_int, fname: *mut Object) -> *mut Object {
    unsafe {
        let mut buf = [0 as c_char; 4096];
        if fname.is_null() { snprintf(buf.as_mut_ptr(), buf.len(), c"%s".as_ptr(), strerror(errnum)) }
        else { snprintf(buf.as_mut_ptr(), buf.len(), c"%s: %s".as_ptr(), string_cstr(fname), strerror(errnum)) };
        lean_mk_io_user_error(lean_mk_string(buf.as_ptr()))
    }
}

/// An `IO` kernel's result `r` (consumed): its value, owned; on an error, `sym: message` on stderr and exit 1.
#[unsafe(no_mangle)] pub unsafe extern "C" fn qlean_rt_io(r: *mut Object, sym: *const c_char) -> *mut Object {
    unsafe {
        if io_result_is_error(r) {
            let m = string_cstr(*ctor_obj_cptr(io_result_get_error(r))).cast::<c_char>();
            let _ = Err.write_fmt(format_args!("{}: {}\n", cs(sym).to_string_lossy(), cs(m).to_string_lossy()));
            exit(1)
        }
        let v = io_result_get_value(r);
        inc(v);
        dec(r);
        v
    }
}

// ---------------------------------------------------------------------------------- paths a native run never takes

#[unsafe(no_mangle)] pub extern "C" fn lean_big_usize_to_nat(_n: usize) -> *mut Object {
    die(format_args!("lean_big_usize_to_nat: a USize past 2^63 as a Nat, which needs Lean's bignums"))
}
#[unsafe(no_mangle)] pub extern "C" fn lean_apply_1(_f: *mut Object, _a1: *mut Object) -> *mut Object {
    die(format_args!("lean_apply_1: a kernel called back into Lean (qlean_stop's message thunk), which a plan's `fail` replaces"))
}
#[unsafe(no_mangle)] pub extern "C" fn lean_apply_2(_f: *mut Object, _a1: *mut Object, _a2: *mut Object) -> *mut Object {
    die(format_args!("lean_apply_2: a kernel called back into Lean (an index cell with an attribute vector)"))
}
#[unsafe(no_mangle)] pub extern "C" fn lean_apply_5(_f: *mut Object, _a1: *mut Object, _a2: *mut Object, _a3: *mut Object,
                                                    _a4: *mut Object, _a5: *mut Object) -> *mut Object {
    die(format_args!("lean_apply_5: a kernel called back into Lean (an index cell with an attribute vector)"))
}
#[unsafe(no_mangle)] pub extern "C" fn lean_register_external_class(_fin: Option<unsafe extern "C" fn(*mut u8)>,
                                                                    _fe: Option<unsafe extern "C" fn(*mut u8, *mut Object)>)
                                                                    -> *mut ExternalClass {
    die(format_args!("lean_register_external_class: an index cell (search.c), which no column of a native run carries"))
}
#[unsafe(no_mangle)] pub extern "C" fn lean_mark_mt(_o: *mut Object) {
    die(format_args!("lean_mark_mt: sharing an object across Lean tasks, which a native run has none of"))
}
#[unsafe(no_mangle)] pub extern "C" fn lean_mark_persistent(_o: *mut Object) {
    die(format_args!("lean_mark_persistent: an index cell (search.c), which no column of a native run carries"))
}
