//! The runtime a `no_std` staticlib needs: libc's allocator, a panic handler that reports on fd 2 and aborts,
//! and the two unwinder stubs `panic = "abort"` still references (local after build.sh's objcopy).
use core::alloc::{GlobalAlloc, Layout};

unsafe extern "C" {
    fn aligned_alloc(a: usize, n: usize) -> *mut u8;
    fn free(p: *mut u8);
    fn abort() -> !;
    fn write(fd: i32, p: *const u8, n: usize) -> isize;
}

struct Malloc;
unsafe impl GlobalAlloc for Malloc {
    // aligned_alloc wants a size that is a multiple of the alignment
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        unsafe { aligned_alloc(l.align().max(16), l.size().next_multiple_of(l.align().max(16))) }
    }
    unsafe fn dealloc(&self, p: *mut u8, _: Layout) { unsafe { free(p) } }
}
#[global_allocator]
static A: Malloc = Malloc;

struct Err;
impl core::fmt::Write for Err {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        unsafe { write(2, s.as_ptr(), s.len()) };
        Ok(())
    }
}

#[panic_handler]
fn panic(i: &core::panic::PanicInfo) -> ! {
    let _ = core::fmt::write(&mut Err, format_args!("qlean kernel: {i}\n"));
    unsafe { abort() }
}

#[unsafe(no_mangle)]
extern "C" fn rust_eh_personality() {}
#[unsafe(no_mangle)]
extern "C" fn _Unwind_Resume() -> ! { unsafe { abort() } }
