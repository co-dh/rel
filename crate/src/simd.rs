//! The AVX-512 kernels: coc.h:598, 646; reduce.c:261. Each picks its path by `cfg`, as the C picks by `#if`.

/// Dispatches by cfg.
pub fn u8_sum(p: &[u8]) -> i64 { unimplemented!() }
pub fn res_unpack(p: &[u8], w: u8, nb: usize, out: &mut [u8]) { unimplemented!() }
pub fn res_unpack_add(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8], tw: u32) -> bool { unimplemented!() }
