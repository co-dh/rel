#![forbid(unsafe_code)]
//! Column (a), sym.rs (A11): a symbol column as a byte blob plus the `Array Nat` of starts. Rust never sees a
//! `lean_object`: C passes `lean_array_cptr(offs)` as `*const usize`, the boxed words themselves, and `Syms`
//! unboxes them (`w >> 1`; an unboxed word, a bignum pointer, aborts as `off_at` does).



// ---- K20: the kept dictionary hashes and `symdict_concat`'s dictionary half (structural.rs `symtab_*`, `sd_*`) ----






#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    // the specification is sym.rs's byte loops (`sym_eq`) and `memcmp` then lengths (`sym_cmp`): every length 0..20, bytes from both
    // halves of the byte range (q's order is unsigned), and pairs that share a prefix or differ in the last byte only
}

#[cfg(test)]
mod kept_tests {
    use super::*;
    use core::cell::RefCell as RC;


}
