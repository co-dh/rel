#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! `exc_layout` / `for_layout` / `alp_layout` (coc.h:199, 209, 1518) as one function, and own.c's `exc_ok`.
use crate::why::Why;

/// `for_layout` frm=0, frm=1, `alp_layout`.
pub enum Tail { None, Frames, Exps }
pub struct ExcLayout { pub raw: usize, pub off: usize, pub pos: usize, pub tail: usize, pub size: usize }

/// None = overflow.
pub fn exc_layout(nblk: usize, nexc: usize, esz: usize, tail: Tail) -> Option<ExcLayout> { unimplemented!() }
pub fn exc_ok(t: &[u8], nblk: usize, nexc: u64, esz: usize, part: i32, tail: Tail, why: &mut Why) -> bool {
    unimplemented!()
}
