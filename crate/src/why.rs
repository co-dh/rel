#![forbid(unsafe_code)]
//! Replaces `snprintf(why, cap, ...)`: NUL-terminates, truncates, never fails.

pub struct Why<'a> { buf: &'a mut [u8], at: usize }
impl<'a> Why<'a> {
    pub fn new(buf: &'a mut [u8]) -> Self { unimplemented!() }
    pub fn say(&mut self, a: core::fmt::Arguments) { unimplemented!() }
}
