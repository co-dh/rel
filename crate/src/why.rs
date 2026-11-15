#![forbid(unsafe_code)]
//! Replaces `snprintf(why, cap, ...)`: NUL-terminates, truncates, never fails.

pub struct Why<'a> { buf: &'a mut [u8], at: usize }
impl<'a> Why<'a> {
    pub fn new(buf: &'a mut [u8]) -> Self { Why { buf, at: 0 } }
    /// Overwrites the message, as each `snprintf(why, ...)` does.
    pub fn say(&mut self, a: core::fmt::Arguments) {
        self.at = 0;
        let _ = core::fmt::write(self, a); // write_str never fails
        if let Some(z) = self.buf.get_mut(self.at) { *z = 0 }
    }
}
impl core::fmt::Write for Why<'_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let n = s.len().min(self.buf.len().saturating_sub(1 + self.at));
        self.buf[self.at..self.at + n].copy_from_slice(&s.as_bytes()[..n]);
        self.at += n;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn truncates_and_terminates() {
        let mut b = [0xffu8; 6];
        Why::new(&mut b).say(format_args!("part {}", 12345));
        assert_eq!(&b, b"part \0");
    }
    #[test] fn overwrites_and_empty_cap() {
        let mut b = [0u8; 8];
        let mut w = Why::new(&mut b);
        w.say(format_args!("abc")); w.say(format_args!("d"));
        assert_eq!(&b[..2], b"d\0");
        Why::new(&mut []).say(format_args!("x"));
    }
}
