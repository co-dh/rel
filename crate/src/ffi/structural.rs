//! structural.c's Lean exports.
#![deny(unsafe_code)]
use crate::lean::{O, SArr, export};
use crate::{c, pod, structural};

export! {
    /// Spec: `tilLongs n` is `0 .. n - 1` as little-endian `Int64`s. `til 0` is the empty long vector and `til 5` is
    /// `0 1 2 3 4`, measured; a negative count and `0N` are `'domain` and `tilColumn` declines them, so nothing here
    /// has to represent one.
    fn qlean_structural_til(n: usize) -> O {
        let mut a = SArr::new(1, n * 8);
        structural::til(c::pool(), pod::cast_mut(a.bytes_mut()).expect("til: a ByteArray's data is 8-aligned"));
        a.into()
    }
}
