//! interp.rs's Lean exports: the evaluator's own dispatch key and the guid draw.
#![deny(unsafe_code)]
use crate::lean::{B, O, SArr, boxed, ctor, export};
use crate::interp;

export! {
    /// The key a verb spelling reads its cell under (`interp::str_key7`). `s` is `@&`: an owned parameter would make the
    /// compiled caller hand over a reference that is never released.
    fn qlean_str_key7(s: B) -> u64 { interp::str_key7(s.str_bytes()) }

    /// `n` guids drawn from `seed` and the seed after them, as the pair `(ByteArray, UInt32)`.
    fn qlean_draw_guids(seed: u32, n: usize) -> O {
        let mut a = SArr::new(1, 16 * n);
        let s = interp::draw_guids(seed, a.bytes_mut());
        ctor(0, [a.into(), boxed(s as usize)], &[])
    }
}
