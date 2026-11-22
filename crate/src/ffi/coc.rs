//! coc.rs's first ten Lean exports, over `lean.rs` types: the encoder, the decoder, the reductions and the comparisons
//! of an encoded integral column (`meta`, `pack`, `n`; the layout is documented at the top of rust/src/coc.rs and rust/src/coc.rs).
//! Each unpacks the two byte arrays into a `Coc`, makes one call into a kernel and packs the answer.
#![deny(unsafe_code)]
use crate::c::pool;
use crate::coc::{self, Coc, ViewErr};
use crate::blocks::Blocks;
use crate::ffi::Sink;
use crate::lean::{B, O, SArr, boxed, ctor, export};
use crate::{codec, os, pod};

/// What C's `fprintf(stderr, …); exit(1)` did for a call no Lean body makes.
pub fn die(args: core::fmt::Arguments) -> ! {
    os::eprint(args).expect("qlean: stderr");
    os::exit(1)
}

/// coc.rs `coc_view`: the column `meta`, `pack` hold, its count cut to what the blocks can hold. A pack whose patch
/// list does not fit is C's `coc_attach` abort; a metadata array with misaligned or missing sections (which C read
/// past) is the same stop.
pub fn view<'a>(who: &str, meta: B<'a>, pack: B<'a>, n: usize) -> Coc<'a> {
    coc::view(meta.bytes(), pack.bytes(), n).unwrap_or_else(|e| match e {
        ViewErr::Meta => die(format_args!("{who}: {e}\n")),
        ViewErr::Pack { .. } => die(format_args!("qlean: {e}\n")),
    })
}

export! {
    /// `(meta, pack)` of the dense column `x` of elements `width` bytes wide (`elt_width`), its null rows the set bits of
    /// `nul` (empty: none)
    fn qlean_coc_encode(width: usize, x: B, nul: B) -> O { encode(x, elt_width("qlean_coc_encode", width), false, nul.bytes()) }
    /// The column restored: `n` elements of `width` bytes, little-endian
    fn qlean_coc_decode(width: usize, meta: B, pack: B, n: usize) -> O {
        let c = view("qlean_coc_decode", meta, pack, n);
        // the width is chosen once, outside the block loop
        crate::by_width!(int elt_width("qlean_coc_decode", width), dec(&c))
    }
}

/// `width` where it is a Frame of Reference element width, `QAtomicType.width` of an integral type: a power of two
/// bytes up to 8 (a boolean's 0/1 bytes are width 1); a stop naming `who` otherwise.
pub fn elt_width(who: &str, width: usize) -> usize {
    if !(width.is_power_of_two() && width <= 8) { die(format_args!("{who}: element width {width} is not 1, 2, 4 or 8\n")) }
    width
}
/// The column as `n` elements of `T`, by blocks on the pool
pub fn dec<T: pod::Elt + Send>(c: &Coc) -> O {
    let mut out = SArr::new(1, c.meta.n * size_of::<T>());
    codec::decode(pool(), c, pod::cast_mut::<T>(out.bytes_mut()).expect("qlean_coc_decode: the result array is misaligned for its element"));
    out.into()
}






/// The dense column `x` of `w`-byte elements through a `Sink`: the answer, or with `shrinks` `some` of it, `none`
/// where the encoded form is not shorter than `x` (the `*_below` exports).
pub fn encode(x: B, w: usize, shrinks: bool, nul: &[u8]) -> O {
    let (s, p) = (Sink::new(x.bytes().len() / w, w), Blocks::dense(x.bytes(), w));
    if !shrinks { return s.write_nul(&p, false, nul).expect("qlean_coc_encode: a write with no size test has an answer") }
    s.write_nul(&p, true, nul).map_or_else(|| boxed(0), |a| ctor(1, [a], &[]))
}
