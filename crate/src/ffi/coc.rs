//! coc.rs's first ten Lean exports, over `lean.rs` types: the encoder, the decoder, the reductions and the comparisons
//! of an encoded integral column (`meta`, `pack`, `n`; the layout is documented at the top of rust/src/coc.rs and rust/src/coc.rs).
//! Each unpacks the two byte arrays into a `Coc`, makes one call into a kernel and packs the answer.
#![deny(unsafe_code)]
use crate::c::pool;
use crate::alp::Cocf;
use crate::coc::{self, Coc, Meta, ViewErr};
use crate::cocops;
use crate::blocks::Blocks;
use crate::ffi::{Form, Sink};
use crate::lean::{B, O, SArr, boxed, ctor, export};
use crate::{codec, os, pod};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use crate::cocops::CocMut;

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
/// structural.rs `alp_view`: an ALP column's metadata, blob and pack, `n` clamped to what the blocks hold.
pub fn alp_view<'a>(mv: B<'a>, pv: B<'a>, av: B<'a>, n: usize) -> Cocf<'a> {
    Cocf::view(mv.bytes(), pv.bytes(), av.bytes(), n).unwrap_or_else(|| die(format_args!(
        "qlean: an ALP column's metadata of {} bytes or its blob of {} are short or misaligned\n", mv.bytes().len(), av.bytes().len())))
}

export! {
    /// `boolsOf n b`: the bitmap `b`'s first `n` bits as the `u1` Frame of Reference column, a block at a time (a
    /// block starts on a byte: `lo` is a multiple of the block size); a bit past `b` is 0.
    fn qlean_coc_bools_of(n: usize, b: B) -> O {
        let b = b.bytes();
        Sink::new(n, 1, Form::For).bools(crate::QLEAN_COST_ARITH, &|lo, hi, o| {
            let s = b.get(lo / 8..hi.div_ceil(8).min(b.len())).unwrap_or(&[]);
            o[..s.len()].copy_from_slice(s);
            o[s.len()..].fill(0)
        })
    }
    /// `(meta, pack)` of the dense column `x` of elements `width` bytes wide (`elt_width`)
    fn qlean_coc_encode(width: usize, x: B) -> O { encode(x, elt_width("qlean_coc_encode", width), Form::For, false) }
    /// The column restored: `n` elements of `width` bytes, little-endian
    fn qlean_coc_decode(width: usize, meta: B, pack: B, n: usize) -> O {
        let c = view("qlean_coc_decode", meta, pack, n);
        // the width is chosen once, outside the block loop
        crate::by_width!(int elt_width("qlean_coc_decode", width), dec(&c))
    }
    /// An `Int64` crosses the boundary as `uint64_t` (the proto gate). A reduction of the column, `op` one of `QLean.Kernel.Coc.Over`'s six: add, multiply, lesser, greater, all, any
    fn qlean_coc_over(op: u8, nul: u64, meta: B, pack: B, n: usize) -> u64 {
        let nul = nul as i64;
        let c = view("qlean_coc_over", meta, pack, n);
        match op {
            0 => c.sum(nul),
            1 => c.prd(nul),
            2 => c.min(nul) as u64,
            3 => c.max(nul) as u64,
            4 => c.all() as u64,
            5 => c.any() as u64,
            _ => die(format_args!("qlean_coc_over: verb {op} is not one of the six in QLean.Kernel.Coc.Over\n")),
        }
    }
    /// `k + x` (`neg`: `k - x`) as `some (meta, pack)`, or `none` where the column cannot take it. A shift the metadata
    /// absorbs keeps the pack (shared) and rewrites a copy of the metadata; any other goes back through the writer.
    fn qlean_coc_shift(neg: u8, k: u64, meta: B, pack: B, n: usize) -> O {
        let k = k as i64;
        let src = view("qlean_coc_shift", meta, pack, n);
        match src.shift_ok(k, neg != 0) {
            0 => boxed(0),
            2 => ctor(1, [Sink::new(src.meta.n, 8, Form::For).answer(&|buf: &mut [i64], i0: usize| codec::shift_fill(&src, k, neg != 0, i64::MIN, buf, i0))], &[]),
            _ => {
                let mut m2 = SArr::new(1, meta.bytes().len());
                m2.bytes_mut().copy_from_slice(meta.bytes());
                // the metadata alone, at the count its block sums need
                CocMut::meta_only(m2.bytes_mut(), src.meta.n).unwrap_or_else(|| die(format_args!("qlean_coc_shift: the metadata array is not a column's 33 * nblk + 24 bytes\n"))).shift(k, false);
                ctor(1, [ctor(0, [m2.into(), pack.to_owned()], &[])], &[])
            }
        }
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




/// coc.rs `cocf_meta_view` with the pack set (rust/src/coc.rs's `cocf_view`): the ALP column `meta`, `pack`, `alp` hold, its count cut
/// to what the blocks can hold. A metadata or ALP array with misaligned or missing sections, which C read past, is a stop.
pub fn fview<'a>(who: &str, meta: B<'a>, pack: B<'a>, alp: B<'a>, n: usize) -> Cocf<'a> {
    let mut f = Cocf::meta_view(meta.bytes(), alp.bytes(), n).unwrap_or_else(|| die(format_args!(
        "{who}: the metadata array is not a column's 33 * nblk + 24 bytes, or the alp array is misaligned or shorter than its header says\n")));
    f.c.pack = pack.bytes();
    f
}

/// rust/src/coc.rs `coc_val_vv`: `some (meta, pack)` of `a op b` (`b` read from `s` elements back, `fill` off its ends) as the writer
/// encodes what the dense engine writes, `none` where `Coc::vv_ok` refuses; `s = 0` is `x op y`, and `a = b` the prior form.
pub fn val_vv(op: u8, a: &Coc, b: &Coc, s: i64, fill: i64) -> O {
    if op > 2 { die(format_args!("coc_val_vv: verb {op} is not one of the three in QLean.Kernel.Ew\n")) }
    if !a.vv_ok(b, op as i32, s, fill) { return boxed(0) }
    ctor(1, [Sink::new(a.meta.n, 8, Form::For).answer(&|buf: &mut [i64], i0: usize| cocops::vv_fill(a, b, op as i32, s, fill, i0, buf))], &[])
}

export! {
    /// `(meta, (pack, alp))` of the dense `f64` column `x`
    fn qlean_alp_encode_f64(x: B) -> O { encode(x, 8, Form::Alp, false) }
    /// `(meta, (pack, alp))` of the dense `f32` column `x`
    fn qlean_alp_encode_f32(x: B) -> O { encode(x, 4, Form::Alp, false) }
    /// `qlean_alp_encode_f64` as `some`, or `none` when the three parts would not be shorter than `x`
    fn qlean_alp_encode_below_f64(x: B) -> O { encode(x, 8, Form::Alp, true) }
    /// `qlean_alp_encode_f32` as `some`, or `none` when the three parts would not be shorter than `x`
    fn qlean_alp_encode_below_f32(x: B) -> O { encode(x, 4, Form::Alp, true) }
    /// The column restored: `n` little-endian `f64`
    fn qlean_alp_decode_f64(meta: B, pack: B, alp: B, n: usize) -> O { alp_dec(8, fview("qlean_alp_decode_f64", meta, pack, alp, n)) }
    /// The column restored: `n` little-endian `f32`
    fn qlean_alp_decode_f32(meta: B, pack: B, alp: B, n: usize) -> O { alp_dec(4, fview("qlean_alp_decode_f32", meta, pack, alp, n)) }
    /// Element `idxv[j]` of the column, `fill` where `idxv[j]` is not below `n`, at the column's own width
    fn qlean_alp_gather(fill: u64, meta: B, pack: B, alp: B, n: usize, idxv: B) -> O {
        let f = fview("qlean_alp_gather", meta, pack, alp, n);
        let ib = idxv.bytes();
        let idx = pod::cast::<i64>(&ib[..ib.len() / 8 * 8]).expect("qlean_alp_gather: the index array is misaligned for its elements");
        let mut res = SArr::new(1, idx.len() * if f.f32 { 4 } else { 8 });
        codec::alp_gather(pool(), fill, &f, idx, res.bytes_mut());
        res.into()
    }
}

/// The dense column `x` of `w`-byte elements through a `Sink` of `form`: the answer, or with `shrinks` `some` of it, `none`
/// where the encoded form is not shorter than `x` (the `*_below` exports).
pub fn encode(x: B, w: usize, form: Form, shrinks: bool) -> O {
    let (s, p) = (Sink::new(x.bytes().len() / w, w, form), Blocks::dense(x.bytes(), w));
    if !shrinks { return s.answer(&p) }
    s.write(&p, true).map_or_else(|| boxed(0), |a| ctor(1, [a], &[]))
}
/// The ALP column as `f.c.meta.n` elements of `w` bytes, by blocks on the pool
pub fn alp_dec(w: usize, f: Cocf) -> O {
    let mut out = SArr::new(1, f.c.meta.n * w);
    codec::alp_decode(pool(), &f, out.bytes_mut());
    out.into()
}
/// coc.rs `coc_meta_view`: the metadata alone, as `view`'s metadata stop.
pub fn meta<'a>(who: &str, mv: B<'a>, n: usize) -> Meta<'a> {
    Meta::new(mv.bytes(), n).unwrap_or_else(|| die(format_args!("{who}: {}\n", ViewErr::Meta)))
}
