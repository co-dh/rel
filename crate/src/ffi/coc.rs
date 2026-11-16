//! coc.c's first ten Lean exports, over `lean.rs` types: the encoder, the decoder, the reductions and the comparisons
//! of an encoded integral column (`meta`, `pack`, `n`; the layout is documented at the top of c/coc.c and c/coc.h).
//! Each unpacks the two byte arrays into a `Coc`, makes one call into a kernel and packs the answer.
#![deny(unsafe_code)]
use crate::c::pool;
use crate::coc::{Coc, Meta};
use crate::cocops::{CocMut, GE};
use crate::ffi::{encode_dense, encode_fill};
use crate::lean::{B, O, SArr, ctor, export, nat};
use crate::{codec, os, pod};

/// What C's `fprintf(stderr, …); exit(1)` did for a call no Lean body makes.
fn die(args: core::fmt::Arguments) -> ! {
    os::eprint(args).expect("qlean: stderr");
    os::exit(1)
}

/// coc.h `coc_view`: the column `meta`, `pack` hold, its count cut to what the blocks can hold. A pack whose patch
/// list does not fit is C's `coc_attach` abort; a metadata array with misaligned or missing sections (which C read
/// past) is the same stop.
fn view<'a>(who: &str, meta: B<'a>, pack: B<'a>, n: usize) -> Coc<'a> {
    let Some(m) = Meta::new(meta.bytes(), n) else { die(format_args!("{who}: the metadata array is not a column's 33 * nblk + 16 bytes\n")) };
    let (e, mblk, pb) = (m.res_end(), m.mblk, pack.bytes().len());
    Coc::attach(m, pack.bytes()).unwrap_or_else(|| die(format_args!(
        "qlean: a Frame of Reference pack of {pb} bytes whose residuals end at {e} holds no patch list of {mblk} blocks after them\n")))
}

export! {
    /// Byte offset in the pack of block `bv`, or the pack's length for the block past the last (`Nat`)
    fn qlean_coc_block_start(mv: B, bv: B) -> O {
        let Some(m) = Meta::new(mv.bytes(), usize::MAX) else { die(format_args!("qlean_coc_block_start: the metadata array is not a column's 33 * nblk + 16 bytes\n")) };
        if !bv.is_scalar() {
            die(format_args!("qlean_coc_block_start: the block index is a bignum; a column is bounded by its byte count and cannot have 2^63 blocks\n"))
        }
        nat(codec::block_start(&m, bv.unbox()))
    }
    /// `(meta, pack)` of the dense column `x` of elements `width` bytes wide (2, 4 or 8)
    fn qlean_coc_encode(width: usize, x: B) -> O {
        if !matches!(width, 2 | 4 | 8) { die(format_args!("qlean_coc_encode: element width {width} is not 2, 4 or 8\n")) }
        encode_dense(x.bytes(), width, false, usize::MAX).expect("qlean_coc_encode: a dense buffer cannot fail").into_pair()
    }
    /// `qlean_coc_encode` as `some`, or `none` when the encoded form would not be shorter than `x`
    fn qlean_coc_encode_below(width: usize, x: B) -> O {
        if !matches!(width, 2 | 4 | 8) { die(format_args!("qlean_coc_encode_below: element width {width} is not 2, 4 or 8\n")) }
        // the encoded form must be shorter than the whole elements it replaces
        match encode_dense(x.bytes(), width, false, x.bytes().len() / width * width) { Some(p) => ctor(1, [p.into_pair()], &[]), None => crate::lean::boxed(0) }
    }
    /// The column restored: `n` elements of `width` bytes, little-endian
    fn qlean_coc_decode(width: usize, meta: B, pack: B, n: usize) -> O {
        let c = view("qlean_coc_decode", meta, pack, n);
        // the width is chosen once, outside the block loop
        match width {
            2 => dec::<i16>(&c), 4 => dec::<i32>(&c), 8 => dec::<i64>(&c),
            _ => die(format_args!("qlean_coc_decode: element width {width} is not 2, 4 or 8\n")),
        }
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
    /// How many elements are below `v`
    fn qlean_coc_count_lt(meta: B, pack: B, n: usize, v: u64) -> usize { view("qlean_coc_count_lt", meta, pack, n).count_lt(v as i64) }
    /// Whether any element is the null `nul`
    fn qlean_coc_any_null(nul: u64, meta: B, pack: B, n: usize) -> u8 { view("qlean_coc_any_null", meta, pack, n).any_null(nul as i64) as u8 }
    /// `x op v` as a `Column.bits` payload
    fn qlean_coc_mask_cmp(op: u8, v: u64, meta: B, pack: B, n: usize) -> O {
        let v = v as i64;
        let c = view("qlean_coc_mask_cmp", meta, pack, n);
        if op as i32 > GE { die(format_args!("qlean_coc_mask_cmp: verb {op} is not one of the six in QLean.Kernel.Ew\n")) }
        mask_with(c.meta.n, |out| codec::mask_cmp(pool(), op, v, &c, out))
    }
    /// `k + x` (`neg`: `k - x`) as `some (meta, pack)`, or `none` where the column cannot take it. A shift the metadata
    /// absorbs keeps the pack (shared) and rewrites a copy of the metadata; any other goes back through the writer.
    fn qlean_coc_shift(neg: u8, k: u64, meta: B, pack: B, n: usize) -> O {
        let k = k as i64;
        let src = view("qlean_coc_shift", meta, pack, n);
        match src.shift_ok(k, neg != 0) {
            0 => crate::lean::boxed(0),
            2 => ctor(1, [encode_fill(src.meta.n, 8, &|buf, i0| codec::shift_fill(&src, k, neg != 0, i64::MIN, buf, i0))], &[]),
            _ => {
                let mut m2 = SArr::new(1, meta.bytes().len());
                m2.bytes_mut().copy_from_slice(meta.bytes());
                // the metadata alone, at the count its block sums need
                CocMut::meta_only(m2.bytes_mut(), src.meta.n).unwrap_or_else(|| die(format_args!("qlean_coc_shift: the metadata array is not a column's 33 * nblk + 16 bytes\n"))).shift(k, false);
                ctor(1, [ctor(0, [m2.into(), pack.to_owned()], &[])], &[])
            }
        }
    }
    /// `a op b` over the shorter of the two as a `Column.bits` payload
    fn qlean_coc_mask_cmp_vv(op: u8, ma: B, pa: B, mb: B, pb: B, n: usize) -> O {
        let (mut a, b) = (view("qlean_coc_mask_cmp_vv", ma, pa, n), view("qlean_coc_mask_cmp_vv", mb, pb, n));
        if op as i32 > GE { die(format_args!("qlean_coc_mask_cmp_vv: verb {op} is not one of the six in QLean.Kernel.Ew\n")) }
        // the shorter of the two decides how far the kernel walks
        a.meta.n = a.meta.n.min(b.meta.n);
        let mut deep = pod::uninit::<u32>(a.meta.nblk);
        mask_with(a.meta.n, |out| {
            let nd = codec::cmp_meta(&a, Some(&b), op as i32, 0, out, &mut deep);
            codec::cmp2(pool(), op as i32, &a, &b, &deep[..nd], out)
        })
    }
}

/// The column as `n` elements of `T`, by blocks on the pool
fn dec<T: pod::Lane + Send>(c: &Coc) -> O {
    let mut out = SArr::new(1, c.meta.n * size_of::<T>());
    codec::decode(pool(), c, pod::cast_mut::<T>(out.bytes_mut()).expect("qlean_coc_decode: the result array is misaligned for its element"));
    out.into()
}



/// coc.c `mask_alloc` and the kernel that fills it: a `Column.bits` payload of `ceil(n / 8)` bytes inside the `ceil(n / 64)`
/// words the kernels write (the bits between `n` and the last word's end are the kernel's to set to 0); `f` gets the
/// words, any contents.
fn mask_with(n: usize, f: impl FnOnce(&mut [u64])) -> O {
    let mut a = SArr::with_capacity(1, n.div_ceil(8), n.div_ceil(64) * 8);
    f(pod::cast_mut::<u64>(a.capacity_mut()).expect("a bitmap array is misaligned for its 64-bit words"));
    a.into()
}
