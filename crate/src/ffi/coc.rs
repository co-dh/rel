//! coc.c's first ten Lean exports, over `lean.rs` types: the encoder, the decoder, the reductions and the comparisons
//! of an encoded integral column (`meta`, `pack`, `n`; the layout is documented at the top of c/coc.c and c/coc.h).
//! Each unpacks the two byte arrays into a `Coc`, makes one call into a kernel and packs the answer.
#![deny(unsafe_code)]
use crate::c::pool;
use crate::coc::{Coc, Meta};
use crate::alp::Cocf;
use crate::cocops::{self, CocMut, GE};
use crate::ffi::{encode_dense, encode_fill};
use crate::lean::{B, O, SArr, boxed, ctor, export, nat};
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
        match encode_dense(x.bytes(), width, false, x.bytes().len() / width * width) { Some(p) => ctor(1, [p.into_pair()], &[]), None => boxed(0) }
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
            0 => boxed(0),
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

/// coc.h `cocf_meta_view` with the pack set (c/coc.c's `cocf_view`): the ALP column `meta`, `pack`, `alp` hold, its count cut
/// to what the blocks can hold. A metadata or ALP array with misaligned or missing sections, which C read past, is a stop.
fn fview<'a>(who: &str, meta: B<'a>, pack: B<'a>, alp: B<'a>, n: usize) -> Cocf<'a> {
    let mut f = Cocf::meta_view(meta.bytes(), alp.bytes(), n).unwrap_or_else(|| die(format_args!(
        "{who}: the metadata array is not a column's 33 * nblk + 16 bytes, or the alp array is misaligned or shorter than its header says\n")));
    f.c.pack = pack.bytes();
    f
}

/// c/coc.c `coc_val_vv`: `some (meta, pack)` of `a op b` (`b` read from `s` elements back, `fill` off its ends) as the writer
/// encodes what the dense engine writes, `none` where `Coc::vv_ok` refuses; `s = 0` is `x op y`, and `a = b` the prior form.
fn val_vv(op: u8, a: &Coc, b: &Coc, s: i64, fill: i64) -> O {
    if op > 2 { die(format_args!("coc_val_vv: verb {op} is not one of the three in QLean.Kernel.Ew\n")) }
    if !a.vv_ok(b, op as i32, s, fill) { return boxed(0) }
    ctor(1, [encode_fill(a.meta.n, 8, &|buf, i0| cocops::vv_fill(a, b, op as i32, s, fill, i0, buf))], &[])
}

export! {
    /// `Option (ByteArray × ByteArray)`: the new (meta, pack) of `x + y`, `x - y` or `x * y`
    fn qlean_coc_val_vv(op: u8, ma: B, pa: B, mb: B, pb: B, n: usize) -> O {
        val_vv(op, &view("qlean_coc_val_vv", ma, pa, n), &view("qlean_coc_val_vv", mb, pb, n), 0, 0)
    }
    /// `Option (ByteArray × ByteArray)`: the new (meta, pack) of `x - (k _ x)` and its two siblings, `fill` standing off the end
    fn qlean_coc_val_prior(op: u8, k: u64, fill: u64, meta: B, pack: B, n: usize) -> O {
        let c = view("qlean_coc_val_prior", meta, pack, n);
        val_vv(op, &c, &c, k as i64, fill as i64)
    }
    /// `Option (ByteArray × ByteArray)`: the new (meta, pack) of `x * k`, `none` where `Coc::scale_ok` refuses
    fn qlean_coc_scale(k: u64, meta: B, pack: B, n: usize) -> O {
        let k = k as i64;
        let c = view("qlean_coc_scale", meta, pack, n);
        if !c.scale_ok(k) { return boxed(0) }
        ctor(1, [encode_fill(c.meta.n, 8, &|buf, i0| cocops::scale_fill(&c, k, i0, buf))], &[])
    }
    /// `res_unpack` against `res_unpack_scalar`, both readers of `Column.resAt`'s layout
    fn qlean_coc_unpack_agrees(w: u8, nb: usize) -> u8 { crate::res::res_unpack_agrees(w, nb) as u8 }
    /// The set bits among the first `n` bits of `bits`
    fn qlean_coc_popcount(bits: B, n: usize) -> usize { let p = bits.bytes(); crate::bits::popcount(p, n.min(p.len() * 8)) }
    /// Whether some bit among the first `n` is `set` (`set` clear: is clear)
    fn qlean_coc_some_bit(set: u8, bits: B, n: usize) -> u8 { crate::bits::some_bit(set != 0, bits.bytes(), n) as u8 }
    /// `(meta, (pack, alp))` of the dense `f64` column `x`
    fn qlean_alp_encode_f64(x: B) -> O { alp_encode(x, 8) }
    /// `(meta, (pack, alp))` of the dense `f32` column `x`
    fn qlean_alp_encode_f32(x: B) -> O { alp_encode(x, 4) }
    /// `qlean_alp_encode_f64` as `some`, or `none` when the three parts would not be shorter than `x`
    fn qlean_alp_encode_below_f64(x: B) -> O { alp_encode_below(x, 8) }
    /// `qlean_alp_encode_f32` as `some`, or `none` when the three parts would not be shorter than `x`
    fn qlean_alp_encode_below_f32(x: B) -> O { alp_encode_below(x, 4) }
    /// The column restored: `n` little-endian `f64`
    fn qlean_alp_decode_f64(meta: B, pack: B, alp: B, n: usize) -> O { alp_dec(8, fview("qlean_alp_decode_f64", meta, pack, alp, n)) }
    /// The column restored: `n` little-endian `f32`
    fn qlean_alp_decode_f32(meta: B, pack: B, alp: B, n: usize) -> O { alp_dec(4, fview("qlean_alp_decode_f32", meta, pack, alp, n)) }
    /// q's `float` sum of the column, `avg` choosing the order q's `avg` takes on a column holding a null
    fn qlean_alp_sum_f64(avg: u8, meta: B, pack: B, alp: B, n: usize) -> f64 {
        codec::alp_sum_f64(pool(), &fview("qlean_alp_sum_f64", meta, pack, alp, n), avg != 0)
    }
    /// q's `real` sum of the column
    fn qlean_alp_sum_f32(meta: B, pack: B, alp: B, n: usize) -> f64 { codec::alp_sum_f32(&fview("qlean_alp_sum_f32", meta, pack, alp, n)) }
    /// Element `idxv[j]` of the column, `fill` where `idxv[j]` is not below `n`, at the column's own width
    fn qlean_alp_gather(fill: u64, meta: B, pack: B, alp: B, n: usize, idxv: B) -> O {
        let f = fview("qlean_alp_gather", meta, pack, alp, n);
        let ib = idxv.bytes();
        let idx = pod::cast::<i64>(&ib[..ib.len() / 8 * 8]).expect("qlean_alp_gather: the index array is misaligned for its elements");
        let mut res = SArr::new(1, idx.len() * if f.f32 { 4 } else { 8 });
        codec::alp_gather(pool(), fill, &f, idx, res.bytes_mut());
        res.into()
    }
    /// The smallest element, seeded with +inf
    fn qlean_alp_min(meta: B, pack: B, alp: B, n: usize) -> f64 { fview("qlean_alp_min", meta, pack, alp, n).min() }
    /// The largest element, seeded with -inf
    fn qlean_alp_max(meta: B, pack: B, alp: B, n: usize) -> f64 { fview("qlean_alp_max", meta, pack, alp, n).max() }
    /// The `Column.bits` payload of `(atoms f).map (· < v)`
    fn qlean_alp_mask_lt(meta: B, pack: B, alp: B, n: usize, v: f64) -> O {
        let f = fview("qlean_alp_mask_lt", meta, pack, alp, n);
        mask_with(f.c.meta.n, |out| f.mask_lt(v, out))
    }
}

/// `qlean_alp_encode_{f64,f32}`: the three parts of the dense column of `w`-byte elements
fn alp_encode(x: B, w: usize) -> O {
    encode_dense(x.bytes(), w, true, usize::MAX).expect("qlean_alp_encode: a dense buffer cannot fail").into_triple()
}
/// `qlean_coc_encode_below`'s rule at ALP: the three parts against the dense bytes
fn alp_encode_below(x: B, w: usize) -> O {
    match encode_dense(x.bytes(), w, true, x.bytes().len() / w * w) { Some(p) => ctor(1, [p.into_triple()], &[]), None => boxed(0) }
}
/// The ALP column as `f.c.meta.n` elements of `w` bytes, by blocks on the pool
fn alp_dec(w: usize, f: Cocf) -> O {
    let mut out = SArr::new(1, f.c.meta.n * w);
    codec::alp_decode(pool(), &f, out.bytes_mut());
    out.into()
}
