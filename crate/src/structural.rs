#![forbid(unsafe_code)]
//! Column (a), structural.rs: bit helpers and the encoded-column readers (A34), the encoder sources of reverse,
//! cycle, shift and concat (A35), concat of encoded columns (A36), gathers (A37–A38), cycles, concats and
//! enumerations (A39), the symbol dictionary table (A40), dictionary concat (A41a), `til` and `scatter` (A41b).
//! The `qlean_structural_*` entries and the `sd_*` dictionary cache (which holds `lean_object`s) stay C (§1).
//! An encoder source (`coc_fill`, `coc_hint`, `coc_ints`, coc.rs) is a Rust fn here over views; its C
//! callback keeps a one-line body that unpacks its `ctx` and calls the `qrs_*` shim.

use crate::blocks::Blocks;
use crate::coc::Coc;

// ---- A34: structural.rs ----








// ---- A36: structural.rs (the rest of the concat entries is Lean glue) ----



// ---- A37: structural.rs ----
/// `(T)v` of structural.rs's kernels: the low `W` bytes of `v`, zero-extended past 8.
pub fn word<const W: usize>(v: u64) -> [u8; W] { let b = v.to_le_bytes(); core::array::from_fn(|k| if k < 8 { b[k] } else { 0 }) }
/// structural.rs `GATHER_AHEAD`: how far ahead of the index being read the source is prefetched.
pub const GATHER_AHEAD: usize = 16;
/// structural.rs `qlean_structural_all_below`: every index, read unsigned, is below `n`.
pub fn all_below(n: usize, idx: &[i64]) -> bool { idx.is_empty() || idx.iter().fold(0u64, |m, &x| m.max(x as u64)) < n as u64 }
// One unsigned compare rejects all three of q's misses (past the end, negative, `0N` = 2^63 unsigned), as `get` does.
// One width for the whole column makes the pack a flat array of residuals, so `u * width / 8` is the address and the
// block structure cancels out of it: one scaled index plus the block's base, which stays in L1.
pub fn flat<const W: usize>(c: &Coc, sw: u8, f: [u8; W], ix: &[i64], o: &mut [u8], rd: impl Fn(usize) -> u64) {
    let sn = c.meta.n as u64;
    for (j, (d, &i)) in o.as_chunks_mut::<W>().0.iter_mut().zip(ix).enumerate() {
        // `coc_prefetch`'s reason at the flat address; a wild one is skipped, where C's is a hint that never faults
        if let Some(&a) = ix.get(j + GATHER_AHEAD) {
            if let Some(r) = c.pack.get(((a as u64).wrapping_mul(sw as u64) >> 3) as usize) { crate::simd::prefetch(r) }
        }
        let u = i as u64;
        *d = if u < sn { word(rd(u as usize)) } else { f };
    }
}
// A column whose blocks disagree, or that carries a patch list, has no flat form: a run of indices in one block that
// is an eighth of a block long decodes the block once into the scratch (on the source's own grid, whatever its `lg`;
// allocated at the first such run, so a gather of short runs never zeroes it), a shorter one is read through `get`.
pub fn runs<const W: usize>(c: &Coc, f: [u8; W], ix: &[i64], o: &mut [u8]) {
    let (sn, lg) = (c.meta.n, c.meta.lg);
    let mut buf: Option<crate::pod::Scr<u64>> = None;
    let d = o.as_chunks_mut::<W>().0;
    let mut j = 0;
    while j < ix.len() {
        let u0 = ix[j] as u64;
        if u0 >= sn as u64 { d[j] = f; j += 1; continue }
        let (b, blo) = (u0 as usize >> lg, u0 as usize >> lg << lg);
        let mut e = j + 1;
        while e < ix.len() && ix[e] as u64 >> lg == b as u64 { e += 1 }
        if e - j < c.meta.blk() / 8 {
            for k in j..e {
                if let Some(&a) = ix.get(k + GATHER_AHEAD) { c.prefetch(a as usize) }
                let u = ix[k] as u64;
                d[k] = if u < sn as u64 { word(c.get(u as usize) as u64) } else { f };
            }
        } else {
            let s = Blocks::new(crate::blocks::Src::For(*c), sn);
            let bb = s.load_w(b, s.span(b).1, W, crate::pod::bytes_mut(buf.get_or_insert_with(|| crate::pod::Scr::new(c.meta.blk() * W.div_ceil(8)))));
            for k in j..e {
                let u = ix[k] as u64;
                d[k] = if u < sn as u64 { bb[(u as usize - blo) * W..][..W].try_into().unwrap() } else { f };
            }
        }
        j = e;
    }
}
// One slice of `gather_enc`: `sw` is the source's one width, decided by the entry once rather than per slice.
pub fn enc_w<const W: usize>(c: &Coc, sw: u8, fill: u64, ix: &[i64], o: &mut [u8]) {
    let f = word::<W>(fill);
    // the block of `u` on the source's own grid: a column of any `lg` the layout admits
    let (sb, sp, lg) = (c.meta.base, c.pack, c.meta.lg);
    let base = |u: usize| sb[u >> lg] as u64;
    let at = |k: usize, n: usize| &sp[k..k + n];
    match sw {
        0 => flat(c, sw, f, ix, o, base),
        1 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add((sp[u >> 3] >> (u & 7) & 1) as u64)),
        2 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add((sp[u >> 2] >> ((u & 3) * 2) & 3) as u64)),
        4 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add((sp[u >> 1] >> ((u & 1) * 4) & 15) as u64)),
        8 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(sp[u] as u64)),
        16 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(u16::from_ne_bytes(at(2 * u, 2).try_into().unwrap()) as u64)),
        32 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(u32::from_ne_bytes(at(4 * u, 4).try_into().unwrap()) as u64)),
        64 => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(u64::from_ne_bytes(at(8 * u, 8).try_into().unwrap()))),
        // `check_enc` refused width 16 here at the entry: coc.rs `coc_load_blk_at` decodes at 8 bytes, which C misreads as a `u128`
        255 if W <= 8 => runs(c, f, ix, o),
        255 => unreachable!("an unequal-blocks gather at width {W} is refused at the entry"),
        _ => flat(c, sw, f, ix, o, |u| base(u).wrapping_add(crate::res::res_get_in(sp, sw, u, sp.len()))),
    }
}
pub fn enc(w: usize, c: &Coc, sw: u8, fill: u64, ix: &[i64], o: &mut [u8]) {
    match w {
        1 => enc_w::<1>(c, sw, fill, ix, o),
        2 => enc_w::<2>(c, sw, fill, ix, o),
        4 => enc_w::<4>(c, sw, fill, ix, o),
        8 => enc_w::<8>(c, sw, fill, ix, o),
        _ => enc_w::<16>(c, sw, fill, ix, o),
    }
}

// ---- A38: structural.rs ----
// One width of `expand`: `fill` is the C's `(T)fill`, its low `W` bytes (zero-extended past 8).
// A row past `s` (an unsigned compare: negative and `0N` too) is the empty symbol.
// One id gathered: a miss (an unsigned compare folds past-the-end, negative and `0N`) is `fill`.

// ---- A39: structural.rs ----


// ---- A40: structural.rs, the symbol dictionary's hash table ----

// ---- A41a: structural.rs ----

// ---- A41b: structural.rs, 3005-3030 ----





/// `f::<W, K>` for the widths and column counts that `rows_k` and `cols_k` are instantiated at; false = neither is.
#[macro_export]
macro_rules! by_wk {
    ($w:expr, $k:expr, $f:ident($($a:expr),*)) => { match ($w, $k) {
        (1, 2) => $f::<1, 2>($($a),*), (2, 2) => $f::<2, 2>($($a),*), (4, 2) => $f::<4, 2>($($a),*), (8, 2) => $f::<8, 2>($($a),*),
        (1, 3) => $f::<1, 3>($($a),*), (2, 3) => $f::<2, 3>($($a),*), (4, 3) => $f::<4, 3>($($a),*), (8, 3) => $f::<8, 3>($($a),*),
        (1, 4) => $f::<1, 4>($($a),*), (2, 4) => $f::<2, 4>($($a),*), (4, 4) => $f::<4, 4>($($a),*), (8, 4) => $f::<8, 4>($($a),*),
        _ => return false,
    } };
}













// ---- B28: structural.rs, the part of the Lean boundary that holds no object ----


// ---- K22: structural.rs `amend_index` ----
// ---- K23: structural.rs `fsc_*`, `fsx_check`: scatter into an encoded column ----
// ---- A35: structural.rs, the encoder sources ----
