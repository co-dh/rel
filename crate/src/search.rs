#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), search.c: operands (A28), the probe table (A29), find/member (A30), bits and symbols (A31), binary
//! search (A32), run starts (A33). The `qlean_search_*` entries unbox and allocate and stay C (§1).
use alloc::vec::Vec;

use crate::c::Runner;
use crate::coc::Coc;
use crate::ids;
use crate::sym::Syms;

/// search.c:114 `opnd`: a dense payload (`enc` 0), an encoded column (1), or ids at `lw` bits (2); `n` elements.
#[derive(Clone, Copy)]
pub enum Src<'a> { Dense(&'a [u8]), Enc(Coc<'a>), Ids(&'a [u8], u32) }
#[derive(Clone, Copy)]
pub struct Opnd<'a> { pub src: Src<'a>, pub n: usize }
/// search.c:405 `kind`: the key type, chosen once per operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind { U8, U16, U32, U64, F32, F64, U128 }

// ---- A28: search.c:53-180, 407, 818 ----
/// search.c:53 `coc_exc_within`: every patch of block `b` lies in `lo ..= hi`.
pub fn coc_exc_within(c: &Coc, b: usize, lo: i64, hi: i64) -> bool {
    c.exc.filter(|e| !e.pos.is_empty()).is_some_and(|e| (e.off[b] as usize..e.off[b + 1] as usize).any(|j| (lo..=hi).contains(&c.exc(j))))
}
/// search.c:142 `ids_top`: one past the largest id at `lw` bits.
pub fn ids_top(lw: u32) -> u64 { if lw >= 64 { !0 } else { (1u64 << lw) - 1 } }
impl<'a> Opnd<'a> {
    /// search.c:144 `opnd_blk`: block `b` at key width `w`: a slice of the payload, or restored into `buf`
    /// (BLK * w); the element count is the answer's length / `w`.
    pub fn blk<'b>(&self, b: usize, w: usize, buf: &'b mut [u8]) -> &'b [u8] where 'a: 'b {
        let (at, cnt) = (b * crate::BLK, (self.n - b * crate::BLK).min(crate::BLK));
        match self.src {
            Src::Dense(d) => &d[at * w..(at + cnt) * w],
            Src::Ids(p, lw) => {
                // `ids_key_width` answers at most 8; the clamp is for the `guid` instantiation, never run
                let cw = w.min(8);
                let out = &mut buf[..cnt * w];
                for k in 0..cnt { out[k * w..k * w + cw].copy_from_slice(&(ids::id_at(p, lw, at + k) as u64).to_le_bytes()[..cw]) }
                out
            }
            Src::Enc(c) => {
                let out = &mut buf[..cnt * w];
                let n = out.len();
                let bad = || -> ! { panic!("qlean search: a block buffer of {n} bytes is misaligned for {w}-byte elements") };
                match w {
                    1 => c.decode_blk(b, cnt, crate::pod::cast_mut::<u8>(out).unwrap_or_else(|| bad())),
                    2 => c.decode_blk(b, cnt, crate::pod::cast_mut::<i16>(out).unwrap_or_else(|| bad())),
                    4 => c.decode_blk(b, cnt, crate::pod::cast_mut::<i32>(out).unwrap_or_else(|| bad())),
                    _ => c.decode_blk(b, cnt, crate::pod::cast_mut::<i64>(out).unwrap_or_else(|| bad())),
                }
                out
            }
        }
    }
}
/// search.c:164 `coc_srange`: the column's value range from its metadata.
pub fn coc_srange(c: &Coc) -> (i64, i64) {
    let m = &c.meta;
    let nb = m.n.div_ceil(crate::BLK);
    let (mut a, mut z) = (i64::MAX, i64::MIN);
    for b in 0..nb { a = a.min(m.base[b]); z = z.max(m.maxv[b]) }
    for j in 0..c.exc.map_or(0, |e| e.pos.len()) { let v = c.exc(j); a = a.min(v); z = z.max(v) }
    (a, z)
}
/// search.c:179 `sext`: the low `w` bytes of `v`, sign-extended.
pub fn sext(v: u64, w: usize) -> i64 { let s = 64 - 8 * w as u32; if s == 0 { v as i64 } else { (v << s) as i64 >> s } }
/// search.c:407 `kind_of`: aborts naming `who` for a width the dispatch never sends.
pub fn kind_of(w: usize, is_float: bool, who: &str) -> Kind {
    match (w, is_float) {
        (1, false) => Kind::U8, (2, false) => Kind::U16, (4, false) => Kind::U32, (4, true) => Kind::F32,
        (8, false) => Kind::U64, (8, true) => Kind::F64, (16, false) => Kind::U128,
        _ => panic!("qlean search: {who} got element width {w} with is_float={}; the kernels are instantiated at 1, 2, 4, 8 and 16 bytes, and only 4 and 8 have a float kind", is_float as u32),
    }
}
impl Kind {
    /// search.c:818 `kind_width`
    pub fn width(self) -> usize {
        match self { Kind::U8 => 1, Kind::U16 => 2, Kind::U32 | Kind::F32 => 4, Kind::U64 | Kind::F64 => 8, Kind::U128 => 16 }
    }
}

// ---- A29: search.c:190-399, the probe table, one instance per key type ----
/// A key the probe table holds: `RAW`/`FKEY` of search.c:190 (floats compare as search.c:186 says: both zeros
/// one value, every NaN one value).
pub trait PKey: Copy + Send + Sync { fn of(b: &[u8]) -> Self; fn key(self) -> u128; }
impl PKey for u8 { fn of(b: &[u8]) -> Self { unimplemented!("A29: PKey u8") } fn key(self) -> u128 { unimplemented!("A29: PKey u8") } }
impl PKey for u16 { fn of(b: &[u8]) -> Self { unimplemented!("A29: PKey u16") } fn key(self) -> u128 { unimplemented!("A29: PKey u16") } }
impl PKey for u32 { fn of(b: &[u8]) -> Self { unimplemented!("A29: PKey u32") } fn key(self) -> u128 { unimplemented!("A29: PKey u32") } }
impl PKey for u64 { fn of(b: &[u8]) -> Self { unimplemented!("A29: PKey u64") } fn key(self) -> u128 { unimplemented!("A29: PKey u64") } }
impl PKey for u128 { fn of(b: &[u8]) -> Self { unimplemented!("A29: PKey u128") } fn key(self) -> u128 { unimplemented!("A29: PKey u128") } }
/// `f32` and `f64` keys by their bits, normalised as `FKEY` does
#[derive(Clone, Copy)] pub struct F32(pub u32);
#[derive(Clone, Copy)] pub struct F64(pub u64);
impl PKey for F32 { fn of(b: &[u8]) -> Self { unimplemented!("A29: PKey f32") } fn key(self) -> u128 { unimplemented!("A29: PKey f32") } }
impl PKey for F64 { fn of(b: &[u8]) -> Self { unimplemented!("A29: PKey f64") } fn key(self) -> u128 { unimplemented!("A29: PKey f64") } }
/// search.c:103 `ptab`: direct (`slot` indexed by key − `lo`) or hashed (`sh`); `tab[g]` the first index + 1.
pub struct Ptab<K> { pub tab: Vec<usize>, pub slot: Vec<u32>, pub key: Vec<K>, pub top: u64, pub lo: u64, pub n: usize,
                     pub used: usize, pub direct: bool, pub sh: u32 }
/// search.c:251 `table_*`: the table over the haystack `o`.
pub fn table<K: PKey>(o: &Opnd) -> Ptab<K> { unimplemented!("A29: table") }
impl<K: PKey> Ptab<K> {
    /// search.c:231 `dslot_*`, 235 `hslot_*`: the slot of `k`.
    pub fn slot_of(&self, k: K) -> usize { unimplemented!("A29: dslot/hslot") }
    /// search.c:335 `hits_*`: block-wise lookups of `x`'s keys `lo .. hi` into `out` (first index, or `n`).
    pub fn hits(&self, x: &Opnd, lo: usize, hi: usize, out: &mut [i64]) { unimplemented!("A29: hits") }
    /// search.c:360 `findtab_*`: `x ? hay` for `lo .. hi`.
    pub fn find(&self, x: &Opnd, lo: usize, hi: usize, out: &mut [i64]) { unimplemented!("A29: findtab") }
    /// search.c:376 `membertab_*`: `x in hay` for `lo .. hi`, a byte each.
    pub fn member(&self, x: &Opnd, lo: usize, hi: usize, out: &mut [u8]) { unimplemented!("A29: membertab") }
}
/// search.c:218 `scan_*`: the linear search for a short haystack.
pub fn scan<K: PKey>(h: &Opnd, x: &Opnd, lo: usize, hi: usize, out: &mut [i64]) { unimplemented!("A29: scan") }
/// search.c:319 `srange_*`: the haystack's key range, which decides direct against hashed.
pub fn srange<K: PKey>(o: &Opnd) -> (u64, u64) { unimplemented!("A29: srange") }

// ---- A30: search.c:829-965 ----
/// search.c:881 `search` past the allocation: `x ? h` (index, `h.n` when absent) or `x in h` (`member`, a byte
/// each) into `out`, threaded (`find_run`, `member_run`).
pub fn search(run: Runner, kd: Kind, h: &Opnd, x: &Opnd, member: bool, out: &mut [u8]) { unimplemented!("A30: search") }
/// search.c:946 `ids_key_width`
pub fn ids_key_width(a: usize, b: usize) -> usize { unimplemented!("A30: ids_key_width") }

// ---- A31: search.c:974-1272 ----
/// search.c:980 `word_at`: 64 bits from bit `i` of the bitmap `b`.
pub fn word_at(b: &[u8], i: usize) -> u64 { unimplemented!("A31: word_at") }
/// search.c:990 `find_bit`: the first index of `needle` among `n` bits.
pub fn find_bit(b: &[u8], n: usize, needle: u8) -> usize { unimplemented!("A31: find_bit") }
/// search.c:1010 `qlean_search_find_bit_vec` past the unboxing: each needle's first index.
pub fn find_bit_vec(n: usize, hay: &[u8], ndl: &[u8], m: usize, out: &mut [i64]) { unimplemented!("A31: qlean_search_find_bit_vec") }
/// search.c:1023 `bin_bit`: binary search of a sorted bitmap for `k`.
pub fn bin_bit(b: &[u8], n: usize, k: i32, right: bool) -> i64 { unimplemented!("A31: bin_bit") }
/// search.c:1041 `qlean_search_bin_bits` past the unboxing.
pub fn bin_bits(n: usize, hay: &[u8], ndl: &[u8], m: usize, right: bool, out: &mut [i64]) { unimplemented!("A31: qlean_search_bin_bits") }
/// search.c:1054 `qlean_search_member_bits` past the unboxing.
pub fn member_bits(m: usize, xs: &[u8], n: usize, hay: &[u8], out: &mut [u8]) { unimplemented!("A31: qlean_search_member_bits") }
/// search.c:1074 `spread`: the set bits of word `v` (word `i`) as indices into `out` at `at`; answers the new `at`.
pub fn spread(out: &mut [i64], at: usize, i: usize, v: u64) -> usize { unimplemented!("A31: spread") }
/// search.c:1107 `qlean_search_where_bits` past the allocation (`out` holds the popcount); answers the count.
pub fn where_bits(n: usize, bits: &[u8], out: &mut [i64]) -> usize { unimplemented!("A31: qlean_search_where_bits") }
/// search.c:1174 `symscan`: a short symbol haystack indexed by first byte.
pub struct Symscan<'a> { pub hay: Vec<&'a [u8]>, pub empty: usize, pub first: [u8; 256] }
impl<'a> Symscan<'a> {
    /// search.c:1176 `symscan_build`
    pub fn build(hay: Vec<&'a [u8]>) -> Self { unimplemented!("A31: symscan_build") }
    /// search.c:1185 `symscan_find`
    pub fn find(&self, k: &[u8]) -> usize { unimplemented!("A31: symscan_find") }
}
/// search.c:1209 `sym_pack`: the first `n` symbols as 8-byte keys.
pub fn sym_pack(s: &Syms, n: usize, k: &mut [u64]) { unimplemented!("A31: sym_pack") }
/// search.c:1236 `sym_scan`
pub fn sym_scan(s: &Syms, n: usize, k: &[u8]) -> usize { unimplemented!("A31: sym_scan") }
/// search.c:1243 `sym_build`: the hash table `tab` (`mask + 1` slots) over the first `n` symbols.
pub fn sym_build(s: &Syms, n: usize, tab: &mut [usize], mask: u64) { unimplemented!("A31: sym_build") }
/// search.c:1253 `sym_probe`
pub fn sym_probe(s: &Syms, tab: &[usize], mask: u64, n: usize, k: &[u8]) -> usize { unimplemented!("A31: sym_probe") }
/// search.c:1266 `qlean_search_find_sym_scalar` past the unboxing.
pub fn find_sym_scalar(s: &Syms, ndl: &[u8]) -> usize { unimplemented!("A31: qlean_search_find_sym_scalar") }

// ---- A32: search.c:1497-1716 ----
/// search.c:1497 `bin_key`: `v` as an unsigned key in the column's order.
pub fn bin_key(w: usize, is_float: bool, is_signed: bool, v: u64) -> u64 { unimplemented!("A32: bin_key") }
/// search.c:1510 `bin_at`: element `i` of a `w`-byte payload.
pub fn bin_at(p: &[u8], w: usize, i: usize) -> u64 { unimplemented!("A32: bin_at") }
/// search.c:1519 `norm_key`
pub fn norm_key(w: usize, is_float: bool, v: u64) -> u64 { unimplemented!("A32: norm_key") }
/// search.c:1706 `qlean_search_bin` past the unboxing: for each of the `m` keys (dense `keys`, or `kenc`), the
/// binary-search position in the sorted haystack (dense `hay`, or `enc`) of `n`, into `out`; threaded
/// (`bin_run`, `bin_tab_run`, `bin_gather_run`).
pub fn bin(run: Runner, w: usize, is_float: bool, is_signed: bool, right: bool, hay: &[u8], enc: Option<&Coc>, n: i64,
           keys: &[u8], kenc: Option<&Coc>, m: usize, out: &mut [i64]) {
    unimplemented!("A32: qlean_search_bin")
}

// ---- A33: search.c:731-740, 2004-2099 ----
/// search.c:2004 `run_starts` past the allocation: the start of each run of equal elements into `out`; answers
/// the count.
pub fn run_starts(o: &Opnd, w: usize, is_float: bool, out: &mut [i64]) -> usize { unimplemented!("A33: run_starts") }
/// search.c:731 `qlean_search_run_starts_ids`
pub fn run_starts_ids(n: usize, w: u32, ids: &[u8], out: &mut [i64]) -> usize { unimplemented!("A33: qlean_search_run_starts_ids") }
/// search.c:2056 `qlean_search_run_starts_syms`
pub fn run_starts_syms(s: &Syms, out: &mut [i64]) -> usize { unimplemented!("A33: qlean_search_run_starts_syms") }
/// search.c:2078 `qlean_search_run_starts_bits`
pub fn run_starts_bits(n: usize, bits: &[u8], out: &mut [i64]) -> usize { unimplemented!("A33: qlean_search_run_starts_bits") }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coc::{Exc, Meta};
    // expected values: search.c at 04ecc24 (coc_srange, coc_exc_within, sext, ids_top, kind_of, kind_width, opnd_blk)
    #[test] fn sext_and_ids_top() {
        assert_eq!(sext(0xff, 1), -1); assert_eq!(sext(0x80, 1), -128); assert_eq!(sext(0x7f, 1), 127);
        assert_eq!(sext(0xffff_ffff, 4), -1); assert_eq!(sext(u64::MAX, 8), -1); assert_eq!(sext(5, 8), 5);
        assert_eq!((ids_top(0), ids_top(1), ids_top(8), ids_top(63), ids_top(64), ids_top(70)), (0, 1, 255, i64::MAX as u64, !0, !0));
    }
    #[test] fn kinds() {
        use Kind::*;
        let all = [(1, false, U8), (2, false, U16), (4, false, U32), (4, true, F32), (8, false, U64), (8, true, F64), (16, false, U128)];
        for (w, f, k) in all { assert_eq!(kind_of(w, f, "t"), k); assert_eq!(k.width(), w) }
    }
    #[test] #[should_panic(expected = "qlean search: find_vec got element width 2 with is_float=1; the kernels are instantiated at 1, 2, 4, 8 and 16 bytes")]
    fn float_at_two_bytes_aborts() { kind_of(2, true, "find_vec"); }
    fn col<'a>(base: &'a [i64], maxv: &'a [i64], off: &'a [u64], width: &'a [u8], n: usize, exc: Option<Exc<'a>>) -> Coc<'a> {
        let m = base.len();
        Coc { meta: Meta { base, maxv, off, bsum: base, width, sumnul: 0, sumn: 0, n, nblk: m, mblk: m }, pack: &[], exc, fdelta: None }
    }
    #[test] fn srange_and_exc_within() {
        let (raw, pos, off) = ([(-9i64).to_ne_bytes(), 40i64.to_ne_bytes()].concat(), [1u16, 2], [0u32, 0, 2]);
        let e = Exc { off: &off, pos: &pos, raw: &raw, esz: 8 };
        let c = col(&[10, 20], &[15, 30], &[0, 0], &[0, 0], 1025, Some(e));
        assert_eq!(coc_srange(&c), (-9, 40));
        assert!(!coc_exc_within(&c, 0, -100, 100) && coc_exc_within(&c, 1, -9, -9) && coc_exc_within(&c, 1, 40, 41));
        assert!(!coc_exc_within(&c, 1, -8, 39));
        let c = col(&[10, 20], &[15, 30], &[0, 0], &[0, 0], 1024, None);
        assert_eq!((coc_srange(&c), coc_exc_within(&c, 0, i64::MIN, i64::MAX)), ((10, 15), false));
    }
    #[test] fn blk_dense_ids_enc() {
        let d: Vec<u8> = (0..2100u32).flat_map(|i| (i as u16).to_le_bytes()).collect();
        let o = Opnd { src: Src::Dense(&d), n: 2100 };
        let mut buf = [0u64; 1024 * 2 / 8];
        let b = crate::pod::bytes_mut(&mut buf);
        assert_eq!((o.blk(2, 2, b).len(), o.blk(0, 2, b).len()), (52 * 2, 2048));
        assert_eq!(o.blk(2, 2, b)[..4], [0, 8, 1, 8]);
        // ids at 4 bits: id i is i % 16; written at 4-byte keys
        let p: Vec<u8> = (0..1050usize).map(|i| ((2 * i % 16) as u8) | ((((2 * i + 1) % 16) as u8) << 4)).collect();
        let o = Opnd { src: Src::Ids(&p, 4), n: 2100 };
        let mut buf = vec![0u64; 1024 * 4 / 8];
        let b = crate::pod::bytes_mut(&mut buf);
        let r = o.blk(2, 4, b);
        assert_eq!(r.len(), 52 * 4);
        assert_eq!(&r[..12], &[(2048 % 16) as u8, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]);
        // a short block of a column of 1 block: base 7 at width 0 is 7 each
        let c = col(&[7], &[7], &[0], &[0], 100, None);
        let o = Opnd { src: Src::Enc(c), n: 100 };
        let mut buf = vec![0u64; 1024];
        let b = crate::pod::bytes_mut(&mut buf);
        let r = o.blk(0, 8, b);
        assert_eq!(r.len(), 800);
        assert!(r.chunks_exact(8).all(|x| x == 7i64.to_ne_bytes()));
    }
}
