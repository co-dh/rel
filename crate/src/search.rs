#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), search.c: operands (A28), the probe table (A29), find/member (A30), bits and symbols (A31), binary
//! search (A32), run starts (A33). The `qlean_search_*` entries unbox and allocate and stay C (§1).
use alloc::vec::Vec;

use crate::c::Runner;
use crate::coc::Coc;
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
pub fn coc_exc_within(c: &Coc, b: usize, lo: i64, hi: i64) -> bool { unimplemented!("A28: coc_exc_within") }
/// search.c:142 `ids_top`: one past the largest id at `lw` bits.
pub fn ids_top(lw: u32) -> u64 { unimplemented!("A28: ids_top") }
impl<'a> Opnd<'a> {
    /// search.c:144 `opnd_blk`: block `b` at key width `w`: a slice of the payload, or restored into `buf`
    /// (BLK * w); the element count is the answer's length / `w`.
    pub fn blk<'b>(&self, b: usize, w: usize, buf: &'b mut [u8]) -> &'b [u8] where 'a: 'b { unimplemented!("A28: opnd_blk") }
}
/// search.c:164 `coc_srange`: the column's value range from its metadata.
pub fn coc_srange(c: &Coc) -> (i64, i64) { unimplemented!("A28: coc_srange") }
/// search.c:179 `sext`: the low `w` bytes of `v`, sign-extended.
pub fn sext(v: u64, w: usize) -> i64 { unimplemented!("A28: sext") }
/// search.c:407 `kind_of`: aborts naming `who` for a width the dispatch never sends.
pub fn kind_of(w: usize, is_float: bool, who: &str) -> Kind { unimplemented!("A28: kind_of") }
impl Kind {
    /// search.c:818 `kind_width`
    pub fn width(self) -> usize { unimplemented!("A28: kind_width") }
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
