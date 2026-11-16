#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), search.c: operands (A28), the probe table (A29), find/member (A30), bits and symbols (A31), binary
//! search (A32), run starts (A33). The `qlean_search_*` entries unbox and allocate and stay C (§1).
use alloc::{vec, vec::Vec};

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
/// The build starts a slot's cache line this many keys early (search.c:105 `SEARCH_AHEAD`).
const AHEAD: usize = 32;
/// A key the probe table holds: `RAW`/`F32Z`/`F64Z` of search.c:186 (floats compare as that comment says: both zeros
/// one value, every NaN one value). `of` reads the key at the start of `b` already normalised, so every use of a key
/// is the one that table, scan and walk agree on.
pub trait PKey: Copy + Send + Sync {
    /// bytes per key
    const W: usize;
    fn of(b: &[u8]) -> Self;
    /// the normalised bits, zero-extended
    fn key(self) -> u128;
    /// search.c `KEY_HASH`: the key up to eight bytes, a sixteen-byte key's two words folded into one
    fn hash(self) -> u64 { let v = self.key(); v as u64 ^ ((v >> 64) as u64).wrapping_mul(0xc2b2_ae3d_27d4_eb4f) }
}
macro_rules! raw_key { ($($t:ty),*) => {$(impl PKey for $t {
    const W: usize = core::mem::size_of::<$t>();
    fn of(b: &[u8]) -> Self { Self::from_le_bytes(b[..Self::W].try_into().expect("a key's bytes")) }
    fn key(self) -> u128 { self as u128 }
})*} }
raw_key!(u8, u16, u32, u64, u128);
/// `f32` and `f64` keys by their bits, normalised as `F32Z`/`F64Z` do
#[derive(Clone, Copy)] pub struct F32(pub u32);
#[derive(Clone, Copy)] pub struct F64(pub u64);
impl PKey for F32 {
    const W: usize = 4;
    fn of(b: &[u8]) -> Self {
        let v = u32::from_le_bytes(b[..4].try_into().expect("a key's bytes"));
        let m = v & 0x7fff_ffff;
        F32(if m == 0 { 0 } else if m > 0x7f80_0000 { 0xffc0_0000 } else { v })
    }
    fn key(self) -> u128 { self.0 as u128 }
}
impl PKey for F64 {
    const W: usize = 8;
    fn of(b: &[u8]) -> Self {
        let v = u64::from_le_bytes(b[..8].try_into().expect("a key's bytes"));
        let m = v & 0x7fff_ffff_ffff_ffff;
        F64(if m == 0 { 0 } else if m > 0x7ff0_0000_0000_0000 { 0xfff8_0000_0000_0000 } else { v })
    }
    fn key(self) -> u128 { self.0 as u128 }
}
/// the low `8 * W` bits (all 64 from eight bytes up): a direct slot is `key - lo` taken in the key's own width
fn mask<K: PKey>() -> u64 { if K::W >= 8 { !0 } else { (1u64 << (8 * K::W)) - 1 } }

/// search.c:103 `ptab`: direct (`slot` indexed by key − `lo`) or hashed (`sh`); `tab[g]` the first index + 1.
pub struct Ptab<K> { pub tab: Vec<usize>, pub slot: Vec<u32>, pub key: Vec<K>, pub top: u64, pub lo: u64, pub n: usize,
                     pub used: usize, pub direct: bool, pub sh: u32 }

/// The blocks of `x` covering elements `lo .. hi`, each as the slice of those elements starting at element `at`.
fn blocks(x: &Opnd, w: usize, lo: usize, hi: usize, mut f: impl FnMut(usize, &[u8])) {
    let mut buf = [0u64; 2 * crate::BLK];
    let bb = crate::pod::bytes_mut(&mut buf);
    let mut at = lo;
    while at < hi {
        let (b, end) = (at / crate::BLK, ((at / crate::BLK + 1) * crate::BLK).min(hi));
        let blo = b * crate::BLK;
        f(at, &x.blk(b, w, bb)[(at - blo) * w..(end - blo) * w]);
        at = end;
    }
}

/// search.c:251 `table_*`: the table over the haystack `o`, a block at a time, each slot holding the first index its key
/// occurs at plus one. Direct when the keys span at most `4n + 8`; a direct table whose every slot is filled stops there.
pub fn table<K: PKey>(o: &Opnd) -> Ptab<K> {
    let mut p = Ptab { tab: Vec::new(), slot: Vec::new(), key: Vec::new(), top: 0, lo: 0, n: o.n, used: 0, direct: false, sh: 0 };
    let mut buf = [0u64; 2 * crate::BLK];
    let bb = crate::pod::bytes_mut(&mut buf);
    let nb = o.n.div_ceil(crate::BLK);
    if o.n > 0 && K::W <= 8 {
        let (lo, span) = match o.src {
            Src::Ids(_, lw) => (0, ids_top(lw)),
            Src::Enc(c) => { let (a, z) = coc_srange(&c); (a as u64 & mask::<K>(), (z as u64).wrapping_sub(a as u64)) }
            Src::Dense(d) => {
                let (mn, mx) = d.chunks_exact(K::W).take(o.n).map(|c| K::of(c).key() as u64)
                    .fold((!0u64, 0u64), |(a, z), k| (a.min(k), z.max(k)));
                (mn, mx - mn)
            }
        };
        if span < o.n as u64 * 4 + 8 {
            (p.direct, p.lo, p.top) = (true, lo, span);
            p.tab = vec![0usize; span as usize + 1];
            for b in 0..nb {
                for (j, c) in o.blk(b, K::W, bb).chunks_exact(K::W).enumerate() {
                    let d = ((K::of(c).key() as u64).wrapping_sub(lo) & mask::<K>()) as usize;
                    if p.tab[d] == 0 {
                        p.tab[d] = b * crate::BLK + j + 1;
                        p.used += 1;
                        if p.used as u64 > span { return p }
                    }
                }
            }
            return p;
        }
    }
    if o.n >= u32::MAX as usize {
        panic!("qlean search: a hashed table numbers its keys in 32 bits and cannot hold the {} elements it was handed", o.n);
    }
    let cap = crate::group::cap_for(o.n);
    p.top = cap as u64 - 1;
    p.sh = 64 - cap.trailing_zeros();
    p.slot = vec![0u32; cap];
    p.tab = Vec::with_capacity(o.n);
    p.key = Vec::with_capacity(o.n);
    let at = |k: K, sh: u32| (k.hash().wrapping_mul(crate::group::PHI64) >> sh) as usize;
    for b in 0..nb {
        let blk = o.blk(b, K::W, bb);
        let cnt = blk.len() / K::W;
        for (j, c) in blk.chunks_exact(K::W).enumerate() {
            let k = K::of(c);
            if j + AHEAD < cnt { crate::simd::prefetch(&p.slot[at(K::of(&blk[(j + AHEAD) * K::W..]), p.sh)]) }
            let mut s = at(k, p.sh);
            while p.slot[s] != 0 && p.key[p.slot[s] as usize - 1].key() != k.key() { s = (s + 1) & p.top as usize }
            if p.slot[s] == 0 {
                p.key.push(k);
                p.tab.push(b * crate::BLK + j + 1);
                p.used += 1;
                p.slot[s] = p.used as u32;
            }
        }
    }
    p
}
impl<K: PKey> Ptab<K> {
    /// search.c:195 `dslot_*`: the slot key `k` names, or `usize::MAX` where none can hold it.
    #[inline(always)]
    fn dslot(&self, k: K) -> usize {
        let d = (k.key() as u64).wrapping_sub(self.lo) & mask::<K>();
        if d <= self.top { d as usize } else { usize::MAX }
    }
    /// search.c:199 `hslot_*`: the key number of `k`, or `usize::MAX`.
    #[inline(always)]
    fn hslot(&self, k: K) -> usize {
        let mut s = (k.hash().wrapping_mul(crate::group::PHI64) >> self.sh) as usize;
        while self.slot[s] != 0 {
            let g = self.slot[s] as usize - 1;
            if self.key[g].key() == k.key() { return g }
            s = (s + 1) & self.top as usize;
        }
        usize::MAX
    }
    /// the slot of `k`, `usize::MAX` where there is none.
    pub fn slot_of(&self, k: K) -> usize { if self.direct { self.dslot(k) } else { self.hslot(k) } }
    /// search.c:335 `hits_*`: the haystack `h` walked in order to the first occurrence of each key of a table built over
    /// the needles, `ans[s]` that index plus one; it stops once every key is found. An encoded block whose `[base, maxv]`
    /// misses the needles' `[lo, hi]` is passed over on its metadata.
    pub fn hits(&self, h: &Opnd, lo: i64, hi: i64, ans: &mut [usize]) {
        let mut left = self.used;
        let mut buf = [0u64; 2 * crate::BLK];
        let bb = crate::pod::bytes_mut(&mut buf);
        for b in 0..h.n.div_ceil(crate::BLK) {
            if left == 0 { return }
            if let Src::Enc(c) = h.src {
                if (c.meta.maxv[b] < lo || c.meta.base[b] > hi) && !coc_exc_within(&c, b, lo, hi) { continue }
            }
            for (j, c) in h.blk(b, K::W, bb).chunks_exact(K::W).enumerate() {
                let s = self.slot_of(K::of(c));
                if s != usize::MAX && self.tab[s] != 0 && ans[s] == 0 {
                    ans[s] = b * crate::BLK + j + 1;
                    left -= 1;
                    if left == 0 { return }
                }
            }
        }
    }
    /// each element `i` of `x`'s `lo .. hi` with its slot; which table was built is settled before the loop, not per element.
    fn each(&self, x: &Opnd, lo: usize, hi: usize, mut f: impl FnMut(usize, usize)) {
        blocks(x, K::W, lo, hi, |at, q| {
            if self.direct { for (j, c) in q.chunks_exact(K::W).enumerate() { f(at + j, self.dslot(K::of(c))) } }
            else { for (j, c) in q.chunks_exact(K::W).enumerate() { f(at + j, self.hslot(K::of(c))) } }
        })
    }
    /// search.c:360 `findtab_*`: `x ? hay` for `lo .. hi` into `out[i - lo]`, `ans` the table's own `tab` or the walk's
    /// `hits`; an absent key answers `n`.
    pub fn find(&self, ans: &[usize], x: &Opnd, lo: usize, hi: usize, out: &mut [i64]) {
        self.each(x, lo, hi, |i, s| out[i - lo] = if s != usize::MAX && ans[s] != 0 { ans[s] as i64 - 1 } else { self.n as i64 })
    }
    /// search.c:376 `membertab_*`: `x in hay` for `lo .. hi`, bit `i - lo` of `out` (`lo` a multiple of 8) set when found.
    pub fn member(&self, ans: &[usize], x: &Opnd, lo: usize, hi: usize, out: &mut [u8]) {
        self.each(x, lo, hi, |i, s| if s != usize::MAX && ans[s] != 0 { out[(i - lo) >> 3] |= 1 << ((i - lo) & 7) })
    }
}
/// search.c:182 `scan_*`: the first index of each needle `lo .. hi` of `x` in the dense haystack `h`, or `h.n`; eight
/// keys at a time so that the comparison vectorises.
pub fn scan<K: PKey>(h: &Opnd, x: &Opnd, lo: usize, hi: usize, out: &mut [i64]) {
    let Src::Dense(hb) = h.src else { panic!("qlean search: scan reads a dense haystack") };
    let at = |i: usize| K::of(&hb[i * K::W..]).key();
    blocks(x, K::W, lo, hi, |a, q| {
        for (c, r) in q.chunks_exact(K::W).zip(&mut out[a - lo..]) {
            let k = K::of(c).key();
            let mut i = 0;
            *r = loop {
                if i + 8 > h.n { break (i..h.n).find(|&i| at(i) == k).unwrap_or(h.n) as i64 }
                let m = (0..8).fold(0u32, |m, t| m | ((at(i + t) == k) as u32) << t);
                if m != 0 { break (i + m.trailing_zeros() as usize) as i64 }
                i += 8;
            };
        }
    })
}
/// search.c:283 `srange_*`: the operand's signed key range, which a walk over an encoded haystack tests each block's
/// metadata against.
pub fn srange<K: PKey>(o: &Opnd) -> (i64, i64) {
    match o.src {
        Src::Ids(_, lw) => (0, (ids_top(lw) >> 1) as i64),
        Src::Enc(c) => coc_srange(&c),
        Src::Dense(d) => {
            let w = K::W.min(8);
            d.chunks_exact(K::W).take(o.n).map(|c| { let mut b = [0u8; 8]; b[..w].copy_from_slice(&c[..w]); sext(u64::from_le_bytes(b), w) })
                .fold((i64::MAX, i64::MIN), |(a, z), v| (a.min(v), z.max(v)))
        }
    }
}

/// The seven key types as one handle the C side holds: the table, and the answers of a walk when it was built over the
/// needles (`hit`; absent: the table's own `tab`).
enum Any { U8(Ptab<u8>), U16(Ptab<u16>), U32(Ptab<u32>), U64(Ptab<u64>), F32(Ptab<F32>), F64(Ptab<F64>), U128(Ptab<u128>) }
pub struct Probe { t: Any, hit: Option<Vec<usize>> }
/// the key type of `Kind`, as `K` and the `Any` constructor as `V`, in `$e`
macro_rules! by_kind { ($kd:expr, $K:ident, $V:ident => $e:expr) => { match $kd {
    Kind::U8 => { type $K = u8; #[allow(unused_imports)] use Any::U8 as $V; $e } Kind::U16 => { type $K = u16; #[allow(unused_imports)] use Any::U16 as $V; $e }
    Kind::U32 => { type $K = u32; #[allow(unused_imports)] use Any::U32 as $V; $e } Kind::U64 => { type $K = u64; #[allow(unused_imports)] use Any::U64 as $V; $e }
    Kind::F32 => { type $K = F32; #[allow(unused_imports)] use Any::F32 as $V; $e } Kind::F64 => { type $K = F64; #[allow(unused_imports)] use Any::F64 as $V; $e }
    Kind::U128 => { type $K = u128; #[allow(unused_imports)] use Any::U128 as $V; $e }
} } }
macro_rules! any { ($s:expr, $p:ident => $e:expr) => { match $s {
    Any::U8($p) => $e, Any::U16($p) => $e, Any::U32($p) => $e, Any::U64($p) => $e, Any::F32($p) => $e, Any::F64($p) => $e,
    Any::U128($p) => $e,
} } }
pub const KINDS: [Kind; 7] = [Kind::U8, Kind::U16, Kind::U32, Kind::U64, Kind::F32, Kind::F64, Kind::U128];
impl Probe {
    /// the table over the haystack `o`
    pub fn new(kd: Kind, o: &Opnd) -> Probe { by_kind!(kd, K, V => Probe { t: V(table::<K>(o)), hit: None }) }
    /// search.c:810 `SEARCH_TABLE`'s smaller-side branch: the table over the needles `x`, and the haystack `h` walked to
    /// the first occurrence of each needle key.
    pub fn over(kd: Kind, h: &Opnd, x: &Opnd) -> Probe {
        by_kind!(kd, K, V => {
            let mut t = table::<K>(x);
            let (lo, hi) = if matches!(h.src, Src::Enc(_)) { srange::<K>(x) } else { (i64::MIN, i64::MAX) };
            let mut ans = vec![0usize; t.top as usize + 1];
            t.hits(h, lo, hi, &mut ans);
            t.n = h.n;
            Probe { t: V(t), hit: Some(ans) }
        })
    }
    pub fn width(&self) -> usize { fn w<K: PKey>(_: &Ptab<K>) -> usize { K::W } any!(&self.t, p => w(p)) }
    /// `x ? hay` for `lo .. hi`
    pub fn find(&self, x: &Opnd, lo: usize, hi: usize, out: &mut [i64]) {
        any!(&self.t, p => p.find(self.hit.as_deref().unwrap_or(&p.tab), x, lo, hi, out))
    }
    /// `x in hay` for `lo .. hi`
    pub fn member(&self, x: &Opnd, lo: usize, hi: usize, out: &mut [u8]) {
        any!(&self.t, p => p.member(self.hit.as_deref().unwrap_or(&p.tab), x, lo, hi, out))
    }
}
/// `scan` at the key type of `kd`
pub fn scan_kind(kd: Kind, h: &Opnd, x: &Opnd, out: &mut [i64]) {
    by_kind!(kd, K, V => scan::<K>(h, x, 0, x.n, out))
}

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
pub fn bin_key(w: usize, is_float: bool, is_signed: bool, v: u64) -> u64 {
    let mask = if w == 8 { !0 } else { (1u64 << (8 * w)) - 1 };
    let top = 1u64 << (8 * w - 1);
    if is_float {
        let (inf, nan) = if w == 8 { (0x7ff0_0000_0000_0000u64, 0xfff8_0000_0000_0000u64) } else { (0x7f80_0000, 0xffc0_0000) };
        let mut u = v & mask;
        // -0.0 folds onto 0.0, and every NaN is q's null
        if u & (top - 1) == 0 { u = 0 } else if u & (top - 1) > inf { u = nan }
        return if u & top != 0 { !u & mask } else { u | top };
    }
    if is_signed { (v & mask) ^ top } else { v & mask }
}
/// search.c:1510 `bin_at`: element `i` of a `w`-byte payload.
pub fn bin_at(p: &[u8], w: usize, i: usize) -> u64 {
    let mut b = [0u8; 8];
    b[..w].copy_from_slice(&p[i * w..(i + 1) * w]);
    u64::from_le_bytes(b)
}
/// search.c:1519 `norm_key`
pub fn norm_key(w: usize, is_float: bool, v: u64) -> u64 {
    if !is_float { return v }
    let (low, inf, nan) = if w == 8 { (0x7fff_ffff_ffff_ffffu64, 0x7ff0_0000_0000_0000u64, 0xfff8_0000_0000_0000u64) }
                          else { (0x7fff_ffff, 0x7f80_0000, 0xffc0_0000) };
    if v & low == 0 { 0 } else if v & low > inf { nan } else { v }
}

/// A haystack or a needle column where it lies: dense, or encoded with one residual width `uw` (`one_width`).
#[derive(Clone, Copy)]
struct Col<'a> { d: &'a [u8], c: Option<&'a Coc<'a>>, uw: u8 }
impl Col<'_> {
    fn at(&self, w: usize, i: usize) -> u64 { self.c.map_or_else(|| bin_at(self.d, w, i), |c| c.get_w(self.uw, i) as u64) }
}
/// The flags every walk is handed.
#[derive(Clone, Copy)]
struct Walk { w: usize, f: bool, s: bool, right: bool }
impl Walk {
    /// search.c:1483 `bin_step`: the partition point in `lo .. hi` of key `k`. Branchless, which is what makes the
    /// timing a property of the code and not of the branch predictor's aliasing (the C comment's measurement).
    fn step(self, h: &Col, k: u64, mut lo: i64, hi: i64) -> i64 {
        let mut len = hi - lo;
        while len > 0 {
            let (half, mid) = (len / 2, lo + len / 2);
            let v = bin_key(self.w, self.f, self.s, h.at(self.w, mid as usize));
            let adv = if self.right { v < k } else { v <= k };
            let (nlo, nlen) = (mid + 1, len - half - 1);
            lo = if adv { nlo } else { lo };
            len = if adv { nlen } else { half };
        }
        lo
    }
    /// `bin` for key `k` over `n` elements: the position, `- 1` for `bin` and as is for `binr`.
    fn pos(self, h: &Col, k: u64, n: i64) -> i64 { let at = self.step(h, k, 0, n); if self.right { at } else { at - 1 } }
}
/// search.c:1661 `kcur`: a worker's view of the needles, the dense payload or the last block restored.
struct Kcur<'a> { k: Col<'a>, w: usize, b: usize, buf: [u64; crate::BLK] }
impl<'a> Kcur<'a> {
    fn new(k: Col<'a>, w: usize) -> Self { Kcur { k, w, b: usize::MAX, buf: [0; crate::BLK] } }
    /// search.c:1668 `kcur_at`
    fn at(&mut self, j: usize) -> u64 {
        let Some(c) = self.k.c else { return bin_at(self.k.d, self.w, j) };
        let b = j / crate::BLK;
        if b != self.b {
            let (at, w) = (b * crate::BLK, self.w);
            let cnt = (c.meta.n - at).min(crate::BLK);
            let o = crate::pod::bytes_mut(&mut self.buf);
            match w {
                1 => c.decode_blk::<u8>(b, cnt, o),
                2 => c.decode_blk::<i16>(b, cnt, crate::pod::cast_mut(o).expect("kcur: u64 buffer is aligned")),
                4 => c.decode_blk::<i32>(b, cnt, crate::pod::cast_mut(o).expect("kcur: u64 buffer is aligned")),
                _ => c.decode_blk::<i64>(b, cnt, crate::pod::cast_mut(o).expect("kcur: u64 buffer is aligned")),
            }
            self.b = b;
        }
        bin_at(crate::pod::bytes(&self.buf), self.w, j % crate::BLK)
    }
}
/// search.c:1741 `BIN_TAB_MAX`, `BIN_TAB_SAMPLE`
const BIN_TAB_MAX: u64 = 1 << 16;
const BIN_TAB_SAMPLE: usize = 4096;

fn i64s(o: &mut [u8]) -> &mut [i64] { crate::pod::cast_mut(o).expect("bin: the answer is 8-byte aligned") }

/// search.c:1706 `qlean_search_bin` past the unboxing: for each of the `m` keys (dense `keys`, or `kenc`), the
/// binary search position in the sorted haystack (dense `hay`, or `enc`) of `n`, into `out`; threaded
/// (`bin_run`, `bin_tab_run`, `bin_gather_run`).
///
/// `step`'s answer is a function of the needle's `bin_key` and the haystack alone, so where the keys occupy a small
/// range (taken from a stride sample, not a min/max pass) the walks collapse to one per key in the range and a gather;
/// a needle the sample missed takes the walk. `BIN_TAB_MAX` keeps the table in L2, `m / 8` keeps the build under an
/// eighth of the walks it replaces.
pub fn bin(run: Runner, w: usize, is_float: bool, is_signed: bool, right: bool, hay: &[u8], enc: Option<&Coc>, n: i64,
           keys: &[u8], kenc: Option<&Coc>, m: usize, out: &mut [i64]) {
    assert!(matches!(w, 1 | 2 | 4 | 8), "qlean search: bin got element width {w}; the kernel is instantiated at 1, 2, 4 and 8 bytes");
    let wk = Walk { w, f: is_float, s: is_signed, right };
    let h = Col { d: hay, c: enc, uw: enc.map_or(0, |c| c.one_width()) };
    let kc = Col { d: keys, c: kenc, uw: 0 };
    let ob = crate::pod::bytes_mut(&mut out[..m]);
    let walk = |lo: usize, hi: usize, o: &mut [u8]| {
        let (o, mut k) = (i64s(o), Kcur::new(kc, w));
        for (j, x) in (lo..hi).zip(o) { *x = wk.pos(&h, bin_key(w, is_float, is_signed, k.at(j)), n) }
    };
    if m >= 8 * BIN_TAB_SAMPLE && n >= 64 {
        let step = m / BIN_TAB_SAMPLE;
        let (mut klo, mut khi) = (!0u64, 0u64);
        for j in (0..m).step_by(step) {
            let k = bin_key(w, is_float, is_signed, kenc.map_or_else(|| bin_at(keys, w, j), |c| c.get(j) as u64));
            klo = klo.min(k); khi = khi.max(k);
        }
        let (span, cnt) = (khi - klo, (khi - klo) as usize + 1);
        if span < BIN_TAB_MAX && cnt <= m / 8 {
            let mut tab = alloc::vec![0i64; cnt];
            crate::c::run_map(run, crate::pod::bytes_mut(&mut tab), cnt, 8, crate::QLEAN_COST_MATH, 8, &|lo, hi, o: &mut [u8]| {
                for (i, x) in (lo..hi).zip(i64s(o)) { *x = wk.pos(&h, klo + i as u64, n) }
            });
            let tab = &tab[..];
            crate::c::run_map(run, ob, m, 8, crate::QLEAN_COST_ARITH, 8, &|lo, hi, o: &mut [u8]| {
                let (o, mut k) = (i64s(o), Kcur::new(kc, w));
                for (j, x) in (lo..hi).zip(o) {
                    let key = bin_key(w, is_float, is_signed, k.at(j));
                    let d = key.wrapping_sub(klo);
                    *x = if d <= span { tab[d as usize] } else { wk.pos(&h, key, n) }
                }
            });
            return;
        }
    }
    crate::c::run_map(run, ob, m, 8, crate::QLEAN_COST_MATH, 8, &walk);
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
    // A32: expected values are search.c's `bin_key` (1439) and `bin_step` (1483), checked against the old C by /data/tmp/qrs/A32/diff.c
    #[test] fn bin_keys() {
        assert_eq!((bin_key(1, false, true, 0x80), bin_key(1, false, true, 0x7f), bin_key(1, false, false, 0x1ff)), (0, 0xff, 0xff));
        let (z, nz) = (bin_key(8, true, false, 0), bin_key(8, true, false, 1 << 63));
        assert_eq!(z, nz, "-0.0 folds onto 0.0");
        assert_eq!(bin_key(4, true, false, 0x7fc0_0001), bin_key(4, true, false, 0x7f80_0001), "every NaN is one value");
        assert!(bin_key(8, true, false, (-1.5f64).to_bits()) < bin_key(8, true, false, 0) && bin_key(8, true, false, 0) < bin_key(8, true, false, 2.5f64.to_bits()));
        assert_eq!(norm_key(4, true, 0x8000_0000), 0); assert_eq!(norm_key(8, false, 5), 5);
        assert_eq!(norm_key(8, true, 0x7ff0_0000_0000_0001), 0xfff8_0000_0000_0000);
    }
    fn bytes_of(v: &[i64], w: usize) -> alloc::vec::Vec<u8> { v.iter().flat_map(|x| x.to_le_bytes()[..w].to_vec()).collect() }
    fn run_bin(w: usize, right: bool, hay: &[i64], keys: &[i64]) -> alloc::vec::Vec<i64> {
        let mut out = vec![0i64; keys.len()];
        bin(crate::c::qlean_run_c, w, false, true, right, &bytes_of(hay, w), None, hay.len() as i64, &bytes_of(keys, w), None, keys.len(), &mut out);
        out
    }
    // `10 20 20 20 30 bin 20` is 3 and `binr 20` is 1 (the C comment's measurements); `bin` below every element is -1
    #[test] fn bin_and_binr() {
        let h = [10, 20, 20, 20, 30];
        assert_eq!(run_bin(8, false, &h, &[20, 5, 40, 10]), [3, -1, 4, 0]);
        assert_eq!(run_bin(8, true, &h, &[20, 5, 40, 10]), [1, 0, 5, 0]);
        assert_eq!(run_bin(1, false, &[-128, 0, 127], &[-128, 1]), [0, 1]);
        assert_eq!(run_bin(8, false, &[], &[3]), [-1]);
    }
    // the gather path: 40000 keys in a 100-wide range over 200 haystack elements, a stride-missed outlier takes the walk
    #[test] fn bin_table_path() {
        let h: alloc::vec::Vec<i64> = (0..200).map(|i| i * 3).collect();
        let mut keys: alloc::vec::Vec<i64> = (0..40000).map(|i| (i * 7919) % 100).collect();
        keys[1] = 5000; keys[39999] = -7;
        for right in [false, true] {
            let want: alloc::vec::Vec<i64> = keys.iter().map(|k| { let p = h.partition_point(|x| if right { x < k } else { x <= k }) as i64; if right { p } else { p - 1 } }).collect();
            assert_eq!(run_bin(8, right, &h, &keys), want);
        }
    }
    fn dense(b: &[u8], w: usize) -> Opnd<'_> { Opnd { src: Src::Dense(b), n: b.len() / w } }
    fn finds(kd: Kind, h: &[u8], x: &[u8]) -> Vec<i64> {
        let (hh, xx) = (dense(h, kd.width()), dense(x, kd.width()));
        let mut a = vec![0i64; xx.n];
        Probe::new(kd, &hh).find(&xx, 0, xx.n, &mut a);
        let mut b = vec![0i64; xx.n];
        Probe::over(kd, &hh, &xx).find(&xx, 0, xx.n, &mut b);
        let mut c = vec![0i64; xx.n];
        scan_kind(kd, &hh, &xx, &mut c);
        assert_eq!((&a, &b), (&c, &c), "table over the haystack, over the needles and the scan agree");
        a
    }
    fn le<const W: usize>(v: &[u64]) -> Vec<u8> { v.iter().flat_map(|x| x.to_le_bytes()[..W].to_vec()).collect() }
    // expected values: q (search.c's comments): `1 1 2?1` is 0, `1 1 2?9` is 3; one NaN, one zero (search.c:186)
    #[test] fn first_index_and_absent() {
        assert_eq!(finds(Kind::U32, &le::<4>(&[1, 1, 2]), &le::<4>(&[1, 2, 9])), [0, 2, 3]);
        assert_eq!(finds(Kind::U8, &[], &[1]), [0]);
        assert_eq!(finds(Kind::U64, &le::<8>(&[u64::MAX, 0]), &le::<8>(&[0, u64::MAX, 7])), [1, 0, 2]);
    }
    #[test] fn floats_one_zero_one_nan() {
        let h = le::<4>(&[0, 0x7fc0_0001, 0x3f80_0000]);
        assert_eq!(finds(Kind::F32, &h, &le::<4>(&[0x8000_0000, 0xffc0_0000, 0x3f80_0000, 0xbf80_0000])), [0, 1, 2, 3]);
        assert_eq!(finds(Kind::U32, &h, &le::<4>(&[0x8000_0000])), [3]);
        let h = le::<8>(&[0x8000_0000_0000_0000, 0x7ff0_0000_0000_0001]);
        assert_eq!(finds(Kind::F64, &h, &le::<8>(&[0, 0xfff8_0000_0000_0000, 0x7ff0_0000_0000_0000])), [0, 1, 2]);
    }
    #[test] fn direct_when_dense_hashed_when_spread() {
        let h: Vec<u8> = (10..21u8).collect();
        let t = table::<u8>(&dense(&h, 1));
        assert!(t.direct && t.lo == 10 && t.top == 10);
        assert_eq!(finds(Kind::U8, &h, &[10, 20, 21, 9]), [0, 10, 11, 11]);
        let h: Vec<u64> = (0..100).map(|i| i * 1_000_003).collect();
        let t = table::<u64>(&dense(&le::<8>(&h), 8));
        assert!(!t.direct && t.used == 100 && t.slot.len() == 256);
        assert_eq!(finds(Kind::U64, &le::<8>(&h), &le::<8>(&[h[57], 5, h[0], h[99]])), [57, 100, 0, 99]);
        // sixteen bytes are always hashed, and the high word counts
        let g: Vec<u8> = [[1u64, 0], [1, 1], [0, 1]].iter().flat_map(|p| le::<8>(p)).collect();
        assert!(!table::<u128>(&dense(&g, 16)).direct);
        assert_eq!(finds(Kind::U128, &g, &[g[16..32].to_vec(), g[32..].to_vec(), vec![0; 16]].concat()), [1, 2, 3]);
    }
    #[test] fn member_sets_bits_from_lo() {
        let h = le::<2>(&[3, 9, 4]);
        let x = le::<2>(&[9, 1, 3, 3, 8, 4, 4, 0, 3, 9, 0, 0]);
        let mut out = [0u8; 2];
        Probe::new(Kind::U16, &dense(&h, 2)).member(&dense(&x, 2), 0, 12, &mut out);
        assert_eq!(out, [0b0110_1101, 0b0000_0011]);
        let mut out = [0u8; 1];
        Probe::new(Kind::U16, &dense(&h, 2)).member(&dense(&x, 2), 8, 12, &mut out);
        assert_eq!(out, [0b0000_0011]);
    }
    #[test] fn srange_is_signed_at_the_key_width() {
        assert_eq!(srange::<u8>(&dense(&[0xff, 0x7f, 1], 1)), (-1, 127));
        assert_eq!(srange::<u32>(&dense(&[], 4)), (i64::MAX, i64::MIN));
        assert_eq!(srange::<u128>(&dense(&le::<8>(&[1, 0, u64::MAX, 0]), 16)), (-1, 1));
        assert_eq!(srange::<u16>(&Opnd { src: Src::Ids(&[], 8), n: 0 }), (0, 127));
    }
}
