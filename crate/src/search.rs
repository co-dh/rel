#![forbid(unsafe_code)]
//! Column (a), search.rs: operands (A28), the probe table (A29), find/member (A30), bits and symbols (A31), binary
//! search (A32), run starts (A33). The `qlean_search_*` entries unbox and allocate and stay C (§1).
use alloc::{vec, vec::Vec};

use crate::c::Runner;
use crate::coc::Coc;
use crate::ids;
use crate::sym::Syms;
pub use crate::blocks::{Blocks, Src};
/// search.rs `kind`: the key type, chosen once per operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind { U8, U16, U32, U64, F32, F64, U128 }

// ---- A28: search.rs, 407, 818 ----
/// search.rs `coc_exc_within`: every patch of block `b` lies in `lo ..= hi`.
pub fn coc_exc_within(c: &Coc, b: usize, lo: i64, hi: i64) -> bool {
    c.exc.filter(|e| !e.pos.is_empty()).is_some_and(|e| (e.off[b] as usize..e.off[b + 1] as usize).any(|j| (lo..=hi).contains(&c.exc(j))))
}
/// search.rs `ids_top`: one past the largest id at `lw` bits.
pub fn ids_top(lw: u32) -> u64 { if lw >= 64 { !0 } else { (1u64 << lw) - 1 } }
/// search.rs `coc_srange`: the column's value range from its metadata.
pub fn coc_srange(c: &Coc) -> (i64, i64) {
    let m = &c.meta;
    let (mut a, mut z) = (i64::MAX, i64::MIN);
    for (b, ..) in Blocks::from(*c).walk() { a = a.min(m.base[b]); z = z.max(m.maxv[b]) }
    for j in 0..c.exc.map_or(0, |e| e.pos.len()) { let v = c.exc(j); a = a.min(v); z = z.max(v) }
    (a, z)
}
/// search.rs `sext`: the low `w` bytes of `v`, sign-extended.
pub fn sext(v: u64, w: usize) -> i64 { let s = 64 - 8 * w as u32; if s == 0 { v as i64 } else { (v << s) as i64 >> s } }
/// search.rs `kind_of`: aborts naming `who` for a width the dispatch never sends.
pub fn kind_of(w: usize, is_float: bool, who: &str) -> Kind {
    match (w, is_float) {
        (1, false) => Kind::U8, (2, false) => Kind::U16, (4, false) => Kind::U32, (4, true) => Kind::F32,
        (8, false) => Kind::U64, (8, true) => Kind::F64, (16, false) => Kind::U128,
        _ => panic!("qlean search: {who} got element width {w} with is_float={}; the kernels are instantiated at 1, 2, 4, 8 and 16 bytes, and only 4 and 8 have a float kind", is_float as u32),
    }
}
impl Kind {
    /// search.rs `kind_width`
    pub fn width(self) -> usize {
        match self { Kind::U8 => 1, Kind::U16 => 2, Kind::U32 | Kind::F32 => 4, Kind::U64 | Kind::F64 => 8, Kind::U128 => 16 }
    }
}

// ---- A29: search.rs, the probe table, one instance per key type ----
/// The build starts a slot's cache line this many keys early (search.rs `SEARCH_AHEAD`).
pub const AHEAD: usize = 32;
/// A key the probe table holds: `RAW`/`F32Z`/`F64Z` of search.rs (floats compare as that comment says: both zeros
/// one value, every NaN one value). `of` reads the key at the start of `b` already normalised, so every use of a key
/// is the one that table, scan and walk agree on.
pub trait PKey: Copy + Send + Sync {
    /// bytes per key
    const W: usize;
    fn of(b: &[u8]) -> Self;
    /// the normalised bits, zero-extended
    fn key(self) -> u128;
    /// search.rs `KEY_HASH`: the key up to eight bytes, a sixteen-byte key's two words folded into one
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
pub fn mask<K: PKey>() -> u64 { if K::W >= 8 { !0 } else { (1u64 << (8 * K::W)) - 1 } }

/// search.rs `ptab`: direct (`slot` indexed by key − `lo`) or hashed (`sh`); `tab[g]` the first index + 1.
pub struct Ptab<K> { pub tab: Vec<usize>, pub slot: Vec<u32>, pub key: Vec<K>, pub top: u64, pub lo: u64, pub n: usize,
                     pub used: usize, pub direct: bool, pub sh: u32 }

/// The blocks of `x` covering elements `lo .. hi`, each as the slice of those elements starting at element `at`.
pub fn blocks(x: &Blocks, w: usize, lo: usize, hi: usize, mut f: impl FnMut(usize, &[u8])) {
    let mut buf = crate::pod::Scr::<u64>::new(2 * x.blk());
    let bb = crate::pod::bytes_mut(&mut buf);
    for (b, blo, at, end) in x.tiles(lo, hi) { f(at, &x.view(b, w, bb)[(at - blo) * w..(end - blo) * w]) }
}

/// search.rs `table_*`: the table over the haystack `o`, a block at a time, each slot holding the first index its key
/// occurs at plus one. Direct when the keys span at most `4n + 8`; a direct table whose every slot is filled stops there.
pub fn table<K: PKey>(o: &Blocks) -> Ptab<K> {
    let mut p = Ptab { tab: Vec::new(), slot: Vec::new(), key: Vec::new(), top: 0, lo: 0, n: o.n, used: 0, direct: false, sh: 0 };
    let (lg, mut buf) = (o.lg(), crate::pod::Scr::<u64>::new(2 << o.lg()));
    let bb = crate::pod::bytes_mut(&mut buf);
    let nb = o.nblk();
    if o.n > 0 && K::W <= 8 {
        let (lo, span) = match o.src {
            Src::Ids(_, lw) => (0, ids_top(lw)),
            Src::For(c) => { let (a, z) = coc_srange(&c); (a as u64 & mask::<K>(), (z as u64).wrapping_sub(a as u64)) }
            Src::Dense(_) | Src::Alp(_) => {
                // the C reads exactly `n` elements; a shorter payload is a caller bug and would fold to an empty range
                if let Src::Dense(d) = o.src { assert!(d.len() >= o.n * K::W, "qlean search: a dense haystack of {} bytes holds fewer than its {} elements of {} bytes", d.len(), o.n, K::W) }
                let mut buf = crate::pod::Scr::<u64>::new(o.blk() * K::W / 8 + 1);
                let (mn, mx) = o.walk().fold((!0u64, 0u64), |acc, (b, ..)| o.view(b, K::W, crate::pod::bytes_mut(&mut buf)).chunks_exact(K::W)
                    .map(|c| K::of(c).key() as u64).fold(acc, |(a, z), k| (a.min(k), z.max(k))));
                (mn, mx - mn)
            }
        };
        if span < o.n as u64 * 4 + 8 {
            (p.direct, p.lo, p.top) = (true, lo, span);
            p.tab = vec![0usize; span as usize + 1];
            for b in 0..nb {
                for (j, c) in o.view(b, K::W, bb).chunks_exact(K::W).enumerate() {
                    let d = ((K::of(c).key() as u64).wrapping_sub(lo) & mask::<K>()) as usize;
                    if p.tab[d] == 0 {
                        p.tab[d] = (b << lg) + j + 1;
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
        let blk = o.view(b, K::W, bb);
        let cnt = blk.len() / K::W;
        for (j, c) in blk.chunks_exact(K::W).enumerate() {
            let k = K::of(c);
            if j + AHEAD < cnt { crate::simd::prefetch(&p.slot[at(K::of(&blk[(j + AHEAD) * K::W..]), p.sh)]) }
            let mut s = at(k, p.sh);
            while p.slot[s] != 0 && p.key[p.slot[s] as usize - 1].key() != k.key() { s = (s + 1) & p.top as usize }
            if p.slot[s] == 0 {
                p.key.push(k);
                p.tab.push((b << lg) + j + 1);
                p.used += 1;
                p.slot[s] = p.used as u32;
            }
        }
    }
    p
}
impl<K: PKey> Ptab<K> {
    /// search.rs `dslot_*`: the slot key `k` names, or `usize::MAX` where none can hold it.
    #[inline(always)]
    fn dslot(&self, k: K) -> usize {
        let d = (k.key() as u64).wrapping_sub(self.lo) & mask::<K>();
        if d <= self.top { d as usize } else { usize::MAX }
    }
    /// search.rs `hslot_*`: the key number of `k`, or `usize::MAX`.
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
    /// search.rs `hits_*`: the haystack `h` walked in order to the first occurrence of each key of a table built over
    /// the needles, `ans[s]` that index plus one; it stops once every key is found. An encoded block whose `[base, maxv]`
    /// misses the needles' `[lo, hi]` is passed over on its metadata.
    pub fn hits(&self, h: &Blocks, lo: i64, hi: i64, ans: &mut [usize]) {
        let mut left = self.used;
        let lg = h.lg();
        let mut buf = crate::pod::Scr::<u64>::new(2 << lg);
        let bb = crate::pod::bytes_mut(&mut buf);
        for b in 0..h.nblk() {
            if left == 0 { return }
            if let Src::For(c) = h.src {
                if (c.meta.maxv[b] < lo || c.meta.base[b] > hi) && !coc_exc_within(&c, b, lo, hi) { continue }
            }
            for (j, c) in h.view(b, K::W, bb).chunks_exact(K::W).enumerate() {
                let s = self.slot_of(K::of(c));
                if s != usize::MAX && self.tab[s] != 0 && ans[s] == 0 {
                    ans[s] = (b << lg) + j + 1;
                    left -= 1;
                    if left == 0 { return }
                }
            }
        }
    }
    /// each element `i` of `x`'s `lo .. hi` with its slot; which table was built is settled before the loop, not per element.
    fn each(&self, x: &Blocks, lo: usize, hi: usize, mut f: impl FnMut(usize, usize)) {
        blocks(x, K::W, lo, hi, |at, q| {
            if self.direct { for (j, c) in q.chunks_exact(K::W).enumerate() { f(at + j, self.dslot(K::of(c))) } }
            else { for (j, c) in q.chunks_exact(K::W).enumerate() { f(at + j, self.hslot(K::of(c))) } }
        })
    }
    /// search.rs `findtab_*`: `x ? hay` for `lo .. hi` into `out[i - lo]`, `ans` the table's own `tab` or the walk's
    /// `hits`; an absent key answers `n`.
    pub fn find(&self, ans: &[usize], x: &Blocks, lo: usize, hi: usize, out: &mut [i64]) {
        self.each(x, lo, hi, |i, s| out[i - lo] = if s != usize::MAX && ans[s] != 0 { ans[s] as i64 - 1 } else { self.n as i64 })
    }
    /// search.rs `membertab_*`: `x in hay` for `lo .. hi`, bit `i - lo` of `out` (`lo` a multiple of 8) set when found.
    pub fn member(&self, ans: &[usize], x: &Blocks, lo: usize, hi: usize, out: &mut [u8]) {
        self.each(x, lo, hi, |i, s| if s != usize::MAX && ans[s] != 0 { out[(i - lo) >> 3] |= 1 << ((i - lo) & 7) })
    }
}
/// search.rs `scan_*`: the first index of each needle `lo .. hi` of `x` in the dense haystack `h`, or `h.n`; eight
/// keys at a time so that the comparison vectorises.
pub fn scan<K: PKey>(h: &Blocks, x: &Blocks, lo: usize, hi: usize, out: &mut [i64]) {
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
/// search.rs `srange_*`: the operand's signed key range, which a walk over an encoded haystack tests each block's
/// metadata against.
pub fn srange<K: PKey>(o: &Blocks) -> (i64, i64) {
    match o.src {
        Src::Ids(_, lw) => (0, (ids_top(lw) >> 1) as i64),
        Src::Dense(_) | Src::Alp(_) => {
            let (w, mut buf) = (K::W.min(8), crate::pod::Scr::<u64>::new(o.blk() * K::W / 8 + 1));
            o.walk().fold((i64::MAX, i64::MIN), |acc, (b, ..)| o.view(b, K::W, crate::pod::bytes_mut(&mut buf)).chunks_exact(K::W)
                .map(|c| { let mut b = [0u8; 8]; b[..w].copy_from_slice(&c[..w]); sext(u64::from_le_bytes(b), w) })
                .fold(acc, |(a, z), v| (a.min(v), z.max(v))))
        }
        Src::For(c) => coc_srange(&c),
    }
}

/// The seven key types as one handle the C side holds: the table, and the answers of a walk when it was built over the
/// needles (`hit`; absent: the table's own `tab`).
pub enum Any { U8(Ptab<u8>), U16(Ptab<u16>), U32(Ptab<u32>), U64(Ptab<u64>), F32(Ptab<F32>), F64(Ptab<F64>), U128(Ptab<u128>) }
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
impl Probe {
    /// the table over the smaller side: the needles `x` where they are fewer than the haystack `h`
    pub fn of(kd: Kind, h: &Blocks, x: &Blocks) -> Probe { if x.n < h.n { Probe::over(kd, h, x) } else { Probe::new(kd, h) } }
    /// the table over the haystack `o`
    pub fn new(kd: Kind, o: &Blocks) -> Probe { by_kind!(kd, K, V => Probe { t: V(table::<K>(o)), hit: None }) }
    /// search.rs `SEARCH_TABLE`'s smaller-side branch: the table over the needles `x`, and the haystack `h` walked to
    /// the first occurrence of each needle key.
    pub fn over(kd: Kind, h: &Blocks, x: &Blocks) -> Probe {
        by_kind!(kd, K, V => {
            let mut t = table::<K>(x);
            let (lo, hi) = if matches!(h.src, Src::For(_)) { srange::<K>(x) } else { (i64::MIN, i64::MAX) };
            let mut ans = vec![0usize; t.top as usize + 1];
            t.hits(h, lo, hi, &mut ans);
            t.n = h.n;
            Probe { t: V(t), hit: Some(ans) }
        })
    }
    /// `x ? hay` for `lo .. hi`
    pub fn find(&self, x: &Blocks, lo: usize, hi: usize, out: &mut [i64]) {
        any!(&self.t, p => p.find(self.hit.as_deref().unwrap_or(&p.tab), x, lo, hi, out))
    }
    /// `x in hay` for `lo .. hi`
    pub fn member(&self, x: &Blocks, lo: usize, hi: usize, out: &mut [u8]) {
        any!(&self.t, p => p.member(self.hit.as_deref().unwrap_or(&p.tab), x, lo, hi, out))
    }
}
/// `scan` at the key type of `kd`
pub fn scan_kind(kd: Kind, h: &Blocks, x: &Blocks, out: &mut [i64]) {
    by_kind!(kd, K, V => scan::<K>(h, x, 0, x.n, out))
}

// ---- A30: search.rs ----
/// search.rs `search` past the allocation: `x ? h` (index, `h.n` when absent; `out` is `8 * x.n` bytes) or `x in h`
/// (`member`, a bit each, LSB first; `out` is `x.n.div_ceil(8)` bytes) into `out`, threaded. The table goes over the
/// smaller side, so the haystack is walked to the first occurrence of each needle key when the needles are fewer.
/// The table is read-only for the whole pass, so slices are disjoint in `out`; a probe is `QLEAN_COST_ARITH` rather than
/// `GATHER` (measured 0.40 ns an element against 0.05 for a straight read: 400 ns a thousand on one thread, 66 on 24).
pub fn search(run: Runner, kd: Kind, h: &Blocks, x: &Blocks, member: bool, out: &mut [u8]) {
    let m = x.n;
    if m == 0 { return }
    let t = Probe::of(kd, h, x);
    if member {
        out.fill(0); // `member` ORs bits in
        // a unit is a byte of the answer, so no two slices touch the same byte
        let bytes = m.div_ceil(8);
        crate::c::run_map(run, out, bytes, 1, crate::QLEAN_COST_ARITH, kd.width() * 8, &|lo, hi, o: &mut [u8]| {
            t.member(x, lo * 8, (hi * 8).min(m), o)
        });
    } else {
        crate::c::run_map(run, out, m, 8, crate::QLEAN_COST_ARITH, 8, &|lo, hi, o: &mut [u8]| t.find(x, lo, hi, i64s(o)));
    }
}
/// search.rs `ids_key_width`: bytes an id key takes where one side is at `a` bits and the other at `b`.
pub fn ids_key_width(a: usize, b: usize) -> usize { match a.max(b) { ..=8 => 1, ..=16 => 2, ..=32 => 4, _ => 8 } }

// ---- A31: search.rs ----
/// rust/src/coc.rs `bit_at`: bit `i` of the payload, 0 past its end.
pub fn bit_at(b: &[u8], i: usize) -> u8 { b.get(i >> 3).map_or(0, |&x| x >> (i & 7) & 1) }
/// search.rs `word_at`: the 8 payload bytes from byte `i` as one little-endian word, zero past the end.
pub fn word_at(b: &[u8], i: usize) -> u64 {
    let src = b.get(i..).unwrap_or(&[]);
    let mut w = [0u8; 8];
    let m = src.len().min(8);
    w[..m].copy_from_slice(&src[..m]);
    u64::from_le_bytes(w)
}
/// search.rs `find_bit`: the first index of `needle` among `n` bits, whole bytes at a time, `n` when there is none.
pub fn find_bit(b: &[u8], n: usize, needle: u8) -> usize {
    let mut i = 0;
    while i < n {
        let byte = i >> 3;
        let raw = b.get(byte).copied().unwrap_or(0);
        let v = (if needle != 0 { raw } else { !raw }) & (0xffu8 << (i & 7));
        if v != 0 { return ((byte << 3) + v.trailing_zeros() as usize).min(n) }
        i = (byte + 1) << 3;
    }
    n
}
/// search.rs `qlean_search_find_bit_vec` past the unboxing: each needle's first index. Only two answers exist, so
/// both are computed once.
pub fn find_bit_vec(n: usize, hay: &[u8], ndl: &[u8], m: usize, out: &mut [i64]) {
    let at = [find_bit(hay, n, 0) as i64, find_bit(hay, n, 1) as i64];
    for (j, o) in out[..m].iter_mut().enumerate() { *o = at[bit_at(ndl, j) as usize] }
}
/// search.rs `qlean_search_member_bits` past the unboxing: bit `i` of `out` (`m.div_ceil(8)` bytes) is set when
/// `xs`' bit `i` occurs among the first `n` bits of `hay`; the tail bits stay zero.
pub fn member_bits(m: usize, xs: &[u8], n: usize, hay: &[u8], out: &mut [u8]) {
    out.fill(0);
    member_bits_at(bits_held(n, hay), xs, 0, m, out)
}
/// Which of 0 and 1 occur among the first `n` bits of `hay`.
pub fn bits_held(n: usize, hay: &[u8]) -> [bool; 2] { [find_bit(hay, n, 0) < n, find_bit(hay, n, 1) < n] }
/// `member_bits` over elements `lo .. hi` (`lo` a multiple of 8) into the zeroed `out`, its bit 0 element `lo`.
pub fn member_bits_at(has: [bool; 2], xs: &[u8], lo: usize, hi: usize, out: &mut [u8]) {
    for i in lo..hi { if has[bit_at(xs, i) as usize] { out[(i - lo) >> 3] |= 1 << (i & 7) } }
}
/// search.rs `spread`: the set bits of word `v` (word `i`) as indices into `out` at `at`; answers the new `at`.
pub fn spread(out: &mut [i64], mut at: usize, i: usize, mut v: u64) -> usize {
    while v != 0 { out[at] = ((i << 6) + v.trailing_zeros() as usize) as i64; at += 1; v &= v - 1 }
    at
}
/// the mask of word `i` of `n` bits: the last word (`n >> 6`) keeps the low `n & 63` bits, every other all 64
pub fn word_mask(n: usize, i: usize) -> u64 { if i == n >> 6 { if n & 63 != 0 { !0 >> (64 - (n & 63)) } else { 0 } } else { !0 } }
/// search.rs `qlean_search_where_bits`, the first pass: how many of the first `n` bits are set. A word inside the
/// payload is read straight (`full` of them), the ragged end and the masked tail go through `word_at`.
pub fn where_count(n: usize, bits: &[u8]) -> usize {
    let (whole, full) = (n >> 6, (bits.len() / 8).min(n >> 6));
    let k: usize = bits[..full * 8].chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().expect("8 bytes")).count_ones() as usize).sum();
    k + (full..=whole).map(|i| (word_at(bits, i * 8) & word_mask(n, i)).count_ones() as usize).sum::<usize>()
}
/// search.rs `qlean_search_where_bits`, the second pass (`out` holds `where_count`): the ascending indices of the set
/// bits among the first `n`; answers the count. A clear group of eight words is skipped on one test, as the mask of a
/// selective `where` is mostly clear.
pub fn where_bits(n: usize, bits: &[u8], out: &mut [i64]) -> usize {
    let (whole, full) = (n >> 6, (bits.len() / 8).min(n >> 6));
    let (mut at, mut i) = (0, 0);
    while i + 8 <= full {
        let g = &bits[i * 8..(i + 8) * 8];
        if g.iter().any(|&b| b != 0) { for (j, c) in g.chunks_exact(8).enumerate() { at = spread(out, at, i + j, u64::from_le_bytes(c.try_into().expect("8 bytes"))) } }
        i += 8;
    }
    for i in i..=whole { at = spread(out, at, i, word_at(bits, i * 8) & word_mask(n, i)) }
    at
}
/// search.rs `sym_scan`: the first of the first `n` symbols equal to `k`, or `n`.
pub fn sym_scan(s: &Syms, n: usize, k: &[u8]) -> usize {
    if n == 0 { return 0 }
    let mut lo = s.off(0);
    for i in 0..n {
        let hi = s.off(i + 1);
        let len = hi.saturating_sub(lo + 1);
        if len == k.len() && (len == 0 || crate::sym::sym_eq(&s.blob[lo..lo + len], k)) { return i }
        lo = hi;
    }
    n
}
/// search.rs `qlean_search_find_sym_scalar` past the unboxing and the kept hash: one scan.
pub fn find_sym_scalar(s: &Syms, ndl: &[u8]) -> usize { sym_scan(s, s.count(), ndl) }


// ---- A32: search.rs ----
/// search.rs `bin_key`: `v` as an unsigned key in the column's order.
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
/// search.rs `bin_at`: element `i` of a `w`-byte payload. One fixed-width load per width: a `w`-byte copy into a
/// `u64` compiles to a `memcpy` call per element, which was most of `runStarts`' pass.
#[inline(always)]
pub fn bin_at(p: &[u8], w: usize, i: usize) -> u64 {
    fn ld<const W: usize>(p: &[u8], i: usize) -> [u8; W] { p[i * W..(i + 1) * W].try_into().unwrap() }
    match w {
        1 => p[i] as u64,
        2 => u16::from_le_bytes(ld(p, i)) as u64,
        4 => u32::from_le_bytes(ld(p, i)) as u64,
        8 => u64::from_le_bytes(ld(p, i)),
        _ => { let mut b = [0u8; 8]; b[..w].copy_from_slice(&p[i * w..(i + 1) * w]); u64::from_le_bytes(b) }
    }
}
/// search.rs `norm_key`
pub fn norm_key(w: usize, is_float: bool, v: u64) -> u64 {
    if !is_float { return v }
    let (low, inf, nan) = if w == 8 { (0x7fff_ffff_ffff_ffffu64, 0x7ff0_0000_0000_0000u64, 0xfff8_0000_0000_0000u64) }
                          else { (0x7fff_ffff, 0x7f80_0000, 0xffc0_0000) };
    if v & low == 0 { 0 } else if v & low > inf { nan } else { v }
}

/// A haystack or a needle column where it lies: dense, or encoded with one residual width `uw` (`one_width`).
#[derive(Clone, Copy)]
pub struct Col<'a> { pub d: &'a [u8], pub c: Option<&'a Coc<'a>>, pub uw: u8 }
impl Col<'_> {
    pub fn at(&self, w: usize, i: usize) -> u64 { self.c.map_or_else(|| bin_at(self.d, w, i), |c| c.get_w(self.uw, i) as u64) }
}
/// The flags every walk is handed.
#[derive(Clone, Copy)]
pub struct Walk { pub w: usize, pub f: bool, pub s: bool, pub right: bool }
impl Walk {
    /// search.rs `bin_step`: the partition point in `lo .. hi` of key `k`. Branchless, which is what makes the
    /// timing a property of the code and not of the branch predictor's aliasing (the C comment's measurement).
    /// `ix` is the index payload the walk reads `h` through (`order`), `|i| i` where each position is its own index.
    pub fn step(self, h: &Col, ix: impl Fn(usize) -> usize, k: u64, mut lo: i64, hi: i64) -> i64 {
        let mut len = hi - lo;
        while len > 0 {
            let (half, mid) = (len / 2, lo + len / 2);
            let v = bin_key(self.w, self.f, self.s, h.at(self.w, ix(mid as usize)));
            let adv = if self.right { v < k } else { v <= k };
            let (nlo, nlen) = (mid + 1, len - half - 1);
            lo = if adv { nlo } else { lo };
            len = if adv { nlen } else { half };
        }
        lo
    }
    /// `bin` for key `k` over `n` elements: the position, `- 1` for `bin` and as is for `binr`.
    fn pos(self, h: &Col, k: u64, n: i64) -> i64 { let at = self.step(h, |i| i, k, 0, n); if self.right { at } else { at - 1 } }
}
/// search.rs `kcur`: a worker's view of the needles, the dense payload or the last block restored.
pub struct Kcur<'a> { k: Col<'a>, w: usize, b: usize, buf: crate::pod::Scr<u64> }
impl<'a> Kcur<'a> {
    fn new(k: Col<'a>, w: usize) -> Self { Kcur { k, w, b: usize::MAX, buf: crate::pod::Scr::<u64>::new(k.c.map_or(0, |c| c.meta.blk())) } }
    /// search.rs `kcur_at`
    fn at(&mut self, j: usize) -> u64 {
        let Some(c) = self.k.c else { return bin_at(self.k.d, self.w, j) };
        let s = Blocks::from(*c);
        let b = j >> s.lg();
        if b != self.b {
            s.load_w(b, s.span(b).1, self.w, crate::pod::bytes_mut(&mut self.buf));
            self.b = b;
        }
        bin_at(crate::pod::bytes(&self.buf), self.w, j & (s.blk() - 1))
    }
}
/// search.rs `BIN_TAB_MAX`, `BIN_TAB_SAMPLE`
pub const BIN_TAB_MAX: u64 = 1 << 16;
pub const BIN_TAB_SAMPLE: usize = 4096;

pub fn i64s(o: &mut [u8]) -> &mut [i64] { crate::pod::cast_mut(o).expect("bin: the answer is 8-byte aligned") }

/// search.rs `qlean_search_bin` past the unboxing: for each of the `m` keys (dense `keys`, or `kenc`), the
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





/// search.rs `run_starts` past the allocation: the start of each run of equal elements of `o` (`norm_key`'s equality)
/// into `out` (`o.n + 1` long), then `o.n` as the terminator; answers the count with the terminator. The payload is read
/// a block at a time at width `w`, 1, 2, 4 or 8.
pub fn run_starts(o: &Blocks, w: usize, is_float: bool, out: &mut [i64]) -> usize {
    assert!(matches!(w, 1 | 2 | 4 | 8), "qlean search: run_starts got element width {w}; the kernel is instantiated at 1, 2, 4 and 8 bytes");
    // one block at element width `W` from element `skip`: a start is written when the key moves off the previous one
    #[inline(always)]
    fn blk<const W: usize>(h: &[u8], at: usize, skip: usize, prev: &mut u64, g: &mut usize, out: &mut [i64], key: impl Fn(u64) -> u64) {
        for (j, c) in h.chunks_exact(W).enumerate().skip(skip) {
            let mut b = [0u8; 8];
            b[..W].copy_from_slice(c);
            let v = key(u64::from_le_bytes(b));
            if v != *prev { out[*g] = (at + j) as i64; *g += 1; *prev = v }
        }
    }
    let (mut buf, mut g, mut prev) = (crate::pod::Scr::<u64>::new(o.blk()), 0, 0u64);
    for (b, at, nb) in o.walk() {
        // a bit block runs the word algorithm of `run_starts_bits`, the key being the bit itself
        if let (false, Src::For(c)) = (is_float, &o.src) { if let Some(p) = c.bit_blk(b) {
            if b == 0 { out[0] = 0; g = 1; prev = (p[0] & 1) as u64 }
            crate::bitblk::run_starts(p, nb, at, &mut prev, &mut g, out);
            continue
        } }
        let h = o.view(b, w, crate::pod::bytes_mut(&mut buf));
        // row 0 starts a run whatever its key; the loop then needs no test for it
        let skip = if b == 0 { out[0] = 0; g = 1; prev = norm_key(w, is_float, bin_at(h, w, 0)); 1 } else { 0 };
        // the width switch hoisted out of the element loop, as search.rs's `RS_RUNS` hoists it
        match (is_float, w) {
            (true, 1) => blk::<1>(h, at, skip, &mut prev, &mut g, out, |v| norm_key(1, true, v)),
            (true, 2) => blk::<2>(h, at, skip, &mut prev, &mut g, out, |v| norm_key(2, true, v)),
            (true, 4) => blk::<4>(h, at, skip, &mut prev, &mut g, out, |v| norm_key(4, true, v)),
            (true, _) => blk::<8>(h, at, skip, &mut prev, &mut g, out, |v| norm_key(8, true, v)),
            (_, 1) => blk::<1>(h, at, skip, &mut prev, &mut g, out, |v| v),
            (_, 2) => blk::<2>(h, at, skip, &mut prev, &mut g, out, |v| v),
            (_, 4) => blk::<4>(h, at, skip, &mut prev, &mut g, out, |v| v),
            _ => blk::<8>(h, at, skip, &mut prev, &mut g, out, |v| v),
        }
    }
    out[g] = o.n as i64;
    g + 1
}
/// search.rs `qlean_search_run_starts_ids`: `runStarts` over `n` ids at `w` bits; the dictionary is distinct, so equal
/// ids are equal elements. `out` is `n + 1` long; answers the count with the terminator `n`.
pub fn run_starts_ids(n: usize, w: u32, ids: &[u8], out: &mut [i64]) -> usize {
    let g = ids::runs(ids, n, w, usize::MAX, n, out);
    out[g] = n as i64;
    g + 1
}
/// search.rs `qlean_search_run_starts_bits`: `runStarts` over `n` booleans packed LSB first, a byte past the end
/// reading 0. A word at a time: bit i of `x ^ (x << 1 | top)` is set where bit i differs from bit i-1, `top` the previous
/// word's last bit. `out` is `n + 1` long.
pub fn run_starts_bits(n: usize, bits: &[u8], out: &mut [i64]) -> usize {
    let (mut g, mut top) = (0, 0u64);
    for k in 0..n.div_ceil(64) {
        let mut b = [0u8; 8];
        let src = bits.get(k * 8..).unwrap_or(&[]);
        let m = src.len().min(8);
        b[..m].copy_from_slice(&src[..m]);
        let x = u64::from_le_bytes(b);
        let mut d = x ^ (x << 1 | top);
        top = x >> 63;
        if k == 0 { d |= 1 } // row 0 starts a run whatever its bit
        if n - k * 64 < 64 { d &= (1u64 << (n - k * 64)) - 1 }
        while d != 0 { out[g] = (k * 64 + d.trailing_zeros() as usize) as i64; g += 1; d &= d - 1 }
    }
    out[g] = n as i64;
    g + 1
}






// ---- B17: search.rs's scalar find, the Frame-of-Reference equality walks, the id mask ----
/// `qlean_search_find_scalar`'s body: the least `i < hay.len() / w` whose key equals the needle's, `hay.len() / w` when
/// none does. The needle is `scan`'s one key, the low `w` bytes of `needle` little-endian (zero above, for `w` 16).
pub fn find_scalar(w: usize, is_float: bool, hay: &[u8], needle: u64) -> usize {
    let kd = kind_of(w, is_float, "find_scalar"); // before dividing by `w`
    let nb = (needle as u128).to_le_bytes();
    let mut r = [0i64];
    scan_kind(kd, &Blocks::new(Src::Dense(hay), hay.len() / w), &Blocks::new(Src::Dense(&nb[..w]), 1), &mut r);
    r[0] as usize
}

/// `qlean_coc_find_scalar`'s body: the least row of `c` holding `v`, `c.meta.n` when none does.
pub fn coc_find(c: &Coc, v: i64) -> usize {
    eq_blocks(c, v, |b, at, cnt, buf| match c.bit_blk(b) {
        Some(p) => crate::bitblk::find(p, cnt, v).map(|i| at + i),
        None => { c.decode_blk(b, cnt, buf); buf[..cnt].iter().position(|&x| x == v).map(|i| at + i) }
    }).unwrap_or(c.meta.n)
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::coc::{Exc, Meta};
    // expected values: search.rs at 04ecc24 (coc_srange, coc_exc_within, sext, ids_top, kind_of, kind_width, opnd_blk)
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
        Coc { meta: Meta { lg: crate::DEFAULT_LG, base, maxv, off, bsum: base, width, sumnul: 0, sumn: 0, n, nblk: m, mblk: m }, pack: &[], exc, fdelta: None }
    }
    #[test] fn srange_and_exc_within() {
        let (raw, pos, off) = ([(-9i64).to_ne_bytes(), 40i64.to_ne_bytes()].concat(), [1u16, 2], [0u32, 0, 2]);
        let e = Exc { off: &off, pos: &pos, raw: &raw, esz: 8, asc: crate::coc::ascending(&off, &pos) };
        let c = col(&[10, 20], &[15, 30], &[0, 0], &[0, 0], 1025, Some(e));
        assert_eq!(coc_srange(&c), (-9, 40));
        assert!(!coc_exc_within(&c, 0, -100, 100) && coc_exc_within(&c, 1, -9, -9) && coc_exc_within(&c, 1, 40, 41));
        assert!(!coc_exc_within(&c, 1, -8, 39));
        let c = col(&[10, 20], &[15, 30], &[0, 0], &[0, 0], 1024, None);
        assert_eq!((coc_srange(&c), coc_exc_within(&c, 0, i64::MIN, i64::MAX)), ((10, 15), false));
    }
    #[test] fn blk_dense_ids_enc() {
        let d: Vec<u8> = (0..2100u32).flat_map(|i| (i as u16).to_le_bytes()).collect();
        let o = Blocks::new(Src::Dense(&d), 2100);
        let mut buf = [0u64; 1024 * 2 / 8];
        let b = crate::pod::bytes_mut(&mut buf);
        assert_eq!((o.view(2, 2, b).len(), o.view(0, 2, b).len()), (52 * 2, 2048));
        assert_eq!(o.view(2, 2, b)[..4], [0, 8, 1, 8]);
        // ids at 4 bits: id i is i % 16; written at 4-byte keys
        let p: Vec<u8> = (0..1050usize).map(|i| ((2 * i % 16) as u8) | ((((2 * i + 1) % 16) as u8) << 4)).collect();
        let o = Blocks::new(Src::Ids(&p, 4), 2100);
        let mut buf = vec![0u64; 1024 * 4 / 8];
        let b = crate::pod::bytes_mut(&mut buf);
        let r = o.view(2, 4, b);
        assert_eq!(r.len(), 52 * 4);
        assert_eq!(&r[..12], &[(2048 % 16) as u8, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]);
        // a short block of a column of 1 block: base 7 at width 0 is 7 each
        let c = col(&[7], &[7], &[0], &[0], 100, None);
        let o = Blocks::new(Src::For(c), 100);
        let mut buf = vec![0u64; 1024];
        let b = crate::pod::bytes_mut(&mut buf);
        let r = o.view(0, 8, b);
        assert_eq!(r.len(), 800);
        assert!(r.chunks_exact(8).all(|x| x == 7i64.to_ne_bytes()));
    }
    // A32: expected values are search.rs's `bin_key` (1439) and `bin_step` (1483), checked against the old C by /data/tmp/qrs/A32/diff.c
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
    // A33: expected values are the C comments' measurements of q 4.1 (`(`s#1 1 2 2 3)?2` is 2, `?9` is 5, `?0.0` over `-0.0 0.0 1.0` is 0)
    #[test] fn sorted_find_and_member() {
        let h = bytes_of(&[1, 1, 2, 2, 3], 8);
        let mut out = [0i64; 4];
        find_sorted(crate::c::qlean_run_c, 8, false, true, &h, None, 5, &bytes_of(&[2, 9, 1, -4], 8), 4, &mut out);
        assert_eq!(out, [2, 5, 0, 5]);
        let mut bits = [0xffu8; 2];
        member_sorted(crate::c::qlean_run_c, 8, false, true, &h, None, 5, &bytes_of(&[1, 2, 9], 8), 3, &mut bits);
        assert_eq!(bits, [0b011, 0xff]);
        let fh: alloc::vec::Vec<u8> = [-0.0f64, 0.0, 1.0].iter().flat_map(|x| x.to_bits().to_le_bytes()).collect();
        let fk: alloc::vec::Vec<u8> = [0.0f64, -0.0, 2.0, f64::NAN].iter().flat_map(|x| x.to_bits().to_le_bytes()).collect();
        find_sorted(crate::c::qlean_run_c, 8, true, false, &fh, None, 3, &fk, 4, &mut out);
        assert_eq!(out, [0, 0, 3, 3]);
        find_sorted(crate::c::qlean_run_c, 8, false, true, &[], None, 0, &bytes_of(&[1], 8), 1, &mut out);
        assert_eq!(out[0], 0);
    }
    // the walk through the ids: ranks `[10, 20, 30]`, elements `ids = [0, 1, 1, 2]` read as `10 20 20 30`, at 2 bits per id
    #[test] fn bin_over_ids() {
        let (vals, ids) = (bytes_of(&[10, 20, 30], 8), [0b10_01_01_00u8]);
        let mut out = [0i64; 3];
        bin_ids(false, &vals, 4, 2, &ids, &bytes_of(&[20, 5, 40], 8), &mut out);
        assert_eq!(out, [2, -1, 3]);
        bin_ids(true, &vals, 4, 2, &ids, &bytes_of(&[20, 5, 40], 8), &mut out);
        assert_eq!(out, [1, 0, 4]);
    }
    // two groups over the haystack `1 2 3 | 10 20`, read through `order`; rows are named by `order`, `miss` = -7
    #[test] fn bin_rows_groups() {
        let hay = bytes_of(&[20, 10, 3, 2, 1], 8);
        let order: alloc::vec::Vec<u8> = [4i64, 3, 2, 1, 0].iter().flat_map(|x| x.to_le_bytes()).collect();
        let mut out = [0i64; 5];
        bin_rows(crate::c::qlean_run_c, 8, false, true, false, &hay, None, &bytes_of(&[2, 0, 15, 99, 5], 8), &order, &[0, 3, 5], &[0, 0, 1, 2], -7, 5, &mut out);
        // key 2 in group 0 (1 2 3): the row of `2` is order[1] = 3; key 0 is below the group; key 15 in group 1 (10 20): row of 10 is order[3] = 1;
        // gid 2 names no group; no gid for the fifth
        assert_eq!(out, [3, -7, 1, -7, -7]);
        bin_rows(crate::c::qlean_run_c, 8, false, true, false, &bytes_of(&[1, 2, 3], 8), None, &bytes_of(&[2], 8), &[], &[0, 3], &[0], -7, 1, &mut out);
        assert_eq!(out[0], 1);
    }
    fn starts(f: impl FnOnce(&mut [i64]) -> usize, n: usize) -> alloc::vec::Vec<i64> { let mut o = vec![0i64; n + 1]; let g = f(&mut o); o.truncate(g); o }
    #[test] fn run_starts_all_shapes() {
        let d = bytes_of(&[5, 5, 6, 6, 6, 7, 5], 2);
        assert_eq!(starts(|o| run_starts(&Blocks::new(Src::Dense(&d), 7), 2, false, o), 7), [0, 2, 5, 6, 7]);
        // -0.0 and 0.0 are one value, and every NaN is one value
        let f: alloc::vec::Vec<u8> = [0.0f32, -0.0, f32::NAN, -f32::NAN, 1.0].iter().flat_map(|x| x.to_bits().to_le_bytes()).collect();
        assert_eq!(starts(|o| run_starts(&Blocks::new(Src::Dense(&f), 5), 4, true, o), 5), [0, 2, 4, 5]);
        assert_eq!(starts(|o| run_starts(&Blocks::new(Src::Dense(&[]), 0), 8, false, o), 0), [0]);
        // 1500 elements in blocks of 1024: a run across the block edge is one run
        let big: alloc::vec::Vec<u8> = (0..1500u32).flat_map(|i| u32::from(i >= 1023 && i < 1030).to_le_bytes()).collect();
        assert_eq!(starts(|o| run_starts(&Blocks::new(Src::Dense(&big), 1500), 4, false, o), 1500), [0, 1023, 1030, 1500]);
        // ids at 2 bits: 0 0 1 1 3 3 3 0
        assert_eq!(starts(|o| run_starts_ids(8, 2, &[0b0101_0000, 0b0011_1111], o), 8), [0, 2, 4, 7, 8]);
        let (b, off) = ([b'a', 0, b'a', 0, b'b', 0], [1usize, 2 << 1 | 1, 4 << 1 | 1, 6 << 1 | 1]);
        assert_eq!(starts(|o| run_starts_syms(&Syms { blob: &b, offs: &off }, o), 3), [0, 2, 3]);
        // bits LSB first: 0 0 1 1 1 0 over 6 bits, and a 70-bit run crossing a word edge
        assert_eq!(starts(|o| run_starts_bits(6, &[0b011100], o), 6), [0, 2, 5, 6]);
        assert_eq!(starts(|o| run_starts_bits(70, &[0xff; 9], o), 70), [0, 70]);
        assert_eq!(starts(|o| run_starts_bits(0, &[], o), 0), [0]);
    }
    fn dense(b: &[u8], w: usize) -> Blocks<'_> { Blocks::new(Src::Dense(b), b.len() / w) }
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
    // expected values: q (search.rs's comments): `1 1 2?1` is 0, `1 1 2?9` is 3; one NaN, one zero (search.rs)
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
    // an empty haystack builds nothing, and a dense payload shorter than its `n` is refused by name, never folded to an empty range
    #[test] fn table_of_an_empty_or_short_haystack() {
        let t = table::<u64>(&Blocks::new(Src::Dense(&[]), 0));
        assert_eq!(t.used, 0);
        let r = std::panic::catch_unwind(|| table::<u32>(&Blocks::new(Src::Dense(&[1, 0, 0, 0]), 3)));
        assert!(r.is_err());
        let r = std::panic::catch_unwind(|| table::<u8>(&Blocks::new(Src::Dense(&[]), 1)));
        assert!(r.is_err());
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
    // expected values: the C of e33ad4a (`search`): 5 needles against 3 keys (table over the haystack) and 2 against 5 (over the needles)
    #[test] fn search_find_and_member_on_both_table_sides() {
        let run = crate::c::qlean_run_c;
        for (h, x) in [(le::<2>(&[3, 9, 4]), le::<2>(&[9, 1, 3, 3, 4])), (le::<2>(&[3, 9, 4, 7, 7]), le::<2>(&[7, 5]))] {
            let (hh, xx) = (dense(&h, 2), dense(&x, 2));
            let mut f = vec![0u8; 8 * xx.n];
            search(run, Kind::U16, &hh, &xx, false, &mut f);
            let want: Vec<u8> = finds(Kind::U16, &h, &x).iter().flat_map(|v| v.to_le_bytes()).collect();
            assert_eq!(f, want);
            let mut m = vec![0xffu8; xx.n.div_ceil(8)];
            search(run, Kind::U16, &hh, &xx, true, &mut m);
            let bits = finds(Kind::U16, &h, &x).iter().enumerate().fold(0u8, |a, (i, &v)| a | ((v < hh.n as i64) as u8) << i);
            assert_eq!(m, [bits]);
        }
        search(run, Kind::U8, &dense(&[1], 1), &dense(&[], 1), true, &mut []);
        assert_eq!((ids_key_width(1, 8), ids_key_width(9, 3), ids_key_width(17, 1), ids_key_width(5, 33), ids_key_width(0, 0)), (1, 2, 4, 8, 1));
    }
    #[test] fn srange_is_signed_at_the_key_width() {
        assert_eq!(srange::<u8>(&dense(&[0xff, 0x7f, 1], 1)), (-1, 127));
        assert_eq!(srange::<u32>(&dense(&[], 4)), (i64::MAX, i64::MIN));
        assert_eq!(srange::<u128>(&dense(&le::<8>(&[1, 0, u64::MAX, 0]), 16)), (-1, 1));
        assert_eq!(srange::<u16>(&Blocks::new(Src::Ids(&[], 8), 0)), (0, 127));
    }
    // A31: expected values are search.rs's (4ebc95c) own, which `/data/tmp/qrs/A31/diff` compares on 41026 random cases;
    // the q facts are the ones QLean/Kernel/Search.lean measured
    #[test] fn bit_kernels() {
        let b = [0b101u8];
        assert_eq!((find_bit(&b, 3, 1), find_bit(&b, 3, 0), find_bit(&[], 0, 1), find_bit(&[0], 9, 1), find_bit(&[0xff], 70, 0)), (0, 1, 0, 9, 8));
        // a payload shorter than the count reads 0 past its end
        assert_eq!((find_bit(&[0xff], 12, 0), word_at(&[1, 2], 0), word_at(&[1, 2], 5), bit_at(&[1], 8)), (8, 0x201, 0, 0));
        let mut o = [0i64; 3];
        find_bit_vec(3, &b, &[0b010], 3, &mut o);
        assert_eq!(o, [1, 0, 1]);
        // `bin` of 000111b: key 0 is last-<= at 2 (right: first >= at 0), key 1 at 5 (right: 3)
        let h = [0b111000u8];
        assert_eq!((bin_bit(&h, 6, 0, false), bin_bit(&h, 6, 1, false), bin_bit(&h, 6, 0, true), bin_bit(&h, 6, 1, true)), (2, 5, 0, 3));
        bin_bits(6, &h, &[0b10], 2, false, &mut o[..2]);
        assert_eq!(o[..2], [2, 5]);
        let mut m = [0xffu8; 2];
        member_bits(10, &[0b11], 1, &[1], &mut m);
        assert_eq!(m, [0b11, 0]);
        member_bits(10, &[0b11], 3, &[0], &mut m);
        assert_eq!(m, [0xfc, 0b11]);
    }
    #[test] fn where_bits_all_shapes() {
        let w = |n: usize, b: &[u8]| { let mut o = vec![0i64; where_count(n, b)]; assert_eq!(where_bits(n, b, &mut o), o.len()); o };
        assert_eq!((w(3, &[0b101]), w(3, &[0]), w(0, &[])), (vec![0, 2], vec![], vec![]));
        // the tail is masked, a short payload reads 0, a clear group of eight words is skipped, a full one is not
        assert_eq!(w(4, &[0xff]), [0, 1, 2, 3]);
        assert_eq!(w(130, &[0xff; 3]), (0..24).collect::<Vec<i64>>());
        let mut big = vec![0u8; 8 * 17];
        big[8 * 12 + 1] = 0x80;
        assert_eq!(w(64 * 17, &big), [64 * 12 + 15]);
        assert_eq!(w(64 * 17, &vec![0xff; 8 * 17]).len(), 64 * 17);
        assert_eq!(spread(&mut [0; 3], 1, 2, 0b101), 3);
    }
    #[test] fn symbol_kernels() {
        // blob "ab\0\0b\0": symbols "ab", "", "b"; offsets are boxed (`2 * start + 1`)
        let blob = b"ab\0\0b\0";
        let offs = [1usize, 7, 9, 13];
        let s = Syms { blob, offs: &offs };
        assert_eq!((sym_scan(&s, 3, b"ab"), sym_scan(&s, 3, b""), sym_scan(&s, 3, b"b"), sym_scan(&s, 3, b"a"), sym_scan(&s, 0, b"")), (0, 1, 2, 3, 0));
        assert_eq!((find_sym_scalar(&s, b"b"), find_sym_scalar(&Syms { blob: &[], offs: &[] }, b"b")), (2, 0));
        let sc = Symscan::build(s.slices(3));
        assert_eq!((sc.find(b"ab"), sc.find(b""), sc.find(b"b"), sc.find(b"bb"), sc.find(b"z")), (0, 1, 2, 3, 3));
        let mut k = [0u64; 3];
        sym_pack(&s, 3, &mut k);
        assert_eq!(k, [0x6162_0000_0000_0000, 0, 0x6200_0000_0000_0000]);
        let mut tr = [0usize; 3];
        sym_translate(&s, 3, &s, 3, &mut tr);
        assert_eq!(tr, [0, 1, 2]);
        let mut o = [0u8; 24];
        sym_search(false, &s, &s, &mut o);
        assert_eq!(crate::pod::cast::<i64>(&o).unwrap(), [0, 1, 2]);
        let mut bits = [0u8; 1];
        sym_search(true, &Syms { blob: b"b\0z\0", offs: &[1, 5, 9] }, &s, &mut bits);
        assert_eq!(bits, [1]);
    }
    #[test] fn symbol_search_past_eight_symbols_and_a_declining_block() {
        // 20 haystack symbols hash; a needle of nine bytes declines the packed key and the byte path answers it
        let (mut blob, mut offs) = (Vec::new(), vec![1usize]);
        for i in 0..20 { blob.extend_from_slice(format!("s{i}\0").as_bytes()); offs.push(blob.len() * 2 + 1) }
        let h = Syms { blob: &blob, offs: &offs };
        let (nb, no) = (b"s7\0s19\0wwwwwwwww\0".to_vec(), [1usize, 7, 15, 35]);
        let n = Syms { blob: &nb, offs: &no };
        let mut o = [0u8; 24];
        sym_search(false, &n, &h, &mut o);
        assert_eq!(crate::pod::cast::<i64>(&o).unwrap(), [7, 19, 20]);
        let mut bits = [0u8; 1];
        sym_search(true, &n, &h, &mut bits);
        assert_eq!(bits, [0b011]);
    }
    fn pack(ids: &[u64], w: u32) -> Vec<u8> { let mut o = vec![0u8; ids::ids_bytes(ids.len(), w)]; ids::pack(&mut o, w, ids.len(), |i| ids[i]); o }
    // the index against a map from key to least position, at every id width, sizes either side of a capacity step
    #[test] fn index_build_find_extend_agree_with_a_map() {
        for w in [0u32, 1, 2, 4, 8, 16, 32, 64] {
            for n in [0usize, 1, 2, 10, 11, 12, 24, 25, 26, 100, 1000] {
                let top = if w == 0 { 1u64 } else if w >= 64 { u64::MAX } else { 1u64 << w };
                let keys: Vec<u64> = (0..n as u64).map(|i| (i / 3).wrapping_mul(0x9e37_79b9_7f4a_7c15) % top).collect();
                let kb = pack(&keys, w);
                let mut t = vec![0u64; ix_bytes(ix_distinct(&kb, w, n)) / 8];
                ix_init(&mut t);
                ix_build(&mut t, &kb, w, n);
                assert_eq!(t[t.len() - 1], n as u64);
                let least = |k: u64| keys.iter().position(|&x| x == k).unwrap_or(n);
                let mut out = vec![0i64; n + 2];
                let nd: Vec<u64> = keys.iter().copied().chain([top.wrapping_sub(1), 0]).collect();
                ix_find(&t, &pack(&nd, w), w, n, &mut out);
                for (i, &k) in nd.iter().enumerate() { assert_eq!(out[i] as usize, least(k), "w {w} n {n} key {k}") }
                // rows at or past `miss` are another value's: hidden
                ix_find(&t, &pack(&nd, w), w, n / 2, &mut out);
                for (i, &k) in nd.iter().enumerate() { assert_eq!(out[i] as usize, if least(k) < n / 2 { least(k) } else { n / 2 }) }
                // rehash below `base`, then extend by the rest
                let base = n / 2;
                let mut u = vec![0u64; ix_bytes(2 * n) / 8];
                ix_init(&mut u);
                ix_rehash(&mut u, &t, base, n);
                ix_extend(&mut u, &pack(&keys[base..], w), w, base, n - base);
                ix_find(&u, &pack(&nd, w), w, n, &mut out);
                for (i, &k) in nd.iter().enumerate() { assert_eq!(out[i] as usize, least(k)) }
            }
        }
    }
    // equal 64-bit keys of different symbols: the bytes decide, and a chain of them is probed past
    #[test] fn mask_by_ids_is_the_per_id_lookup() {
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        let mut nx = move || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
        let mask: Vec<u8> = (0..40).map(|_| nx() as u8).collect();
        for w in [0u32, 1, 2, 4, 8, 16, 32, 64] {
            for n in [0usize, 1, 7, 8, 9, 63, 64, 65, 200] {
                for nmask in [0usize, 1, 3, 17, 300] {
                    let lim = if w == 0 { 0 } else if w >= 16 { 400 } else { (1u64 << w) - 1 };
                    let v: Vec<u64> = (0..n).map(|_| nx() % (lim + 1)).collect();
                    let mut out = vec![0u8; n.div_ceil(8)];
                    mask_by_ids(&mask, nmask, n, w, &pack(&v, w), &mut out);
                    for (i, &u) in v.iter().enumerate() {
                        let want = (u as usize) < nmask && mask[u as usize >> 3] >> (u & 7) & 1 != 0;
                        assert_eq!(out[i >> 3] >> (i & 7) & 1 != 0, want, "w {w} n {n} nmask {nmask} id {i}");
                    }
                    assert!(n % 8 == 0 || out[n / 8] >> (n % 8) == 0, "bits past n are zero: w {w} n {n}");
                }
            }
        }
    }
    #[test] fn index_put_probes_past_a_key_collision() {
        let mut t = vec![0u64; ix_bytes(4) / 8];
        ix_init(&mut t);
        let (s, mask) = ix_geom(t.len() / 2);
        let sl = ix_slots_mut(&mut t);
        let syms = [b"a".as_slice(), b"b", b"a", b"c"];
        for (i, x) in syms.iter().enumerate() { ix_put(sl, 7, i, s, mask, |r| syms[r] == *x) }
        let at = |x: &[u8]| ix_get(sl, 7, s, mask, 4, |r| syms[r] == x);
        assert_eq!((at(b"a"), at(b"b"), at(b"c"), at(b"z")), (0, 1, 3, 4));
    }
    #[test] fn remap_renames_with_a_stray_id_reading_entry_zero() {
        for (w, wout) in [(0u32, 0u32), (1, 1), (2, 4), (4, 2), (8, 8), (4, 16), (16, 1), (64, 64), (0, 8)] {
            let (tw, to) = (if w == 0 { 1 } else { 1u64 << w.min(20) }, if wout == 0 { 1 } else { 1u64 << wout.min(20) });
            for (n, nm) in [(0usize, 3usize), (7, 3), (8, 5), (1001, 17), (1000, 300)] {
                let nm = nm.min(to as usize);
                let ids: Vec<u64> = (0..n as u64).map(|i| i.wrapping_mul(2654435761) % tw).collect();
                let map: Vec<u64> = (0..nm as u64).map(|u| (u * 7 + 1) % to).collect();
                let mut out = vec![0u8; ids::ids_bytes(n, wout)];
                remap_ids(crate::c::qlean_run_c, &pack(&ids, w), n, w, &pack(&map, wout), wout, &mut out);
                let want: Vec<u64> = if wout == 0 { vec![] } else { ids.iter().map(|&i| map.get(i as usize).copied().unwrap_or(0)).collect() };
                assert_eq!(out, pack(&want, wout), "w {w} wout {wout} n {n} nm {nm}");
            }
        }
    }
    #[test] fn symbol_matches_and_the_wide_halving() {
        // boxed starts (`2 * off + 1`): a = `ab`,`c`; b the same symbols in a longer blob; d = `c`,`ab` as a dictionary
        let (a, b, d) = (Syms { blob: b"ab\0c\0", offs: &[1, 7, 11] }, Syms { blob: b"zab\0c\0", offs: &[3, 9, 13] }, Syms { blob: b"c\0ab\0", offs: &[1, 5, 11] });
        assert!(match_syms(&a, &b) && match_syms(&a, &a) && !match_syms(&a, &d) && !match_syms(&a, &Syms { blob: &[], offs: &[] }));
        // ids 0, 1 of a read as d's ids 1, 0: translated, equal; with n different, not
        assert!(match_ids(2, 2, &a, &[0b10], &d, &[0b01]) && !match_ids(2, 3, &a, &[0b10], &d, &[0b01]) && !match_ids(2, 2, &a, &[0b10], &d, &[0b10]));
        assert!(match_syms_ids(&a, 2, &a, &[0b10]) && !match_syms_ids(&a, 2, &d, &[0b10]) && !match_syms_ids(&a, 3, &a, &[0b10]));
        let hay = [[1u8, 0], [1, 5], [1, 5], [2, 0]].concat();
        let (mut o, mut r) = ([0i64; 3], [0i64; 3]);
        bin_wide(2, false, &hay, &[1, 5, 0, 0, 3, 0], &mut o);
        bin_wide(2, true, &hay, &[1, 5, 0, 0, 3, 0], &mut r);
        assert_eq!((o, r), ([2, -1, 3], [1, 0, 4]));
    }
}
/// `qlean_coc_rows_eq`'s body: every row of `c` equal to `v`, ascending: `coc_find`'s walk carried past the first hit. A
/// block's hits are written branch-free into a stack buffer and appended whole, so a hit costs no branch.
pub fn coc_rows_eq(c: &Coc, v: i64) -> Vec<i64> {
    let (mut rows, mut t) = (Vec::with_capacity(c.meta.blk()), crate::pod::Scr::<i64>::new(c.meta.blk()));
    eq_blocks::<()>(c, v, |b, at, cnt, buf| {
        if let Some(p) = c.bit_blk(b) { crate::bitblk::rows_eq(p, cnt, at, v, &mut rows); return None }
        c.decode_blk(b, cnt, buf);
        let mut k = 0;
        for (i, &x) in buf[..cnt].iter().enumerate() { t[k] = (at + i) as i64; k += (x == v) as usize }
        rows.extend_from_slice(&t[..k]);
        None
    });
    rows
}
/// search.rs `bin_bit`: binary search of a sorted bitmap for `k`, with the `-1` of `bin` already applied.
pub fn bin_bit(b: &[u8], n: usize, k: i32, right: bool) -> i64 {
    let (mut lo, mut hi) = (0, n);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let v = bit_at(b, mid) as i32;
        if if right { v < k } else { v <= k } { lo = mid + 1 } else { hi = mid }
    }
    if right { lo as i64 } else { lo as i64 - 1 }
}
/// search.rs `qlean_search_bin_bits` past the unboxing: two keys exist, so two halvings and a select.
pub fn bin_bits(n: usize, hay: &[u8], ndl: &[u8], m: usize, right: bool, out: &mut [i64]) {
    let at = [bin_bit(hay, n, 0, right), bin_bit(hay, n, 1, right)];
    for (j, o) in out[..m].iter_mut().enumerate() { *o = at[bit_at(ndl, j) as usize] }
}
/// search.rs `qlean_search_bin_ids` past the unboxing: `binBytes 8 false true right` of the `n` ranks `vals[ids[i]]`
/// (`ids` at `w` bits) for each 8-byte key of `keys`, into `out` (one per key). The ids are the walk's index payload.
pub fn bin_ids(right: bool, vals: &[u8], n: usize, w: u32, ids: &[u8], keys: &[u8], out: &mut [i64]) {
    struct J<'a> { right: bool, vals: &'a [u8], n: usize, ids: &'a [u8], keys: &'a [u8], out: &'a mut [i64] }
    impl IdsFn<()> for J<'_> {
        fn go<const W: u32>(self) {
            let wk = Walk { w: 8, f: false, s: true, right: self.right };
            let h = Col { d: self.vals, c: None, uw: 0 };
            for (j, x) in self.out.iter_mut().enumerate() {
                let lo = wk.step(&h, |i| ids::id_at(self.ids, W, i), bin_key(8, false, true, bin_at(self.keys, 8, j)), 0, self.n as i64);
                *x = if self.right { lo } else { lo - 1 }
            }
        }
    }
    with_ids_width(w, J { right, vals, n, ids, keys, out })
}
/// search.rs `bin_rows` past the unboxing: for each of the `m` dense keys, the row `binRows` names inside group
/// `g = gids[j]`: the walk over `bounds[g] .. bounds[g + 1]` reading the haystack (dense `hay` or `enc`) through `order`
/// (64-bit rows; empty: each position is its own row), then the row at the partition point's predecessor. `miss` where `gids`
/// has no entry `j`, `g` names no group, or the group holds nothing at or before the key. Threaded.
pub fn bin_rows(run: Runner, w: usize, is_float: bool, is_signed: bool, right: bool, hay: &[u8], enc: Option<&Coc>, keys: &[u8],
                order: &[u8], bounds: &[i64], gids: &[i64], miss: i64, m: usize, out: &mut [i64]) {
    let (wk, h) = (Walk { w, f: is_float, s: is_signed, right }, sorted_col(w, hay, enc));
    let ng = bounds.len().saturating_sub(1);
    let row = |i: usize| if order.is_empty() { i } else { ids::id_at(order, 64, i) };
    crate::c::run_map(run, crate::pod::bytes_mut(&mut out[..m]), m, 8, crate::QLEAN_COST_MATH, 8, &|lo, hi, o: &mut [u8]| {
        for (j, x) in (lo..hi).zip(i64s(o)) {
            let g = gids.get(j).map_or(u64::MAX, |&g| g as u64);
            if g >= ng as u64 { *x = miss; continue }
            let (b, g) = (bounds[g as usize], g as usize);
            let at = wk.step(&h, row, bin_key(w, is_float, is_signed, bin_at(keys, w, j)), b, bounds[g + 1]);
            *x = if at == b { miss } else { row(at as usize - 1) as i64 }
        }
    });
}
/// `qlean_search_bin_wide`: `bin`'s halving with an element compared as `w` bytes in address order (`memcmp`), for each of the
/// `out.len()` keys; `p - 1` when `!right`, `p` when `right`. Sixteen bytes have no `u64` key, so this walk is not `Walk::step`.
pub fn bin_wide(w: usize, right: bool, hay: &[u8], keys: &[u8], out: &mut [i64]) {
    let n = hay.len() / w;
    // the halving at a constant `right`, over elements of an ordered type `T` read by `at`
    fn walk<const R: bool, T: Ord>(n: usize, out: &mut [i64], keys: impl Iterator<Item = T>, at: impl Fn(usize) -> T) {
        for (k, x) in keys.zip(out) {
            let (mut lo, mut hi) = (0, n);
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                let c = at(mid).cmp(&k);
                if if R { c.is_lt() } else { c.is_le() } { lo = mid + 1 } else { hi = mid }
            }
            *x = if R { lo as i64 } else { lo as i64 - 1 }
        }
    }
    // `memcmp` order on 16 bytes is the order of the big-endian `u128`: one compare, no call
    let g = |p: &[u8], i: usize| u128::from_be_bytes(p[i * 16..(i + 1) * 16].try_into().unwrap());
    match (w, right) {
        (16, false) => walk::<false, _>(n, out, keys.chunks_exact(16).map(|k| g(k, 0)), |i| g(hay, i)),
        (16, true) => walk::<true, _>(n, out, keys.chunks_exact(16).map(|k| g(k, 0)), |i| g(hay, i)),
        (_, false) => walk::<false, _>(n, out, keys.chunks_exact(w), |i| &hay[i * w..(i + 1) * w]),
        (_, true) => walk::<true, _>(n, out, keys.chunks_exact(w), |i| &hay[i * w..(i + 1) * w]),
    }
}
/// search.rs `COC_EQ_BLOCKS`: each block of `c` that may hold `v`, in order, handed to `f(b, at, cnt, buf)` (block, first row, row count, a
/// scratch to decode into; a bit block is read in place), and a `Some` ends the walk. `?` at an atom asks about one element, so a block whose
/// `[base, maxv]` cannot hold the needle is skipped from its 16 bytes of metadata instead of its 8 KB of elements.
pub fn eq_blocks<R>(c: &Coc, v: i64, mut f: impl FnMut(usize, usize, usize, &mut [i64]) -> Option<R>) -> Option<R> {
    let (s, mut buf) = (Blocks::from(*c), crate::pod::Scr::<i64>::new(c.meta.blk()));
    let nb = s.nblk();
    for b0 in (0..nb).step_by(64) {
        let mut m = coc_may_hold64(c, b0, (nb - b0).min(64), v);
        while m != 0 {
            let b = b0 + m.trailing_zeros() as usize;
            m &= m - 1;
            let (at, cnt) = s.span(b);
            if let Some(r) = f(b, at, cnt, &mut buf) { return Some(r) }
        }
    }
    None
}
/// search.rs `qlean_search_find_sorted`, `qlean_coc_find_sorted` past the unboxing: each of the `m` dense keys'
/// first index in the sorted haystack (dense `hay`, or `enc`) of `n`, `n` where absent, into `out`; threaded.
pub fn find_sorted(run: Runner, w: usize, is_float: bool, is_signed: bool, hay: &[u8], enc: Option<&Coc>, n: i64, keys: &[u8], m: usize, out: &mut [i64]) {
    let (wk, h) = (Walk { w, f: is_float, s: is_signed, right: true }, sorted_col(w, hay, enc));
    crate::c::run_map(run, crate::pod::bytes_mut(&mut out[..m]), m, 8, crate::QLEAN_COST_MATH, 8, &|lo, hi, o: &mut [u8]| {
        for (j, x) in (lo..hi).zip(i64s(o)) { *x = sorted_probe(wk, &h, keys, n, j) }
    });
}
/// `qlean_index_hash_build`'s fill: slots hashing the `n` keys `p` holds at `w` bits to the least position of each.
pub fn ix_build(t: &mut [u64], p: &[u8], w: u32, n: usize) { ids::by_width!(w, build_w(t, p, n)); ix_set_rows(t, n) }
/// search.rs `ix_alloc`'s size: the capacity is a power of two, at least 16 and 1.5 times the distinct keys.
pub fn ix_bytes(distinct: usize) -> usize {
    let mut cap = 16usize;
    while cap < distinct + distinct / 2 { cap <<= 1 }
    cap * 16 + 8
}
/// The runs of equal neighbours of `n` ids at `w` bits: what the table sizes itself by (distinct keys at most).
pub fn ix_distinct(p: &[u8], w: u32, n: usize) -> usize { ids::by_width!(w, distinct_w(p, n)) }
/// `qlean_index_hash_extend`'s fill: the `m` keys `p` holds at `w` bits added as rows `base` on.
pub fn ix_extend(t: &mut [u64], p: &[u8], w: u32, base: usize, m: usize) { ids::by_width!(w, extend_w(t, p, base, m)) }
/// `qlean_index_hash_find`: each of the `out.len()` needles `p` holds at `w` bits, its position in the slots, `miss` where
/// they hold none.
pub fn ix_find(t: &[u64], p: &[u8], w: u32, miss: usize, out: &mut [i64]) { ids::by_width!(w, find_w(t, p, miss, out)) }
/// The shift and mask of a table of `cap` slots (an empty table reads 0 and 0).
pub fn ix_geom(cap: usize) -> (u32, u64) { if cap == 0 { (0, 0) } else { (cap.trailing_zeros(), cap as u64 - 1) } }
/// The least position of `k` among the first `miss` rows, or `miss`; a position at or past `miss` is a row appended to a
/// later value, not this one's. `same` decides a key match (symbols compare their bytes).
#[inline(always)]
pub fn ix_get(sl: &[[u64; 2]], k: u64, s: u32, mask: u64, miss: usize, same: impl Fn(usize) -> bool) -> usize {
    let mut h = ix_slot(k, s, mask);
    loop {
        let e = sl[h];
        if e[1] == IX_EMPTY { return miss }
        if e[0] == k && (e[1] as usize) < miss && same(e[1] as usize) { return e[1] as usize }
        h = (h + 1) & mask as usize;
    }
}
/// search.rs `ix_alloc`'s fill: every slot empty, no rows hashed.
pub fn ix_init(t: &mut [u64]) { let n = t.len() & !1; t[..n].fill(IX_EMPTY); ix_set_rows(t, 0) }
/// Row `row` under key `k` at the first slot from `ix_slot` that is empty (written) or holds `k` with `same` of its
/// position (kept: an earlier position holds it).
#[inline(always)]
pub fn ix_put(sl: &mut [[u64; 2]], k: u64, row: usize, s: u32, mask: u64, same: impl Fn(usize) -> bool) {
    let mut h = ix_slot(k, s, mask);
    loop {
        let e = &mut sl[h];
        if e[1] == IX_EMPTY { *e = [k, row as u64]; return }
        if e[0] == k && same(e[1] as usize) { return }
        h = (h + 1) & mask as usize;
    }
}
/// search.rs `ix_room`'s copy: `src`'s slots below `base` rehashed into the fresh `dst`, which then hashes `keys` rows.
/// Where another value has claimed past `base`, its rows are not this value's, and open addressing cannot delete them
/// from a copy.
pub fn ix_rehash(dst: &mut [u64], src: &[u64], base: usize, keys: usize) {
    let (s, mask) = ix_geom(dst.len() / 2);
    let ds = ix_slots_mut(dst);
    for e in ix_slots(src) { if e[1] != IX_EMPTY && e[1] < base as u64 { ix_put(ds, e[0], e[1] as usize, s, mask, |_| false) } }
    ix_set_rows(dst, keys)
}
pub fn ix_slots_mut(t: &mut [u64]) -> &mut [[u64; 2]] { let n = t.len() & !1; t[..n].as_chunks_mut::<2>().0 }
/// `qlean_search_mask_by_ids`' body: bit `i` of `out` (`n.div_ceil(8)` bytes) is set exactly when id `i` of `ids` (`w` bits,
/// `n` of them held) is inside `nmask` and `mask` has that bit.
pub fn mask_by_ids(mask: &[u8], nmask: usize, n: usize, w: u32, ids: &[u8], out: &mut [u8]) {
    match w {
        1 | 2 | 4 | 3 | 5 | 6 | 7 => mask_packed(mask, nmask, n, w as usize, ids, out),
        _ => ids::by_width!(w, mask_wide(mask, nmask, n, ids, out)),
    }
}
/// `qlean_search_match_ids`: the `n` ids `ia` (read at the width of dictionary `da`) name the symbols the `m` ids `ib` name
/// in `db`, position by position. Two columns do not agree on ids, so `da` is translated into `db` first (an entry `db` lacks
/// translates past its last id, which no id of `db` is); one dictionary object needs no translation.
pub fn match_ids(n: usize, m: usize, da: &Syms, ia: &[u8], db: &Syms, ib: &[u8]) -> bool {
    if n != m { return false }
    let (na, nb) = (da.count(), db.count());
    let (wa, wb) = (ids::id_width(na), ids::id_width(nb));
    let n = n.min(ids::ids_avail(ia.len(), wa)).min(ids::ids_avail(ib.len(), wb));
    let same = same_syms(da, db);
    // one column against itself: translating a dictionary into itself to compare a million ids with themselves is the cost
    if same && core::ptr::eq(ia.as_ptr(), ib.as_ptr()) { return true }
    if same { return (0..n).all(|i| ids::id_at(ia, wa, i) == ids::id_at(ib, wb, i)) }
    let mut tr = vec![0usize; na];
    sym_translate(da, na, db, nb, &mut tr);
    (0..n).all(|i| { let (ua, ub) = (ids::id_at(ia, wa, i), ids::id_at(ib, wb, i)); ua < na && ub < nb && tr[ua] == ub })
}
/// `qlean_match_syms`: `Column.symKey` equal at every index, symbol by symbol (a gather leaves equal symbols in blobs that
/// differ), `false` when the starts arrays differ in length.
pub fn match_syms(a: &Syms, b: &Syms) -> bool {
    a.offs.len() == b.offs.len() && (same_syms(a, b) || (0..a.count()).all(|i| crate::sym::sym_eq(a.at(i), b.at(i))))
}
/// `qlean_search_match_syms_ids`: element `i` of `b` equals entry `ids[i]` of dictionary `d`, an id past the dictionary (or the
/// ids) reading the empty symbol. `false` when `b` does not hold `n` symbols.
pub fn match_syms_ids(b: &Syms, n: usize, d: &Syms, ids: &[u8]) -> bool {
    if b.count() != n { return false }
    let nd = d.count();
    let w = ids::id_width(nd);
    let have = ids::ids_avail(ids.len(), w);
    (0..n).all(|i| {
        let e = if i < have { ids::id_at(ids, w, i) } else { 0 };
        crate::sym::sym_eq(b.at(i), if e < nd { d.at(e) } else { &[] })
    })
}
/// `qlean_match_bytes`' body: `QAtom.identical` element by element of two dense payloads; at the float widths the two zeros
/// are one value and every other pattern matches only itself.
pub fn match_bytes(w: usize, is_float: bool, a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() { return false }
    // one payload against itself is `x~x`; reading it twice is the whole cost
    if core::ptr::eq(a, b) { return true }
    if !is_float { return a == b }
    fn same<const W: usize>(a: &[u8], b: &[u8], mask: u64) -> bool {
        a.chunks_exact(W).zip(b.chunks_exact(W)).all(|(x, y)| {
            let (x, y) = (word::<W>(x), word::<W>(y));
            x == y || (x | y) & mask == 0
        })
    }
    fn word<const W: usize>(c: &[u8]) -> u64 { let mut v = [0u8; 8]; v[..W].copy_from_slice(c); u64::from_le_bytes(v) }
    if w == 8 { same::<8>(a, b, 0x7fff_ffff_ffff_ffff) } else { same::<4>(a, b, 0x7fff_ffff) }
}
/// `qlean_coc_match`'s body: two operands of `w`-byte elements equal, a block of each at a time, stopping at the first
/// that differs.
pub fn coc_match(a: &Blocks, b: &Blocks, w: usize) -> bool {
    if a.n != b.n { return false }
    let (la, lb) = (a.lg(), b.lg());
    if la == lb {
        let (mut xa, mut xb) = (crate::pod::Scr::<u8, 8192>::new(8 << la), crate::pod::Scr::<u8, 8192>::new(8 << la));
        return (0..a.nblk()).all(|k| a.view(k, w, &mut xa) == b.view(k, w, &mut xb));
    }
    // blocks of two sizes: each side restores the span the larger block covers, from as many of its own blocks as that takes
    let g = if la > lb { a } else { b };
    let (mut xa, mut xb) = (crate::pod::Scr::<u8, 8192>::new(w << g.lg()), crate::pod::Scr::<u8, 8192>::new(w << g.lg()));
    g.walk().all(|(_, lo, cnt)| a.range(lo, cnt, w, &mut xa) == b.range(lo, cnt, w, &mut xb))
}
/// search.rs `qlean_search_member_sorted`, `qlean_coc_member_sorted` past the unboxing: bit `j` of `out` (LSB
/// first, `m.div_ceil(8)` bytes, the tail bits left zero) is set when key `j` is in the haystack. Threaded by output
/// byte, so no two slices touch one byte.
pub fn member_sorted(run: Runner, w: usize, is_float: bool, is_signed: bool, hay: &[u8], enc: Option<&Coc>, n: i64, keys: &[u8], m: usize, out: &mut [u8]) {
    let (wk, h) = (Walk { w, f: is_float, s: is_signed, right: true }, sorted_col(w, hay, enc));
    let bytes = m.div_ceil(8);
    out[..bytes].fill(0);
    crate::c::run_map(run, &mut out[..bytes], bytes, 1, crate::QLEAN_COST_MATH, w * 8, &|lo, hi, o: &mut [u8]| {
        for j in lo * 8..(hi * 8).min(m) { if sorted_probe(wk, &h, keys, n, j) < n { o[(j >> 3) - lo] |= 1 << (j & 7) } }
    });
}
/// search.rs `qlean_search_remap_ids`' body: `map` (`wout`-bit entries) read at each of the `n` ids of `ids` (`w` bits),
/// the entry past the map answering a stray id, into `out` at `wout` bits. It is `ids::map`, `idGroups`' pass, over
/// the map read out once into a dictionary-sized table: `d` entries where the column is millions, which keeps the
/// map's own width out of the loop.
pub fn remap_ids(run: Runner, ids: &[u8], n: usize, w: u32, map: &[u8], wout: u32, out: &mut [u8]) {
    let nm = if wout == 0 { 0 } else { map.len() * 8 / wout as usize };
    let mut tab = vec![0usize; nm + 1];
    fn read<const W: u32>(map: &[u8], nm: usize, tab: &mut [usize]) { ids::each::<W>(map, nm, |u, v| tab[u] = v) }
    ids::by_width!(wout, read(map, nm, &mut tab));
    ids::map(run, &ids[..ids::ids_bytes(n, w)], n, w, nm, &tab, wout, out)
}
/// search.rs `qlean_search_run_starts_syms`: the run starts of the symbols, then their count. `out` is `count + 1` long.
pub fn run_starts_syms(s: &Syms, out: &mut [i64]) -> usize {
    let (n, mut g, mut prev) = (s.count(), 0, &[][..]);
    // one `at` per element, the previous symbol carried, as search.rs's loop carries `prev`
    for i in 0..n { let x = s.at(i); if i == 0 || !crate::sym::sym_eq(x, prev) { out[g] = i as i64; g += 1 } prev = x }
    out[g] = n as i64;
    g + 1
}
/// search.rs `sym_pack`: the first `n` symbols as 8-byte keys, big-endian and zero-padded, so `=` on a key is symbol
/// equality (a symbol holds no NUL). Every symbol must fit (`Syms::packs`).
pub fn sym_pack(s: &Syms, n: usize, k: &mut [u64]) {
    for (k, v) in k[..n].iter_mut().zip(s.keys(n)) { *k = v }
}
/// search.rs `symscan`: a short symbol haystack indexed by first byte. `first[b]` is the lowest index whose first
/// byte is `b`, plus one; `empty` the index of the empty symbol, a legal element with no first byte.
pub struct Symscan<'a> { pub hay: Vec<&'a [u8]>, pub empty: usize, pub first: [u8; 256] }
impl<'a> Symscan<'a> {
    /// search.rs `symscan_build`: backwards, so the lowest index wins
    pub fn build(hay: Vec<&'a [u8]>) -> Self {
        let (mut empty, mut first) = (hay.len(), [0u8; 256]);
        for (i, h) in hay.iter().enumerate().rev() { match h.first() { None => empty = i, Some(&b) => first[b as usize] = (i + 1) as u8 } }
        Symscan { hay, empty, first }
    }
    /// search.rs `symscan_find`: the first index holding `k`, the count when none does
    pub fn find(&self, k: &[u8]) -> usize {
        let Some(&b) = k.first() else { return self.empty };
        let c = self.first[b as usize] as usize;
        if c == 0 { return self.hay.len() }
        (c - 1..self.hay.len()).find(|&i| crate::sym::sym_eq(self.hay[i], k)).unwrap_or(self.hay.len())
    }
}
/// search.rs `sym_search`: `needles ? hay` (`bits` false: `out` is `8 * m` bytes of `Int64`s) or `needles in hay` (`bits`
/// true: `out` is `m.div_ceil(8)` bytes, zeroed) for symbol columns with no kept hash. A haystack whose symbols fit the
/// 8-byte key goes through the `u64` probe table (or a scan of up to `SYM_SCAN_MAX` keys), the needles a block at a time;
/// a block that does not fit abandons that for the byte path, a `Symscan` or a hash table over the bytes.
pub fn sym_search(bits: bool, nd: &Syms, hb: &Syms, out: &mut [u8]) {
    let (n, m) = (hb.count(), nd.count());
    if m == 0 { return }
    // an empty haystack answers `n = 0` for every needle, which sets no bit
    if n > 0 && hb.packs(n) {
        let hk: Vec<u64> = hb.keys(n).collect();
        let h = Blocks::new(Src::Dense(crate::pod::bytes(&hk)), n);
        let p = (n > SYM_SCAN_MAX).then(|| Probe::new(Kind::U64, &h));
        let mut buf = [0u64; SYM_KEY_BLOCK];
        let mut at = 0;
        while at < m {
            let cnt = (m - at).min(SYM_KEY_BLOCK);
            let blk = Syms { blob: nd.blob, offs: &nd.offs[at..=at + cnt] };
            if !blk.packs(cnt) { break }
            sym_pack(&blk, cnt, &mut buf);
            let x = Blocks::new(Src::Dense(crate::pod::bytes(&buf[..cnt])), cnt);
            match &p {
                Some(p) if bits => p.member(&x, 0, cnt, &mut out[at / 8..]),
                Some(p) => p.find(&x, 0, cnt, &mut i64s(out)[at..at + cnt]),
                None => {
                    let mut r = vec![0i64; cnt];
                    scan::<u64>(&h, &x, 0, cnt, &mut r);
                    for (j, &r) in r.iter().enumerate() { sym_put(bits, out, n, at + j, r as usize) }
                }
            }
            at += cnt;
        }
        if at >= m { return }
        // the bits a declining block left behind, before the byte path
        if bits { out.fill(0) }
    }
    if n <= SYM_SCAN_MAX {
        let s = Symscan::build(hb.slices(n));
        for j in 0..m { sym_put(bits, out, n, j, s.find(nd.at(j))) }
        return;
    }
    let cap = crate::group::cap_for(n);
    let mut tab = vec![0usize; cap];
    sym_build(hb, n, &mut tab, cap as u64 - 1);
    for j in 0..m { sym_put(bits, out, n, j, sym_probe(hb, &tab, cap as u64 - 1, n, nd.at(j))) }
}
/// search.rs `qlean_search_match_ids`'s translation: for each of the `na` entries of `a`, its index in `b` (`nb` when
/// `b` does not hold it), through one hash table over `b`.
pub fn sym_translate(a: &Syms, na: usize, b: &Syms, nb: usize, tr: &mut [usize]) {
    let cap = crate::group::cap_for(nb.max(1));
    let mut tab = vec![0usize; cap];
    sym_build(b, nb, &mut tab, cap as u64 - 1);
    for (i, t) in tr[..na].iter_mut().enumerate() { *t = sym_probe(b, &tab, cap as u64 - 1, nb, a.at(i)) }
}
pub fn build_w<const W: u32>(t: &mut [u64], p: &[u8], n: usize) {
    let (s, mask) = ix_geom(t.len() / 2);
    let sl = ix_slots_mut(t);
    ids::each::<W>(p, n, |i, k| ix_put(sl, k as u64, i, s, mask, |_| true));
}
// ---- K17: search.rs `coc_may_hold64`, `remap_ids_run`, the index's slots (`ix_*`) ----
/// search.rs `coc_may_hold64`: the blocks `[b0, b0 + k)`, `k <= 64`, that may hold `v` as a bit mask: those whose
/// `[base, maxv]` holds it, and a patched block one of whose exceptions is it. The OR reduction first is what vectorises
/// where the shift by `j` does not, and most chunks hold no candidate.
pub fn coc_may_hold64(c: &Coc, b0: usize, k: usize, v: i64) -> u64 {
    let (base, maxv) = (&c.meta.base[b0..b0 + k], &c.meta.maxv[b0..b0 + k]);
    let any = base.iter().zip(maxv).fold(false, |a, (&b, &x)| a | ((b <= v) & (v <= x)));
    let exc = c.exc.filter(|e| !e.pos.is_empty()).is_some_and(|e| e.off[b0 + k] != e.off[b0]);
    if !any && !exc { return 0 }
    let mut m = base.iter().zip(maxv).enumerate().fold(0u64, |m, (j, (&b, &x))| m | (((b <= v) & (v <= x)) as u64) << j);
    if exc { for j in 0..k { if m >> j & 1 == 0 && coc_exc_within(c, b0 + j, v, v) { m |= 1 << j } } }
    m
}
pub fn distinct_w<const W: u32>(p: &[u8], n: usize) -> usize {
    let (mut d, mut prev) = (n.min(1), 0);
    ids::each::<W>(p, n, |i, k| { d += (i > 0 && k != prev) as usize; prev = k });
    d
}
pub fn extend_w<const W: u32>(t: &mut [u64], p: &[u8], base: usize, m: usize) {
    let (s, mask) = ix_geom(t.len() / 2);
    let sl = ix_slots_mut(t);
    ids::each::<W>(p, m, |i, k| ix_put(sl, k as u64, base + i, s, mask, |_| true));
}
pub fn find_w<const W: u32>(t: &[u64], p: &[u8], miss: usize, out: &mut [i64]) {
    // a few needles ahead, so a run of misses into a table larger than the cache overlaps rather than queues
    const AHEAD: usize = 8;
    let (sl, m) = (ix_slots(t), out.len());
    let (s, mask) = ix_geom(sl.len());
    ids::unpack::<W, i64>(p, out, |i, e, k| {
        if !sl.is_empty() && i + AHEAD < m { crate::simd::prefetch(&sl[ix_slot(ids::id_at(p, W, i + AHEAD) as u64, s, mask)]) }
        *e = (if sl.is_empty() { miss } else { ix_get(sl, k as u64, s, mask, miss, |_| true) }) as i64;
    });
}
pub trait IdsFn<R> { fn go<const W: u32>(self) -> R; }
/// The slots an index keeps: open addressing over 16-byte slots, a key and the least position holding it, the position
/// `IX_EMPTY` in an empty slot; then one word, how many rows the slots hash. A table is `2 * cap + 1` words.
pub const IX_EMPTY: u64 = u64::MAX;
pub fn ix_set_rows(t: &mut [u64], rows: usize) { let n = t.len() & !1; t[n] = rows as u64 }
/// search.rs `ix_slot`: a key below the capacity is its own slot, so needles near each other read slots near each other;
/// the bits above are mixed (murmur3's fmix64, 0 at 0) before they reach the slot, since xor-folding them kept their
/// structure.
#[inline(always)]
pub fn ix_slot(k: u64, s: u32, mask: u64) -> usize {
    let mut h = k >> s;
    h ^= h >> 33; h = h.wrapping_mul(0xff51afd7ed558ccd); h ^= h >> 33; h = h.wrapping_mul(0xc4ceb9fe1a85ec53); h ^= h >> 33;
    ((k ^ h) & mask) as usize
}
pub fn ix_slots(t: &[u64]) -> &[[u64; 2]] { t[..t.len() & !1].as_chunks::<2>().0 }
/// `maskByIds` at an id width below a byte: a whole source byte answered at a time out of a 256-entry table, `8 / w`
/// elements an instruction where a four-byte payload took one element a load. The predicate is already decided per
/// dictionary entry, so the table folds the unpack and the lookup together: `w` source bytes make one answer byte, `per`
/// bits from each. `inline(always)` so `w` is a constant at the widths ids use.
#[inline(always)]
pub fn mask_packed(mask: &[u8], nmask: usize, n: usize, w: usize, ids: &[u8], out: &mut [u8]) {
    let (per, msk, src) = (8 / w, (1usize << w) - 1, &ids[..ids::ids_bytes(n, w as u32)]);
    let mut lut = [0u8; 256];
    for (b, l) in lut.iter_mut().enumerate() { *l = (0..per).fold(0u32, |v, j| v | (passes(mask, nmask, (b >> (j * w)) & msk) as u32) << j) as u8 }
    let at = |s: u8, t: usize| (lut[s as usize] as u32) << (t * per);
    let full = src.len() / w; // the answer bytes whose `w` source bytes are all there
    for (o, c) in out.iter_mut().zip(src.chunks_exact(w)) { *o = c.iter().enumerate().fold(0u32, |v, (t, &s)| v | at(s, t)) as u8 }
    for (k, o) in out.iter_mut().enumerate().skip(full) { *o = (0..w).fold(0u32, |v, t| v | src.get(k * w + t).map_or(0, |&s| at(s, t))) as u8 }
    // the fields past `n` are stored as zero and a zero id can pass the mask, so the bits the count does not reach are
    // cleared here rather than left to the table
    if n % 8 != 0 { if let Some(l) = out.last_mut() { *l &= ((1u32 << (n % 8)) - 1) as u8 } }
}
/// `maskByIds` at a whole-byte width (or none): the answer byte is built in a register and stored once, for the reason
/// `ids::pack` gives: an `|=` per element is eight dependent read-modify-writes to one byte.
pub fn mask_wide<const W: u32>(mask: &[u8], nmask: usize, n: usize, ids: &[u8], out: &mut [u8]) {
    for (k, o) in out.iter_mut().enumerate() {
        let (blo, bhi) = (k << 3, ((k << 3) + 8).min(n));
        *o = (blo..bhi).fold(0u32, |b, i| b | (passes(mask, nmask, ids::id_at(ids, W, i)) as u32) << (i - blo)) as u8;
    }
}
/// One column's symbols are one object when its blob and its starts are the same objects, so equal without a read.
pub fn same_syms(a: &Syms, b: &Syms) -> bool { core::ptr::eq(a.blob.as_ptr(), b.blob.as_ptr()) && core::ptr::eq(a.offs.as_ptr(), b.offs.as_ptr()) }
pub fn sorted_col<'a>(w: usize, hay: &'a [u8], enc: Option<&'a Coc<'a>>) -> Col<'a> {
    assert!(matches!(w, 1 | 2 | 4 | 8), "qlean search: a sorted-haystack probe got element width {w}; the kernel is instantiated at 1, 2, 4 and 8 bytes");
    Col { d: hay, c: enc, uw: enc.map_or(0, |c| c.one_width()) }
}
/// search.rs `sorted_probe`: the least index of the `n`-element sorted haystack whose key equals key `j`'s, `n` where none.
/// `bin_key` is a bijection on each class once the float fold has run, so key equality is the equality `kind_of`'s
/// keys give; the walk is `binr`'s (the first index not below the needle).
pub fn sorted_probe(wk: Walk, h: &Col, keys: &[u8], n: i64, j: usize) -> i64 {
    let k = bin_key(wk.w, wk.f, wk.s, bin_at(keys, wk.w, j));
    let lo = wk.step(h, |i| i, k, 0, n);
    if lo < n && bin_key(wk.w, wk.f, wk.s, h.at(wk.w, lo as usize)) == k { lo } else { n }
}
/// search.rs `sym_build`: the hash table `tab` (`mask + 1` slots, zeroed) over the first `n` symbols, each slot the
/// first index holding its symbol, plus one.
pub fn sym_build(s: &Syms, n: usize, tab: &mut [usize], mask: u64) {
    for i in 0..n {
        let k = s.at(i);
        let mut h = (crate::sym::sym_hash(k) & mask) as usize;
        while tab[h] != 0 && !crate::sym::sym_eq(s.at(tab[h] - 1), k) { h = (h + 1) & mask as usize }
        if tab[h] == 0 { tab[h] = i + 1 }
    }
}
/// The needles are packed and probed this many at a time (rust/src/sym.rs `SYM_KEY_BLOCK`).
pub const SYM_KEY_BLOCK: usize = 4096;
/// search.rs `sym_probe`: the index `sym_build` stored for `k`, `n` when none.
pub fn sym_probe(s: &Syms, tab: &[usize], mask: u64, n: usize, k: &[u8]) -> usize {
    let mut h = (crate::sym::sym_hash(k) & mask) as usize;
    while tab[h] != 0 {
        if crate::sym::sym_eq(s.at(tab[h] - 1), k) { return tab[h] - 1 }
        h = (h + 1) & mask as usize;
    }
    n
}
/// The answer for needle `j` is index `idx`, absent being `n`: `out` holds `Int64`s, or bits (set where `idx < n`).
pub fn sym_put(bits: bool, out: &mut [u8], n: usize, j: usize, idx: usize) {
    if bits { if idx < n { out[j >> 3] |= 1 << (j & 7) } } else { i64s(out)[j] = idx as i64 }
}
/// Below this a symbol haystack is scanned rather than hashed (search.rs `SYM_SCAN_MAX`).
pub const SYM_SCAN_MAX: usize = 8;
// ---- A33: search.rs, 1539-1830, 2004-2099: the per-element callers of A32's walk, whole loops in Rust ----
/// The width switch hoisted out of the loop, as C's `IDS_WIDTHS`: `W` is a constant inside `go`, so `id_at` folds to a shift and a mask.
pub fn with_ids_width<R>(w: u32, f: impl IdsFn<R>) -> R {
    crate::by_width!(w, f.go())
}
/// Id `u` is inside `nmask` and `mask` has its bit.
pub fn passes(mask: &[u8], nmask: usize, u: usize) -> bool { u < nmask && mask[u >> 3] >> (u & 7) & 1 != 0 }
