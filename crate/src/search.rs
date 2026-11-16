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
/// search.c `search` past the allocation: `x ? h` (index, `h.n` when absent; `out` is `8 * x.n` bytes) or `x in h`
/// (`member`, a bit each, LSB first; `out` is `x.n.div_ceil(8)` bytes) into `out`, threaded. The table goes over the
/// smaller side, so the haystack is walked to the first occurrence of each needle key when the needles are fewer.
/// The table is read-only for the whole pass, so slices are disjoint in `out`; a probe is `QLEAN_COST_ARITH` rather than
/// `GATHER` (measured 0.40 ns an element against 0.05 for a straight read: 400 ns a thousand on one thread, 66 on 24).
pub fn search(run: Runner, kd: Kind, h: &Opnd, x: &Opnd, member: bool, out: &mut [u8]) {
    let m = x.n;
    if m == 0 { return }
    let t = if m < h.n { Probe::over(kd, h, x) } else { Probe::new(kd, h) };
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
/// search.c `ids_key_width`: bytes an id key takes where one side is at `a` bits and the other at `b`.
pub fn ids_key_width(a: usize, b: usize) -> usize { match a.max(b) { ..=8 => 1, ..=16 => 2, ..=32 => 4, _ => 8 } }

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
    /// `ix` is the index payload the walk reads `h` through (`order`), `|i| i` where each position is its own index.
    fn step(self, h: &Col, ix: impl Fn(usize) -> usize, k: u64, mut lo: i64, hi: i64) -> i64 {
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

// ---- A33: search.c:731-740, 1539-1830, 2004-2099: the per-element callers of A32's walk, whole loops in Rust ----
/// The width switch hoisted out of the loop, as C's `IDS_WIDTHS`: `W` is a constant inside `go`, so `id_at` folds to a shift and a mask.
fn with_ids_width<R>(w: u32, f: impl IdsFn<R>) -> R {
    match w { 0 => f.go::<0>(), 1 => f.go::<1>(), 2 => f.go::<2>(), 4 => f.go::<4>(), 8 => f.go::<8>(), 16 => f.go::<16>(), 32 => f.go::<32>(), _ => f.go::<64>() }
}
trait IdsFn<R> { fn go<const W: u32>(self) -> R; }

/// search.c:1609 `qlean_search_bin_ids` past the unboxing: `binBytes 8 false true right` of the `n` ranks `vals[ids[i]]`
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

fn sorted_col<'a>(w: usize, hay: &'a [u8], enc: Option<&'a Coc<'a>>) -> Col<'a> {
    assert!(matches!(w, 1 | 2 | 4 | 8), "qlean search: a sorted-haystack probe got element width {w}; the kernel is instantiated at 1, 2, 4 and 8 bytes");
    Col { d: hay, c: enc, uw: enc.map_or(0, |c| c.one_width()) }
}
/// search.c:1651 `sorted_probe`: the least index of the `n`-element sorted haystack whose key equals key `j`'s, `n` where none.
/// `bin_key` is a bijection on each class once the float fold has run, so key equality is the equality `kind_of`'s
/// keys give; the walk is `binr`'s (the first index not below the needle).
fn sorted_probe(wk: Walk, h: &Col, keys: &[u8], n: i64, j: usize) -> i64 {
    let k = bin_key(wk.w, wk.f, wk.s, bin_at(keys, wk.w, j));
    let lo = wk.step(h, |i| i, k, 0, n);
    if lo < n && bin_key(wk.w, wk.f, wk.s, h.at(wk.w, lo as usize)) == k { lo } else { n }
}
/// search.c:1684-1734 `qlean_search_find_sorted`, `qlean_coc_find_sorted` past the unboxing: each of the `m` dense keys'
/// first index in the sorted haystack (dense `hay`, or `enc`) of `n`, `n` where absent, into `out`; threaded.
pub fn find_sorted(run: Runner, w: usize, is_float: bool, is_signed: bool, hay: &[u8], enc: Option<&Coc>, n: i64, keys: &[u8], m: usize, out: &mut [i64]) {
    let (wk, h) = (Walk { w, f: is_float, s: is_signed, right: true }, sorted_col(w, hay, enc));
    crate::c::run_map(run, crate::pod::bytes_mut(&mut out[..m]), m, 8, crate::QLEAN_COST_MATH, 8, &|lo, hi, o: &mut [u8]| {
        for (j, x) in (lo..hi).zip(i64s(o)) { *x = sorted_probe(wk, &h, keys, n, j) }
    });
}
/// search.c:1697-1734 `qlean_search_member_sorted`, `qlean_coc_member_sorted` past the unboxing: bit `j` of `out` (LSB
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

/// search.c:1773 `bin_rows` past the unboxing: for each of the `m` dense keys, the row `binRows` names inside group
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

/// search.c:2004 `run_starts` past the allocation: the start of each run of equal elements of `o` (`norm_key`'s equality)
/// into `out` (`o.n + 1` long), then `o.n` as the terminator; answers the count with the terminator. The payload is read
/// a block at a time at width `w`, 1, 2, 4 or 8.
pub fn run_starts(o: &Opnd, w: usize, is_float: bool, out: &mut [i64]) -> usize {
    assert!(matches!(w, 1 | 2 | 4 | 8), "qlean search: run_starts got element width {w}; the kernel is instantiated at 1, 2, 4 and 8 bytes");
    let (mut buf, mut g, mut prev) = ([0u64; crate::BLK], 0, 0u64);
    for b in 0..o.n.div_ceil(crate::BLK) {
        let h = o.blk(b, w, crate::pod::bytes_mut(&mut buf));
        for (j, c) in h.chunks_exact(w).enumerate() {
            let v = norm_key(w, is_float, bin_at(c, w, 0));
            if (b | j) == 0 || v != prev { out[g] = (b * crate::BLK + j) as i64; g += 1 }
            prev = v;
        }
    }
    out[g] = o.n as i64;
    g + 1
}
/// search.c:731 `qlean_search_run_starts_ids`: `runStarts` over `n` ids at `w` bits; the dictionary is distinct, so equal
/// ids are equal elements. `out` is `n + 1` long; answers the count with the terminator `n`.
pub fn run_starts_ids(n: usize, w: u32, ids: &[u8], out: &mut [i64]) -> usize {
    let g = ids::runs(ids, n, w, usize::MAX, n, out);
    out[g] = n as i64;
    g + 1
}
/// search.c:2056 `qlean_search_run_starts_syms`: the run starts of the symbols, then their count. `out` is `count + 1` long.
pub fn run_starts_syms(s: &Syms, out: &mut [i64]) -> usize {
    let (n, mut g) = (s.count(), 0);
    for i in 0..n { if i == 0 || s.at(i) != s.at(i - 1) { out[g] = i as i64; g += 1 } }
    out[g] = n as i64;
    g + 1
}
/// search.c:2078 `qlean_search_run_starts_bits`: `runStarts` over `n` booleans packed LSB first, a byte past the end
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
        assert_eq!(starts(|o| run_starts(&Opnd { src: Src::Dense(&d), n: 7 }, 2, false, o), 7), [0, 2, 5, 6, 7]);
        // -0.0 and 0.0 are one value, and every NaN is one value
        let f: alloc::vec::Vec<u8> = [0.0f32, -0.0, f32::NAN, -f32::NAN, 1.0].iter().flat_map(|x| x.to_bits().to_le_bytes()).collect();
        assert_eq!(starts(|o| run_starts(&Opnd { src: Src::Dense(&f), n: 5 }, 4, true, o), 5), [0, 2, 4, 5]);
        assert_eq!(starts(|o| run_starts(&Opnd { src: Src::Dense(&[]), n: 0 }, 8, false, o), 0), [0]);
        // 1500 elements in blocks of 1024: a run across the block edge is one run
        let big: alloc::vec::Vec<u8> = (0..1500u32).flat_map(|i| u32::from(i >= 1023 && i < 1030).to_le_bytes()).collect();
        assert_eq!(starts(|o| run_starts(&Opnd { src: Src::Dense(&big), n: 1500 }, 4, false, o), 1500), [0, 1023, 1030, 1500]);
        // ids at 2 bits: 0 0 1 1 3 3 3 0
        assert_eq!(starts(|o| run_starts_ids(8, 2, &[0b0101_0000, 0b0011_1111], o), 8), [0, 2, 4, 7, 8]);
        let (b, off) = ([b'a', 0, b'a', 0, b'b', 0], [1usize, 2 << 1 | 1, 4 << 1 | 1, 6 << 1 | 1]);
        assert_eq!(starts(|o| run_starts_syms(&Syms { blob: &b, offs: &off }, o), 3), [0, 2, 3]);
        // bits LSB first: 0 0 1 1 1 0 over 6 bits, and a 70-bit run crossing a word edge
        assert_eq!(starts(|o| run_starts_bits(6, &[0b011100], o), 6), [0, 2, 5, 6]);
        assert_eq!(starts(|o| run_starts_bits(70, &[0xff; 9], o), 70), [0, 70]);
        assert_eq!(starts(|o| run_starts_bits(0, &[], o), 0), [0]);
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
        assert_eq!(srange::<u16>(&Opnd { src: Src::Ids(&[], 8), n: 0 }), (0, 127));
    }
}
