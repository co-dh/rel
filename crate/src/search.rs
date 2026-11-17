#![forbid(unsafe_code)]
//! Column (a), search.rs: operands (A28), the probe table (A29), find/member (A30), bits and symbols (A31), binary
//! search (A32), run starts (A33). The `qlean_search_*` entries unbox and allocate and stay C (§1).
use alloc::{vec, vec::Vec};

use crate::c::Runner;
use crate::coc::Coc;
use crate::ids;
use crate::sym::Syms;

/// search.rs `opnd`: a dense payload (`enc` 0), an encoded column (1), or ids at `lw` bits (2); `n` elements.
#[derive(Clone, Copy)]
pub enum Src<'a> { Dense(&'a [u8]), Enc(Coc<'a>), Ids(&'a [u8], u32) }
#[derive(Clone, Copy)]
pub struct Opnd<'a> { pub src: Src<'a>, pub n: usize }
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
impl<'a> Opnd<'a> {
    /// The block size exponent of this operand: an encoded column's own, the writer's grid for a payload with none.
    pub fn lg(&self) -> u32 { match self.src { Src::Enc(c) => c.meta.lg, _ => crate::DEFAULT_LG } }
    /// Elements `at .. at + cnt` at width `w`, as the slice of `buf` they are restored into: one or more of this operand's own
    /// blocks, whichever its block size cuts them from.
    pub fn range<'b>(&self, at: usize, cnt: usize, w: usize, buf: &'b mut [u8]) -> &'b [u8] where 'a: 'b {
        let (lg, blk) = (self.lg(), 1usize << self.lg());
        let mut tmp = crate::pod::Scr::<u64, 1024>::new(2 * blk);
        let mut k = 0;
        while k < cnt {
            let (b, o) = ((at + k) >> lg, (at + k) & (blk - 1));
            let t = (blk - o).min(cnt - k);
            let x = self.blk(b, w, crate::pod::bytes_mut(&mut tmp));
            buf[k * w..(k + t) * w].copy_from_slice(&x[o * w..(o + t) * w]);
            k += t;
        }
        &buf[..cnt * w]
    }
    /// search.rs `opnd_blk`: block `b` at key width `w`: a slice of the payload, or restored into `buf`
    /// (block size * w); the element count is the answer's length / `w`.
    pub fn blk<'b>(&self, b: usize, w: usize, buf: &'b mut [u8]) -> &'b [u8] where 'a: 'b {
        let (at, cnt) = (b << self.lg(), (self.n - (b << self.lg())).min(1 << self.lg()));
        match self.src {
            Src::Dense(d) => &d[at * w..(at + cnt) * w],
            Src::Ids(p, lw) => {
                // `ids_key_width` answers at most 8; the clamp is for the `guid` instantiation, never run
                let out = &mut buf[..cnt * w];
                if matches!(w, 1 | 2 | 4 | 8) {
                    // `id_put` at `8w` bits is the fixed-width store; a `w`-byte copy here was a `memcpy` call per id
                    let ow = 8 * w as u32;
                    for k in 0..cnt { ids::id_put(out, ow, k, ids::id_at(p, lw, at + k) as u64) }
                } else {
                    let cw = w.min(8);
                    for k in 0..cnt { out[k * w..k * w + cw].copy_from_slice(&(ids::id_at(p, lw, at + k) as u64).to_le_bytes()[..cw]) }
                }
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
/// search.rs `coc_srange`: the column's value range from its metadata.
pub fn coc_srange(c: &Coc) -> (i64, i64) {
    let m = &c.meta;
    let nb = m.n.div_ceil(m.blk());
    let (mut a, mut z) = (i64::MAX, i64::MIN);
    for b in 0..nb { a = a.min(m.base[b]); z = z.max(m.maxv[b]) }
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
pub fn blocks(x: &Opnd, w: usize, lo: usize, hi: usize, mut f: impl FnMut(usize, &[u8])) {
    let lg = x.lg();
    let mut buf = crate::pod::Scr::<u64>::new(2 << lg);
    let bb = crate::pod::bytes_mut(&mut buf);
    let mut at = lo;
    while at < hi {
        let (b, end) = (at >> lg, (((at >> lg) + 1) << lg).min(hi));
        let blo = b << lg;
        f(at, &x.blk(b, w, bb)[(at - blo) * w..(end - blo) * w]);
        at = end;
    }
}

/// search.rs `table_*`: the table over the haystack `o`, a block at a time, each slot holding the first index its key
/// occurs at plus one. Direct when the keys span at most `4n + 8`; a direct table whose every slot is filled stops there.
pub fn table<K: PKey>(o: &Opnd) -> Ptab<K> {
    let mut p = Ptab { tab: Vec::new(), slot: Vec::new(), key: Vec::new(), top: 0, lo: 0, n: o.n, used: 0, direct: false, sh: 0 };
    let (lg, mut buf) = (o.lg(), crate::pod::Scr::<u64>::new(2 << o.lg()));
    let bb = crate::pod::bytes_mut(&mut buf);
    let nb = o.n.div_ceil(1 << lg);
    if o.n > 0 && K::W <= 8 {
        let (lo, span) = match o.src {
            Src::Ids(_, lw) => (0, ids_top(lw)),
            Src::Enc(c) => { let (a, z) = coc_srange(&c); (a as u64 & mask::<K>(), (z as u64).wrapping_sub(a as u64)) }
            Src::Dense(d) => {
                // the C reads exactly `n` elements; a shorter payload is a caller bug and would fold to an empty range
                assert!(d.len() >= o.n * K::W, "qlean search: a dense haystack of {} bytes holds fewer than its {} elements of {} bytes", d.len(), o.n, K::W);
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
        let blk = o.blk(b, K::W, bb);
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
    pub fn hits(&self, h: &Opnd, lo: i64, hi: i64, ans: &mut [usize]) {
        let mut left = self.used;
        let lg = h.lg();
        let mut buf = crate::pod::Scr::<u64>::new(2 << lg);
        let bb = crate::pod::bytes_mut(&mut buf);
        for b in 0..h.n.div_ceil(1 << lg) {
            if left == 0 { return }
            if let Src::Enc(c) = h.src {
                if (c.meta.maxv[b] < lo || c.meta.base[b] > hi) && !coc_exc_within(&c, b, lo, hi) { continue }
            }
            for (j, c) in h.blk(b, K::W, bb).chunks_exact(K::W).enumerate() {
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
    fn each(&self, x: &Opnd, lo: usize, hi: usize, mut f: impl FnMut(usize, usize)) {
        blocks(x, K::W, lo, hi, |at, q| {
            if self.direct { for (j, c) in q.chunks_exact(K::W).enumerate() { f(at + j, self.dslot(K::of(c))) } }
            else { for (j, c) in q.chunks_exact(K::W).enumerate() { f(at + j, self.hslot(K::of(c))) } }
        })
    }
    /// search.rs `findtab_*`: `x ? hay` for `lo .. hi` into `out[i - lo]`, `ans` the table's own `tab` or the walk's
    /// `hits`; an absent key answers `n`.
    pub fn find(&self, ans: &[usize], x: &Opnd, lo: usize, hi: usize, out: &mut [i64]) {
        self.each(x, lo, hi, |i, s| out[i - lo] = if s != usize::MAX && ans[s] != 0 { ans[s] as i64 - 1 } else { self.n as i64 })
    }
    /// search.rs `membertab_*`: `x in hay` for `lo .. hi`, bit `i - lo` of `out` (`lo` a multiple of 8) set when found.
    pub fn member(&self, ans: &[usize], x: &Opnd, lo: usize, hi: usize, out: &mut [u8]) {
        self.each(x, lo, hi, |i, s| if s != usize::MAX && ans[s] != 0 { out[(i - lo) >> 3] |= 1 << ((i - lo) & 7) })
    }
}
/// search.rs `scan_*`: the first index of each needle `lo .. hi` of `x` in the dense haystack `h`, or `h.n`; eight
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
/// search.rs `srange_*`: the operand's signed key range, which a walk over an encoded haystack tests each block's
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
    /// the table over the haystack `o`
    pub fn new(kd: Kind, o: &Opnd) -> Probe { by_kind!(kd, K, V => Probe { t: V(table::<K>(o)), hit: None }) }
    /// search.rs `SEARCH_TABLE`'s smaller-side branch: the table over the needles `x`, and the haystack `h` walked to
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

// ---- A30: search.rs ----
/// search.rs `search` past the allocation: `x ? h` (index, `h.n` when absent; `out` is `8 * x.n` bytes) or `x in h`
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
    let has = [find_bit(hay, n, 0) < n, find_bit(hay, n, 1) < n];
    out.fill(0);
    for i in 0..m { if has[bit_at(xs, i) as usize] { out[i >> 3] |= 1 << (i & 7) } }
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
        let b = j >> c.meta.lg;
        if b != self.b {
            let (at, w) = (b << c.meta.lg, self.w);
            let cnt = (c.meta.n - at).min(c.meta.blk());
            let o = crate::pod::bytes_mut(&mut self.buf);
            match w {
                1 => c.decode_blk::<u8>(b, cnt, o),
                2 => c.decode_blk::<i16>(b, cnt, crate::pod::cast_mut(o).expect("kcur: u64 buffer is aligned")),
                4 => c.decode_blk::<i32>(b, cnt, crate::pod::cast_mut(o).expect("kcur: u64 buffer is aligned")),
                _ => c.decode_blk::<i64>(b, cnt, crate::pod::cast_mut(o).expect("kcur: u64 buffer is aligned")),
            }
            self.b = b;
        }
        bin_at(crate::pod::bytes(&self.buf), self.w, j & (c.meta.blk() - 1))
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
pub fn run_starts(o: &Opnd, w: usize, is_float: bool, out: &mut [i64]) -> usize {
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
    let (lg, mut buf, mut g, mut prev) = (o.lg(), crate::pod::Scr::<u64>::new(1 << o.lg()), 0, 0u64);
    for b in 0..o.n.div_ceil(1 << lg) {
        let at = b << lg;
        // a bit block runs the word algorithm of `run_starts_bits`, the key being the bit itself
        if let (false, Src::Enc(c)) = (is_float, &o.src) { if let Some(p) = c.bit_blk(b) {
            if b == 0 { out[0] = 0; g = 1; prev = (p[0] & 1) as u64 }
            crate::bitblk::run_starts(p, (o.n - at).min(1 << lg), at, &mut prev, &mut g, out);
            continue
        } }
        let h = o.blk(b, w, crate::pod::bytes_mut(&mut buf));
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
    scan_kind(kd, &Opnd { src: Src::Dense(hay), n: hay.len() / w }, &Opnd { src: Src::Dense(&nb[..w]), n: 1 }, &mut r);
    r[0] as usize
}



/// The operand a dense payload `p` of `w`-byte elements is (`opnd_dense`).
impl<'a> Opnd<'a> {
    pub fn dense(p: &'a [u8], w: usize) -> Self { Opnd { src: Src::Dense(p), n: p.len() / w } }
    /// `Column.idsCap`'s count of `n` ids at `lw` bits, which is all `id_at` may read (`opnd_ids`).
    pub fn ids(p: &'a [u8], n: usize, lw: u32) -> Self {
        let n = n.min(ids::ids_avail(p.len(), lw));
        Opnd { src: Src::Ids(&p[..ids::ids_bytes(n, lw)], lw), n }
    }
}

