#![forbid(unsafe_code)]
//! Column (a), sym.rs (A11): a symbol column as a byte blob plus the `Array Nat` of starts. Rust never sees a
//! `lean_object`: C passes `lean_array_cptr(offs)` as `*const usize`, the boxed words themselves, and `Syms`
//! unboxes them (`w >> 1`; an unboxed word, a bignum pointer, aborts as `off_at` does).
use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::RefCell;
use core::cmp::Ordering;
use crate::pod;
use crate::structural::{self, Symtab, Symview, symtab_build};

/// A symbol column: `offs[i]` is symbol `i`'s start in `blob`, boxed; symbol `i` runs to `offs[i + 1]`.
#[derive(Clone, Copy)]
pub struct Syms<'a> { pub blob: &'a [u8], pub offs: &'a [usize] }

impl<'a> Syms<'a> {
    /// sym.rs `off_at`: start `i`, unboxed. Per element: C keeps its body while a C caller remains.
    #[inline]
    pub fn off(&self, i: usize) -> usize { {
        let w = self.offs[i];
        if w & 1 == 0 { panic!("qlean: symbol offset {i} is a bignum; an offset is bounded by the blob's byte count and cannot reach 2^63") }
        w >> 1
    } }
    /// sym.rs `sym_at`
    #[inline]
    pub fn at(&self, i: usize) -> &'a [u8] { {
        let (lo, hi) = (self.off(i), self.off(i + 1));
        let n = hi.saturating_sub(lo + 1); // an empty symbol never reads the blob, as C's `sym_at` does not (`dof` may point past an empty dictionary)
        if n == 0 { &self.blob[..0] } else { &self.blob[lo..lo + n] }
    } }
    /// sym.rs `sym_count`: the symbol count, `offs.len() - 1` (0 for an empty `offs`).
    pub fn count(&self) -> usize { self.offs.len().saturating_sub(1) }
    /// `key` of the symbol at the unboxed starts `lo`, `hi`: one 8-byte load and a mask while the load stays inside the
    /// blob (the C `whole` prefix), the bytes folded for the last few; a loop over a column carries `lo`, as C does.
    #[inline]
    pub fn key_of(&self, lo: usize, hi: usize) -> u64 {
        let len = hi.wrapping_sub(lo + 1);
        if len == 0 { 0 }
        else if lo + 8 <= self.blob.len() { self.key_whole(lo, len) }
        else { self.blob[lo..lo + len].iter().fold(0, |w, &b| w << 8 | b as u64) << (8 * (8 - len)) }
    }
    /// the keys of the first `n` symbols, in order, `lo` carried as C's loop does. The caller has seen `packs(n)`: every tag
    /// bit is set, so the starts unbox without a test.
    pub fn keys(&self, n: usize) -> impl Iterator<Item = u64> + '_ {
        let mut lo = if n > 0 { self.offs[0] >> 1 } else { 0 };
        self.offs[..n.saturating_add(1).min(self.offs.len())].windows(2).map(move |w| { let hi = w[1] >> 1; let k = self.key_of(lo, hi); lo = hi; k })
    }
    /// the load of `key_of` where it stays inside the blob and `len` is 1 ..= 8
    #[inline]
    pub fn key_whole(&self, lo: usize, len: usize) -> u64 {
        u64::from_be_bytes(self.blob[lo..lo + 8].try_into().unwrap()) & (!0u64 << (8 * (8 - len)))
    }
    /// sym.rs `sym_slices`: the first `n` symbols.
    pub fn slices(&self, n: usize) -> Vec<&'a [u8]> { (0..n).map(|i| self.at(i)).collect() }
    /// sym.rs `sym_packs`: every symbol of the first `n` fits the 8-byte key `sym_pack` makes.
    pub fn packs(&self, n: usize) -> bool { {
        let (mut tags, mut wide) = (self.offs[n], false);
        for i in 0..n {
            tags &= self.offs[i]; // a clear tag bit is a bignum, which the blob rules out
            wide |= (self.offs[i + 1] >> 1).wrapping_sub(self.offs[i] >> 1).wrapping_sub(1) > 8;
        }
        tags & 1 != 0 && !wide && self.offs[n] >> 1 <= self.blob.len()
    } }
}
/// sym.rs `sym_eq`: length first, then the bytes in overlapping loads (8, 4, 2, 1), so a short symbol is a few
/// compares and never a `bcmp` call (`[u8] ==` is one, and a symbol is two to six bytes).
#[inline]
pub fn sym_eq(a: &[u8], b: &[u8]) -> bool {
    let n = a.len();
    if n != b.len() { return false }
    let w = |s: &[u8], at: usize| u64::from_le_bytes(s[at..at + 8].try_into().unwrap());
    let d = |s: &[u8], at: usize| u32::from_le_bytes(s[at..at + 4].try_into().unwrap());
    let h = |s: &[u8], at: usize| u16::from_le_bytes(s[at..at + 2].try_into().unwrap());
    if n >= 8 {
        let mut i = 0;
        while i + 8 < n { if w(a, i) != w(b, i) { return false } i += 8 }
        w(a, n - 8) == w(b, n - 8)
    } else if n >= 4 { d(a, 0) == d(b, 0) && d(a, n - 4) == d(b, n - 4) }
    else if n >= 2 { h(a, 0) == h(b, 0) && h(a, n - 2) == h(b, n - 2) }
    else { n == 0 || a[0] == b[0] }
}
/// sym.rs `sym_cmp`: q's symbol order (bytes unsigned, then length), which is `[u8]`'s.
pub fn sym_cmp(a: &[u8], b: &[u8]) -> Ordering { a.cmp(b) }
/// sym.rs `sym_hash`: FNV-1a.
pub fn sym_hash(s: &[u8]) -> u64 { s.iter().fold(0xcbf29ce484222325, |h, &b| (h ^ b as u64).wrapping_mul(0x100000001b3)) }
/// sym.rs `sym_msort`: the indices `a` (`v.len()` of them) stably sorted by `v[a[i]]`; `tmp` is scratch, as long.
pub fn sym_msort(v: &[&[u8]], a: &mut [usize], tmp: &mut [usize]) { {
    let n = a.len();
    let mut w = 1;
    while w < n {
        let mut lo = 0;
        while lo < n {
            let (mid, hi) = ((lo + w).min(n), (lo + 2 * w).min(n));
            let (mut i, mut j, mut o) = (lo, mid, lo);
            while i < mid && j < hi {
                if v[a[i]] <= v[a[j]] { tmp[o] = a[i]; i += 1 } else { tmp[o] = a[j]; j += 1 }
                o += 1;
            }
            tmp[o..o + mid - i].copy_from_slice(&a[i..mid]);
            o += mid - i;
            tmp[o..o + hi - j].copy_from_slice(&a[j..hi]);
            lo += 2 * w;
        }
        a.copy_from_slice(&tmp[..n]);
        w <<= 1;
    }
} }

// ---- K20: the kept dictionary hashes and `symdict_concat`'s dictionary half (structural.rs `symtab_*`, `sd_*`) ----
/// One hash of a chain of dictionaries, each a prefix of the next (structural.rs's `symtab`): `slot` is `mask + 1`
/// ids + 1, `stale` the slots a fork copied that hold another chain's entry. The reference count is the `Rc`'s.
pub struct Htab { pub cnt: usize, pub mask: usize, pub stale: usize, pub slot: Vec<u32> }
/// The shared handle: the cache's slots and the one concat in flight hold it; the table is written in place.
pub struct Tab(pub RefCell<Htab>);

impl Htab {
    /// Runs `f` on the borrowed view and writes its counts back.
    fn with<R>(&mut self, f: impl FnOnce(&mut Symtab) -> R) -> R {
        let (cnt, mask, stale) = (self.cnt, self.mask, self.stale);
        let mut s = Symtab { cnt, mask, stale, slot: &mut self.slot };
        let r = f(&mut s);
        (self.cnt, self.stale) = (s.cnt, s.stale);
        r
    }
    /// structural.rs `symtab_fit`: half full at most with the stale slots counted; the entries are re-hashed from
    /// the dictionary `v` that holds all of them, which drops the stale ones.
    fn fit(&mut self, v: &Symview, n: usize) {
        if 2 * (n + self.stale) <= self.mask + 1 { return }
        let mut cap = self.mask + 1;
        while 2 * n > cap { cap *= 2 }
        (self.stale, self.slot, self.mask) = (0, vec![0; cap], cap - 1);
        self.with(|s| s.fill(v));
    }
    /// structural.rs `symtab_build`: a table over the `d` entries of the plain dictionary `v`, `None` when one repeats
    /// an earlier one (the joined dictionary is then not the base's with symbols after it, and `concatEnum` interns).
    fn build(v: &Symview, d: usize) -> Option<Tab> {
        let mut t = Htab { cnt: 0, mask: 15, stale: 0, slot: vec![0; 16] };
        t.fit(v, d);
        t.with(|s| symtab_build(s, v, d)).then(|| Tab(RefCell::new(t)))
    }
    /// structural.rs `symtab_fork`: the table of the dictionary `d` entries into `s`'s chain, its slots copied (a
    /// memcpy of 4 bytes a slot against a hash and a missed line a symbol); entries at or past `d` count as stale.
    fn fork(s: &Htab, d: usize) -> Htab {
        let mut t = Htab { cnt: d, mask: s.mask, stale: 0, slot: pod::uninit(s.mask + 1) };
        t.with(|f| f.fork(&s.slot, s.cnt, s.stale, d));
        t
    }
}

/// A dictionary object and its starts array, as the cache holds them and `concat` reads and writes them. The
/// implementation over Lean objects is ffi.rs's; every method is the one lean.h inline its name says.
pub trait Heap: Copy + PartialEq {
    /// `m_rc`
    fn rc(self) -> i32;
    fn inc(self);
    fn dec(self);
    /// a byte array's / an array's capacity
    fn cap(self) -> usize;
    /// a byte array's byte count
    fn len(self) -> usize;
    /// sets the byte count of `self` and the length of `offs`, inside their capacity
    fn resize(self, offs: Self, bytes: usize, n: usize);
    /// a byte array of `bytes` bytes (room for `cap`) and a starts array of `n` (room for `ncap`), each at `rc` 1
    fn alloc(bytes: usize, cap: usize, n: usize, ncap: usize) -> (Self, Self);
    /// `src` into the bytes at `at`
    fn put_bytes(self, at: usize, src: &[u8]);
    /// the starts `it` (unboxed, boxed on the way in) into the array from `at`
    fn put_starts(self, at: usize, it: impl Iterator<Item = usize>);
}

pub const SLOTS: usize = 16;
pub struct Slot<H> { dict: H, offs: H, t: Rc<Tab>, d: usize, used: u64 }
/// structural.rs's `sd[]`: the last 16 dictionaries kept with their table at their count. Not thread safe: the
/// caller holds one lock around every call (C's `sd_mu`).
pub struct Cache<H> { slots: [Option<Slot<H>>; SLOTS], clock: u64 }

/// One part of a concatenation: its dictionary and starts, and the symbols they hold.
pub struct Part<'a, H> { pub dict: H, pub offs: H, pub syms: Syms<'a> }
/// `concat`'s answer: the joined dictionary and starts (one reference each, the caller's), its symbol count, and for
/// each part past the first the id every one of its symbols has in it (`None` where they are the base's own);
/// each map has a 0 past its last entry.
pub struct Dicts<H> { pub dict: H, pub offs: H, pub cnt: usize, pub maps: Vec<Option<Vec<usize>>> }

impl<H: Heap> Cache<H> {
    pub const fn new() -> Self { Cache { slots: [const { None }; SLOTS], clock: 0 } }
    fn at(&self, i: usize) -> &Slot<H> { self.slots[i].as_ref().expect("qlean sym: an empty dictionary-cache slot") }
    /// `sd_free`
    fn free(&mut self, i: usize) {
        let s = self.slots[i].take().expect("qlean sym: freeing an empty dictionary-cache slot");
        s.dict.dec();
        s.offs.dec();
    }
    /// `sd_alone`: no one else holds slot `i`'s dictionary (`rc` 1, or the one reference of a multi-threaded object).
    fn alone(&self, i: usize) -> bool { matches!(self.at(i).dict.rc(), 1 | -1) }
    /// `sd_mine`: only the cache holds slot `i`'s dictionary and starts, single-threaded, so they may be written.
    fn mine(&self, i: usize) -> bool { self.at(i).dict.rc() == 1 && self.at(i).offs.rc() == 1 }
    /// `sd_find`: the slot keeping `dict` at `d` entries; entries no one else holds are released, except a spare,
    /// whose table a dictionary held elsewhere shares.
    pub fn find(&mut self, dict: H, d: usize) -> Option<usize> {
        let mut hit = None;
        for i in 0..SLOTS {
            let Some(s) = &mut self.slots[i] else { continue };
            if s.dict == dict && s.d == d { self.clock += 1; s.used = self.clock; hit = Some(i); continue }
            if !self.alone(i) { continue }
            let live = self.mine(i) && (0..SLOTS).any(|j| j != i && self.slots[j].is_some() && Rc::ptr_eq(&self.at(j).t, &self.at(i).t) && !self.alone(j));
            if !live { self.free(i) }
        }
        hit
    }
    /// The table of slot `i`, for a probe (valid while the caller's lock holds).
    pub fn table(&self, i: usize) -> &Tab { &self.at(i).t }
    /// `sd_spare`: a slot of `t`'s chain at no more than `d0` entries, so a prefix of the `d0`-entry dictionary
    /// that holds `t` at its count.
    fn spare(&self, t: &Rc<Tab>, d0: usize) -> Option<usize> {
        (0..SLOTS).find(|&i| self.slots[i].is_some() && Rc::ptr_eq(&self.at(i).t, t) && self.at(i).d <= d0 && self.mine(i))
    }
    /// `sd_put`: keeps `dict`/`offs` at `d` entries with `t`, in the slot already holding that pair (a fork replaces
    /// the base's own, whose table has moved past it), else an empty one, else the least recently used.
    fn put(&mut self, dict: H, offs: H, t: &Rc<Tab>, d: usize) {
        let mut at = 0;
        for i in 0..SLOTS {
            match &self.slots[i] {
                Some(s) if s.dict == dict && s.d == d => { at = i; break }
                None => { at = i; break }
                Some(s) => if s.used < self.at(at).used { at = i },
            }
        }
        // taken before the eviction, which may drop the last other reference to `t`
        dict.inc();
        offs.inc();
        let t = t.clone();
        if self.slots[at].is_some() { self.free(at) }
        self.clock += 1;
        self.slots[at] = Some(Slot { dict, offs, t, d, used: self.clock });
    }

    /// structural.rs `symdict_concat`'s dictionary half, over the first part's dictionary as the base (or a later
    /// part's, when it is longer and in the same chain): `None` when the base holds a symbol twice or the joined
    /// dictionary would not fit 32-bit ids, `Spec: Kernel.hashConcat`'s decline.
    pub fn concat(&mut self, parts: &[Part<H>]) -> Option<Dicts<H>> {
        let k = parts.len();
        if k == 0 { return None }
        let mut d0 = parts[0].syms.count();
        if d0 >= u32::MAX as usize - 1 { return None }
        let (extra, ecap) = parts[1..].iter().fold((0, 0), |(x, e), p| (x + p.syms.blob.len(), e + p.syms.count()));
        let mut hit = self.find(parts[0].dict, d0);
        // A later part whose dictionary is in the first's chain -- one table, so the first's is a prefix of it -- is
        // the base instead when it is longer: the joined dictionary is then that dictionary with the other parts'
        // new symbols after it, and the chain's parts need no probe at all.
        let t0 = hit.map(|h| self.at(h).t.clone());
        let mut base = 0;
        if let Some(t0) = &t0 {
            for (i, p) in parts.iter().enumerate().skip(1) {
                let di = p.syms.count();
                if di <= d0 { continue }
                if let Some(h) = self.find(p.dict, di) && Rc::ptr_eq(&self.at(h).t, t0) { (hit, base, d0) = (Some(h), i, di) }
            }
        }
        let b = &parts[base];
        let v = Symview { base: b.syms, d0, tb: &[], to: &[] };
        let t = match hit {
            None => Rc::new(Htab::build(&v, d0)?),
            Some(h) if self.at(h).t.0.borrow().cnt == d0 => self.at(h).t.clone(),
            Some(h) => Rc::new(Tab(RefCell::new(Htab::fork(&self.at(h).t.0.borrow(), d0)))),
        };
        // the base is kept at its own count too, so a part read off a later state of it is known for one
        let built = hit.is_none();
        if built { self.put(b.dict, b.offs, &t, d0) }
        if d0 + ecap >= u32::MAX as usize - 1 { return None }
        let (mut tb, mut to): (Vec<u8>, Vec<usize>) = (pod::uninit(extra + 1), pod::uninit(ecap + 1));
        to[0] = 0;
        let mut maps: Vec<Option<Vec<usize>>> = (0..k).map(|_| None).collect();
        let mut cnt = d0;
        for (i, p) in parts.iter().enumerate().skip(1) {
            let di = p.syms.count();
            if p.dict == b.dict { continue }
            if let Some(t0) = &t0 && di <= d0 && let Some(h) = self.find(p.dict, di) && Rc::ptr_eq(&self.at(h).t, t0) { continue }
            let mut map: Vec<usize> = pod::uninit(di + 1);
            let mut j = 0;
            while j < di {
                let mut h = t.0.borrow_mut();
                j = h.with(|s| structural::symdict_intern(s, &b.syms, d0, &mut tb, &mut to, &p.syms, &mut map[..di], j));
                // the slots cannot grow inside the intern: it stops where they must, `fit` does that, and it resumes
                if j < di { let n = h.cnt + 1; h.fit(&Symview { base: b.syms, d0, tb: &tb, to: &to }, n) }
            }
            map[di] = 0;
            maps[i] = Some(map);
            cnt = t.0.borrow().cnt;
        }
        let (dict, offs) = if cnt == d0 {
            // nothing new: the answer's dictionary is the base's own object, and its table stays
            b.dict.inc();
            b.offs.inc();
            if !built && hit.is_some_and(|h| self.slots[h].as_ref().is_none_or(|s| !Rc::ptr_eq(&s.t, &t))) { self.put(b.dict, b.offs, &t, d0) }
            (b.dict, b.offs)
        } else {
            let (s0, sn) = (b.syms.blob.len(), to[cnt - d0]);
            let sp = self.spare(&t, d0);
            // the spare's first `dr` entries and `sr` bytes are already the answer's
            let (dict, offs, dr, sr) = match sp.map(|i| (i, self.at(i))) {
                Some((i, s)) if s.dict.cap() >= s0 + sn && s.offs.cap() >= cnt + 1 => {
                    let (dict, offs, dr, sr) = (s.dict, s.offs, s.d, s.dict.len());
                    dict.resize(offs, s0 + sn, cnt + 1);
                    self.clock += 1;
                    let s = self.slots[i].as_mut().expect("qlean sym: the spare slot vanished");
                    (s.d, s.used) = (cnt, self.clock);
                    dict.inc();
                    offs.inc();
                    (dict, offs, dr, sr)
                }
                _ => {
                    // a spare too small is a chain growing in a loop: double, so its copies amortise
                    let g = if sp.is_some() { 2 } else { 1 };
                    if let Some(i) = sp { self.free(i) }
                    let (dict, offs) = H::alloc(s0 + sn, g * (s0 + sn), cnt + 1, g * (cnt + 1));
                    self.put(dict, offs, &t, cnt);
                    (dict, offs, 0, 0)
                }
            };
            dict.put_bytes(sr, &b.syms.blob[sr..s0]);
            dict.put_bytes(s0, &tb[..sn]);
            // an empty dictionary may come with no starts at all, `Syms::count`'s case
            offs.put_starts(0, core::iter::once(0));
            offs.put_starts(dr + 1, (dr + 1..=d0).map(|i| b.syms.off(i)));
            offs.put_starts(d0 + 1, (1..=cnt - d0).map(|i| s0 + to[i]));
            (dict, offs)
        };
        Some(Dicts { dict, offs, cnt, maps })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    /// `offs` for the symbols `ss`, each NUL-terminated in the blob, boxed
    fn col(ss: &[&[u8]]) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (vec![], vec![1]);
        for s in ss { b.extend_from_slice(s); b.push(0); o.push(b.len() << 1 | 1) }
        (b, o)
    }
    #[test] fn order_and_empty() {
        let (b, o) = col(&[b"ab", b"a", b"aa", b"", "\u{e9}".as_bytes(), b"e", b"z"]);
        let s = Syms { blob: &b, offs: &o };
        assert_eq!(s.count(), 7);
        assert_eq!(s.at(3), b"");
        let v = s.slices(7);
        let (mut a, mut t) = ((0..7).collect::<Vec<_>>(), vec![0; 7]);
        sym_msort(&v, &mut a, &mut t);
        assert_eq!(a, [3, 1, 2, 0, 5, 6, 4]);
        assert_eq!(Syms { blob: &[], offs: &[] }.count(), 0);
        assert!(s.packs(7));
        let (b, o) = col(&[b"123456789"]);
        assert!(!Syms { blob: &b, offs: &o }.packs(1));
        assert_eq!(sym_hash(b""), 0xcbf29ce484222325);
    }
    // the specification is sym.rs's byte loops (`sym_eq`) and `memcmp` then lengths (`sym_cmp`): every length 0..20, bytes from both
    // halves of the byte range (q's order is unsigned), and pairs that share a prefix or differ in the last byte only
    #[test] fn eq_and_cmp_match_the_byte_loops() {
        let mut s = 0x9E3779B97F4A7C15u64;
        let mut r = move || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        for _ in 0..200_000 {
            let (n, m) = ((r() % 21) as usize, (r() % 21) as usize);
            let a: Vec<u8> = (0..n).map(|_| if r() % 3 == 0 { 0x80 + (r() % 128) as u8 } else { (r() % 4) as u8 }).collect();
            let mut b: Vec<u8> = if r() % 2 == 0 { a.iter().copied().chain((0..m).map(|_| r() as u8)).take(m).collect() } else { (0..m).map(|_| (r() % 4) as u8).collect() };
            if r() % 4 == 0 && b.len() == a.len() && !b.is_empty() { b.copy_from_slice(&a); let l = b.len() - 1; b[l] ^= 1 << (r() % 8); }
            let by_loop = a.len() == b.len() && a.iter().zip(&b).all(|(x, y)| x == y);
            let first = a.iter().zip(&b).find(|(x, y)| x != y).map(|(x, y)| x.cmp(y));
            assert_eq!((sym_eq(&a, &b), sym_cmp(&a, &b)), (by_loop, first.unwrap_or(a.len().cmp(&b.len()))), "{a:?} {b:?}");
        }
    }
}

#[cfg(test)]
mod kept_tests {
    use super::*;
    use core::cell::RefCell as RC;
    /// a mock object: `bytes` for a dictionary, `starts` (boxed) for a starts array; `cap` is its capacity
    struct O { rc: i32, bytes: Vec<u8>, starts: Vec<usize>, cap: usize }
    thread_local! { static HEAP: RC<Vec<O>> = const { RC::new(Vec::new()) }; }
    #[derive(Clone, Copy, PartialEq)] struct M(usize);
    fn new(bytes: usize, n: usize, cap: usize) -> M {
        HEAP.with(|h| { let mut h = h.borrow_mut(); h.push(O { rc: 1, bytes: vec![0; bytes], starts: vec![0; n], cap }); M(h.len() - 1) })
    }
    impl Heap for M {
        fn rc(self) -> i32 { HEAP.with(|h| h.borrow()[self.0].rc) }
        fn inc(self) { HEAP.with(|h| h.borrow_mut()[self.0].rc += 1) }
        fn dec(self) { HEAP.with(|h| h.borrow_mut()[self.0].rc -= 1) }
        fn cap(self) -> usize { HEAP.with(|h| h.borrow()[self.0].cap) }
        fn len(self) -> usize { HEAP.with(|h| h.borrow()[self.0].bytes.len()) }
        fn resize(self, offs: Self, bytes: usize, n: usize) {
            HEAP.with(|h| { let mut h = h.borrow_mut(); h[self.0].bytes.resize(bytes, 0); h[offs.0].starts.resize(n, 0) })
        }
        fn alloc(bytes: usize, cap: usize, n: usize, ncap: usize) -> (Self, Self) { (new(bytes, 0, cap), new(0, n, ncap)) }
        fn put_bytes(self, at: usize, src: &[u8]) { HEAP.with(|h| h.borrow_mut()[self.0].bytes[at..at + src.len()].copy_from_slice(src)) }
        fn put_starts(self, at: usize, it: impl Iterator<Item = usize>) {
            HEAP.with(|h| for (k, v) in it.enumerate() { h.borrow_mut()[self.0].starts[at + k] = v << 1 | 1 })
        }
    }
    /// the dictionary of `ss`: `m` is the pair of objects, and the bytes and boxed starts the parts read
    fn dict(ss: &[Vec<u8>]) -> (M, M, Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (vec![], vec![1]);
        for s in ss { b.extend_from_slice(s); b.push(0); o.push(b.len() << 1 | 1) }
        let (d, os) = (new(b.len(), 0, b.len()), new(0, o.len(), o.len()));
        HEAP.with(|h| { let mut h = h.borrow_mut(); h[d.0].bytes.copy_from_slice(&b); h[os.0].starts.copy_from_slice(&o) });
        (d, os, b, o)
    }
    fn snap(d: M, o: M) -> (Vec<u8>, Vec<usize>) { HEAP.with(|h| (h.borrow()[d.0].bytes.clone(), h.borrow()[o.0].starts.clone())) }
    fn name(i: u64) -> Vec<u8> { alloc::format!("s{i}").into_bytes() }

    #[test] fn chain_of_appends_matches_the_set_semantics() {
        let (mut seed, mut c) = (12345u64, Cache::<M>::new());
        let mut rnd = |n: u64| { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); (seed >> 33) % n };
        let (mut d, mut o, _, _) = dict(&[]);
        let mut joined: Vec<Vec<u8>> = vec![];
        for it in 0..400 {
            let mut ss: Vec<Vec<u8>> = vec![];
            for _ in 0..rnd(7) { let s = if rnd(9) == 0 { vec![] } else { name(rnd(90)) }; if !ss.contains(&s) { ss.push(s) } }
            let (nd, no, pb, po) = dict(&ss);
            let (bb, bo) = snap(d, o);
            let r = c.concat(&[Part { dict: d, offs: o, syms: Syms { blob: &bb, offs: &bo } },
                               Part { dict: nd, offs: no, syms: Syms { blob: &pb, offs: &po } }]).expect("a unique base");
            let want: Vec<usize> = ss.iter().map(|s| joined.iter().position(|j| j == s).unwrap_or_else(|| { joined.push(s.clone()); joined.len() - 1 })).collect();
            let (rb, ro) = snap(r.dict, r.offs);
            let (wb, wo) = { let t = dict(&joined); snap(t.0, t.1) };
            assert_eq!((r.cnt, &rb, &ro), (joined.len(), &wb, &wo), "iteration {it}");
            let map = r.maps[1].as_ref().expect("a part of its own dictionary");
            assert_eq!((&map[..ss.len()], map[ss.len()]), (&want[..], 0), "iteration {it}");
            // the previous answer is dropped, as Lean does: the cache then holds it alone, a spare to write into
            for h in [d, o, nd, no] { h.dec() }
            (d, o) = (r.dict, r.offs);
        }
    }

    #[test] fn base_switch_decline_and_empty() {
        let mut c = Cache::<M>::new();
        let strs = |r: core::ops::Range<u64>| r.map(name).collect::<Vec<_>>();
        let (d1, o1, b1, p1) = dict(&strs(0..10));
        let (e, _) = (c.concat(&[]), ());
        assert!(e.is_none());
        // `[d1, d1 + 20..24]`, then `[d1, longer, fresh]`: the longer part of the chain is the base
        let (nb, np, bb, bp) = dict(&strs(20..24));
        let a = c.concat(&[Part { dict: d1, offs: o1, syms: Syms { blob: &b1, offs: &p1 } }, Part { dict: nb, offs: np, syms: Syms { blob: &bb, offs: &bp } }]).unwrap();
        let (ab, ao) = snap(a.dict, a.offs);
        let (fb, fo, fbb, fbo) = dict(&[name(3), name(30), name(21)]);
        let r = c.concat(&[Part { dict: d1, offs: o1, syms: Syms { blob: &b1, offs: &p1 } },
                           Part { dict: a.dict, offs: a.offs, syms: Syms { blob: &ab, offs: &ao } },
                           Part { dict: fb, offs: fo, syms: Syms { blob: &fbb, offs: &fbo } }]).unwrap();
        assert_eq!(r.cnt, 15);
        assert!(r.maps[1].is_none());
        assert_eq!(&r.maps[2].as_ref().unwrap()[..3], &[3, 14, 11]);
        // a base holding a symbol twice declines
        let (xd, xo, xb, xp) = dict(&[name(1), name(2), name(1)]);
        assert!(c.concat(&[Part { dict: xd, offs: xo, syms: Syms { blob: &xb, offs: &xp } }]).is_none());
    }
}
