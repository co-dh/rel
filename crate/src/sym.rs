#![forbid(unsafe_code)]
//! Column (a), sym.rs (A11): a symbol column as a byte blob plus the `Array Nat` of starts. Rust never sees a
//! `lean_object`: C passes `lean_array_cptr(offs)` as `*const usize`, the boxed words themselves, and `Syms`
//! unboxes them (`w >> 1`; an unboxed word, a bignum pointer, aborts as `off_at` does).



// ---- K20: the kept dictionary hashes and `symdict_concat`'s dictionary half (structural.rs `symtab_*`, `sd_*`) ----






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
