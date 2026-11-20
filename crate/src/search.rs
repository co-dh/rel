#![forbid(unsafe_code)]
//! Column (a), search.rs: operands (A28), the probe table (A29), find/member (A30), bits and symbols (A31), binary
//! search (A32), run starts (A33). The `qlean_search_*` entries unbox and allocate and stay C (§1).


// ---- A28: search.rs, 407, 818 ----

// ---- A29: search.rs, the probe table, one instance per key type ----





// ---- A30: search.rs ----

// ---- A31: search.rs ----


// ---- A32: search.rs ----














// ---- B17: search.rs's scalar find, the Frame-of-Reference equality walks, the id mask ----

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
        Coc { meta: Meta { lg: crate::DEFAULT_LG, base, maxv, off, bsum: base, width, n, nblk: m, mblk: m }, pack: &[], exc, fdelta: None }
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
// ---- K17: search.rs `coc_may_hold64`, `remap_ids_run`, the index's slots (`ix_*`) ----

// ---- A33: search.rs, 1539-1830, 2004-2099: the per-element callers of A32's walk, whole loops in Rust ----
