#![forbid(unsafe_code)]
//! Column (a), ew.rs: scalar helpers (A42), the two-operand verbs and comparisons (A43; `ew_val_avx` and
//! `ew_cmp_avx` are `simd::ew_val`/`simd::ew_cmp`), bit verbs and the monadic ones (A44), casts and time (A45),
//! widening (A46a), the fused chain's stage table (A46b; its runner is `c::run_chain`). `op`, `cls`, `shape` are
//! ew.rs's `EW_*`. The `qlean_ew_*` entries unbox and allocate and stay C (§1).

// ---- A42: ew.rs (per element: C keeps these bodies while a C caller remains) ----
// q's order on floats as two predicates: a null (a NaN) below everything, two nulls equal (ew.rs)

// ---- A43: ew.rs ----

/// `EW_*` codes of ew.rs that this section reads; the two lists cannot change apart.
pub mod k {
    
    
    
    
    
    
}





/// `floor` at double width; `core` has none. A NaN, an infinity, a magnitude from 2^52 and a zero are their own floor.
pub fn floor64(x: f64) -> f64 {
    if !(x.abs() < 4503599627370496.0) || x == 0.0 { return x }
    let t = x as i64 as f64;
    if t > x { t - 1.0 } else { t }
}






// ---- A44: ew.rs ----
/// `EW_*` codes of ew.rs this section reads (the verbs `k` does not hold).
mod k44 {
    
    
    // `EW_BCMP + EW_EQ ..= EW_GE`
    
    
}


// ---- A45: ew.rs ----


// ---- A46a: ew.rs ----







// ---- A46b: ew.rs (the stage workers stay C until `c::run_chain` calls Rust ones) ----
/// ew.rs's engine codes, the `Ew.Engine` constants of QLean/Kernel/Elementwise.lean.
pub mod eng {
    
    
    // 10 was the encoder's pack pass, which `ENC` now stages in its one pass
    
    
}

// ---- K9: the chain's tile workers over a packed id column (ew.rs `ew_ids_run`, :1315 `ew_pack_run`) ----

// ---- K10: the statistics fold, a chain's last stage (ew.rs `ew_stats_run`, `ew_stats_sum`) ----
/// ew.rs's `ST_*`: the five phases, each one pass over the column.
pub mod st { }






// ---- E: the fused chain's program, its builder and its two folds (ew.rs `ew_chain_build`, `qlean_ew_chain*`, `qlean_stats_chain`) ----






#[cfg(test)]
mod a45 {
    use super::*;
    // expected values are the C's comments (ew.rs "Eval.castAtom ... measured against q 4.1") and its helpers
    #[test] fn round_is_half_away_and_saturates() {
        assert_eq!((cast_round(2.5), cast_round(-2.5), cast_round(0.49999999999999994)), (3, -3, 0));
        assert_eq!((cast_round(1e19), cast_round(-1e19), cast_round(f64::INFINITY)), (i64::MAX, i64::MIN + 1, i64::MAX));
    }
    #[test] fn casts_clamp_at_a_null_target_and_wrap_without() {
        let x: Vec<u8> = [70000.0f64, -32768.0, 300.0, f64::NAN].iter().flat_map(|v| v.to_bits().to_le_bytes()).collect();
        let mut o = [0u8; 8];
        cast_lane(5, 1, 0, &x, &mut o);
        assert_eq!([i16::from_le_bytes([o[0], o[1]]), i16::from_le_bytes([o[2], o[3]]), i16::from_le_bytes([o[4], o[5]]), i16::from_le_bytes([o[6], o[7]])],
                   [32767, -32767, 300, i16::MIN]);
        let mut o = [0u8; 4];
        cast_lane(5, 0, 0, &x, &mut o);
        assert_eq!(o, [0x70, 0, 0x2c, 0]);
    }
    #[test] fn calendar_round_trips() {
        assert_eq!((fdiv64(-7, 2), days_of_first(0), month_of_days(0), days_of_first(1), days_of_first(-1)), (-4, 0, 0, 31, -31));
        for m in -20000..30000 { assert_eq!(month_of_days(days_of_first(m)), m); assert_eq!(month_of_days(days_of_first(m + 1) - 1), m) }
    }
    #[test] fn tick_counts_a_month_in_days() {
        // su 5 (month) to du 4 (day): months 0, 1, 2 from 2000.01 are 0, 31, 60 days; the null stays the target's
        let x: Vec<u8> = [0i32, 1, 2, i32::MIN].iter().flat_map(|v| v.to_le_bytes()).collect();
        let mut o = [0u8; 32];
        tick(crate::c::qlean_run_c, 5 * 16 + 4, 2, 3, i32::MIN as i64, i64::MIN, &x, 4, &mut o);
        let v: Vec<i64> = o.chunks(8).map(|c| i64::from_le_bytes(c.try_into().unwrap())).collect();
        assert_eq!(v, [0, 31, 60, i64::MIN]);
    }
}
#[cfg(test)]
mod a46a {
    use super::*;
    #[test] fn widen_nulls_and_floats() {
        let x: Vec<u8> = [i16::MIN, 5, -7].iter().flat_map(|v| v.to_le_bytes()).collect();
        let mut o = [0u8; 24];
        widen(crate::c::qlean_run_c, 1, 3, i16::MIN as i64, i64::MIN, &x, 3, &mut o);
        assert_eq!(&o[..8], &i64::MIN.to_le_bytes());
        assert_eq!(&o[8..16], &5i64.to_le_bytes());
        let f: Vec<u8> = [0xffc00000u32, 0x3f800000].iter().flat_map(|v| v.to_le_bytes()).collect();
        let mut o = [0u8; 16];
        widen(crate::c::qlean_run_c, 4, 5, 0, 0, &f, 2, &mut o);
        assert_eq!(u64::from_le_bytes(o[..8].try_into().unwrap()), 0xfff8000000000000);
        assert_eq!(u64::from_le_bytes(o[8..].try_into().unwrap()), 1f64.to_bits());
    }
}
#[cfg(test)]
mod tests_k8 {
    use super::*;
    use crate::c::qlean_run_c;
    /// a symbol column of `ss`: NUL-terminated blob, boxed starts
    fn col(ss: &[&[u8]]) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (Vec::new(), alloc::vec![1]);
        for s in ss { b.extend_from_slice(s); b.push(0); o.push(b.len() << 1 | 1) }
        (b, o)
    }
    fn like(pat: &[u8], ss: &[&[u8]]) -> Option<Vec<u8>> {
        let (b, o) = col(ss);
        let mut out = alloc::vec![0xAAu8; ss.len().div_ceil(8)];
        like_syms(pat, &Syms { blob: &b, offs: &o }, &mut out).then_some(out)
    }
    fn hits(atom: bool, pat: &[u8], b: &[u8]) -> Option<Vec<i64>> {
        let w = fixed_width(atom, pat);
        if w == 0 { return None }
        let mut h = alloc::vec![0i64; b.len() / w + 1];
        let k = fixed_scan(atom, pat, b, &mut h);
        h.truncate(k);
        Some(h)
    }
    #[test] fn like_language() {
        let ss: [&[u8]; 5] = [b"abc", b"", b"a-c", b"xbz", b"ab"];
        assert_eq!(like(b"a*", &ss), Some(alloc::vec![0b10101]));
        assert_eq!(like(b"?b?", &ss), Some(alloc::vec![0b01001]));
        assert_eq!(like(b"[a-b]*", &ss), Some(alloc::vec![0b10101]));
        assert_eq!(like(b"[^a]*", &ss), Some(alloc::vec![0b01000]));
        assert_eq!(like(b"", &ss), Some(alloc::vec![0b00010]));
        assert_eq!(like(b"*", &ss), Some(alloc::vec![0b11111]));
        assert_eq!(like(b"a**", &ss), None); // q's `'nyi`
        assert_eq!(like(b"[abc", &ss), None); // q's `'[`
        assert_eq!(like(b"[]]", &[b"]"]), Some(alloc::vec![1])); // a `]` first in a class is a member
        assert_eq!(like(b"[a-]", &[b"-", b"a"]), Some(alloc::vec![0b11])); // a range needs a byte after `-` that is not `]`
    }
    #[test] fn fixed_matches_do_not_overlap() {
        assert_eq!(hits(false, b"aa", b"aaaa"), Some(alloc::vec![0, 2])); // measured: `"aaaa" ss "aa"` is `0 2`
        assert_eq!(hits(true, b"?", b"abc"), Some(alloc::vec![]));
        assert_eq!(hits(false, b"?", b"abc"), Some(alloc::vec![0, 1, 2]));
        assert_eq!(hits(true, b"[", b"a[c"), Some(alloc::vec![1]));
        assert_eq!(hits(false, b"[", b"a[c"), None);
        assert_eq!(hits(false, b"", b"abc"), None);
        assert_eq!(hits(false, b"a*", b"abc"), None);
        // the vector path (64 positions at a time) and the item walk agree, hits across a 64-byte step included
        let b: Vec<u8> = (0..300).map(|i| if i % 5 == 3 || i % 7 == 0 { b'a' } else { b'b' }).collect();
        for pat in [&b"ab"[..], b"a", b"aba", b"abbab", b"b"] {
            let item: Vec<u8> = pat.iter().flat_map(|&c| [b'[', c, b']']).collect(); // the same needle as `[a][b]`: no vector path
            assert_eq!(hits(false, pat, &b), hits(false, &item, &b), "{}", core::str::from_utf8(pat).unwrap());
        }
    }
    #[test] fn ssr_replaces_the_scan() {
        let run = |pat: &[u8], t: &[u8], b: &[u8]| {
            let (w, mut h) = (fixed_width(false, pat), alloc::vec![0i64; b.len() + 1]);
            let k = fixed_scan(false, pat, b, &mut h);
            let mut o = alloc::vec![0u8; b.len() - k * w + k * t.len() + 16];
            ssr_fill(&mut o, b, &h[..k], w, t);
            o.truncate(b.len() - k * w + k * t.len());
            o
        };
        assert_eq!(run(b"aa", b"b", b"aaa"), b"ba"); // measured: `ssr["aaa";"aa";"b"]` is `"ba"`
        assert_eq!(run(b"[ab]", b"X", b"abc"), b"XXc"); // the step is the item count, not the byte count
        let long = [b'z'; 40];
        assert_eq!(run(b"a", &long, b"xay"), [&b"x"[..], &long, b"y"].concat());
    }
    #[test] fn sym_order_is_slice_order() {
        let mut s = 0x2545F4914F6CDD1Du64;
        let mut next = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        for _ in 0..20000 {
            let (la, lb) = (next() as usize % 40, next() as usize % 40);
            let mut a: Vec<u8> = (0..la).map(|_| (next() % 3) as u8 * 100).collect();
            let mut b: Vec<u8> = (0..lb).map(|_| (next() % 3) as u8 * 100).collect();
            if next() % 3 == 0 { let k = la.min(lb); b[..k].copy_from_slice(&a[..k]) }
            if next() % 7 == 0 { b = a.clone(); a.push(0) }
            assert_eq!(sym_ord(&a, &b), a.cmp(&b), "{a:?} {b:?}");
        }
    }
    #[test] fn cmp_all_shapes() {
        let (ba, oa) = col(&[b"ab", b"", b"b", "\u{e9}".as_bytes(), b"ab", b"abc", b"z", b"a", b"b", b"q"]);
        let (bb, ob) = col(&[b"ab", b"a", b"a", b"z", b"abc", b"ab", b"z", b"", b"b", b"q"]);
        let (a, b) = (Syms { blob: &ba, offs: &oa }, Syms { blob: &bb, offs: &ob });
        let n = 10;
        let go = |op, sh, a: &Syms, b: &Syms| { let mut o = alloc::vec![0xFFu8; 2]; cmp_syms(qlean_run_c, op, sh, a, b, n, &mut o); o };
        let want = |op: u8, f: &dyn Fn(usize) -> (Vec<u8>, Vec<u8>)| {
            let mut o = alloc::vec![0u8; 2];
            for i in 0..n { let (x, y) = f(i); let r = match op { 0 => x == y, 1 => x != y, 2 => x < y, 3 => x <= y, 4 => x > y, _ => x >= y }; o[i / 8] |= (r as u8) << (i % 8) }
            o
        };
        let (sa, sb) = (a.slices(10), b.slices(10));
        for op in 0..6 {
            assert_eq!(go(op, k::VV, &a, &b), want(op, &|i| (sa[i].to_vec(), sb[i].to_vec())), "VV {op}");
            assert_eq!(go(op, k::VA, &a, &b), want(op, &|i| (sa[i].to_vec(), sb[0].to_vec())), "VA {op}");
            assert_eq!(go(op, k::AV, &a, &b), want(op, &|i| (sa[0].to_vec(), sb[i].to_vec())), "AV {op}");
        }
    }
}
#[cfg(test)]
mod a46b {
    use super::*;
    // expected values are ew.rs's `ew_stage_bits` / `ew_stage_fixed` read off the C switch
    #[test] fn stage_costs_and_widths() {
        use crate::{QLEAN_COST_ARITH as A, QLEAN_COST_COPY as C, QLEAN_COST_MATH as M};
        assert_eq!(stage_bits(eng::VAL, k::POW as u32, 5, 0), (M, 64, 64, 64));
        assert_eq!(stage_bits(eng::VAL, k::ADD as u32, 0, 0), (A, 8, 8, 8));
        assert_eq!(stage_bits(eng::CMP, 0, 3, 0), (A, 64, 64, 1));
        assert_eq!(stage_bits(eng::WIDEN, 0, 6, 3), (C, 1, 0, 64));
        assert_eq!(stage_bits(eng::WIDEN, 0, 1, 2), (C, 16, 0, 32));
        assert_eq!(stage_bits(eng::BIT, 0, 0, 0), (C, 1, 1, 1));
        assert_eq!(stage_bits(eng::PACK, 0, 3, 2), (C, 64, 0, 2));
        assert_eq!(stage_bits(eng::ENC, 0, 2, 0), (A, 32, 0, 0));
        assert_eq!(stage_bits(eng::DECODE, 0, 2, 0), (C, 0, 0, 32));
    }
    #[test] fn atoms_and_encoded_views_are_not_rebased() {
        assert!(stage_fixed(eng::VAL, k::AV as u32, true) && !stage_fixed(eng::VAL, k::AV as u32, false));
        assert!(stage_fixed(eng::CMP, k::VA as u32, false) && !stage_fixed(eng::CMP, k::VV as u32, true));
        assert!(stage_fixed(eng::DECODE, 0, true) && stage_fixed(eng::ALP, 0, false));
        // a monadic engine has no left atom, and its right side is always fixed
        assert!(!stage_fixed(eng::MON, 0, true) && stage_fixed(eng::MON, 0, false));
    }
}
#[cfg(test)]
mod a42 {
    use super::*;
    fn h(s: &str) -> u64 { u64::from_str_radix(s, 16).unwrap() }
    /// Replays vectors dumped by ew.rs's own bodies (testdata/ew_a42.vec); `EW_A42_VEC` names a bigger dump.
    fn replay(text: &str) -> usize {
        let mut gm: Option<Magic> = None;
        let mut n = 0;
        for l in text.lines() {
            let f: Vec<&str> = l.split(' ').collect();
            match f[0] {
                "w" => assert_eq!(ew_width(f[1].parse().unwrap()), f[2].parse::<usize>().unwrap(), "{l}"),
                "tol" => assert_eq!(ew_tol(f64::from_bits(h(f[1])), f64::from_bits(h(f[2]))), f[3] == "1", "{l}"),
                "ord64" => assert_eq!(ew_ord64(h(f[1]), h(f[2])), f[3].parse::<i32>().unwrap(), "{l}"),
                "ord32" => assert_eq!(ew_ord32(h(f[1]) as u32, h(f[2]) as u32), f[3].parse::<i32>().unwrap(), "{l}"),
                "out" => assert_eq!(ew_outside_long(f64::from_bits(h(f[1]))), f[2] == "1", "{l}"),
                "fdiv" => assert_eq!(ew_fdiv(h(f[1]) as i64, h(f[2]) as i64), h(f[3]) as i64, "{l}"),
                "magic" => {
                    let d = h(f[1]) as i64;
                    gm = magic_of(d);
                    // C's add is 1, -1 or 0: nonzero is `add`, its sign follows d
                    let want = (f[2] == "1").then(|| Magic { m: h(f[3]) as i64, d, sh: f[4].parse().unwrap(), add: f[5] != "0" });
                    assert_eq!(gm, want, "{l}");
                    if let (Some(g), Some(_)) = (gm, want) { assert_eq!(g.add, f[5] != "0"); assert!(f[5] != "-1" || d < 0); }
                }
                "fm" => assert_eq!(fdiv_magic(&gm.unwrap(), h(f[2]) as i64), h(f[3]) as i64, "{l}"),
                k => panic!("unknown vector {k}"),
            }
            n += 1;
        }
        n
    }
    #[test] fn vectors() { assert!(replay(include_str!("../testdata/ew_a42.vec")) > 1000); }
    #[test] fn big() { if let Ok(p) = std::env::var("EW_A42_VEC") { println!("{} vectors", replay(&std::fs::read_to_string(p).unwrap())); } }
    #[test] #[should_panic(expected = "storage class 6 has no dense element width")] fn width_bits() { ew_width(6); }
    #[test] #[should_panic(expected = "qlean_ew_val: no case for verb 9 at storage class 0. The dispatch")] fn unsupported() { ew_unsupported("qlean_ew_val", 9, 0); }
    #[test] fn named() {
        assert_eq!((ew_fdiv(-7, 2), ew_fdiv(7, -2), ew_fdiv(-7, -2), ew_fdiv(i64::MIN, -1)), (-4, -4, 3, i64::MIN));
        assert_eq!(magic_of(1), None); assert_eq!(magic_of(-1), None); assert_eq!(magic_of(0), None);
        assert!(ew_outside_long(9.3e18) && !ew_outside_long(9.2e18) && ew_outside_long(-9223372036854775808.0));
    }
}
#[cfg(test)]
mod tests43 {
    use crate::BLK;
    use super::*;
    use crate::c::qlean_run_c;
    use crate::coc::Meta;
    use crate::pod::bytes_mut;
    use std::vec::Vec;

    fn by<T: Pod>(v: &mut [T]) -> &[u8] { bytes_mut(v) }
    fn run_val<T: Pod>(op: u8, cls: u8, shape: u8, nul: i64, a: &mut [T], b: &mut [T], n: usize) -> Vec<u64> {
        let mut o = vec![0u64; n];
        val(qlean_run_c, op, cls, shape, nul, by(a), by(b), n, bytes_mut(&mut o[..]));
        o
    }
    // expected values below are the C worker's (`ew_val_run`, `ew_cmp_run` of a43be95) answers on the same inputs
    #[test] fn floored_division_and_remainder() {
        let mut a = [-7i64, 7, 0, i64::MIN, i64::MAX];
        let n = i64::MIN;
        assert_eq!(run_val(7, 3, k::VA, n, &mut a, &mut [2i64], 5), [0xfffffffffffffffc, 3, 0, 1 << 63, 0x3fffffffffffffff]);
        assert_eq!(run_val(7, 3, k::VA, n, &mut a, &mut [-2i64], 5), [3, 0xfffffffffffffffc, 0, 1 << 63, 0xc000000000000000]);
        assert_eq!(run_val(8, 3, k::VA, n, &mut a, &mut [7i64], 5), [0, 0, 0, 1 << 63, 0]);
        assert_eq!(run_val(7, 3, k::VA, n, &mut a, &mut [0i64], 5), [1 << 63; 5]);
    }
    #[test] fn byte_wraps_and_never_meets_its_null() {
        let mut a = [250u8, 3, 255, 100];
        let mut o = [0u8; 4];
        val(qlean_run_c, k::ADD, 0, k::VA, 256, by(&mut a), &[10], 4, &mut o);
        assert_eq!(o, [4, 0xd, 9, 0x6e]);
        val(qlean_run_c, k::MUL, 0, k::VA, 256, by(&mut a), &[10], 4, &mut o);
        assert_eq!(o, [0xc4, 0x1e, 0xf6, 0xe8]);
    }
    #[test] fn float_nulls_come_back_as_they_are_and_the_right_one_of_minus_flips() {
        let mut f = [0xfff8000000000000u64, 0x3ff0000000000000, 0x43f0000000000000, 0x4015800000000000, 0xc015800000000000, 0x7e37e43c8800759c];
        let (mut one, mut two) = ([0x3ff0000000000000u64], [0x4000000000000000u64]);
        assert_eq!(run_val(k::SUB, 5, k::AV, 0, &mut one, &mut f, 6),
                   [0x7ff8000000000000, 0, 0xc3f0000000000000, 0xc011800000000000, 0x4019800000000000, 0xfe37e43c8800759c]);
        assert_eq!(run_val(k::ADD, 5, k::VA, 0, &mut f, &mut one, 6),
                   [0xfff8000000000000, 0x4000000000000000, 0x43f0000000000000, 0x4019800000000000, 0xc011800000000000, 0x7e37e43c8800759c]);
        // a quotient outside q's long is a null, and `mod` of it the other one
        assert_eq!(run_val(k::IDIV, 5, k::VA, 0, &mut f, &mut one, 6),
                   [0xfff8000000000000, 0x3ff0000000000000, 0xfff8000000000000, 0x4014000000000000, 0xc018000000000000, 0xfff8000000000000]);
        assert_eq!(run_val(k::IMOD, 5, k::VA, 0, &mut f, &mut two, 6),
                   [0xfff8000000000000, 0x3ff0000000000000, 0x7ff8000000000000, 0x3ff6000000000000, 0x3fe4000000000000, 0x7ff8000000000000]);
    }
    // `pow` (libm) at both float widths, the f32 one computed at double width and narrowed; a NaN operand is `0n`
    #[test] fn pow_through_libm() {
        let (mut x, mut y) = ([2.0f64.to_bits(), f64::NAN.to_bits(), 4.0f64.to_bits()], [10.0f64.to_bits(), 1.0f64.to_bits(), 0.5f64.to_bits()]);
        assert_eq!(run_val(k::POW, 5, k::VV, 0, &mut x, &mut y, 3), [0x4090000000000000, 0xfff8000000000000, 0x4000000000000000]);
        let (mut x, mut y) = ([2.0f32.to_bits(), f32::NAN.to_bits()], [10.0f32.to_bits(), 1.0f32.to_bits()]);
        let mut o = [0u32; 2];
        val(qlean_run_c, k::POW, 4, k::VV, 0, by(&mut x), by(&mut y), 2, bytes_mut(&mut o[..]));
        assert_eq!(o, [1024.0f32.to_bits(), 0xffc00000]);
    }
    fn run_cmp<T: Pod>(op: u8, cls: u8, shape: u8, a: &mut [T], b: &mut [T], n: usize) -> Vec<u8> {
        let mut o = vec![0xABu8; n.div_ceil(8)];
        cmp(qlean_run_c, op, cls, shape, by(a), by(b), n, &mut o);
        o
    }
    #[test] fn comparisons_pack_lsb_first_with_zero_tail() {
        let mut t = [0x3ff0000000000000u64, 0x3ff0000000000001, 0x3ff00000000fffff, 0xfff8000000000000];
        assert_eq!(run_cmp(k::EQ, 5, k::VA, &mut t, &mut [0x3ff0000000000000u64], 4), [0x03]);
        assert_eq!(run_cmp(k::LT, 5, k::VA, &mut t, &mut [0x3ff0000000000000u64], 4), [0x08]);
        let mut u = t;
        assert_eq!(run_cmp(k::LE, 5, k::VV, &mut t, &mut u, 4), [0x0f]);
        let mut i: [i32; 11] = core::array::from_fn(|k| k as i32 + 1);
        assert_eq!(run_cmp(k::LT, 2, k::VA, &mut i, &mut [3i32], 11), [0x03, 0x00]);
        assert_eq!(run_cmp(k::GE, 2, k::AV, &mut [3i32], &mut i, 11), [0x07, 0x00]);
        // the tail past `n` stays zero whatever the verb answers there
        assert_eq!(run_cmp(k::NE, 0, k::VA, &mut [1u8; 9], &mut [0u8], 9), [0xff, 0x01]);
    }
    #[test] fn bitwise_and_low_zero() {
        let (mut a, mut b) = ([0b1100u64, !0, 5, 0, 9], [0b1010u64; 5]);
        let mut o = [0u64; 5];
        for (op, want) in [(0u8, [0b1000u64, 0b1010, 0, 0, 8]), (1, [0b1110, !0, 0b1111, 0b1010, 0b1011]), (2, [0b0100, !0b1010, 5, 0, 1]), (7, [0b1000, 0b1010, 0, 0, 8])] {
            bitw(qlean_run_c, op, by(&mut a), by(&mut b), 5, bytes_mut(&mut o));
            assert_eq!(o, want, "op {op}");
        }
        let mut z = vec![0xABu8; 1];
        low_zero(qlean_run_c, by(&mut a), by(&mut [0b0001u64]), 5, &mut z);
        assert_eq!(z, [0b01001]);
    }
    /// three blocks of 1024 longs and a tail of 452: block 0 and 2 at 8-bit residuals, block 1 constant
    fn coc_data() -> (Vec<u8>, Vec<i64>, Vec<u64>, Vec<u64>, Vec<i64>) {
        let (mut s, mut pack) = (0x9e3779b97f4a7c15u64, vec![]);
        let mut next = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        for _ in 0..2048 { pack.push(next() as u8) }
        (pack, vec![-1000, 77, 1 << 40], vec![0, 1024, 1024], vec![0; 3], vec![0, 0, 0])
    }
    #[test] fn encoded_operands_equal_their_decodes() {
        let n = 2 * BLK + 452;
        let (pack, base, off, _, bsum) = coc_data();
        let (maxv, width) = (vec![base[0] + 255, 77, base[2] + 255], [8u8, 0, 8]);
        let meta = Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &maxv, off: &off, bsum: &bsum, width: &width, n, nblk: 3, mblk: 3 };
        let c = Coc { meta, pack: &pack, exc: None, fdelta: None };
        let mut dense = vec![0i64; 3 * BLK];
        for b in 0..3 { c.decode_blk::<i64>(b, if b < 2 { BLK } else { 452 }, &mut dense[b * BLK..]) }
        let mut other: Vec<i64> = (0..n as i64).map(|i| i * 3 - 2000).collect();
        let mut ds = dense[..n].to_vec();
        let mut o = vec![0u64; n];
        val_enc(qlean_run_c, k::ADD, 3, i64::MIN, &c, &c, bytes_mut(&mut o));
        assert_eq!(o, run_val(k::ADD, 3, k::VV, i64::MIN, &mut ds, &mut dense[..n].to_vec(), n));
        for (shape, op) in [(k::VA, k::SUB), (k::AV, k::MUL), (k::VA, k::IDIV)] {
            let mut atom = [7i64];
            let want = if shape == k::VA { run_val(op, 3, shape, i64::MIN, &mut ds, &mut atom, n) } else { run_val(op, 3, shape, i64::MIN, &mut atom, &mut ds, n) };
            val_enc_atom(qlean_run_c, op, 3, shape, i64::MIN, &c, by(&mut atom), bytes_mut(&mut o));
            assert_eq!(o, want, "shape {shape} op {op}");
        }
        for m in [0u64, 0xff, 1 << 40, 77, 1] {
            let mut want = vec![0u8; n.div_ceil(8)];
            let mut got = vec![0xABu8; n.div_ceil(8)];
            let mut me = [m];
            let _ = &mut other;
            low_zero(qlean_run_c, by(&mut ds), by(&mut me), n, &mut want);
            low_zero_enc(qlean_run_c, &c, by(&mut me), &mut got);
            assert_eq!(got, want, "mask {m:#x}");
        }
    }
    fn syms(ss: &[&[u8]]) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (vec![], vec![1]);
        for s in ss { b.extend_from_slice(s); b.push(0); o.push(b.len() << 1 | 1) }
        (b, o)
    }
    #[test] fn ranks_in_the_merged_distinct_order_and_ids_through_them() {
        let ((ba, oa), (bb, ob)) = (syms(&[b"b", b"a", b"b"]), syms(&[b"c", b"a", b"", b"b"]));
        let (da, db) = (Syms { blob: &ba, offs: &oa }, Syms { blob: &bb, offs: &ob });
        let (mut ra, mut rb) = (vec![9; 3], vec![9; 4]);
        rank_pair(&da, &db, &mut ra, &mut rb);
        assert_eq!((ra.as_slice(), rb.as_slice()), (&[2, 1, 2][..], &[3, 1, 0, 2][..]));
        // ids at 2 bits, four to a byte: 0 1 2 3 0 | 3 2 1 0 3
        let (ia, ib) = ([0b11100100u8, 0b00000000], [0b00011011u8, 0b00000011]);
        let mut o = [0xABu8; 1];
        eq_ids(qlean_run_c, k::EQ, k::VV, &ia, &ib, 2, 5, &mut o);
        assert_eq!(o, [0b00000000]);
        eq_ids(qlean_run_c, k::NE, k::VV, &ia, &ib, 2, 5, &mut o);
        assert_eq!(o, [0b11111]);
        // ranks: ra = [2, 1, 2] for ids 0..2, past the table reads 0; rb = [3, 1, 0, 2]
        cmp_ids(qlean_run_c, k::LT, k::VV, &ra, &ia, 2, &rb, &ib, 2, 5, &mut o);
        assert_eq!(o, [0b01000]);
        cmp_ids(qlean_run_c, k::GE, k::VV, &ra, &ia, 2, &rb, &ib, 2, 5, &mut o);
        assert_eq!(o, [0b10111]);
        eq_ids(qlean_run_c, k::EQ, k::VA, &ia, &[0b10], 2, 5, &mut o);
        assert_eq!(o, [0b00100]);
    }
}
#[cfg(test)]
mod tests44 {
    use super::*;
    use crate::c::qlean_run_c;
    use crate::coc::Meta;
    use std::vec::Vec;

    fn hex(s: &str) -> Vec<u8> { (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect() }
    fn mon_of(op: u8, cls: u8, nul: i64, x: &[u8], n: usize) -> Vec<u8> {
        let mut o = vec![0u8; n * ew_width(cls as u32)];
        mon_lane(op, cls, nul, &x[..n * ew_width(cls as u32)], &mut o);
        o
    }
    #[test] fn neg_abs_edges() {
        // null stays null; the wrapping minimum of the class is its own negation
        assert_eq!(mon_of(0, 3, i64::MIN, &i64::MIN.to_ne_bytes(), 1), i64::MIN.to_ne_bytes());
        assert_eq!(mon_of(1, 3, i64::MIN, &(i64::MIN + 1).to_ne_bytes(), 1), i64::MAX.to_ne_bytes());
        assert_eq!(mon_of(0, 1, -32768, &(-32768i16).to_ne_bytes(), 1), (-32768i16).to_ne_bytes());
        assert_eq!(mon_of(0, 0, 256, &[0, 1, 255], 3), [0, 255, 1]);
        assert_eq!(mon_of(0, 5, 0, &0f64.to_bits().to_ne_bytes(), 1), (-0f64).to_bits().to_ne_bytes());
        assert_eq!(mon_of(1, 5, 0, &(-0f64).to_bits().to_ne_bytes(), 1), 0f64.to_bits().to_ne_bytes());
        assert_eq!(mon_of(0, 4, 0, &1.5f32.to_bits().to_ne_bytes(), 1), (-1.5f32).to_bits().to_ne_bytes());
    }
    #[test] fn floor_bounds() {
        let x: Vec<u8> = [9.3e18f64, f64::INFINITY, f64::NAN, -2.5, 9.2e18, -9.3e18].iter().flat_map(|v| v.to_bits().to_ne_bytes()).collect();
        let mut o = vec![0u8; 48];
        floor_lane(5, &x, &mut o);
        let r: Vec<i64> = o.chunks(8).map(|c| i64::from_ne_bytes(c.try_into().unwrap())).collect();
        assert_eq!(r, [i64::MIN, i64::MIN, i64::MIN, -3, 9_200_000_000_000_000_000, i64::MIN]);
    }
    #[test] fn bit_tail_is_masked() {
        let mut o = [0xabu8; 2];
        bit(qlean_run_c, 16 + 5, 1, &[0, 0], &[0], 11, &mut o); // not-zero by `>=` against a zero atom: all ones
        assert_eq!(o, [0xff, 0x07]);
    }
    /// the vectors `/data/tmp/qrs/A44/drv` dumps from the C of 78a5c06; run with EW_A44_VEC=<file> --ignored
    #[test] #[ignore] fn diff44() {
        let path = std::env::var("EW_A44_VEC").expect("EW_A44_VEC: the file `drv N file` wrote");
        let (mut cnt, mut bad) = (0, 0);
        for l in std::fs::read_to_string(path).unwrap().lines() {
            let f: Vec<&str> = l.split(' ').collect();
            let num = |i: usize| f[i].parse::<i64>().unwrap();
            match f[0] {
                "mon" => {
                    let (op, cls, nul, n) = (num(1) as u8, num(2) as u8, num(3), num(4) as usize);
                    if mon_of(op, cls, nul, &hex(f[5]), n) != hex(f[6]) { bad += 1 }
                }
                "floor" => {
                    let (cls, n) = (num(2) as u8, num(4) as usize);
                    let mut o = vec![0u8; n * 8];
                    floor_lane(cls, &hex(f[5]), &mut o);
                    if o != hex(f[6]) { bad += 1 }
                }
                _ => {
                    let (op, shape, n) = (num(1) as u8, num(2) as u8, num(3) as usize);
                    let mut o = vec![0u8; n.div_ceil(8)];
                    bit(qlean_run_c, op, shape, &hex(f[4]), &hex(f[5]), n, &mut o);
                    if o != hex(f[6]) { bad += 1 }
                }
            }
            cnt += 1;
        }
        eprintln!("diff44: {cnt} vectors, {bad} mismatches");
        assert_eq!(bad, 0);
    }
    /// `foRMon = mon (decode ..)`: three blocks at widths 8, 16, 0 bits, the last one short
    #[test] fn enc_and_fill_equal_mon_of_the_decode() {
        let (n, nblk) = (2500usize, 3usize);
        let (base, maxv, bsum) = ([-5i64, 100, 7], [0i64; 3], [0i64; 3]);
        let width = [8u8, 16, 0];
        let mut off = [0u64; 3];
        let mut pack: Vec<u8> = vec![];
        for b in 0..nblk { off[b] = pack.len() as u64; pack.extend((0..crate::BLK * width[b] as usize / 8).map(|i| (i * 37 + b * 11) as u8)) }
        let meta = Meta { lg: crate::DEFAULT_LG, base: &base, maxv: &maxv, off: &off, bsum: &bsum, width: &width, n, nblk, mblk: nblk };
        let c = Coc { meta, pack: &pack, exc: None, fdelta: None };
        for (cls, w) in [(1u8, 2usize), (2, 4), (3, 8)] {
            for op in 0..2u8 {
                let mut dense = vec![0u8; n * w];
                for b in 0..nblk {
                    let (cnt, mut xv) = ((n - b * crate::BLK).min(crate::BLK), [0u64; crate::BLK]);
                    let x = Blocks::from(c).load_w(b, cnt, w, bytes_mut(&mut xv));
                    dense[b * crate::BLK * w..(b * crate::BLK + cnt) * w].copy_from_slice(&x[..cnt * w]);
                }
                let want = mon_of(op, cls, i64::MIN, &dense, n);
                let map = Map { src: Blocks::from(c), wi: w, lane: |x: &[u8], o: &mut [u8]| mon_lane(op, cls, i64::MIN, x, o) };
                // the writer's blocks, aligned and (at 100 elements, off the source's grid) cut across the source's
                for step in [crate::BLK, 100] {
                    for lo in (0..n).step_by(step) {
                        let (nb, mut buf) = (step.min(n - lo), vec![0u64; 2 * crate::BLK]);
                        let got = crate::enc::Producer::block(&map, lo / crate::BLK, lo, nb, w, bytes_mut(&mut buf));
                        assert_eq!(got, &want[lo * w..(lo + nb) * w], "map cls {cls} op {op} at {lo}");
                    }
                }
            }
        }
    }
}
#[cfg(test)]
mod k9 {
    use super::*;
    use crate::c::qlean_run_c;
    fn mon_f64(op: u8, x: &[u64]) -> Vec<u64> {
        let mut o = vec![0u64; x.len()];
        mon_lane(op, k44::F64, 0, bytes_mut(&mut x.to_vec()[..]), bytes_mut(&mut o[..]));
        o
    }
    // expected bits are the C's own answers: `sqrt -1`, `log -1`, `tan 0w` are 0n; `asin 2`, `acos -0w` are the positive NaN
    #[test] fn libm_maps_answer_q_nulls() {
        let (inf, ninf) = (f64::INFINITY.to_bits(), f64::NEG_INFINITY.to_bits());
        assert_eq!(mon_f64(2, &[(-1f64).to_bits(), 4f64.to_bits(), 0x7ff8000000000001]), [NAN64, 2f64.to_bits(), NAN64]);
        assert_eq!(mon_f64(4, &[(-1f64).to_bits(), 0, 1f64.to_bits()]), [NAN64, ninf, 0]);
        assert_eq!(mon_f64(7, &[inf]), [NAN64]);
        assert_eq!(mon_f64(8, &[2f64.to_bits()]), [PNAN64]);
        assert_eq!(mon_f64(9, &[ninf]), [PNAN64]);
        assert_eq!(mon_f64(10, &[0f64.to_bits(), inf]), [0, (core::f64::consts::FRAC_PI_2).to_bits()]);
    }
    #[test] #[should_panic(expected = "qlean_ew_mon: no case for verb 11 at storage class 5")]
    fn a_verb_past_atan_is_refused() { mon_f64(11, &[0]); }
    #[test] #[should_panic(expected = "qlean_ew_mon: no case for verb 2 at storage class 3")]
    fn a_libm_map_at_long_is_refused() { mon_lane(2, 3, 0, &[0; 8], &mut [0; 8]); }
    // `pack_stage` then `ids_stage` returns every id, whole or cut in two at a point inside a word
    #[test] fn ids_round_trip_cut_anywhere() {
        for w in [0u32, 1, 2, 4, 8, 16, 32, 64] {
            for n in [0usize, 1, 7, 64, 65, 200] {
                let x: Vec<u64> = (0..n as u64).map(|i| if w == 0 { 0 } else { i.wrapping_mul(0x9e3779b97f4a7c15) & (if w == 64 { !0 } else { (1 << w) - 1 }) }).collect();
                let mut p = vec![0u8; ids_len(n, w)];
                let nb = if matches!(w, 1 | 2 | 4) { p.len() } else { n };
                pack_stage(3, w, bytes_mut(&mut x.clone()[..]), n, 0, nb, &mut p);
                for cut in [0, n / 3, n / 2, n] {
                    let mut o = vec![0u64; n];
                    for (lo, hi) in [(0, cut), (cut, n)] { ids_stage(3, w, &p, lo, hi, bytes_mut(&mut o[..])) }
                    assert_eq!(o, x, "w {w} n {n} cut {cut}");
                }
            }
        }
    }
    #[test] fn widen_stage_cuts_a_bit_source_inside_a_byte() {
        let x = [0b1010_0110u8, 0b0000_0101];
        let mut whole = [0u8; 10 * 4];
        widen(qlean_run_c, 6, 2, 7, 9, &x, 10, &mut whole);
        let mut o = [0xAAu8; 10 * 4];
        widen_stage(6, 2, 7, 9, &x, 0, 3, &mut o);
        widen_stage(6, 2, 7, 9, &x, 3, 10, &mut o);
        assert_eq!(o, whole);
    }
}
// ---- K8: ew.rs `like_*`, `fixed_*`, `ew_cmp_syms_run` (symbol patterns, fixed-width search, symbol comparisons) ----
