#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), elementwise.c: scalar helpers (A42), the two-operand verbs and comparisons (A43; `ew_val_avx` and
//! `ew_cmp_avx` are `simd::ew_val`/`simd::ew_cmp`), bit verbs and the monadic ones (A44), casts and time (A45),
//! widening (A46a), the fused chain's stage table (A46b; its runner is `c::run_chain`). `op`, `cls`, `shape` are
//! elementwise.c:86-100's `EW_*`. The `qlean_ew_*` entries unbox and allocate and stay C (§1).
use crate::c::Runner;
use crate::coc::Coc;
use crate::sym::Syms;

// ---- A42: elementwise.c:140-299 (per element: C keeps these bodies while a C caller remains) ----
/// elementwise.c:140 `ew_unsupported`: the abort naming the engine, `op` and `cls`.
pub fn ew_unsupported(engine: &str, op: u32, cls: u32) -> ! {
    // C exits 1 after this text; no_std has no exit, so the panic handler prints it and aborts
    panic!("{engine}: no case for verb {op} at storage class {cls}. The dispatch in QLean/Kernel/Elementwise.lean is the only caller and must not claim this pair; answering anything here would be a wrong column rather than a fallback.")
}
/// elementwise.c:149 `ew_width`: an element's bytes in class `cls`.
pub fn ew_width(cls: u32) -> usize {
    match cls {
        0 => 1,
        1 => 2,
        2 | 4 => 4,
        3 | 5 => 8,
        _ => panic!("qlean_ew: storage class {cls} has no dense element width"),
    }
}
// q's order on floats as two predicates: a null (a NaN) below everything, two nulls equal (elementwise.c:177)
fn lt64(x: u64, y: u64) -> bool { if f64::from_bits(x).is_nan() { !f64::from_bits(y).is_nan() } else { f64::from_bits(x) < f64::from_bits(y) } }
fn lt32(x: u32, y: u32) -> bool { if f32::from_bits(x).is_nan() { !f32::from_bits(y).is_nan() } else { f32::from_bits(x) < f32::from_bits(y) } }
/// elementwise.c:195 `ew_tol`: q's tolerant float equality.
pub fn ew_tol(x: f64, y: f64) -> bool {
    let (ax, ay) = (x.abs(), y.abs());
    (x - y).abs() < 1.0 / (1u64 << 43) as f64 * if ax < ay { ax } else { ay }
}
/// elementwise.c:203 `ew_ord64`: a double's bits as an order-preserving key.
pub fn ew_ord64(x: u64, y: u64) -> i32 { if lt64(x, y) { -1 } else if lt64(y, x) { 1 } else { 0 } }
/// elementwise.c:207 `ew_ord32`
pub fn ew_ord32(x: u32, y: u32) -> i32 { if lt32(x, y) { -1 } else if lt32(y, x) { 1 } else { 0 } }
/// elementwise.c:240 `ew_outside_long`: `f` has no long.
pub fn ew_outside_long(f: f64) -> bool { f <= -9223372036854775808.0 || f >= 9223372036854775808.0 }
/// elementwise.c:250 `ew_fdiv`: floor division, q's nulls.
pub fn ew_fdiv(x: i64, y: i64) -> i64 {
    // the caller excluded y = 0 and the null x, the one dividend whose quotient by -1 overflows
    let (q, r) = (x.wrapping_div(y), x.wrapping_rem(y));
    q - ((r ^ y) < 0 && r != 0) as i64
}
/// elementwise.c:263 `ew_magic`: a divisor's multiply-shift form.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Magic { pub m: i64, pub d: i64, pub sh: u32, pub add: bool }
/// elementwise.c:265 `ew_magic_of`; `None` where C answers 0.
pub fn magic_of(d: i64) -> Option<Magic> {
    const TWO63: u64 = 1 << 63;
    let ad = d.unsigned_abs();
    if ad < 2 { return None; }
    let t = TWO63 + ((d as u64) >> 63);
    let anc = t - 1 - t % ad;
    let (mut q1, mut r1) = (TWO63 / anc, TWO63 - TWO63 / anc * anc);
    let (mut q2, mut r2) = (TWO63 / ad, TWO63 - TWO63 / ad * ad);
    let mut p = 63u32;
    loop {
        p += 1;
        q1 = q1.wrapping_mul(2); r1 = r1.wrapping_mul(2);
        if r1 >= anc { q1 = q1.wrapping_add(1); r1 = r1.wrapping_sub(anc); }
        q2 = q2.wrapping_mul(2); r2 = r2.wrapping_mul(2);
        if r2 >= ad { q2 = q2.wrapping_add(1); r2 = r2.wrapping_sub(ad); }
        let delta = ad - r2;
        if !(q1 < delta || (q1 == delta && r1 == 0)) { break; }
    }
    let m = q2.wrapping_add(1) as i64;
    let m = if d < 0 { m.wrapping_neg() } else { m };
    // C's `add` is 1, -1 or 0; the -1 only arises for d < 0, so `fdiv_magic` reads its sign from d
    Some(Magic { m, d, sh: p - 64, add: (d > 0 && m < 0) || (d < 0 && m > 0) })
}
/// elementwise.c:293 `ew_fdiv_magic`: `ew_fdiv(x, g.d)` by the magic.
pub fn fdiv_magic(g: &Magic, x: i64) -> i64 {
    let add = if !g.add { 0 } else if g.d > 0 { x } else { x.wrapping_neg() };
    let mut q = (((g.m as i128 * x as i128) >> 64) as i64).wrapping_add(add) >> g.sh;
    q += ((q as u64) >> 63) as i64;
    let rem = x.wrapping_sub(q.wrapping_mul(g.d));
    q - ((rem ^ g.d) < 0 && rem != 0) as i64
}

// ---- A43: elementwise.c:482-1092 ----
/// elementwise.c:501 `ew_val_run` and its entry: `a op b` of class `cls` (`shape` vector/atom) into `out`, `n` long.
pub fn val(run: Runner, op: u8, cls: u8, shape: u8, nul: i64, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) {
    unimplemented!("A43: ew_val_run")
}
/// elementwise.c:539 `ew_val_foR_run`: two encoded columns, the answer dense.
pub fn val_enc(run: Runner, op: u8, cls: u8, nul: i64, a: &Coc, b: &Coc, out: &mut [u8]) { unimplemented!("A43: ew_val_foR_run") }
/// elementwise.c:562 `ew_val_foR_atom_run`: an encoded column and an atom.
pub fn val_enc_atom(run: Runner, op: u8, cls: u8, shape: u8, nul: i64, c: &Coc, atom: &[u8], out: &mut [u8]) {
    unimplemented!("A43: ew_val_foR_atom_run")
}
/// elementwise.c:820 `ew_cmp_run` and its entry: a byte per comparison.
pub fn cmp(run: Runner, op: u8, cls: u8, shape: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A43: ew_cmp_run") }
/// elementwise.c:867 `ew_low_zero_run`
pub fn low_zero(run: Runner, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A43: ew_low_zero_run") }
/// elementwise.c:888 `ew_low_zero_foR_run`
pub fn low_zero_enc(run: Runner, c: &Coc, atom: &[u8], out: &mut [u8]) { unimplemented!("A43: ew_low_zero_foR_run") }
/// elementwise.c:927 `ew_bitw_run`
pub fn bitw(run: Runner, op: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A43: ew_bitw_run") }
/// elementwise.c:970 `qlean_ew_rank_pair` past the unboxing: each symbol's rank in the merged order of `da`, `db`.
pub fn rank_pair(da: &Syms, db: &Syms, ra: &mut [i32], rb: &mut [i32]) { unimplemented!("A43: qlean_ew_rank_pair") }
/// elementwise.c:1040-1079 `ew_cmp_ids_run`, `ew_eq_ids_run` and their entry: ids at `w` compared through the
/// rank tables `ra`, `rb`; a byte each.
pub fn eq_ids(run: Runner, op: u8, shape: u8, ia: &[u8], ib: &[u8], w: u32, n: usize, ra: &[i32], rb: &[i32], out: &mut [u8]) {
    unimplemented!("A43: ew_eq_ids_run")
}

// ---- A44: elementwise.c:1569-1813 ----
/// elementwise.c:1569 `ew_bit_run` and its entry: bitmap verbs.
pub fn bit(run: Runner, op: u8, shape: u8, a: &[u8], b: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A44: ew_bit_run") }
/// elementwise.c:1665 `ew_mon_run` and its entry: the monadic verbs.
pub fn mon(run: Runner, op: u8, cls: u8, nul: i64, x: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A44: ew_mon_run") }
/// elementwise.c:1708-1765 `ew_mon_foR_run`, `ew_mon_foR_blk`: over an encoded column, the answer dense.
pub fn mon_enc(run: Runner, op: u8, cls: u8, nul: i64, c: &Coc, out: &mut [u8]) { unimplemented!("A44: ew_mon_foR_run") }
/// elementwise.c:1743 `ew_mon_fill`: the encoder source of `qlean_coc_ew_mon_enc`.
pub fn mon_fill(op: u8, cls: u8, nul: i64, c: &Coc, buf: &mut [i64], i0: usize) { unimplemented!("A44: ew_mon_fill") }
/// elementwise.c:1789 `ew_floor_run`
pub fn floor(run: Runner, cls: u8, nul: i64, x: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A44: ew_floor_run") }

// ---- A45: elementwise.c:1843-1981 ----
/// elementwise.c:1843 `ew_cast_clamp`
pub fn cast_clamp(v: i64, lo: i64, hi: i64) -> i64 { unimplemented!("A45: ew_cast_clamp") }
/// elementwise.c:1850 `ew_cast_round`: q's round half away from zero.
pub fn cast_round(x: f64) -> i64 { unimplemented!("A45: ew_cast_round") }
/// elementwise.c:1882 `ew_cast_run` and its entry: class `src` to class `dst`.
pub fn cast(run: Runner, src: u8, dst: u8, nul_in: i64, x: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A45: ew_cast_run") }
/// elementwise.c:1921 `ew_fdiv64`
pub fn fdiv64(a: i64, b: i64) -> i64 { unimplemented!("A45: ew_fdiv64") }
/// elementwise.c:1925 `ew_days_of_first`: days from 2000.01.01 to the first of month `m`.
pub fn days_of_first(m: i64) -> i64 { unimplemented!("A45: ew_days_of_first") }
/// elementwise.c:1935 `ew_month_of_days`
pub fn month_of_days(d: i64) -> i64 { unimplemented!("A45: ew_month_of_days") }
/// elementwise.c:1951 `ew_tick_run`: the time-unit conversions (`op`).
pub fn tick(run: Runner, op: u8, cls: u8, nul: i64, x: &[u8], n: usize, out: &mut [u8]) { unimplemented!("A45: ew_tick_run") }

// ---- A46a: elementwise.c:2007-2150 ----
/// elementwise.c:2007 `ew_widen_run` and its entry: class `src` widened to `dst`, nulls mapped.
pub fn widen(run: Runner, src: u8, dst: u8, nul_in: i64, nul_out: i64, x: &[u8], n: usize, out: &mut [u8]) {
    const PNAN64: u64 = 0x7ff8000000000000;
    if n > 0 && (!matches!(dst, 2..=5) || (dst != 5 && matches!(src, 4 | 5))) { ew_unsupported("qlean_ew_widen", src as u32, dst as u32) }
    // the source class is chosen outside the loop, so each pair is its own straight-line pass (elementwise.c:2023)
    fn pass<const W: usize>(src: u8, lo: usize, hi: usize, x: &[u8], o: &mut [u8], f: impl Fn(i64) -> [u8; W]) {
        let os = o.chunks_exact_mut(W);
        match src {
            6 => for (k, c) in os.enumerate() { let i = lo + k; c.copy_from_slice(&f(((x[i >> 3] >> (i & 7)) & 1) as i64)) },
            0 => for (c, &b) in os.zip(&x[lo..hi]) { c.copy_from_slice(&f(b as i64)) },
            1 => for (c, b) in os.zip(x[lo * 2..hi * 2].chunks_exact(2)) { c.copy_from_slice(&f(i16::from_le_bytes([b[0], b[1]]) as i64)) },
            2 => for (c, b) in os.zip(x[lo * 4..hi * 4].chunks_exact(4)) { c.copy_from_slice(&f(i32::from_le_bytes([b[0], b[1], b[2], b[3]]) as i64)) },
            _ => for (c, b) in os.zip(x[lo * 8..hi * 8].chunks_exact(8)) { c.copy_from_slice(&f(i64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]))) },
        }
    }
    let w = if matches!(dst, 2..=5) { ew_width(dst as u32) } else { 1 };
    crate::c::run_map(run, out, n, w, crate::QLEAN_COST_COPY, w, &|lo, hi, o: &mut [u8]| match dst {
        2 => pass(src, lo, hi, x, o, |v| (if v == nul_in { nul_out } else { v } as i32).to_le_bytes()),
        3 => pass(src, lo, hi, x, o, |v| (if v == nul_in { nul_out } else { v }).to_le_bytes()),
        4 => pass(src, lo, hi, x, o, |v| (if v == nul_in { nul_out as u32 } else { (v as f32).to_bits() }).to_le_bytes()),
        _ if src == 4 => for (c, b) in o.chunks_exact_mut(8).zip(x[lo * 4..hi * 4].chunks_exact(4)) {
            let f = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
            // a real null is q's `0n` at double width, the sign kept (elementwise.c:2070)
            let r = if f32::from_bits(f).is_nan() { ((f >> 31) as u64) << 63 | PNAN64 } else { (f32::from_bits(f) as f64).to_bits() };
            c.copy_from_slice(&r.to_le_bytes())
        },
        _ if src == 5 => o.copy_from_slice(&x[lo * 8..hi * 8]),
        _ => pass(src, lo, hi, x, o, |v| (if v == nul_in { nul_out as u64 } else { (v as f64).to_bits() }).to_le_bytes()),
    });
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

// ---- A46b: elementwise.c:2150-2310 (the stage workers stay C until `c::run_chain` calls Rust ones) ----
/// elementwise.c:2242 `ew_stage_bits`: a stage's bits per element of `a`, `b`, `o`; answers the cost.
pub fn stage_bits(engine: u32, op: u32, cls: u32, shape: u32) -> (u32, u16, u16, u16) { unimplemented!("A46b: ew_stage_bits") }
/// elementwise.c:2294 `ew_stage_fixed`: operand `left` of the stage is not re-based per tile.
pub fn stage_fixed(engine: u32, shape: u32, left: bool) -> bool { unimplemented!("A46b: ew_stage_fixed") }

#[cfg(test)]
mod a42 {
    use super::*;
    fn h(s: &str) -> u64 { u64::from_str_radix(s, 16).unwrap() }
    /// Replays vectors dumped by elementwise.c's own bodies (testdata/ew_a42.vec); `EW_A42_VEC` names a bigger dump.
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
