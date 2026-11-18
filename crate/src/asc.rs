#![forbid(unsafe_code)]
//! `asc`, the stable sort (design §4, `Kernel.kasc` in Rel/Kernel/Asc.lean): rows ordered lexicographically by the order
//! codes of several key columns, ties in row order. The Lean body is an insertion sort followed by two scatters; this is
//! the fused form, an LSD radix sort, one stable counting pass per byte of each code.
use alloc::{vec, vec::Vec};

/// `Rel.Kernel.normalise` (Rel/Kernel/Search.lean): a float's `-0.0` to `0` and every NaN to the one quiet NaN.
pub fn normalise(w: usize, float: bool, v: u64) -> u64 {
    if !float { return v }
    let abs = v & ((1u64 << (8 * w - 1)) - 1);
    let inf = if w == 8 { 0x7ff0_0000_0000_0000 } else { 0x7f80_0000 };
    if abs == 0 { 0 } else if inf < abs { if w == 8 { 0xfff8_0000_0000_0000 } else { 0xffc0_0000 } } else { v }
}

/// `Rel.Kernel.ordKey`: the unsigned code whose order is q's order of the `w`-byte word `v`.
pub fn ord_key(w: usize, float: bool, signed: bool, v: u64) -> u64 {
    let mask = if w == 8 { u64::MAX } else { (1u64 << (8 * w)) - 1 };
    let top = 1u64 << (8 * w - 1);
    if float {
        let u = normalise(w, true, v & mask);
        if u & top != 0 { !u & mask } else { u | top }
    } else if signed { (v & mask) ^ top } else { v & mask }
}

/// `Kernel.ascOrd` at the `QAtomicType` constructor index `t` (Rel/Kernel/Value.lean's order): `ordKey`'s width, float
/// and signed flags at `orderKind t`; `None` at `general` (0) and `symbol` (9).
pub fn order(t: u8) -> Option<(usize, bool, bool)> {
    match t {
        1 | 2 | 8 => Some((1, false, false)),
        3 => Some((2, false, true)),
        4 | 11 | 12 | 15 | 16 | 17 => Some((4, false, true)),
        5 | 10 | 14 => Some((8, false, true)),
        6 => Some((4, true, false)),
        7 | 13 => Some((8, true, false)),
        _ => None,
    }
}

/// `Kernel.ascGrade`: `0 .. m` ordered by `keys` lexicographically, the first column the most significant, ties in row
/// order. LSD radix: a stable counting pass per byte, the last column's least significant byte first; a pass whose
/// bytes all fall in one bucket moves nothing and is skipped. Every column holds `m` codes.
pub fn grade(keys: &[Vec<u64>], m: usize) -> Vec<usize> {
    let (mut p, mut q): (Vec<usize>, Vec<usize>) = ((0..m).collect(), vec![0; m]);
    for k in keys.iter().rev() {
        for b in 0..8 {
            let d = |i: usize| (k[i] >> (8 * b)) as u8 as usize;
            let mut cnt = [0usize; 257];
            for &i in &p { cnt[d(i) + 1] += 1 }
            if cnt[1..].iter().any(|&c| c == m) { continue }
            for j in 0..256 { cnt[j + 1] += cnt[j] }
            for &i in &p { let j = d(i); q[cnt[j]] = i; cnt[j] += 1 }
            core::mem::swap(&mut p, &mut q);
        }
    }
    p
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn codes_order_as_q_does() {
        assert_eq!(ord_key(4, false, true, 5), 0x8000_0005);
        assert_eq!(ord_key(4, false, true, 0xffff_ffff), 0x7fff_ffff);
        assert_eq!(ord_key(8, false, true, u64::MAX), 0x7fff_ffff_ffff_ffff);
        // NaN below -1.0 below -0.0 = 0.0 below 1.0
        let f = |x: f64| ord_key(8, true, false, x.to_bits());
        assert!(f(f64::NAN) < f(-1.0) && f(-1.0) < f(0.0) && f(-0.0) == f(0.0) && f(0.0) < f(1.0));
    }
    #[test] fn grade_is_stable_and_lexicographic() {
        // Rel/Kernel/AscTest.lean's `lex`, its codes after the sign flip
        let s = |v: u64| v ^ (1 << 63);
        let keys = vec![[3, 1, 3, 1, u64::MAX].map(s).to_vec(), [0, 9, 0, 5, 7].map(s).to_vec()];
        assert_eq!(grade(&keys, 5), vec![4, 3, 1, 0, 2]);
        assert_eq!(grade(&[], 3), vec![0, 1, 2]);
        assert_eq!(grade(&[vec![0x300, 0x100, 0x2ff]], 3), vec![1, 2, 0]);
    }
}
