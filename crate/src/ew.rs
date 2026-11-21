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

/// `Op.roundEven` (Rel/Kernel/Op.lean) step for step: the `f64` word `x` rounded half to even from `floor64` and the gap
/// `x - floor`, a zero answer keeping `x`'s sign, a NaN itself; `core` has no `round_ties_even`.
pub fn round_even(x: u64) -> u64 {
    let v = f64::from_bits(x);
    let y = floor64(v);
    let d = v - y;
    let r = if d < 0.5 { y } else if 0.5 < d { y + 1.0 } else if floor64(y / 2.0) * 2.0 == y { y } else { y + 1.0 };
    if v.is_nan() { x } else if r == 0.0 { x & 0x8000_0000_0000_0000 } else { r.to_bits() }
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
}
#[cfg(test)]
mod a46a {
    use super::*;
}
#[cfg(test)]
mod tests_k8 {
    use super::*;
    use crate::c::qlean_run_c;
}
#[cfg(test)]
mod a46b {
    use super::*;
    // expected values are ew.rs's `ew_stage_bits` / `ew_stage_fixed` read off the C switch
}
#[cfg(test)]
mod a42 {
    use super::*;
    // the live part of the deleted `floor_bounds` (its subject `floor_lane` is gone): `floor64` at the edges the lane met
    #[test] fn floor64_edges() {
        assert_eq!([floor64(-2.5), floor64(2.5), floor64(9.2e18), floor64(9.3e18), floor64(-9.3e18), floor64(-0.0), floor64(0.0)],
                   [-3.0, 2.0, 9.2e18, 9.3e18, -9.3e18, -0.0, 0.0]);
        assert!(floor64(f64::NAN).is_nan());
        assert_eq!([floor64(f64::INFINITY), floor64(f64::NEG_INFINITY)], [f64::INFINITY, f64::NEG_INFINITY]);
        assert!(floor64(-0.0).is_sign_negative());
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

    // expected values below are the C worker's (`ew_val_run`, `ew_cmp_run` of a43be95) answers on the same inputs
    // `pow` (libm) at both float widths, the f32 one computed at double width and narrowed; a NaN operand is `0n`
}
#[cfg(test)]
mod tests44 {
    use super::*;
    use crate::c::qlean_run_c;
    use crate::coc::Meta;
    use std::vec::Vec;

}
#[cfg(test)]
mod k9 {
    use super::*;
    use crate::c::qlean_run_c;
    // expected bits are the C's own answers: `sqrt -1`, `log -1`, `tan 0w` are 0n; `asin 2`, `acos -0w` are the positive NaN
    // `pack_stage` then `ids_stage` returns every id, whole or cut in two at a point inside a word
}
// ---- K8: ew.rs `like_*`, `fixed_*`, `ew_cmp_syms_run` (symbol patterns, fixed-width search, symbol comparisons) ----
