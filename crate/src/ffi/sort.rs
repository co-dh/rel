//! sort.rs's first fourteen Lean exports: the order tests, the inverse, the grade and ranks, the two middle elements, the
//! sorted bits and values and `xrank`, over a dense payload, an encoded column (`meta`, `pack`) or an id lane. Each
//! unpacks its arguments, sizes the answer and makes one call into `sort.rs`, which owns the loops and the pool split
//! (`c::pool()`). Lean passes `UInt8`/`Bool` as `uint8_t`, `Nat` counts as `size_t` and `Float` as `double`.
#![deny(unsafe_code)]
use crate::c::pool;
use crate::exports::coc::view;
use crate::key::{SK_BIT, SK_KINDS_N, SK_I16, SK_I32, SK_I64};
use crate::lean::{B, O, SArr, export};
use crate::sort::{self, Ksrc};
use crate::{ids, os, pod};

/// What C's `fprintf(stderr, …); exit(1)` did for a call no Lean body makes.
pub fn die(args: core::fmt::Arguments) -> ! {
    os::eprint(args).expect("qlean: stderr");
    os::exit(1)
}
/// coc.rs `sk_dense_width`'s stop: the kind is not one of the eight, or is the boolean.
fn no_dense(kind: u8) -> ! {
    die(format_args!("qlean: element kind {kind} has no dense width -- either it is not one of the {SK_KINDS_N} in QLean/Kernel/Scan.lean, or it is the boolean, whose payload is packed bits\n"))
}
/// coc.rs `sk_avail`, which exits where the kind has no dense width.
pub fn avail(kind: u8, bytes: usize) -> usize { sort::avail(kind, bytes).unwrap_or_else(|| no_dense(kind)) }
/// coc.rs `sk_dense_width`: the bytes an element of `kind` strides by in a payload, which has none for a bit.
pub fn dense_width(kind: u8) -> usize {
    if kind == SK_BIT { no_dense(kind) }
    crate::key::bytes(kind, 1).unwrap_or_else(|| no_dense(kind))
}
/// sort.rs `sk_write_width`.
pub fn width(kind: u8) -> usize {
    sort::write_width(kind).unwrap_or_else(|| die(format_args!("qlean sort: element kind {kind} is not one of the {SK_KINDS_N} in QLean/Kernel/Scan.lean\n")))
}
/// sort.rs `for_kind`: the three kinds Frame of Reference encodes.
fn for_kind(kind: u8) {
    if !matches!(kind, SK_I16 | SK_I32 | SK_I64) {
        die(format_args!("qlean_sort_ascending_foR: kind {kind} is not one Frame of Reference encodes; QLean.Column.encodes names the three that are\n"))
    }
}
/// The answer array's `Int64`s.
pub fn longs(r: &mut SArr) -> &mut [i64] { pod::cast_mut(r.bytes_mut()).expect("qlean sort: the answer array is not 8-aligned") }

/// sort.rs `order_dense`: `grade` and, under `rank`, `ranks` of a dense payload, `n` clamped to what it holds.
fn order_dense(kind: u8, desc: bool, rank: bool, n: usize, b: B) -> O {
    let p = b.bytes();
    let m = avail(kind, p.len()).min(n);
    let mut r = SArr::new(1, m * 8);
    sort::order(pool(), kind, desc, rank, p, m, longs(&mut r));
    r.into()
}
/// sort.rs `order_foR`: `order_dense` off the pack.
fn order_for(who: &str, kind: u8, desc: bool, rank: bool, n: usize, mv: B, pv: B) -> O {
    let c = view(who, mv, pv, n);
    let mut r = SArr::new(1, c.meta.n * 8);
    if c.meta.n != 0 {
        for_kind(kind);
        sort::order_enc(pool(), kind, desc, rank, &c, longs(&mut r));
    }
    r.into()
}
/// `xrank` over `n` keys of `s`, as `Int64`s.
fn xrank(s: &Ksrc, t: f64) -> O {
    let mut r = SArr::new(1, s.n * 8);
    if s.n != 0 { sort::xrank_src(s, t, longs(&mut r)) }
    r.into()
}

export! {
    /// `ascending k desc n b` is `(List.range (m-1)).all` of the adjacent comparison `keyAt` makes, with `m` the count
    /// the payload can serve.
    fn qlean_sort_ascending(kind: u8, desc: u8, strict: u8, n: usize, b: B) -> u8 {
        let p = b.bytes();
        sort::ascending(kind, desc != 0, strict != 0, p, avail(kind, p.len()).min(n)) as u8
    }

    /// `ascendingFoR k desc n metadata pack` is `ascending k desc n (Coc.decode w metadata pack n)` at `w = k.width`.
    fn qlean_sort_ascending_foR(kind: u8, desc: u8, strict: u8, n: usize, mv: B, pv: B) -> u8 {
        for_kind(kind);
        sort::ascending_enc(pool(), kind, desc != 0, strict != 0, &view("qlean_sort_ascending_foR", mv, pv, n)) as u8
    }

    /// `invert p` is, at each `i`, the first `j` with `p[j] = i`, and `m` where there is none.
    fn qlean_sort_invert(pv: B) -> O {
        let v = pv.bytes();
        let p = pod::cast::<i64>(&v[..v.len() - v.len() % 8]).expect("qlean_sort_invert: the permutation is not 8-aligned");
        let mut r = SArr::new(1, p.len() * 8);
        sort::invert(p, longs(&mut r));
        r.into()
    }

    /// `grade k desc n b` is `0 .. m-1` ordered by `keyAt k b`, ties in their original order, as little-endian `Int64`s,
    /// where `m` is `n` clamped to what the payload holds.
    fn qlean_sort_grade(kind: u8, desc: u8, n: usize, b: B) -> O { order_dense(kind, desc != 0, false, n, b) }

    /// `ranks k n b` is `invert (grade k false n b)`.
    fn qlean_sort_ranks(kind: u8, n: usize, b: B) -> O { order_dense(kind, false, true, n, b) }

    /// `gradeFoR k desc n metadata pack` is `grade k desc n (Coc.decode w metadata pack n)`.
    fn qlean_sort_grade_foR(kind: u8, desc: u8, n: usize, mv: B, pv: B) -> O {
        order_for("qlean_sort_grade_foR", kind, desc != 0, false, n, mv, pv)
    }

    /// `gradeLane desc n w ids` is `0 .. m-1` ordered by `Column.idAt ids w`, ties in their original order, `m` being
    /// `Column.idsCap ids w n`.
    fn qlean_sort_grade_lane(desc: u8, n: usize, w: usize, idsv: B) -> O {
        let p = idsv.bytes();
        let n = n.min(ids::ids_avail(p.len(), w as u32));
        let mut r = SArr::new(1, n * 8);
        sort::grade_lane(pool(), desc != 0, w as u32, p, n, longs(&mut r));
        r.into()
    }

    /// `ranksFoR k n metadata pack` is `ranks k n (Coc.decode w metadata pack n)`.
    fn qlean_sort_ranks_foR(kind: u8, n: usize, mv: B, pv: B) -> O {
        order_for("qlean_sort_ranks_foR", kind, false, true, n, mv, pv)
    }

    /// `middle k n b` is `sortValues k false n b` at positions `(m-1)/2` and `m/2`, each at the kind's width, and empty
    /// where `m` is 0.
    fn qlean_sort_middle(kind: u8, n: usize, b: B) -> O {
        let p = b.bytes();
        let m = avail(kind, p.len()).min(n);
        let mut r = SArr::new(1, if m != 0 { 2 * width(kind) } else { 0 });
        if m != 0 { sort::middle(pool(), &Ksrc { kind, p, c: None, n: m }, r.bytes_mut()) }
        r.into()
    }

    /// `middleFoR k n metadata pack` is `middle k n (Coc.decode w metadata pack n)`.
    fn qlean_sort_middle_foR(kind: u8, n: usize, mv: B, pv: B) -> O {
        let c = view("qlean_sort_middle_foR", mv, pv, n);
        let w = width(kind);
        let mut r = SArr::new(1, if c.meta.n != 0 { 2 * w } else { 0 });
        if c.meta.n != 0 { sort::middle(pool(), &Ksrc { kind, p: &[], c: Some(c), n: c.meta.n }, r.bytes_mut()) }
        r.into()
    }

    /// `sortedBits desc n b` is `sortValues .bit desc n b` packed back a bit an element.
    fn qlean_sort_bits_sorted(desc: u8, n: usize, b: B) -> O {
        let p = b.bytes();
        let m = avail(SK_BIT, p.len()).min(n);
        let mut r = SArr::new(1, m.div_ceil(8));
        sort::bits_sorted(desc != 0, m, p, r.bytes_mut());
        r.into()
    }

    /// `xrank k n b t` is `grade k false n b` inverted to ranks, each scaled by `t` and floored, as little-endian `Int64`s.
    fn qlean_sort_xrank(kind: u8, n: usize, b: B, t: f64) -> O {
        let p = b.bytes();
        xrank(&Ksrc { kind, p, c: None, n: avail(kind, p.len()).min(n) }, t)
    }

    /// `xrankFoR k n md pk t` is `xrank k n (Coc.decode w md pk n) t`.
    fn qlean_sort_xrank_foR(kind: u8, n: usize, mv: B, pv: B, t: f64) -> O {
        let c = view("qlean_sort_xrank_foR", mv, pv, n);
        xrank(&Ksrc { kind, p: &[], c: Some(c), n: c.meta.n }, t)
    }

    /// `sortValues k desc n b` is `grade k desc n b`'s permutation gathered out of `b` as `m` elements of `k`'s own width,
    /// where `m` is `n` clamped to what `b` holds.
    fn qlean_sort_values(kind: u8, desc: u8, n: usize, b: B) -> O {
        let p = b.bytes();
        let w = width(kind);
        let m = avail(kind, p.len()).min(n);
        let mut r = SArr::new(1, m * w);
        if m != 0 { sort::sort_values(kind, desc != 0, m, p, r.bytes_mut()) }
        r.into()
    }
}
