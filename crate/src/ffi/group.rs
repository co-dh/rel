//! sort.rs's `distinct` and `group` families (`qlean_sort_distinct` .. `qlean_sort_parted_foR`): the first-occurrence and
//! bucketed answers over a dense payload, an encoded column (`meta`, `pack`, and ALP's `alp`) or id lanes, the group ids
//! of one column or of a pair, the segment grouping and the lane helpers. Each unpacks its arguments, sizes the answer and
//! makes one call into `group.rs` / `sort.rs`, which own the loops and the pool split (`c::pool()`).
#![deny(unsafe_code)]
use alloc::vec::Vec;
use crate::c::pool;
use crate::exports::coc::{alp_view, view};
use crate::exports::sort::{avail, dense_width, longs, width};
use crate::exports::structural::pair;
use crate::ffi::{encode_alp, encode_fill, sarray_set_size};
use crate::group::{self, Dedup};
use crate::ids::{id_width, ids_avail, ids_bytes};
use crate::key::Pass;
use crate::kwin::{self, Kwin};
use crate::lean::{B, O, SArr, arr, box_usize_o, boxed, export};
use crate::pod::{self, uninit};
use crate::{ids, sort};

fn empty() -> O { SArr::new(1, 0).into() }
fn empty_pair() -> O { pair(empty(), empty()) }
/// sort.rs `empty_bounds`: the offsets of no bucket, one `box(0)`.
fn empty_bounds() -> O { arr([boxed(0)].into_iter()) }

/// sort.rs `gather`: the `first.len()` elements of the dense `p` (`m` of `kind`) at their own width.
fn gather(kind: u8, p: &[u8], m: usize, first: &[usize]) -> O {
    let mut r = SArr::new(1, first.len() * width(kind));
    group::gather(kind, group::dense(kind, p, m), first, r.bytes_mut())
        .unwrap_or_else(|| panic!("gather: gather refused kind {kind} (impossible: outside the enum), n {m}, ng {}", first.len()));
    r.into()
}
/// sort.rs `buckets`: `(the indices bucket by bucket, the ng + 1 byte offsets that cut them)`, from the group each element fell in
/// and how many elements name each group.
fn buckets(gid: &[u32], cnt: &[u32], ng: usize) -> O {
    let mut ord = SArr::new(1, gid.len() * 8);
    let mut at = group::bucket_starts(&cnt[..ng]);
    let bnd = arr(at.iter().map(|&a| boxed(a * 8)));
    group::bucket_scatter(gid, &mut at[..ng], longs(&mut ord));
    pair(ord.into(), bnd)
}
/// sort.rs `group_answer`: `groupIds`' pair once `g` holds `m` ids at `max(8, id_width(ng))` bits and `first[..ng]` the first
/// indices: the ids packed in place to `id_width(ng)` when `pack` (else the writer already did) and the size set.
fn group_answer(mut g: SArr, m: usize, ng: usize, first: &[usize], pack: bool) -> O {
    let w = id_width(ng);
    // in place: a byte is stored after the ids it packs are read
    if pack && w < 8 { ids::pack_in_place(&mut g.capacity_mut()[..m], w, m) }
    let mut f = SArr::new(1, ng * 8);
    f.bytes_mut().copy_from_slice(pod::bytes(&first[..ng]));
    pair(sarray_set_size(g.into(), ids_bytes(m, w)), f.into())
}
/// sort.rs `group_ids_of`: `groupIds`' answer for `m` keys spanning `mn ..= mx`, `numbered` writing the ids and first indices
/// (`who` names it in the stop). The capacity is for the lane the groups can need at most, `min(span + 1, m)` of them; the size
/// is set once `ng` is known.
fn group_ids_of(kind: u8, who: &str, m: usize, mn: u64, mx: u64, numbered: impl FnOnce(&mut [u8], &mut [usize]) -> Option<usize>) -> O {
    let bound = if mx - mn < m as u64 { (mx - mn) as usize + 1 } else { m };
    let cw = id_width(bound).max(8);
    let mut g = SArr::with_capacity(1, 0, m * (cw as usize / 8));
    let mut first = uninit::<usize>(m);
    let ng = numbered(g.capacity_mut(), &mut first).unwrap_or_else(|| panic!("group_ids_of: {who} refused kind {kind} (impossible: outside the enum, SK_WIN, a misaligned payload or a short buffer), n {m}, lane {cw}"));
    group_answer(g, m, ng, &first, true)
}
/// sort.rs `pair_ids`: `groupIds` of the pair `(x[i], y[i])` over `m > 0` rows, `x` and `y` keys in `[mnx, mnx + sx]` and
/// `[mny, mny + sy]`, both overwritten. The ids are written at the lane `m` rows can need at most.
fn pair_ids(mut x: Vec<u64>, mut y: Vec<u64>, mnx: u64, sx: u64, mny: u64, sy: u64) -> O {
    let m = x.len();
    let mut g = SArr::with_capacity(1, 0, m * (id_width(m).max(8) as usize / 8));
    let mut first = uninit::<usize>(m);
    let ng = sort::pair_ids(pool(), &mut x, &mut y, mnx, sx, mny, sy, g.capacity_mut(), &mut first);
    group_answer(g, m, ng, &first, true)
}
/// sort.rs `pair_ids_narrow`: `groupIdsPairIds` where the two lanes fit a byte together. `ng` is at most the smaller of the rows
/// and the `2^(wa+wb)` codes, which bounds the width the ids are written at.
fn pair_ids_narrow(wa: u32, wb: u32, m: usize, pa: &[u8], pb: &[u8]) -> O {
    let (codes, nf) = (1usize << (wa + wb), 1usize << id_width(1 << (wa + wb)));
    let mut g = SArr::new(1, ids_bytes(m, id_width(m.min(codes))));
    g.bytes_mut().fill(0);
    // `first` is the numbering's scratch too, `min(m, nf + 1)` long
    let mut first = uninit::<usize>(m.min(nf + 1));
    let ng = sort::pair_ids_narrow(pool(), wa, wb, m, &pa[..ids_bytes(m, wa)], &pb[..ids_bytes(m, wb)], g.bytes_mut(), &mut first);
    group_answer(g, m, ng, &first, false)
}
/// The group scratch of `m` rows, the bound first: `group` numbers groups and counts buckets in `u32`.
fn scratch(m: usize) -> (Vec<usize>, Vec<u32>, Vec<u32>) {
    let first = uninit(m);
    sort::group_bound(m);
    (first, uninit(m), uninit(m))
}

export! {
    /// `distinct k n b` is the elements of `b` at `Order.firsts k m b`, at their own width.
    fn qlean_sort_distinct(kind: u8, n: usize, b: B) -> O {
        let p = b.bytes();
        let m = avail(kind, p.len()).min(n);
        if m == 0 { return empty() }
        let mut first = uninit::<usize>(m);
        let ng = group::dedup_dense(kind, p, m, None, &mut first);
        gather(kind, p, m, &first[..ng])
    }

    /// `group k n b` is `(distinct k n b, the indices concatenated bucket by bucket, the ng + 1 byte offsets that cut them)`.
    fn qlean_sort_group(kind: u8, n: usize, b: B) -> O {
        let p = b.bytes();
        let m = avail(kind, p.len()).min(n);
        if m == 0 { return pair(empty(), pair(empty(), empty_bounds())) }
        let (mut first, mut gid, mut cnt) = scratch(m);
        let ng = group::dedup_dense(kind, p, m, Some((&mut gid, &mut cnt)), &mut first);
        pair(gather(kind, p, m, &first[..ng]), buckets(&gid, &cnt, ng))
    }

    /// `groupIds k n b` is `(the group each element falls in, Order.firsts k m b)`.
    fn qlean_sort_group_ids(kind: u8, n: usize, b: B) -> O {
        let p = b.bytes();
        let m = avail(kind, p.len()).min(n);
        if m == 0 { return empty_pair() }
        let (mn, mx) = group::range_dense(kind, p, m);
        let p = group::dense(kind, p, m);
        group_ids_of(kind, "qrs_group_ids", m, mn, mx, |g, f| group::group_ids(pool(), kind, p, m, mn, mx, g, f))
    }

    /// `groupIdsPair ka kb n a b` is `groupIds` on the key pair `(a[i], b[i])`.
    fn qlean_sort_group_ids_pair(ka: u8, kb: u8, n: usize, a: B, b: B) -> O {
        let (pa, pb) = (a.bytes(), b.bytes());
        let m = avail(ka, pa.len()).min(avail(kb, pb.len())).min(n);
        if m == 0 { return empty_pair() }
        let (mut x, mut y) = (uninit::<u64>(m), uninit::<u64>(m));
        let (mnx, sx) = sort::keys_of(ka, pa, m, &mut x);
        let (mny, sy) = sort::keys_of(kb, pb, m, &mut y);
        pair_ids(x, y, mnx, sx - mnx, mny, sy - mny)
    }

    /// `groupIdsPairIds wa wb n a b` is `groupIdsPair` on the two id payloads, `a` at `wa` bits and `b` at `wb`, repacked as
    /// longs. Nothing is repacked: the ids are read as `keys_of` reads a column.
    fn qlean_sort_group_ids_pair_ids(wa: usize, wb: usize, n: usize, a: B, b: B) -> O {
        let (pa, pb) = (a.bytes(), b.bytes());
        let m = ids_avail(pa.len(), wa as u32).min(ids_avail(pb.len(), wb as u32)).min(n);
        if m == 0 { return empty_pair() }
        if wa + wb <= 8 { return pair_ids_narrow(wa as u32, wb as u32, m, pa, pb) }
        let (mut x, mut y) = (uninit::<u64>(m), uninit::<u64>(m));
        let (mnx, sx) = sort::ids_keys(&pa[..ids_bytes(m, wa as u32)], wa as u32, m, &mut x);
        let (mny, sy) = sort::ids_keys(&pb[..ids_bytes(m, wb as u32)], wb as u32, m, &mut y);
        pair_ids(x, y, mnx, sx - mnx, mny, sy - mny)
    }

    /// `rankSlices w v o` is each of `o`'s segments of `v`'s `w`-bit elements numbered by first occurrence, segments equal as
    /// sequences; empty where `w` passes 64 or the offsets do not ascend inside `v`.
    fn qlean_sort_rank_slices(w: usize, vv: B, ov: B) -> O {
        let (v, ob) = (vv.bytes(), ov.bytes());
        let o = pod::cast::<i64>(&ob[..ob.len() / 8 * 8]).expect("qlean_sort_rank_slices: the offsets are not 8-aligned");
        let no = o.len();
        let nv = if w != 0 { v.len().wrapping_mul(8) / w } else { usize::MAX };
        if w > 64 || no < 2 || o[0] < 0 || o[no - 1] < 0 || o[no - 1] as u64 > nv as u64 || o.windows(2).any(|p| p[1] < p[0]) { return empty() }
        let mut r = SArr::new(1, (no - 1) * 8);
        sort::rank_slices(w, v, o, longs(&mut r));
        r.into()
    }

    /// `groupSizes ng gid` is how many elements name each group, which is what `count … by` answers.
    fn qlean_sort_group_sizes(ng: usize, w: usize, n: usize, gid: B) -> O {
        let g = gid.bytes();
        let n = n.min(ids_avail(g.len(), w as u32));
        let mut r = SArr::new(1, ng * 8);
        sort::group_sizes(ng, w as u32, n, &g[..ids_bytes(n, w as u32)], longs(&mut r));
        r.into()
    }

    /// `groupLasts ng w n gid`, the last row each group id names, 0 for one no row names.
    fn qlean_sort_group_lasts(ng: usize, w: usize, n: usize, gid: B) -> O {
        let g = gid.bytes();
        let n = n.min(ids_avail(g.len(), w as u32));
        let mut r = SArr::new(1, ng * 8);
        sort::group_lasts(ng, w as u32, n, &g[..ids_bytes(n, w as u32)], longs(&mut r));
        r.into()
    }

    /// `idLongs n w ids`, the first `n` ids widened to longs.
    fn qlean_sort_id_longs(n: usize, w: usize, idsv: B) -> O {
        let p = idsv.bytes();
        let n = n.min(ids_avail(p.len(), w as u32));
        let mut r = SArr::new(1, n * 8);
        sort::id_longs(n, w as u32, &p[..ids_bytes(n, w as u32)], longs(&mut r));
        r.into()
    }

    /// `segIds w n offs`, a slices value's byte offsets as a grouping: each element's slice (`ng` outside every one) and each
    /// slice's first element; both empty where the offsets do not ascend or pass `n`. An offset is a byte count, so a boxed
    /// (non-scalar) `Nat` cannot occur; it declines too.
    fn qlean_sort_seg_ids(w: usize, n: usize, offs: B) -> O {
        let o = offs.array();
        let ng = o.len().saturating_sub(1);
        if w == 0 { return empty_pair() }
        for (s, a) in o.iter().enumerate() {
            if !a.is_scalar() || a.unbox() / w > n || (s != 0 && a.unbox() < o[s - 1].unbox()) { return empty_pair() }
        }
        // `ng` names no slice, so the ids span `ng + 1` values
        let iw = id_width(ng + 1);
        let (mut g, mut f) = (SArr::new(1, ids_bytes(n, iw)), SArr::new(1, ng * 8));
        g.bytes_mut().fill(0);
        ids::ids_fill(g.bytes_mut(), iw, 0, n, ng as u64);
        let fl = longs(&mut f);
        for (s, (lo, hi)) in o.windows(2).map(|p| (p[0].unbox() / w, p[1].unbox() / w)).enumerate() {
            fl[s] = lo as i64;
            ids::ids_fill(g.bytes_mut(), iw, lo, hi - lo, s as u64);
        }
        pair(g.into(), f.into())
    }

    /// `distinctFoR k n md pk` is `Coc.encode w (distinct k n (Coc.decode w md pk n))`, `w` the kind's width.
    fn qlean_sort_distinct_foR(kind: u8, n: usize, mv: B, pv: B) -> O {
        let c = view("qlean_sort_distinct_foR", mv, pv, n);
        let (m, w) = (c.meta.n, dense_width(kind));
        if m == 0 { return pair(box_usize_o(0), encode_fill(0, w, &|_: &mut [i64], _: usize| {})) }
        let mut first = uninit::<usize>(m);
        let (mn, mx) = kwin::win_range(kind, &c, false);
        let ng = Dedup { mn, mx, first: &mut first, bucket: None }.run(Kwin::new(kind, c), m);
        let first = &first[..ng];
        // the elements at `first`, which ascend, each block of the answer out of a window of its own
        pair(box_usize_o(ng), encode_fill(ng, w, &|buf: &mut [i64], i0: usize| group::distinct_fill(kind, &c, &first[i0..i0 + buf.len()], buf)))
    }

    /// `distinctALP k n md pk a` is `Coc.alpEncodeAt f32 (distinct k n (the ALP decode))`.
    fn qlean_sort_distinct_alp(kind: u8, n: usize, mv: B, pv: B, av: B) -> O {
        let f = alp_view(mv, pv, av, n);
        let (m, w) = (f.c.meta.n, if f.f32 { 4 } else { 8 });
        if m == 0 { return pair(box_usize_o(0), encode_alp(0, w, &|_: &mut [i64], _: usize| {})) }
        let mut first = uninit::<usize>(m);
        let (mn, mx) = kwin::win_range(kind, &f.c, true);
        let ng = Dedup { mn, mx, first: &mut first, bucket: None }.run(Kwin::with_alp(kind, f), m);
        let first = &first[..ng];
        pair(box_usize_o(ng), encode_alp(ng, w, &|buf: &mut [i64], i0: usize| group::distinct_fill_alp(&f, &first[i0..i0 + buf.len()], buf)))
    }

    /// `groupFoR k n md pk` is `group k n (Coc.decode w md pk n)`: read through a window, so the keys never exist whole.
    fn qlean_sort_group_foR(kind: u8, n: usize, mv: B, pv: B) -> O {
        let c = view("qlean_sort_group_foR", mv, pv, n);
        let m = c.meta.n;
        if m == 0 { return pair(empty(), pair(empty(), empty_bounds())) }
        let (mn, mx) = kwin::win_range(kind, &c, false);
        let (mut first, mut gid, mut cnt) = scratch(m);
        let ng = Dedup { mn, mx, first: &mut first, bucket: Some((&mut gid, &mut cnt)) }.run(Kwin::new(kind, c), m);
        let mut keys = SArr::new(1, ng * (dense_width(kind)));
        group::keys_gather(kind, &c, &first[..ng], keys.bytes_mut());
        pair(keys.into(), buckets(&gid, &cnt, ng))
    }

    /// `groupIdsFoR k n md pk` is `groupIds k n (Coc.decode w md pk n)`.
    fn qlean_sort_group_ids_foR(kind: u8, n: usize, mv: B, pv: B) -> O {
        let c = view("qlean_sort_group_ids_foR", mv, pv, n);
        let m = c.meta.n;
        if m == 0 { return empty_pair() }
        let (mn, mx) = kwin::win_range(kind, &c, false);
        group_ids_of(kind, "qrs_group_ids_win", m, mn, mx, |g, f| group::group_ids_win(pool(), kind, c, m, mn, mx, g, f))
    }

    /// `parted k strict n b` is `(Order.firsts k m b).length` against `m` when `strict` and against
    /// `(Order.runHeads k m b).length` otherwise.
    fn qlean_sort_parted(kind: u8, strict: u8, n: usize, b: B) -> u8 {
        let p = b.bytes();
        let n = avail(kind, p.len()).min(n);
        group::parted(kind, group::dense(kind, p, n), n, strict != 0)
            .unwrap_or_else(|| panic!("qlean sort: parted refused kind {kind} (impossible: outside the enum or a misaligned payload), n {n}")) as u8
    }

    /// `partedFoR k strict n metadata pack` is `parted k strict n (Coc.decode w metadata pack n)`.
    fn qlean_sort_parted_foR(kind: u8, strict: u8, n: usize, mv: B, pv: B) -> u8 {
        group::parted_win(kind, view("qlean_sort_parted_foR", mv, pv, n), strict != 0) as u8
    }
}
