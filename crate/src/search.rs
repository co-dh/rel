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
    // A32: expected values are search.rs's `bin_key` (1439) and `bin_step` (1483), checked against the old C by /data/tmp/qrs/A32/diff.c
    // `10 20 20 20 30 bin 20` is 3 and `binr 20` is 1 (the C comment's measurements); `bin` below every element is -1
    // the gather path: 40000 keys in a 100-wide range over 200 haystack elements, a stride-missed outlier takes the walk
    // A33: expected values are the C comments' measurements of q 4.1 (`(`s#1 1 2 2 3)?2` is 2, `?9` is 5, `?0.0` over `-0.0 0.0 1.0` is 0)
    // the walk through the ids: ranks `[10, 20, 30]`, elements `ids = [0, 1, 1, 2]` read as `10 20 20 30`, at 2 bits per id
    // two groups over the haystack `1 2 3 | 10 20`, read through `order`; rows are named by `order`, `miss` = -7
    // expected values: q (search.rs's comments): `1 1 2?1` is 0, `1 1 2?9` is 3; one NaN, one zero (search.rs)
    // an empty haystack builds nothing, and a dense payload shorter than its `n` is refused by name, never folded to an empty range
    // expected values: the C of e33ad4a (`search`): 5 needles against 3 keys (table over the haystack) and 2 against 5 (over the needles)
    // A31: expected values are search.rs's (4ebc95c) own, which `/data/tmp/qrs/A31/diff` compares on 41026 random cases;
    // the q facts are the ones QLean/Kernel/Search.lean measured
    // the index against a map from key to least position, at every id width, sizes either side of a capacity step
    // equal 64-bit keys of different symbols: the bytes decide, and a chain of them is probed past
}
// ---- K17: search.rs `coc_may_hold64`, `remap_ids_run`, the index's slots (`ix_*`) ----

// ---- A33: search.rs, 1539-1830, 2004-2099: the per-element callers of A32's walk, whole loops in Rust ----
