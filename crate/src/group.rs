#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! `dedup`'s `groupIds` arm (sort.c:2025, `gid` given, no `cnt`) and `ids_run` (sort.c:2006): number the groups on
//! one thread, then write each element's group id threaded at the lane `ng` fixes.
use alloc::borrow::Cow;

use crate::coc::Coc;

/// The numbering's table. Borrowed when C built it (`qrs_group_fill`), owned when `number` did.
/// `Direct`: `tab[key - mn]` is the group + 1, 0 = none yet. `Hashed`: `slot` is a power of two long, `slot[s]` is
/// the group + 1 whose key `gkey[group]` hashes to `s` (`(key * PHI64) >> sh`, linear probing).
pub enum Table<'a> {
    Direct { tab: Cow<'a, [u32]>, mn: u64 },
    Hashed { slot: Cow<'a, [usize]>, gkey: Cow<'a, [u64]>, sh: u32 },
}

/// The numbering pass: groups in order of first occurrence, `first[g]` its first element; answers `ng` and the
/// table. None = an unknown kind or a misaligned `p`.
pub fn number(kind: u8, p: &[u8], n: usize, mn: u64, mx: u64, first: &mut [usize]) -> Option<(usize, Table<'static>)> {
    unimplemented!()
}

/// `ids_run`: element `i`'s group into `gid` at `lane` (8, 16, 32 or 64) bits, threaded by `c::run_map`. False =
/// an unknown kind, a misaligned `p`, or `gid` shorter than `n * lane / 8`.
pub fn fill(kind: u8, p: &[u8], n: usize, t: &Table, lane: u32, gid: &mut [u8]) -> bool { unimplemented!() }

/// `number` then `fill` at `max(8, id_width(ng))`: answers `ng`.
pub fn group_ids(kind: u8, p: &[u8], n: usize, mn: u64, mx: u64, gid: &mut [u8], first: &mut [usize])
    -> Option<usize> {
    unimplemented!()
}

/// `group_ids` over an encoded column's keys, read through `kwin::Kwin` (`qlean_sort_group_ids_foR`, sort.c:2685);
/// `mn`, `mx` from `kwin::range`.
pub fn group_ids_win(kind: u8, c: Coc, n: usize, mn: u64, mx: u64, gid: &mut [u8], first: &mut [usize]) -> usize {
    unimplemented!()
}
