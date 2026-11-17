//! c.rs's Lean export: the pool's counters, which the bench prints per row.
#![deny(unsafe_code)]
use crate::lean::{O, Io, export, nat};
use crate::pool;

export! {
    /// `poolStat k : IO Nat` (QLean/Kernel/TestSupport.lean): counter `k` of the pool (`pool::PASSES` .. `pool::WALL`),
    /// 0 for any other. An `IO` extern takes no world argument in Lean 4.28.
    fn qlean_pool_stats(k: u8) -> O { Io::ok(nat(pool::stat(k) as usize)) }
}
