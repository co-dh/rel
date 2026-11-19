//! seen.rs's Lean export, `Kernel.kseen` (Rel/Kernel/Seen.lean): `(type, foR)` key columns in, read as `kasc` reads them
//! (`ascCol`: `asc::order`, `for_view`), and the two `foR` answers `seen::blocks` writes.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, string::String, vec::Vec}, crate::{asc, blocks::Blocks, c::pool, seen, exports::scatter::{POS, for_view, except},
    ffi::{Form, Sink}, lean::{B, O, ctor, nat}}};

/// `kseen`'s body in its order of failure: each of `es` left to right, `ascCol`'s checks (the type, then the layout),
/// its place in `es` naming it. A `pos` key has no ties, so every row is its own group (`til n` twice).
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn kseen(n: usize, es: B) -> Result<O, String> {
    let (mut ks, mut ts, mut pos, mut l) = (Vec::new(), Vec::new(), false, es);
    while !l.is_scalar() {
        let (e, t, at) = (l.field(0), l.field(0).field(0).unbox() as u8, format!("seen: es[{}]: ", ts.len() + pos as usize));
        let o = asc::order(t).ok_or_else(|| format!("{at}asc: type {t} has no fixed-width order"))?;
        if e.field(1).tag() == POS {
            if t != 4 { return Err(format!("{at}asc: a pos column is type 4, not {t}")) }
            asc::pos_rows(n).map_err(|s| format!("{at}{s}"))?;
            pos = true;
        } else { ks.push(asc::Key::new(for_view("asc", n, e.field(1)).map_err(|s| format!("{at}{s}"))?, o)); ts.push(t) }
        l = l.field(1);
    }
    let (k, g, f) = if pos {
        let til = || Sink::new(n, 8, Form::For).enc().answer(&Blocks::pos(n));
        (n, til(), til())
    } else { seen::blocks(pool(), &ts, &ks, n)? };
    Ok(ctor(0, [nat(k), ctor(0, [g, f], &[])], &[]))
}

export! {
    /// Spec: `kseen n es` reads the `n` words of each `(type, foR)` of `es` as `kasc` does and answers `(k, g, first)`:
    /// the number of distinct rows under the order codes' equality, each row's group numbered by first occurrence, and
    /// each group's first row, both as `Coc.encode 8` writes them; the first column that does not read is the error.
    /// Rows out of order whose key range is too wide for direct addressing are the error too: a hash is not built.
    fn qlean_k_seen(n: usize, es: B) -> O { except(kseen(n, es)) }
}
