//! scatter.rs's Lean export, `Kernel.kscatter` (Rel/Kernel/Scatter.lean), and the reading of an `Enc.packed` argument
//! and the building of an `Except String Enc` answer that every design-§4 kernel export shares.
#![deny(unsafe_code)]
use alloc::{format, string::String};
use crate::lean::{B, O, SArr, ctor, export, string};
use crate::pack::{Pack, Packed};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use crate::{c::pool, scatter};

/// `Ext.Enc.packed`'s constructor tag: the eighth of `Ext.Enc` (Rel/Kernel/Value.lean), after
/// `bytes bits syms foR alp enum gen`. Its fields are `bases widths payload`, then the scalar `lg`.
pub const PACKED: u32 = 7;

/// The parts of a `packed` argument, or `what` and the constructor it has instead (`Kernel.packedWords`).
pub fn parts<'a>(what: &str, e: B<'a>) -> Result<Packed<'a>, String> {
    if e.tag() != PACKED { return Err(format!("{what}: constructor {} is not packed", e.tag())) }
    Ok(Packed { lg: e.u8_at(0), bases: e.field(0).bytes(), widths: e.field(1).bytes(), payload: e.field(2).bytes() })
}

/// A fresh `ByteArray` holding `b`.
pub fn byte_array(b: &[u8]) -> O {
    let mut a = SArr::new(1, b.len());
    a.bytes_mut().copy_from_slice(b);
    a.into()
}

/// `Except.ok (Enc.packed ..)` (tag 1) or `Except.error` (tag 0) of the message.
pub fn except(r: Result<Pack, String>) -> O {
    match r {
        Ok(p) => ctor(1, [ctor(PACKED as u8, [byte_array(&p.bases), byte_array(&p.widths), byte_array(&p.payload)], &[p.lg])], &[]),
        Err(e) => ctor(0, [string(&e)], &[]),
    }
}

export! {
    /// Spec: `kscatter m ix e n fill` reads the `m` words of `ix`, then of `e` (each `packed`, its layout whole), and answers
    /// `n` cells, `fill` but where a row `k` writes `e[k]` at `ix[k]`, the last such row winning, encoded as
    /// `Coc.packedOf lgEnc 8`; the first error met in that order is the answer, an index `>= n` among them.
    fn qlean_k_scatter(m: usize, ix: B, e: B, n: usize, fill: u64) -> O {
        let rd = |what: &str, a: B| parts(what, a).and_then(|p| scatter::unpack(pool(), what, &p, m));
        except(rd("scatter: ix", ix).and_then(|is| rd("scatter: e", e).and_then(|es| scatter::scatter(pool(), &is, &es, n, fill))))
    }
}
