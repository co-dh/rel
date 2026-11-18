//! gather.rs's Lean export, `Kernel.kgather` (Rel/Kernel/Gather.lean): its `foR` arguments read through coc.rs and its
//! answer written by the same `Sink` as `qlean_coc_encode`.
#![deny(unsafe_code)]
use crate::lean::export;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::{format, string::String, vec, vec::Vec}, crate::lean::{B, O, ctor, string}};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use crate::{blocks::Blocks, c::pool, codec, coc, ffi::{Form, Sink}, gather};

/// `Ext.Enc.foR`'s constructor tag: the fourth of `Ext.Enc` (Rel/Kernel/Value.lean), after `bytes bits syms`.
pub const FOR: u32 = 3;

/// `Kernel.foRWords`: the `m` raw 64-bit words of a `foR` argument, or `what` and why it does not hold them — a layout
/// `Coc.foRStd` rejects (coc.rs `std`), or another constructor.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn words(what: &str, e: B, m: usize) -> Result<Vec<u64>, String> {
    if e.tag() != FOR { return Err(format!("{what}: constructor {} is not foR", e.tag())) }
    let bad = || format!("{what}: foR layout does not hold {m} elements");
    let c = coc::view(e.field(0).bytes(), e.field(1).bytes(), m).map_err(|_| bad())?;
    if !c.std(m) { return Err(bad()) }
    let mut out = vec![0u64; m];
    codec::decode(pool(), &c, &mut out);
    Ok(out)
}

/// `Except.ok` (tag 1) of the `foR` that `Coc.encodeAt lgEnc 8` writes of `o`, or `Except.error` (tag 0) of the message.
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
fn except(r: Result<Vec<u64>, String>) -> O {
    match r {
        Ok(o) => {
            let b: Vec<u8> = o.iter().flat_map(|w| w.to_le_bytes()).collect();
            ctor(1, [Sink::new(o.len(), 8, Form::For).enc().answer(&Blocks::dense(&b, 8))], &[])
        }
        Err(e) => ctor(0, [string(&e)], &[]),
    }
}

export! {
    /// Spec: `kgather m ix n e` reads the `m` words of `ix`, then the `n` words of `e` (each `foR`, its layout whole), and
    /// answers `e[ix[i]]` for each row `i`, encoded as `Coc.encodeAt lgEnc 8` writes it; the first error met in that order
    /// is the answer, an index `>= n` among them.
    fn qlean_k_gather(m: usize, ix: B, n: usize, e: B) -> O {
        except(words("gather: ix", ix, m).and_then(|is| words("gather: e", e, n).and_then(|es| gather::words(&is, &es))))
    }
}
