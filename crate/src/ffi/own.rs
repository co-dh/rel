//! own.rs's Lean exports: the whole-file replace, the column writer and the column mapper (`own.rs` holds the file format and
//! the logic). Each is an `IO` extern, so none takes a world argument in Lean 4.28; a failure is an errno the Lean side reports
//! as `path. OS reports: <strerror>`, or the text of a refusal.
#![deny(unsafe_code)]
use crate::lean::{B, Io, O, export};
use crate::own::Fail;
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use {alloc::vec::Vec, crate::lean::{arr, boxed, ctor, sarrays_in, string}, crate::own};

pub fn answer(r: Result<O, Fail>, path: B) -> O {
    match r { Ok(v) => Io::ok(v), Err(Fail::Errno(e)) => Io::errno(e, Some(path)), Err(Fail::User(w)) => Io::user(&w) }
}

export! {

    /// `Db.ownWrite`: the one column writer. `parts` are the constructor's `ByteArray`s in the order the header note of
    /// `own.rs` lists them. `IO Unit`.
    fn qlean_own_write(path: B, code: u8, attr: u8, kind: u8, count: usize, domain: B, parts: B) -> O {
        let ps: Vec<&[u8]> = parts.array().iter().map(|p| p.bytes()).collect();
        answer(own::write(path.cstr(), code, attr, kind, count as u64, domain.str_bytes(), &ps).map(|()| boxed(0)), path)
    }

    /// `Db.ownMap`: the `OwnFile` the file holds, each part a `ByteArray` inside the mapping. `IO OwnFile`, whose ctor holds
    /// `domain` and `parts` as objects, then the `USize` `count`, then the bytes `code`, `attr`, `kind`.
    fn qlean_own_map(path: B) -> O {
        answer(own::map(path.cstr()).map(|m| {
            let mut sc = [0u8; 11];
            sc[..8].copy_from_slice(&(m.n as usize).to_ne_bytes());
            sc[8..].copy_from_slice(&[m.code, m.attr, m.kind]);
            ctor(0, [string(&m.domain), arr(sarrays_in(m.map, &m.spans).into_iter())], &sc)
        }), path)
    }

}
