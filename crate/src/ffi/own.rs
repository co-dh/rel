//! own.c's Lean exports: the whole-file replace, the column writer and the column mapper (`own.rs` holds the file format and
//! the logic). Each is an `IO` extern, so none takes a world argument in Lean 4.28; a failure is an errno the Lean side reports
//! as `path. OS reports: <strerror>`, or the text of a refusal.
#![deny(unsafe_code)]
use alloc::vec::Vec;
use crate::lean::{B, Io, O, SArr, arr, boxed, export, sarrays_in};
use crate::own::{self, Fail};

fn answer(r: Result<O, Fail>, path: B) -> O {
    match r { Ok(v) => Io::ok(v), Err(Fail::Errno(e)) => Io::errno(e, Some(path)), Err(Fail::User(w)) => Io::user(&w) }
}

export! {
    /// `Db.replaceFile`: a whole file's bytes, for every file that is not a column. `IO Unit`.
    fn qlean_file_replace(path: B, bytes: B) -> O {
        answer(own::replace(path.cstr(), &[bytes.bytes()]).map(|()| boxed(0)).map_err(Fail::Errno), path)
    }

    /// `Db.ownWrite`: the one column writer. `parts` are the constructor's `ByteArray`s in the order the header note of
    /// `own.rs` lists them. `IO Unit`.
    fn qlean_own_write(path: B, code: u8, attr: u8, kind: u8, count: usize, domain: B, parts: B) -> O {
        let ps: Vec<&[u8]> = parts.array().iter().map(|p| p.bytes()).collect();
        answer(own::write(path.cstr(), code, attr, kind, count as u64, domain.str_bytes(), &ps).map(|()| boxed(0)), path)
    }

    /// `Db.fileMap`: the header, part table and domain name copied out as element 0, then each part as a `ByteArray` inside
    /// the mapping. `IO (Array ByteArray)`.
    fn qlean_own_map(path: B) -> O {
        answer(own::map(path.cstr()).map(|m| {
            let mut head = SArr::new(1, m.head.len());
            head.bytes_mut().copy_from_slice(&m.head);
            let mut items = sarrays_in(m.map, &m.spans);
            items.insert(0, head.into());
            arr(items.into_iter())
        }), path)
    }
}
