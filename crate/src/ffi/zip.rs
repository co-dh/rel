//! zip.c's four Lean exports: a column file, compressed or plain, as `IO` results. The logic is `crate::zip`; the encoder it
//! feeds is `ffi::encode_zip`.
#![deny(unsafe_code)]
use crate::ffi::encode_zip;
use crate::lean::{B, Io, O, SArr, box_usize_o, ctor, export};
use crate::zip::{Fail, File};

/// the `IO.Error` of a failed read: the errno of a failed open names the file, any other failure is its text
fn fail(e: Fail, path: B) -> O {
    match e { Fail::Errno(n) => Io::errno(n, Some(path)), Fail::Why(w) => Io::user(&w) }
}
fn open(path: B) -> Result<File, O> { File::open(path.cstr()).map_err(|e| fail(e, path)) }

export! {
    /// `Db.fileHead`: the first 4096 bytes of the uncompressed stream, fewer when it is shorter, and the stream's length.
    /// `IO (ByteArray × USize)`.
    fn qlean_zip_head(path: B) -> O {
        let z = match open(path) { Ok(z) => z, Err(e) => return e };
        let mut o = SArr::new(1, z.head_len());
        if let Err(e) = z.head_into(o.bytes_mut()) { return fail(e, path) }
        Io::ok(ctor(0, [o.into(), box_usize_o(z.ulen())], &[]))
    }
    /// `Db.fileSize`: the uncompressed stream's length, `IO USize`; nothing is read or inflated.
    fn qlean_zip_size(path: B) -> O {
        match open(path) { Ok(z) => Io::ok(box_usize_o(z.ulen())), Err(e) => e }
    }
    /// `Db.fileBytes`: the whole uncompressed stream, `IO ByteArray`.
    fn qlean_zip_bytes(path: B) -> O {
        let z = match open(path) { Ok(z) => z, Err(e) => return e };
        let mut o = SArr::new(1, z.ulen());
        if let Err(e) = z.bytes_into(o.bytes_mut()) { return fail(e, path) }
        Io::ok(o.into())
    }
    /// `Db.fileParts`: `n` elements of `width` bytes from byte `start` of the uncompressed stream, in the form `kind` names
    /// (the encoder's SRC_*), as `IO (ByteArray × ByteArray × ByteArray)` = (meta, (body, alp)), the empty array where the
    /// form has no such part.
    fn qlean_zip_parts(path: B, start: usize, n: usize, width: usize, kind: u8) -> O {
        let mut z = match open(path) { Ok(z) => z, Err(e) => return e };
        if let Err(e) = z.region(start, n, width) { return fail(e, path) }
        let Some(p) = encode_zip(&z, n, width, kind) else { return fail(z.error(), path) };
        Io::ok(p.into_triple())
    }
}
