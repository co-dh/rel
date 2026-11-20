#![forbid(unsafe_code)]
//! The CSV reader without the Lean objects (`Rel/Kernel/Db/Csv.lean`'s `csvWords`, IO design C): the file mapped, one
//! sequential pass over its records (`lex`: the quotes of the whole file, the header, the row count, where each block of
//! rows starts), then each column's words a block at a time (`fill`, the step of the encoder's `Sink`), then the first
//! refusal in the model's order (`refusal`). Every error text is the model's, word for word.
use crate::os::{self, File, Map};
use crate::own::Fail;
use alloc::{borrow::Cow, format, string::String, vec::Vec};
use core::ffi::CStr;
use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};

/// A column as the schema declares it (`CsvCols`): header name, `QAtomicType` constructor index, the names of a
/// named-element object in declared order (empty for every other object).
pub struct Col<'a> { pub name: &'a str, pub t: u8, pub names: Vec<&'a str> }

/// The file's bytes, mapped; an empty file has no mapping (`mmap` refuses length 0).
pub fn map(path: &CStr) -> Result<Option<Map>, Fail> {
    let f = File::open(path, os::O_RDONLY | os::O_CLOEXEC, 0)?;
    let st = f.stat()?;
    if st.mode & os::S_IFMT == os::S_IFDIR { return Err(Fail::Errno(os::EISDIR)) }
    if st.size == 0 { return Ok(None) }
    Ok(Some(Map::file(&f, st.size as usize, os::PROT_READ, os::MAP_PRIVATE)?))
}

/// The physical line byte `p` is on, from 1 (`lineAt`).
fn line(b: &[u8], p: usize) -> usize { b[..p].iter().filter(|&&c| c == b'\n').count() + 1 }

/// A field as an error shows it (`shown`): printable ASCII as itself, every other byte `\xNN`, cut at 40 bytes.
pub fn shown(f: &[u8]) -> String {
    let mut s = String::new();
    for &c in f.iter().take(40) { if (32..127).contains(&c) { s.push(c as char) } else { s += &format!("\\x{c:02x}") } }
    if f.len() <= 40 { format!("'{s}'") } else { format!("'{s}' (the first 40 of {} bytes)", f.len()) }
}

/// A field: its bytes `lo .. hi` as written (inside the quotes of a quoted one), the byte after its delimiter, and
/// whether its record ends there.
pub struct Field { lo: usize, hi: usize, quoted: bool, next: usize, end: bool }

/// The field starting at byte `p` (`lex`, one field of it): quoted when it starts with `"`, where `""` is `"` and the
/// closing `"` is followed by `,` or a record end; an unquoted one ends at `,` or `\n`, its last `\r` before `\n` being the
/// `\r\n` record end. A refusal is `lex`'s, at the byte `lex` names.
fn field(b: &[u8], p: usize) -> Result<Field, String> {
    if b.get(p) == Some(&b'"') {
        let mut q = p + 1;
        loop {
            match b.get(q) {
                None => return Err(format!("a quoted field opened at line {} is not closed", line(b, p))),
                Some(b'"') if b.get(q + 1) == Some(&b'"') => q += 2,
                Some(b'"') => break,
                Some(_) => q += 1,
            }
        }
        let f = |next, end| Ok(Field { lo: p + 1, hi: q, quoted: true, next, end });
        let c = q + 1;
        match b.get(c) {
            None => f(c, true),
            Some(b',') => f(c + 1, false),
            Some(b'\n') => f(c + 1, true),
            Some(b'\r') if b.get(c + 1) == Some(&b'\n') => f(c + 2, true),
            Some(b'\r') => Err(format!("line {}: after a closing '\"' comes '\\x0d' with no '\\x0a' after it", line(b, c + 1))),
            Some(&x) => Err(format!("line {}: after a closing '\"' comes {}, not ',' or a record end", line(b, c), shown(&[x]))),
        }
    } else {
        let mut q = p;
        loop {
            match b.get(q) {
                None => return Ok(Field { lo: p, hi: q, quoted: false, next: q, end: true }),
                Some(b',') => return Ok(Field { lo: p, hi: q, quoted: false, next: q + 1, end: false }),
                Some(b'\n') => return Ok(Field { lo: p, hi: if q > p && b[q - 1] == b'\r' { q - 1 } else { q }, quoted: false, next: q + 1, end: true }),
                Some(b'"') => return Err(format!("line {}: a '\"' inside an unquoted field", line(b, q))),
                Some(_) => q += 1,
            }
        }
    }
}

/// A field's bytes as the file means them: a quoted one's `""` read as `"`.
fn content<'b>(b: &'b [u8], x: &Field) -> Cow<'b, [u8]> {
    let s = &b[x.lo..x.hi];
    if !x.quoted || !s.contains(&b'"') { return Cow::Borrowed(s) }
    let mut v = Vec::with_capacity(s.len());
    let mut i = 0;
    while i < s.len() { v.push(s[i]); i += if s[i] == b'"' { 2 } else { 1 } }
    Cow::Owned(v)
}

/// The record starting at byte `p` (`p < b.len()`): `f(k, field)` for each of its fields, then the byte after it.
fn record(b: &[u8], mut p: usize, mut f: impl FnMut(usize, &Field)) -> Result<usize, String> {
    let mut k = 0;
    loop {
        let x = field(b, p)?;
        f(k, &x);
        (k, p) = (k + 1, x.next);
        if x.end { return Ok(p) }
    }
}

/// What the sequential pass learns: the header's fields, the data record count, the byte each block of `2^lg` data
/// records starts at, and the first data record whose field count is not the schema's (row, count, first byte).
pub struct Lexed { pub n: usize, lg: u32, starts: Vec<usize>, head: Vec<Vec<u8>>, short: Option<(usize, usize, usize)> }

/// The one sequential pass (a quoted field may hold a newline, so no record can be found without the ones before it):
/// every record split once, the structure of the whole file checked before anything else is (C.4's order).
pub fn lex(b: &[u8], ncols: usize, lg: u32) -> Result<Lexed, String> {
    let mut lx = Lexed { n: 0, lg, starts: Vec::new(), head: Vec::new(), short: None };
    let (mut p, mut r) = (0, 0usize);
    while p < b.len() {
        let st = p;
        if r == 0 {
            let mut h = Vec::new();
            p = record(b, p, |_, x| h.push(content(b, x).into_owned()))?;
            lx.head = h;
        } else {
            if (r - 1) & ((1 << lg) - 1) == 0 { lx.starts.push(st) }
            let mut k = 0;
            p = record(b, p, |_, _| k += 1)?;
            if k != ncols && lx.short.is_none() { lx.short = Some((r - 1, k, st)) }
        }
        r += 1;
    }
    lx.n = r.saturating_sub(1);
    Ok(lx)
}

/// The schema's names as the errors list them (`names`).
fn names(cols: &[Col]) -> String { format!("[{}]", cols.iter().map(|c| c.name).collect::<Vec<_>>().join(", ")) }

/// The refusals of a schema before any byte (`schema`): no column, a symbol or a general column.
pub fn schema(cols: &[Col]) -> Result<(), String> {
    if cols.is_empty() { return Err("the schema has no column, and a CSV record has at least one field".into()) }
    for c in cols {
        match c.t {
            QT_SYM => return Err(format!("column '{}' is a symbol column, which waits for the own-format sym writer (D.9 step 6)", c.name)),
            QT_GENERAL => return Err(format!("column '{}' is a general column, which the own format does not hold", c.name)),
            _ => {}
        }
    }
    Ok(())
}

/// The header (`header`): its fields are the schema's names in order; refused at the first field that differs, else by
/// the field count.
pub fn header(cols: &[Col], lx: &Lexed) -> Result<(), String> {
    let h = &lx.head;
    if let Some((j, (c, f))) = cols.iter().zip(h).enumerate().find(|(_, (c, f))| c.name.as_bytes() != f.as_slice()) {
        return Err(format!("line 1: header field {j} is {}, the schema {} has '{}'", shown(f), names(cols), c.name));
    }
    if h.len() != cols.len() { return Err(format!("line 1: the header has {} fields, the schema {} has {}", h.len(), names(cols), cols.len())) }
    Ok(())
}

/// Rows `lo .. lo + out.len()` (one block of the encoder's grid) of column `c` read into `out`; a row whose field is no
/// text of the column lowers `bad` to its index and gets the word 0, which `refusal` then refuses.
pub fn fill(b: &[u8], lx: &Lexed, c: usize, col: &Col, lo: usize, out: &mut [i64], bad: &AtomicUsize) {
    let mut p = lx.starts[lo >> lx.lg];
    for (i, o) in out.iter_mut().enumerate() {
        let mut w = None;
        match record(b, p, |k, x| if k == c { w = cell(col, &content(b, x)) }) {
            Ok(q) => p = q,
            // `lex` split every record, so this is never taken; were it, `refusal` walks to this row and answers the text
            Err(_) => { bad.fetch_min(lo + i, Relaxed); return }
        }
        match w { Some(v) => *o = v as i64, None => { bad.fetch_min(lo + i, Relaxed); *o = 0 } }
    }
}

/// The first refusal of the data records in the model's order (`rows`): the first failing row, in it the field count,
/// then its first failing column. `bad[c]` is column `c`'s first failing row (`usize::MAX`: none).
pub fn refusal(b: &[u8], lx: &Lexed, cols: &[Col], bad: &[AtomicUsize]) -> Result<(), String> {
    let r = bad.iter().map(|x| x.load(Relaxed)).min().unwrap_or(usize::MAX);
    if let Some((row, k, st)) = lx.short.filter(|s| s.0 <= r) {
        return Err(format!("row {row} (line {}): {k} fields, the schema {} has {}", line(b, st), names(cols), cols.len()));
    }
    let Some(c) = bad.iter().position(|x| x.load(Relaxed) == r).filter(|_| r != usize::MAX) else { return Ok(()) };
    let mut p = lx.starts[r >> lx.lg];
    for _ in 0..r & ((1 << lx.lg) - 1) { p = record(b, p, |_, _| ())? }
    let mut f = Vec::new();
    record(b, p, |k, x| if k == c { f = content(b, x).into_owned() })?;
    Err(format!("row {r} (line {}), column '{}': expected {}, found {}", line(b, p), cols[c].name, form(&cols[c]), shown(&f)))
}

/// The writer is given `k` word columns, one per schema column (`arity`).
pub fn arity(cols: &[Col], k: usize) -> Result<(), String> {
    if k == cols.len() { Ok(()) } else { Err(format!("{k} word columns, the schema {} has {}", names(cols), cols.len())) }
}

/// The writer (`csvText`, after `csvWrite`'s checks): the header, then the `n` rows `2^lg` at a time — `load(c, lo, out)`
/// puts column `c`'s words of rows `lo ..` into `out` from its encoding, each row's cells are formatted (`text`) into the
/// chunk's bytes, and the chunk is appended to the temporary `own::replace_by` renames over `target`. The first word with
/// no text in row order, then column order (the model's), is the refusal, and `target` keeps what it held.
pub fn write(target: &CStr, cols: &[Col], n: usize, lg: u32, mut load: impl FnMut(usize, usize, &mut [u64])) -> Result<(), Fail> {
    crate::own::replace_by(target, |f| {
        let (blk, mut out, mut s) = (1usize << lg, Vec::new(), Vec::new());
        for (k, c) in cols.iter().enumerate() { if k > 0 { out.push(b',') } field_out(c.name.as_bytes(), &mut out) }
        out.push(b'\n');
        let mut ws: Vec<Vec<u64>> = cols.iter().map(|_| alloc::vec![0; blk.min(n)]).collect();
        for lo in (0..n).step_by(blk) {
            let cnt = blk.min(n - lo);
            for (c, w) in ws.iter_mut().enumerate() { load(c, lo, &mut w[..cnt]) }
            for i in 0..cnt {
                for (c, col) in cols.iter().enumerate() {
                    if c > 0 { out.push(b',') }
                    let w = ws[c][i];
                    if text(col, w, &mut s).is_none() {
                        return Err(Fail::User(format!("row {}, column '{}': the word {w} has no text as {}", lo + i, col.name, form(col))));
                    }
                    field_out(&s, &mut out);
                }
                out.push(b'\n');
            }
            f.write_all(&out)?;
            out.clear();
        }
        Ok(f.write_all(&out)?)
    })
}

/// A field as written (`field`): quoted iff it holds `,` `"` `\r` `\n`, a `"` inside doubled.
fn field_out(f: &[u8], out: &mut Vec<u8>) {
    if !f.iter().any(|c| matches!(c, b',' | b'"' | b'\r' | b'\n')) { return out.extend_from_slice(f) }
    out.push(b'"');
    for &c in f { out.push(c); if c == b'"' { out.push(b'"') } }
    out.push(b'"');
}

/// A column's word written (`cell`) into `s`: its name or its atom's text, and only if that reads back as the word.
fn text(c: &Col, w: u64, s: &mut Vec<u8>) -> Option<()> {
    s.clear();
    if c.names.is_empty() { atom_text(c.t, w, s)? } else { s.extend_from_slice(c.names.get(usize::try_from(w).ok()?)?.as_bytes()) }
    (cell(c, s) == Some(w)).then_some(())
}

/// `fmt` into the bytes `s`; a `Vec` takes every byte, so `None` is never the answer.
fn put(s: &mut Vec<u8>, a: core::fmt::Arguments) -> Option<()> {
    struct V<'a>(&'a mut Vec<u8>);
    impl core::fmt::Write for V<'_> { fn write_str(&mut self, x: &str) -> core::fmt::Result { self.0.extend_from_slice(x.as_bytes()); Ok(()) } }
    core::fmt::Write::write_fmt(&mut V(s), a).ok()
}

/// A word written at an atom (`fmtAtom`), before `text` checks that it reads back.
fn atom_text(t: u8, w: u64, s: &mut Vec<u8>) -> Option<()> {
    match t {
        QT_U1 => s.push(if w == 0 { b'0' } else { b'1' }),
        QT_U8 => s.extend_from_slice(&[HEX[(w >> 4 & 15) as usize], HEX[(w & 15) as usize]]),
        QT_CHAR => s.push(w as u8),
        QT_F32 => { let v = f32::from_bits(w as u32); float_text(s, v.is_nan(), v.is_infinite(), v == 0.0, v.is_sign_negative(), format_args!("{:e}", v.abs()))? }
        QT_F64 => { let v = f64::from_bits(w); float_text(s, v.is_nan(), v.is_infinite(), v == 0.0, v.is_sign_negative(), format_args!("{:e}", v.abs()))? }
        QT_DATE => { let (y, m, d) = civil(w as u32 as i32 as i64); put(s, format_args!("{:04}-{m:02}-{d:02}", y.max(0)))? }
        QT_DATETIME => {
            const DAY: i64 = 86_400_000_000_000;
            let x = w as i64;
            let ((y, m, d), r) = (civil(x.div_euclid(DAY)), x.rem_euclid(DAY));
            put(s, format_args!("{:04}-{m:02}-{d:02}D{:02}:{:02}:{:02}.{:09}", y.max(0), r / 3_600_000_000_000,
                r / 60_000_000_000 % 60, r / 1_000_000_000 % 60, r % 1_000_000_000))?
        }
        QT_SYM | QT_GENERAL => return None,
        t => {
            let b = 8 * crate::scan::qtype_width(t)? as u32;
            // `signed`: the low `b` bits as a two's complement integer
            put(s, format_args!("{}", ((w as i128) << (128 - b)) >> (128 - b)))?
        }
    }
    Some(())
}

const HEX: &[u8; 16] = b"0123456789abcdef";

/// A float written (`fmtFloat`): `0w`, `-0w`, `0` for a zero of either sign (which `cell` then refuses at `-0`), none at a
/// NaN; else the shortest digits that read back, nearest the value (`e` is core's `{:e}` of the magnitude, whose digits
/// are those), in the model's form (`sci`): plain for a decimal exponent in `[-5, 17)`, else `d.ddde-x`.
fn float_text(s: &mut Vec<u8>, nan: bool, inf: bool, zero: bool, neg: bool, e: core::fmt::Arguments) -> Option<()> {
    if nan { return None }
    if neg && !zero { s.push(b'-') }
    if inf { s.extend_from_slice(b"0w"); return Some(()) }
    if zero { s.extend_from_slice(b"0"); return Some(()) }
    let mut m = Vec::new();
    put(&mut m, e)?;
    let at = m.iter().position(|&c| c == b'e')?;
    let x: i32 = core::str::from_utf8(&m[at + 1..]).ok()?.parse().ok()?;
    let mut d: Vec<u8> = m[..at].iter().copied().filter(|&c| c != b'.').collect();
    while d.len() > 1 && d.last() == Some(&b'0') { d.pop(); }
    let (len, zeros) = (d.len() as i32, |s: &mut Vec<u8>, k: i32| s.extend(core::iter::repeat_n(b'0', k as usize)));
    let p = x - (len - 1);
    if (-5..17).contains(&x) {
        if p >= 0 { s.extend_from_slice(&d); zeros(s, p) }
        else if len + p > 0 { let k = (len + p) as usize; s.extend_from_slice(&d[..k]); s.push(b'.'); s.extend_from_slice(&d[k..]) }
        else { s.extend_from_slice(b"0."); zeros(s, -(len + p)); s.extend_from_slice(&d) }
    } else {
        s.push(d[0]);
        if len > 1 { s.push(b'.'); s.extend_from_slice(&d[1..]) }
        put(s, format_args!("e{x}"))?
    }
    Some(())
}

/// The day `z` days after 1970-01-01 as year, month, day (`civil`, H. Hinnant's `civil_from_days`).
fn civil(z: i64) -> (i64, i64, i64) {
    let z = z + 719468;
    let era = z.div_euclid(146097);
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let (d, m) = (doy - (153 * mp + 2) / 5 + 1, if mp < 10 { mp + 3 } else { mp - 9 });
    (yoe + era * 400 + if m <= 2 { 1 } else { 0 }, m, d)
}

/// `QAtomicType`'s constructor indices (Rel/Kernel/Value.lean's order; `scan::qtype_width` reads the same).
const QT_U1: u8 = 0;
const QT_U8: u8 = 1;
const QT_F32: u8 = 5;
const QT_F64: u8 = 6;
const QT_CHAR: u8 = 7;
const QT_SYM: u8 = 9;
const QT_DATE: u8 = 10;
const QT_DATETIME: u8 = 11;
const QT_GENERAL: u8 = 12;

/// What a column's field must be, as an error names it (`form`).
fn form(c: &Col) -> String {
    if !c.names.is_empty() { return format!("one of {}", c.names.join(", ")) }
    match c.t {
        QT_U1 => "u1: 0 or 1",
        QT_U8 => "u8: two hex digits",
        QT_CHAR => "char: one byte",
        8 => "i8: an integer from -128 to 127",
        2 => "i16: an integer from -32768 to 32767",
        3 => "i32: an integer from -2147483648 to 2147483647",
        4 => "i64: an integer from -9223372036854775808 to 9223372036854775807",
        QT_F32 => "f32: a finite decimal, 0w or -0w",
        QT_F64 => "f64: a finite decimal, 0w or -0w",
        QT_DATE => "date: YYYY-MM-DD in years 0001-9999",
        QT_DATETIME => "datetime: YYYY-MM-DDDhh:mm:ss, up to 9 fraction digits, within i64 nanoseconds of 1970-01-01",
        _ => "no text",
    }.into()
}

/// A column's field read (`readCell`): one of its names (the word is the name's index), or else a text of its atom.
fn cell(c: &Col, f: &[u8]) -> Option<u64> {
    if !c.names.is_empty() { return c.names.iter().position(|n| n.as_bytes() == f).map(|i| i as u64) }
    match c.t {
        QT_U1 => match f { b"0" => Some(0), b"1" => Some(1), _ => None },
        QT_U8 => match f { [a, b] => Some(16 * hexv(*a)? + hexv(*b)?), _ => None },
        QT_CHAR => match f { [x] => Some(*x as u64), _ => None },
        QT_F32 => float(f, 23, 8, |s| s.parse::<f32>().ok().filter(|v| v.is_finite()).map(|v| v.to_bits() as u64)),
        QT_F64 => float(f, 52, 11, |s| s.parse::<f64>().ok().filter(|v| v.is_finite()).map(f64::to_bits)),
        QT_DATE => ymd(f).map(|d| d as u64 & 0xffff_ffff),
        QT_DATETIME => stamp(f).map(|x| x as u64),
        t => {
            let w = 8 * crate::scan::qtype_width(t)? as u32;
            let (neg, v) = int(f)?;
            let lim = 1u128 << (w - 1);
            if (neg && v > lim) || (!neg && v >= lim) { return None }
            let x = if neg { (v as i128).wrapping_neg() } else { v as i128 };
            Some(x.rem_euclid(1i128 << w) as u64)
        }
    }
}

fn hexv(c: u8) -> Option<u64> { (c as char).to_digit(16).map(u64::from) }

/// `n` decimal digits as a number, held at `2^100` once past it (every caller refuses that far out).
fn digits(d: &[u8]) -> Option<u128> {
    if d.is_empty() || !d.iter().all(u8::is_ascii_digit) { return None }
    Some(d.iter().fold(0u128, |a, &c| (10 * a + (c - b'0') as u128).min(1 << 100)))
}

/// An integer `-`? digits (`intOf`): its sign and magnitude.
fn int(f: &[u8]) -> Option<(bool, u128)> {
    match f { [b'-', d @ ..] => Some((true, digits(d)?)), d => Some((false, digits(d)?)) }
}

/// A float of `mb` fraction and `eb` exponent bits (`readFloat`): `0w`, `-0w`, or a decimal `-`? digits (`.` digits)?
/// (`e`/`E` `+`? integer)? at its nearest value, ties to even (`near`, core's correctly rounded parse of the same decimal),
/// a zero of either sign `+0`, none beyond the largest finite value. The model's two shortcuts are kept: below
/// `10^-400` it is `+0`, from `10^400` none, which also bounds the exponent written for `near`.
fn float(f: &[u8], mb: u32, eb: u32, near: impl Fn(&str) -> Option<u64>) -> Option<u64> {
    let (inf, sign) = (((1u64 << eb) - 1) << mb, 1u64 << (mb + eb));
    match f { b"0w" => return Some(inf), b"-0w" => return Some(sign | inf), _ => {} }
    let (neg, f) = match f { [b'-', r @ ..] => (true, r), r => (false, r) };
    let ip = f.iter().take_while(|c| c.is_ascii_digit()).count();
    if ip == 0 { return None }
    let r = &f[ip..];
    let (fp, r) = match r {
        [b'.', t @ ..] => { let k = t.iter().take_while(|c| c.is_ascii_digit()).count(); if k == 0 { return None } (&t[..k], &t[k..]) }
        _ => (&r[..0], r),
    };
    let x: i128 = match r {
        [] => 0,
        [b'e' | b'E', t @ ..] => { let (n, v) = int(match t { [b'+', u @ ..] => u, u => u })?; if n { -(v as i128) } else { v as i128 } }
        _ => return None,
    };
    let (ds, e) = ([&f[..ip], fp].concat(), x - fp.len() as i128);
    if ds.iter().all(|&c| c == b'0') || ds.len() as i128 + e <= -400 { return Some(0) }
    if e >= 400 { return None }
    let s = format!("{}e{e}", core::str::from_utf8(&ds).ok()?);
    let b = near(&s)?;
    Some(if neg && b != 0 { sign | b } else { b })
}

/// Days since 1970-01-01 of a proleptic Gregorian day (`daysFrom`, H. Hinnant's `days_from_civil`).
fn days_from(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    era * 146097 + yoe * 365 + yoe / 4 - yoe / 100 + doy - 719468
}

fn mdays(y: i64, m: i64) -> i64 {
    match m { 2 => if y % 4 == 0 && (y % 100 != 0 || y % 400 == 0) { 29 } else { 28 }, 4 | 6 | 9 | 11 => 30, _ => 31 }
}

fn num(d: &[u8]) -> Option<i64> { digits(d).map(|v| v as i64) }

/// `YYYY-MM-DD`, a valid day of years 0001-9999, as days since 1970-01-01 (`ymd`).
fn ymd(f: &[u8]) -> Option<i64> {
    let [a, b, c, d, b'-', e, g, b'-', h, i] = *f else { return None };
    let (y, m, dd) = (num(&[a, b, c, d])?, num(&[e, g])?, num(&[h, i])?);
    if y >= 1 && (1..=12).contains(&m) && dd >= 1 && dd <= mdays(y, m) { Some(days_from(y, m, dd)) } else { None }
}

/// `YYYY-MM-DDDhh:mm:ss` with an optional `.` and 1-9 fraction digits, as nanoseconds since 1970-01-01 in i64 (`stamp`).
fn stamp(f: &[u8]) -> Option<i64> {
    let d = ymd(f.get(..10)?)?;
    let [b'D', h1, h2, b':', m1, m2, b':', s1, s2, ref r @ ..] = f[10..] else { return None };
    let (hh, mm, ss) = (num(&[h1, h2])?, num(&[m1, m2])?, num(&[s1, s2])?);
    if hh >= 24 || mm >= 60 || ss >= 60 { return None }
    let ns = match r { [] => 0, [b'.', fr @ ..] if (1..=9).contains(&fr.len()) => num(fr)? * 10i64.pow(9 - fr.len() as u32), _ => return None };
    let x = (((d as i128 * 24 + hh as i128) * 60 + mm as i128) * 60 + ss as i128) * 1_000_000_000 + ns as i128;
    i64::try_from(x).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    fn col(t: u8) -> Col<'static> { Col { name: "x", t, names: Vec::new() } }
    // the model's float cases (`CsvTest`): ties to even, zeros, underflow, the end of the range, the forms refused
    #[test] fn floats_as_the_model() {
        let c = col(QT_F64);
        let got: Vec<Option<u64>> = ["9007199254740993", "-0", "-0.0e5", "2.4e-324", "2.5e-324", "1e-99999", "1.7976931348623158e308",
            "1.7976931348623159e308", "1e99999", "1E+2", ".5", "+1", "1e", "0w", "-0w", "1e+-1"].iter().map(|s| cell(&c, s.as_bytes())).collect();
        assert_eq!(got, [Some(0x4340000000000000), Some(0), Some(0), Some(0), Some(1), Some(0), Some(0x7fefffffffffffff), None, None,
            Some(0x4059000000000000), None, None, None, Some(0x7ff0000000000000), Some(0xfff0000000000000), Some(0x3fb999999999999a)]);
        assert_eq!(cell(&col(QT_F32), b"3.4028235e38"), Some(0x7f7fffff));
        assert_eq!(cell(&col(QT_F32), b"3.5e38"), None);
    }
    #[test] fn days_and_stamps() {
        assert_eq!([b"1969-12-31", b"0001-01-01", b"9999-12-31"].map(|s| ymd(s)), [Some(-1), Some(-719162), Some(2932896)]);
        assert_eq!(ymd(b"2023-02-29"), None);
        assert_eq!(stamp(b"1969-12-31D23:59:59.999999999"), Some(-1));
        assert_eq!(stamp(b"2262-04-12D00:00:00"), None);
    }
    // the records' refusals at the model's lines, and the order: the quotes of the whole file before the header
    #[test] fn records_as_the_model() {
        let err = |s: &str| lex(s.as_bytes(), 2, 10).err();
        assert_eq!(err("a,b\n1,x\"y\n").as_deref(), Some("line 2: a '\"' inside an unquoted field"));
        assert_eq!(err("a,b\n1,\"x\n").as_deref(), Some("a quoted field opened at line 2 is not closed"));
        assert_eq!(err("a,b\n1,\"x\"y\n").as_deref(), Some("line 2: after a closing '\"' comes 'y', not ',' or a record end"));
        assert_eq!(err("a,b\n1,\"x\"\rx\n").as_deref(), Some("line 2: after a closing '\"' comes '\\x0d' with no '\\x0a' after it"));
        let lx = lex(b"a,\"b\"\r\n\"1\",\"\n\"\n2,\"\r\"\n", 2, 10).unwrap_or_else(|e| panic!("csv tests: {e}"));
        assert_eq!((lx.n, lx.head.clone(), lx.short), (2, alloc::vec![b"a".to_vec(), b"b".to_vec()], None));
        assert_eq!(shown(&[0xef, b'a']), "'\\xefa'");
    }
}
