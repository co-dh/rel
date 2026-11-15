#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), structural.c: bit helpers and the encoded-column readers (A34), the encoder sources of reverse,
//! cycle, shift and concat (A35), concat of encoded columns (A36), gathers (A37–A38), cycles, concats and
//! enumerations (A39), the symbol dictionary table (A40), dictionary concat (A41a), `til` and `scatter` (A41b).
//! The `qlean_structural_*` entries and the `sd_*` dictionary cache (which holds `lean_object`s) stay C (§1).
//! An encoder source (`coc_fill`, `coc_hint`, `coc_ints`, coc.h:2001-2018) is a Rust fn here over views; its C
//! callback keeps a one-line body that unpacks its `ctx` and calls the `qrs_*` shim.

use crate::alp::Cocf;
use crate::c::Runner;
use crate::coc::Coc;
use crate::sym::{sym_eq, sym_hash, Syms};

// ---- A34: structural.c:56-374 ----
/// structural.c:56 `bit_set`
pub fn bit_set(out: &mut [u8], i: usize) { unimplemented!("A34: bit_set") }
/// structural.c:72 `bits64_at`: 64 bits from bit `i`, zeros past the end.
pub fn bits64_at(b: &[u8], i: usize) -> u64 { unimplemented!("A34: bits64_at") }
/// structural.c:84 `or_bits`: the low `cnt` bits of `w` or-ed in at bit `at`.
pub fn or_bits(out: &mut [u8], at: usize, w: u64, cnt: usize) { unimplemented!("A34: or_bits") }
/// structural.c:99 `copy_bits`: `len` bits of `b` from bit `from` to bit `at` of `out`.
pub fn copy_bits(out: &mut [u8], at: usize, b: &[u8], from: usize, len: usize) { unimplemented!("A34: copy_bits") }
/// structural.c:106 `set_bits`
pub fn set_bits(out: &mut [u8], at: usize, len: usize) { unimplemented!("A34: set_bits") }
/// structural.c:112 `bitrev64`
pub fn bitrev64(x: u64) -> u64 { unimplemented!("A34: bitrev64") }
/// structural.c:194 `rev_fields`: a byte's `w`-bit fields reversed.
pub fn rev_fields(x: u8, w: u8) -> u8 { unimplemented!("A34: rev_fields") }
/// structural.c:210 `rev_block`: a full block's `w`-bit residuals reversed.
pub fn rev_block(dp: &mut [u8], sp: &[u8], w: u8) { unimplemented!("A34: rev_block") }
/// structural.c:225 `reverse_foR_run`: every block's residuals reversed into `pack` (the moved column's), threaded.
pub fn reverse_enc(run: Runner, c: &Coc, pack: &mut [u8]) { unimplemented!("A34: reverse_foR_run") }
/// structural.c:320 `trailer_ok`: `c`'s trailer fits `n` elements of `w` bytes (`alp`: an ALP column's).
pub fn trailer_ok(c: &Coc, n: usize, w: usize, alp: bool) -> bool { unimplemented!("A34: trailer_ok") }
/// structural.c:327 `res_bytes`: block `s`'s residuals as whole bytes, from the pack or restored into `buf`.
pub fn res_bytes<'b>(c: &Coc<'b>, s: usize, buf: &'b mut [u8]) -> &'b [u8] { unimplemented!("A34: res_bytes") }
/// structural.c:343 `unpack_run`: elements `lo .. lo + dst.len()` of block `s` (reversed when `rev`) into `dst`.
pub fn unpack_run(dst: &mut [i64], c: &Coc, s: usize, lo: usize, rev: bool) { unimplemented!("A34: unpack_run") }

// ---- A35: structural.c:377-610, the encoder sources ----
/// structural.c:377 `blk_count`
pub fn blk_count(n: usize, b: usize) -> usize { unimplemented!("A35: blk_count") }
/// structural.c:425 `rev_fill`: elements `i0 ..` of `reverse c` into `buf`.
pub fn rev_fill(c: &Coc, buf: &mut [i64], i0: usize) { unimplemented!("A35: rev_fill") }
/// structural.c:473 `cycle_fill`: of `m` elements rotated by `off`.
pub fn cycle_fill(c: &Coc, off: usize, m: usize, buf: &mut [i64], i0: usize) { unimplemented!("A35: cycle_fill") }
/// structural.c:478 `shift_fill`: of `c` shifted by `k`, `fill` entering.
pub fn shift_fill(c: &Coc, k: i64, fill: i64, buf: &mut [i64], i0: usize) { unimplemented!("A35: shift_fill") }
/// structural.c:483 `cat_fill`: of the parts `part(j)` starting at `start[j]` (`start.len()` parts).
pub fn cat_fill<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], w: usize, alp: bool, buf: &mut [i64], i0: usize) {
    unimplemented!("A35: cat_fill")
}
/// structural.c:491 `alp_run`: the decimals of elements `lo .. lo + out.len()` of block `b`.
pub fn alp_run(out: &mut [i64], f: &Cocf, b: usize, lo: usize, rev: bool) { unimplemented!("A35: alp_run") }
/// structural.c:511 `cat_fill_alp`
pub fn cat_fill_alp<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], w: usize, buf: &mut [i64], i0: usize) {
    unimplemented!("A35: cat_fill_alp")
}
/// structural.c:516 `rev_fill_alp`
pub fn rev_fill_alp(f: &Cocf, buf: &mut [i64], i0: usize) { unimplemented!("A35: rev_fill_alp") }
/// structural.c:521 `cycle_fill_alp`
pub fn cycle_fill_alp(f: &Cocf, off: usize, m: usize, buf: &mut [i64], i0: usize) { unimplemented!("A35: cycle_fill_alp") }
/// structural.c:527 `shift_fill_alp`
pub fn shift_fill_alp(f: &Cocf, k: i64, buf: &mut [i64], i0: usize) { unimplemented!("A35: shift_fill_alp") }
/// structural.c:543 `cat_hint`: block `b`'s exponent hint and patch limit `lim`; false = no hint.
pub fn cat_hint<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], b: usize, lim: &mut u32) -> bool {
    unimplemented!("A35: cat_hint")
}
/// structural.c:555 `rev_hint`
pub fn rev_hint(f: &Cocf, b: usize, lim: &mut u32) -> bool { unimplemented!("A35: rev_hint") }
/// structural.c:563 `cycle_hint`
pub fn cycle_hint(f: &Cocf, off: usize, m: usize, b: usize, lim: &mut u32) -> bool { unimplemented!("A35: cycle_hint") }
/// structural.c:572 `shift_hint`
pub fn shift_hint(f: &Cocf, k: i64, b: usize, lim: &mut u32) -> bool { unimplemented!("A35: shift_hint") }
/// structural.c:584 `alp_ints_run`: decimals `d` and exponents `ee` of elements `lo ..` of block `s`; answers the
/// block's float patches as bytes (C's `raw`).
pub fn alp_ints_run<'a>(d: &mut [i64], ee: &mut [i8], f: &Cocf<'a>, s: usize, lo: usize, rev: bool) -> &'a [u8] {
    unimplemented!("A35: alp_ints_run")
}
/// structural.c:602 `cat_ints`: block `b` of the concat as decimals; false = take the general path.
pub fn cat_ints<'a>(part: &dyn Fn(usize) -> Cocf<'a>, start: &[usize], b: usize, d: &mut [i64], ee: &mut [i8]) -> Option<&'a [u8]> {
    unimplemented!("A35: cat_ints")
}

// ---- A36: structural.c:684-760 (the rest of the concat entries is Lean glue) ----
/// structural.c:684 `cat_take`: the part holding block `b` and its block there.
pub fn cat_take(start: &[usize], b: usize) -> Option<(usize, usize)> { unimplemented!("A36: cat_take") }
/// structural.c:704 `put_res`: `v` minus `base` at `w` bits into `p` from field `lo`.
pub fn put_res(p: &mut [u8], w: u8, lo: usize, v: &[i64], base: u64) { unimplemented!("A36: put_res") }

// ---- A37: structural.c:926-1146 ----
/// structural.c:936 `qlean_structural_all_below`: every index is below `n`.
pub fn all_below(n: usize, idx: &[i64]) -> bool { unimplemented!("A37: qlean_structural_all_below") }
/// structural.c:926 `gather_run` and its entry: `src[idx[i]]` (`w` bytes) into `out`, `fill` out of range.
pub fn gather(run: Runner, w: usize, fill: u64, src: &[u8], idx: &[i64], out: &mut [u8]) { unimplemented!("A37: gather_run") }
/// structural.c:1045 `gather_foR_run`: from an encoded column.
pub fn gather_enc(run: Runner, w: usize, fill: u64, c: &Coc, idx: &[i64], out: &mut [u8]) { unimplemented!("A37: gather_foR_run") }
/// structural.c:1084 `gather_foR_idx_run`: encoded column, encoded indices (`count` of them).
pub fn gather_enc_idx(run: Runner, w: usize, fill: u64, c: &Coc, ic: &Coc, count: usize, out: &mut [u8]) {
    unimplemented!("A37: gather_foR_idx_run")
}
/// structural.c:1122 `gather_bits_run`
pub fn gather_bits(run: Runner, n: usize, bits: &[u8], idx: &[i64], out: &mut [u8]) { unimplemented!("A37: gather_bits_run") }

// ---- A38: structural.c:1278-1608 ----
/// structural.c:1278 `expand_run` and its entry: `src[i]` repeated `wv[i]` times.
pub fn expand(run: Runner, w: usize, fill: u64, src: &[u8], wv: &[i64], out: &mut [u8]) { unimplemented!("A38: expand_run") }
/// structural.c:1412 `qlean_structural_rows_of` past the unboxing: the set rows of a bitmap; answers the count.
pub fn rows_of(b: &[u8], out: &mut [i64]) -> usize { unimplemented!("A38: qlean_structural_rows_of") }
/// structural.c:1430 `qlean_structural_gather_syms`: the gathered column's blob length.
pub fn gather_syms_len(s: &Syms, idx: &[i64]) -> usize { unimplemented!("A38: qlean_structural_gather_syms") }
/// structural.c:1430: the gathered blob and its `idx.len() + 1` starts (unboxed).
pub fn gather_syms(s: &Syms, idx: &[i64], blob: &mut [u8], offs: &mut [usize]) { unimplemented!("A38: qlean_structural_gather_syms") }
/// structural.c:1477 `gather_ids_run`: ids at `w` gathered to `wout` bits.
pub fn gather_ids(run: Runner, w: u32, wout: u32, fill: u64, src: &[u8], n: usize, idx: &[i64], out: &mut [u8]) {
    unimplemented!("A38: gather_ids_run")
}
/// structural.c:1514 `gather_ids_foR_run`: encoded indices.
pub fn gather_ids_enc(run: Runner, w: u32, wout: u32, fill: u64, src: &[u8], n: usize, ic: &Coc, count: usize, out: &mut [u8]) {
    unimplemented!("A38: gather_ids_foR_run")
}
/// structural.c:1586 `qlean_structural_cycle_ids`
pub fn cycle_ids(n: usize, off: usize, m: usize, w: u32, ids: &[u8], out: &mut [u8]) { unimplemented!("A38: qlean_structural_cycle_ids") }

// ---- A39: structural.c:1792-2008 ----
/// An enumerated element as an id: `0Nj` is `nullid`, a negative index reads `0`, any other is itself (`enum_ids`
/// finds the out-of-range first in the C entry).
fn enum_id(v: i64, nullid: usize) -> u64 { if v == i64::MIN { nullid as u64 } else { v.max(0) as u64 } }
/// structural.c:1792 `qlean_structural_cycle_bits`
pub fn cycle_bits(n: usize, off: usize, m: usize, b: &[u8], out: &mut [u8]) {
    if m == 0 || n == 0 { return }
    // a run of the source up to its end at a time, the read index wrapped once per lap rather than divided
    let (mut j, mut i) = (0, off % n);
    while j < m { let len = (m - j).min(n - i); copy_bits(out, j, b, i, len); j += len; i = 0 }
}
/// structural.c:1820 `concat_run` and its entry: the parts end to end into `out`.
pub fn concat(run: Runner, parts: &[&[u8]], out: &mut [u8]) {
    let k = parts.len();
    let at: alloc::vec::Vec<usize> = core::iter::once(0).chain(parts.iter().scan(0, |t, p| { *t += p.len(); Some(*t) })).collect();
    assert_eq!(out.len(), at[k], "concat: {} output bytes for {} bytes of parts", out.len(), at[k]);
    if k == 0 { return }
    // each slice bisects the start offsets for its first part, so a slice does not walk every lap of a cycle
    crate::c::run_map(run, out, at[k], 1, crate::QLEAN_COST_COPY, 1, &|lo, hi, o: &mut [u8]| {
        let (mut i, mut j) = (0, k);
        while j - i > 1 { let m = i + (j - i) / 2; if at[m] <= lo { i = m } else { j = m } }
        while i < k && at[i] < hi {
            let (s, e) = (at[i].max(lo), at[i + 1].min(hi));
            if s < e { o[s - lo..e - lo].copy_from_slice(&parts[i][s - at[i]..e - at[i]]) }
            i += 1;
        }
    });
}
/// structural.c:1863 `qlean_structural_concat_bits`: `counts[j]` bits of `parts[j]`.
pub fn concat_bits(counts: &[usize], parts: &[&[u8]], out: &mut [u8]) {
    let mut at = 0;
    for (&cn, p) in counts.iter().zip(parts) { copy_bits(out, at, p, 0, cn); at += cn }
}
/// structural.c:1885 `enum_at`: element `i` of a payload of `have` bytes per element.
pub fn enum_at(src: &[u8], have: usize, i: usize) -> i64 {
    if i >= have { 0 } else { i64::from_le_bytes(src[i * 8..i * 8 + 8].try_into().unwrap()) }
}
/// structural.c:1898 `qlean_structural_enum_ids`: values as ids into `0 .. d` at `w` bits, `nullid` outside.
pub fn enum_ids(n: usize, d: usize, nullid: usize, w: u32, b: &[u8], out: &mut [u8]) {
    for i in 0..n { crate::ids::id_put(out, w, i, enum_id(enum_at(b, b.len() / 8, i), nullid)) }
}
/// structural.c:1924 `qlean_structural_enum_ids_for`: from an encoded column.
pub fn enum_ids_enc(n: usize, d: usize, nullid: usize, w: u32, c: &Coc, out: &mut [u8]) {
    let mut v = [0i64; crate::BLK];
    for b in 0..n.div_ceil(crate::BLK) {
        let (lo, nb) = (b * crate::BLK, crate::BLK.min(n - b * crate::BLK));
        c.decode_blk(b, nb, &mut v);
        for (i, &x) in v[..nb].iter().enumerate() { crate::ids::id_put(out, w, lo + i, enum_id(x, nullid)) }
    }
}
/// structural.c:1949 `ids_place`: `cn` ids at `w` mapped by `tab` (`nm` entries) to `wout` bits at `at`.
pub fn ids_place(out: &mut [u8], at: usize, wout: u32, cn: usize, w: u32, pp: &[u8], tab: &[usize]) {
    let val = |j: usize| tab.get(crate::ids::id_at(pp, w, j)).map_or(0, |&t| t as u64);
    if (at * wout as usize) & 7 == 0 {
        let dst = &mut out[at * wout as usize / 8..];
        for j in 0..cn { crate::ids::id_put(dst, wout, j, val(j)) }
    } else {
        // packed into its own buffer and bit-copied, so no store crosses into the part before it
        let mut tmp = alloc::vec![0u8; crate::ids::ids_bytes(cn, wout) + 1];
        for j in 0..cn { crate::ids::id_put(&mut tmp, wout, j, val(j)) }
        crate::ids::bitcopy(out, at * wout as usize, &tmp, 0, cn * wout as usize);
    }
}
/// structural.c:1969 `qlean_structural_concat_ids`: each part's ids through its map.
pub fn concat_ids(wout: u32, counts: &[usize], widths: &[u32], maps: &[&[usize]], parts: &[&[u8]], out: &mut [u8]) {
    let k = counts.len().min(parts.len());
    let mut at = 0;
    for i in 0..k {
        // the part is read at the `cn` ids `counts` claims and the `w` `widths` claims; short of that it is zeros
        let w = widths.get(i).copied().unwrap_or(0);
        let need = crate::ids::ids_bytes(counts[i], w);
        let padded;
        let pp = if parts[i].len() >= need { parts[i] } else { padded = [parts[i], &alloc::vec![0u8; need - parts[i].len()]].concat(); &padded[..] };
        ids_place(out, at, wout, counts[i], w, pp, maps.get(i).copied().unwrap_or(&[]));
        at += counts[i];
    }
}

// ---- A40: structural.c:2039-2170, the symbol dictionary's hash table ----
/// structural.c:2044 `symview`: a dictionary being extended: the base's first `d0` symbols, then new ones in `tb`
/// at the (unboxed) starts `to`.
#[derive(Clone, Copy)]
pub struct Symview<'a> { pub base: Syms<'a>, pub d0: usize, pub tb: &'a [u8], pub to: &'a [usize] }
/// structural.c:2039 `symtab` without its reference count (the `sd_*` cache's): `slot` is `mask + 1` ids + 1.
pub struct Symtab<'a> { pub cnt: usize, pub mask: usize, pub stale: usize, pub slot: &'a mut [u32] }
impl<'a> Symview<'a> {
    /// structural.c:2046 `symview_at`
    pub fn at(&self, i: usize) -> &'a [u8] {
        if i < self.d0 { return self.base.at(i) }
        let (lo, hi) = (self.to[i - self.d0], self.to[i - self.d0 + 1]);
        &self.tb[lo..hi - 1]
    }
}
/// structural.c:2053 `symtab_find`: the id of `k` among the first `d`, or `d`.
pub fn symtab_find(slot: &[u32], mask: usize, v: &Symview, d: usize, k: &[u8]) -> usize {
    let mut s = sym_hash(k) as usize & mask;
    while slot[s] != 0 {
        let e = slot[s] as usize - 1;
        if e < d && sym_eq(v.at(e), k) { return e }
        s = (s + 1) & mask;
    }
    d
}
impl<'a> Symtab<'a> {
    /// structural.c:2061 `symtab_put`
    pub fn put(&mut self, _v: &Symview, k: &[u8], id: usize) {
        let mut s = sym_hash(k) as usize & self.mask;
        while self.slot[s] != 0 { s = (s + 1) & self.mask }
        self.slot[s] = (id + 1) as u32;
    }
    /// structural.c:2069-2100 `symtab_fit`/`symtab_build` after the slots are allocated: the `cnt` entries of
    /// `v`, both areas, hashed into empty slots.
    pub fn fill(&mut self, v: &Symview) { for i in 0..self.cnt { self.put(v, v.at(i), i) } }
    /// structural.c:2105 `symtab_fork` after the allocation: `s`'s slots copied, entries at or past `d` counted stale.
    pub fn fork(&mut self, s: &[u32], d: usize) {
        // every non-empty slot is an entry of the chain or a stale one, so `s`'s count + stale is their number
        let used = s.iter().filter(|&&x| x != 0).count();
        self.slot.copy_from_slice(s);
        (self.mask, self.cnt, self.stale) = (s.len() - 1, d, used.saturating_sub(d));
    }
}

// ---- A41a: structural.c:2203-2370 ----
/// structural.c:2223 `symdict_concat`'s per-part step: the symbols of `part` from `from` interned into `t` over the
/// base `base` (`d0` entries) and the new-symbol area `tb`/`to` (the starts, `to[0] == 0`), each one's id into
/// `map`. A new symbol is appended to `tb`/`to`. The slots cannot grow here, so it returns the index it stopped at
/// when the next insert would pass half full (`symtab_fit`'s test), and `map.len()` when the part is done.
pub fn symdict_intern(t: &mut Symtab, base: &Syms, d0: usize, tb: &mut [u8], to: &mut [usize], part: &Syms,
                      map: &mut [usize], from: usize) -> usize {
    for j in from..map.len() {
        let (s, cnt) = (part.at(j), t.cnt);
        let e = symtab_find(t.slot, t.mask, &Symview { base: *base, d0, tb: &*tb, to: &*to }, cnt, s);
        if e == cnt {
            if 2 * (cnt + 1 + t.stale) > t.mask + 1 { return j }
            let at = to[cnt - d0];
            tb[at..at + s.len()].copy_from_slice(s);
            tb[at + s.len()] = 0;
            to[cnt - d0 + 1] = at + s.len() + 1;
            t.put(&Symview { base: *base, d0, tb: &*tb, to: &*to }, s, cnt);
            t.cnt = cnt + 1;
        }
        map[j] = e;
    }
    map.len()
}

// ---- A41b: structural.c:2373-2384, 3005-3030 ----
/// structural.c:2373 `til_run` and its entry: `0 .. out.len()`.
pub fn til(run: Runner, out: &mut [i64]) { unimplemented!("A41b: til_run") }
/// structural.c:3005 `qlean_structural_scatter` past the unboxing: `dst[idx[i]] = src[soff + i]` (`bcast`: `src[soff]`)
/// at `wb` bytes; false = an index out of range.
pub fn scatter(wb: usize, dst: &mut [u8], idx: &[i64], src: &[u8], soff: usize, bcast: bool) -> bool {
    unimplemented!("A41b: qlean_structural_scatter")
}


#[cfg(test)]
mod symtab_tests {
    use super::*;
    fn offs(ss: &[&[u8]]) -> (Vec<u8>, Vec<usize>) {
        let (mut b, mut o) = (Vec::new(), Vec::new());
        for s in ss { o.push(b.len() << 1 | 1); b.extend_from_slice(s); b.push(0) }
        o.push(b.len() << 1 | 1);
        (b, o)
    }
    #[test]
    fn view_find_put_fill_fork() {
        let (b, o) = offs(&[b"a", b"", b"bc"]);
        let base = Syms { blob: &b, offs: &o };
        let (tb, to) = (b"xyz\0q\0".to_vec(), vec![0usize, 4, 6]);
        let v = Symview { base, d0: 3, tb: &tb, to: &to };
        assert_eq!((v.at(0), v.at(1), v.at(2), v.at(3), v.at(4)), (&b"a"[..], &b""[..], &b"bc"[..], &b"xyz"[..], &b"q"[..]));
        let mut slot = vec![0u32; 16];
        let mut t = Symtab { cnt: 5, mask: 15, stale: 0, slot: &mut slot };
        t.fill(&v);
        for i in 0..5 { assert_eq!(symtab_find(t.slot, 15, &v, 5, v.at(i)), i) }
        assert_eq!(symtab_find(t.slot, 15, &v, 5, b"nope"), 5);
        assert_eq!(symtab_find(t.slot, 15, &v, 3, b"xyz"), 3); // at or past `d` is absent
        let s = t.slot.to_vec();
        let mut slot2 = vec![0u32; 16];
        let mut f = Symtab { cnt: 0, mask: 0, stale: 0, slot: &mut slot2 };
        f.fork(&s, 3);
        assert_eq!((f.cnt, f.mask, f.stale), (3, 15, 2));
        assert_eq!(f.slot, &s[..]);
    }
    #[test]
    fn intern_dedupes_and_stops_for_a_fit() {
        let (b, o) = offs(&[b"a", b"", b"bc"]);
        let base = Syms { blob: &b, offs: &o };
        let (pb, po) = offs(&[b"bc", b"x", b"a", b"x", b"y"]);
        let part = Syms { blob: &pb, offs: &po };
        let (mut tb, mut to) = (vec![0u8; 8], vec![0usize; 5]);
        let mut slot = vec![0u32; 16];
        let mut t = Symtab { cnt: 3, mask: 15, stale: 0, slot: &mut slot };
        t.fill(&Symview { base, d0: 3, tb: &[], to: &[] });
        let mut map = vec![0usize; 5];
        assert_eq!(symdict_intern(&mut t, &base, 3, &mut tb, &mut to, &part, &mut map, 0), 5);
        assert_eq!((t.cnt, &map[..], &to[..3], &tb[..5]), (5, &[2, 3, 0, 3, 4][..], &[0, 2, 4][..], &b"x\0y\0\0"[..]));
        // half full: 2 * (3 + 1) > 4 + 1 stops before the first new symbol
        let mut slot = vec![0u32; 4];
        let mut t = Symtab { cnt: 3, mask: 3, stale: 0, slot: &mut slot };
        t.fill(&Symview { base, d0: 3, tb: &[], to: &[] });
        let mut map = vec![0usize; 5];
        assert_eq!(symdict_intern(&mut t, &base, 3, &mut tb, &mut to, &part, &mut map, 0), 1);
        assert_eq!((t.cnt, map[0]), (3, 2));
    }
}

#[cfg(test)]
mod a39_tests {
    use super::*;
    use crate::ids::{id_at, ids_bytes};
    fn rng(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }
    fn bit(b: &[u8], i: usize) -> bool { b.get(i / 8).is_some_and(|x| x >> (i % 8) & 1 == 1) }

    #[test] fn concat_is_the_fold_of_append() {
        let mut s = 0x9E3779B97F4A7C15;
        for _ in 0..500 {
            let parts: Vec<Vec<u8>> = (0..rng(&mut s) % 12).map(|_| (0..rng(&mut s) % 40).map(|_| rng(&mut s) as u8).collect()).collect();
            let want = parts.concat();
            let ps: Vec<&[u8]> = parts.iter().map(|p| &p[..]).collect();
            let mut out = vec![0u8; want.len()];
            concat(crate::c::qlean_run_c, &ps, &mut out);
            assert_eq!(out, want);
        }
    }
    #[test] fn enum_at_reads_zero_past_the_payload() {
        let b: Vec<u8> = [5i64, -3].iter().flat_map(|x| x.to_le_bytes()).collect();
        assert_eq!((enum_at(&b, 2, 0), enum_at(&b, 2, 1), enum_at(&b, 2, 2), enum_at(&b, 2, 99)), (5, -3, 0, 0));
    }
    #[test] fn enum_ids_nulls_negatives_and_short_payload() {
        let mut s = 7;
        for w in [0u32, 1, 2, 4, 8, 16, 32, 64] {
            let vals: Vec<i64> = (0..37).map(|_| match rng(&mut s) % 5 { 0 => i64::MIN, 1 => -1, _ => (rng(&mut s) % 3) as i64 }).collect();
            let b: Vec<u8> = vals[..30].iter().flat_map(|x| x.to_le_bytes()).collect();
            let mut out = vec![0u8; ids_bytes(37, w)];
            enum_ids(37, 3, 2, w, &b, &mut out);
            for i in 0..37 {
                let v = vals.get(i).filter(|_| i < 30).copied().unwrap_or(0);
                let want = if v == i64::MIN { 2 } else { v.max(0) as u64 };
                if w != 0 { assert_eq!(id_at(&out, w, i) as u64, want & (u64::MAX >> (64 - w.min(64))), "w {w} i {i}") }
            }
        }
    }
    #[test] fn enum_ids_enc_is_enum_ids_of_the_decoded_column() {
        let n = 1500;
        let pack: Vec<u8> = (0..2 * crate::BLK * 2).map(|i| (i * 7 % 251) as u8).collect();
        let (base, z, off, width) = ([10i64, -4], [0i64; 2], [0u64, 2048], [16u8; 2]);
        let meta = crate::coc::Meta { base: &base, maxv: &z, off: &off, bsum: &z, width: &width, sumnul: 0, sumn: 0, n, nblk: 2, mblk: 2 };
        let c = Coc { meta, pack: &pack, exc: None, fdelta: None };
        let mut v = vec![0i64; 2 * crate::BLK];
        for b in 0..2 { c.decode_blk(b, crate::BLK, &mut v[b * crate::BLK..]) }
        v.truncate(n);
        let raw: Vec<u8> = v.iter().flat_map(|x| x.to_le_bytes()).collect();
        for w in [8u32, 16, 32] {
            let (mut a, mut b) = (vec![0u8; ids_bytes(n, w)], vec![0u8; ids_bytes(n, w)]);
            enum_ids(n, 1 << 20, 0, w, &raw, &mut a);
            enum_ids_enc(n, 1 << 20, 0, w, &c, &mut b);
            assert_eq!(a, b, "w {w}");
        }
    }
    #[test] fn ids_place_and_concat_ids_read_through_each_map() {
        let mut s = 11;
        for _ in 0..400 {
            let wout = [1u32, 2, 4, 8, 16, 32][rng(&mut s) as usize % 6];
            let k = rng(&mut s) as usize % 5;
            let (mut counts, mut widths, mut maps, mut raw) = (vec![], vec![], vec![], vec![]);
            for _ in 0..k {
                let w = [1u32, 2, 4, 8, 16][rng(&mut s) as usize % 5];
                let cn = rng(&mut s) as usize % 50;
                let mut p = vec![0u8; ids_bytes(cn, w)];
                for j in 0..cn { crate::ids::id_put(&mut p, w, j, rng(&mut s)) }
                counts.push(cn); widths.push(w); raw.push(p);
                maps.push((0..rng(&mut s) % 9).map(|_| rng(&mut s) as usize % (1 << wout.min(20))).collect::<Vec<usize>>());
            }
            let total: usize = counts.iter().sum();
            let mut out = vec![0u8; ids_bytes(total, wout)];
            let (mr, pr): (Vec<&[usize]>, Vec<&[u8]>) = (maps.iter().map(|m| &m[..]).collect(), raw.iter().map(|p| &p[..]).collect());
            concat_ids(wout, &counts, &widths, &mr, &pr, &mut out);
            let mut at = 0;
            for i in 0..k {
                for j in 0..counts[i] {
                    let want = maps[i].get(id_at(&raw[i], widths[i], j)).copied().unwrap_or(0);
                    assert_eq!(id_at(&out, wout, at + j), want, "wout {wout} part {i} j {j}");
                }
                at += counts[i];
            }
        }
    }
    // needs A34's `copy_bits`
    #[test] #[ignore = "A34: copy_bits is still a stub in this branch"] fn cycle_bits_and_concat_bits_match_bit_definitions() {
        let mut s = 5;
        for _ in 0..300 {
            let n = 1 + rng(&mut s) as usize % 150;
            let b: Vec<u8> = (0..n.div_ceil(8)).map(|_| rng(&mut s) as u8).collect();
            let (off, m) = (rng(&mut s) as usize % 400, rng(&mut s) as usize % 300);
            let mut out = vec![0u8; m.div_ceil(8)];
            cycle_bits(n, off % n, m, &b, &mut out);
            for j in 0..m { assert_eq!(bit(&out, j), bit(&b, (off % n + j) % n), "n {n} off {off} j {j}") }
            let counts = [rng(&mut s) as usize % 70, rng(&mut s) as usize % 70, rng(&mut s) as usize % 70];
            let parts: Vec<Vec<u8>> = counts.iter().map(|&c| (0..c.div_ceil(8)).map(|_| rng(&mut s) as u8).collect()).collect();
            let pr: Vec<&[u8]> = parts.iter().map(|p| &p[..]).collect();
            let total: usize = counts.iter().sum();
            let mut o = vec![0u8; total.div_ceil(8)];
            concat_bits(&counts, &pr, &mut o);
            let mut at = 0;
            for (i, &c) in counts.iter().enumerate() { for j in 0..c { assert_eq!(bit(&o, at + j), bit(&parts[i], j)) } at += c }
        }
    }
}
