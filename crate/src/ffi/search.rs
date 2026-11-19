//! search.rs's Lean exports that moved: the finds, the membership and run-start walks over ids and bits, the operand
//! searches, the Frame-of-Reference equality walks, the id mask, and the index cell, an external object holding a value's
//! index. Each unboxes its arguments, allocates the answer and makes one call into `search.rs`, which owns the loops.
//! Lean passes `Int64` and `UInt64` as C's `uint64_t`.
#![deny(unsafe_code)]
use crate::coc::Coc;
use crate::ffi::{Form, Sink, sarray_room, sd_kept, syms_of};
use crate::lean::{B, O, SArr, export};
use crate::exports::coc::view;
use crate::search::{Kind, Blocks, Src};
use crate::{c, pod, search};
#[cfg(all(feature = "ffi", not(any(test, feature = "std"))))]
use crate::ids;


/// `x ? h` (`member` false, `Int64`s) or `x in h` (a `u1` Frame of Reference column, `Sink::bools`) at the key type `kd`,
/// over the pool.
pub fn probe(kd: Kind, h: &Blocks, x: &Blocks, member: bool) -> O {
    if member {
        // no needle, no block asks the table
        let t = (x.n > 0).then(|| search::Probe::of(kd, h, x));
        return Sink::new(x.n, 1, Form::For).bools(crate::QLEAN_COST_ARITH, &|lo, hi, o| {
            t.as_ref().expect("qlean probe: a block of needles with no table").member(x, lo, hi, o)
        })
    }
    let mut r = SArr::new(1, x.n * 8);
    search::search(c::pool(), kd, h, x, false, r.bytes_mut());
    r.into()
}
/// A run-starts answer: `f` writes the starts and the terminator into room for `n + 1` and answers how many it wrote; the array
/// is allocated at that room and sized to the count in place (the run count is not known before the pass).
pub fn starts(n: usize, f: impl FnOnce(&mut [i64]) -> usize) -> O {
    let mut r = SArr::with_capacity(1, 0, (n + 1) * 8);
    let g = f(pod::cast_mut(r.capacity_mut()).expect("qlean run_starts: the answer array is misaligned"));
    sarray_room(r.into(), g * 8)
}
/// An answer of `m` `Int64`s, to be written whole.
pub fn longs(m: usize) -> SArr { SArr::new(1, m * 8) }





export! {

    /// Spec: `findSymScalar blob offs ndl` is the least `i` whose `Column.symBytes` slice equals `ndl`, and the symbol count
    /// when there is none. `ndl` is the needle's UTF-8 bytes *without* the trailing NUL, the form `Column.symBytes` reports
    /// and `String.toUTF8` produces.
    fn qlean_search_find_sym_scalar(blob: B, offs: B, ndl: B) -> usize {
        let k = ndl.bytes();
        sd_kept(blob, offs, |probe| probe(k)).unwrap_or_else(|| search::find_sym_scalar(&syms_of(blob, offs), k))
    }







    /// Spec: `runStartsIds n w ids` is `runStarts` over an interned column's ids; the dictionary is distinct, so two
    /// elements are equal exactly when their ids are.
    fn qlean_search_run_starts_ids(n: usize, w: usize, idsv: B) -> O {
        let (ids, w) = (idsv.bytes(), w as u32);
        let n = n.min(ids::ids_avail(ids.len(), w));
        starts(n, |out| search::run_starts_ids(n, w, ids, out))
    }



    /// Spec: `findVec w float hay ndl` is `findScalar w float hay` at each element of `ndl`, as `Int64`s.
    fn qlean_search_find_vec(w: usize, is_float: u8, hay: B, ndl: B) -> O {
        let kd = search::kind_of(w, is_float != 0, "find_vec"); // before dividing by `w`
        probe(kd, &Blocks::dense(hay.bytes(), w), &Blocks::dense(ndl.bytes(), w), false)
    }

    /// Spec: `memberVec w float xs hay` is bit `i` set exactly when `findScalar w float hay xs[i]` is below `hay.size / w`,
    /// packed LSB first with the tail bits of the last byte zero.
    fn qlean_search_member_vec(w: usize, is_float: u8, xs: B, hay: B) -> O {
        let kd = search::kind_of(w, is_float != 0, "member_vec");
        probe(kd, &Blocks::dense(hay.bytes(), w), &Blocks::dense(xs.bytes(), w), true)
    }



    /// Spec: `findIdsVec hw hay hn nw ndl nn` is `findVec` at `idKeyWidth hw nw` bytes over both id payloads repacked there
    /// (nothing is repacked: a block of ids is restored at a time).
    fn qlean_search_find_ids_vec(hw: usize, hay: B, hn: usize, nw: usize, ndl: B, nn: usize) -> O {
        let (h, x) = (Blocks::ids(hay.bytes(), hn, hw as u32), Blocks::ids(ndl.bytes(), nn, nw as u32));
        probe(search::kind_of(search::ids_key_width(hw, nw), false, "find_ids_vec"), &h, &x, false)
    }

    /// Spec: `memberIdsVec xw xs xn hw hay hn` is `memberVec` at `idKeyWidth xw hw` bytes over both id payloads repacked there.
    fn qlean_search_member_ids_vec(xw: usize, xs: B, xn: usize, hw: usize, hay: B, hn: usize) -> O {
        let (x, h) = (Blocks::ids(xs.bytes(), xn, xw as u32), Blocks::ids(hay.bytes(), hn, hw as u32));
        probe(search::kind_of(search::ids_key_width(xw, hw), false, "member_ids_vec"), &h, &x, true)
    }

    /// Spec: `findBit n bits needle` is the least `i < n` with `Column.bitAt bits i = needle`, and `n` when there is none.
    fn qlean_search_find_bit(n: usize, bits: B, needle: u8) -> usize { search::find_bit(bits.bytes(), n, needle) }

    /// Spec: `findBitVec n hay m ndl` is `findBit n hay` at each of the `m` bits of `ndl`, as `Int64`s.
    fn qlean_search_find_bit_vec(n: usize, hay: B, m: usize, ndl: B) -> O {
        let mut r = longs(m);
        search::find_bit_vec(n, hay.bytes(), ndl.bytes(), m, search::i64s(r.bytes_mut()));
        r.into()
    }


    /// Spec: `memberBits m xs n hay` is bit `i` set exactly when `findBit n hay (Column.bitAt xs i)` is below `n`.
    fn qlean_search_member_bits(m: usize, xs: B, n: usize, hay: B) -> O {
        let (has, xs) = (search::bits_held(n, hay.bytes()), xs.bytes());
        Sink::new(m, 1, Form::For).bools(crate::QLEAN_COST_COPY, &|lo, hi, o| search::member_bits_at(has, xs, lo, hi, o))
    }

    /// Spec: `whereBits n bits` is the ascending indices `i < n` with `Column.bitAt bits i`, as `Int64`s; two passes, as
    /// only the first can say how long the answer is.
    fn qlean_search_where_bits(n: usize, bits: B) -> O {
        let b = bits.bytes();
        let mut r = longs(search::where_count(n, b));
        search::where_bits(n, b, search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `findScalar w float hay needle` is the least `i < hay.size / w` whose key equals `needle`'s, and
    /// `hay.size / w` when there is none.
    fn qlean_search_find_scalar(w: usize, is_float: u8, hay: B, needle: u64) -> usize { search::find_scalar(w, is_float != 0, hay.bytes(), needle) }








    /// Spec: `binBytes w float signed right hay keys` is, for each element `k` of `keys`, the partition point `p` of the
    /// halving that advances past `key hay[mid] <= key k` when `right` is false and past `<` when it is true; written out as
    /// `p - 1` for `bin` and `p` for `binr`, as `Int64`s.
    fn qlean_search_bin(w: usize, is_float: u8, is_signed: u8, right: u8, hayv: B, keysv: B) -> O {
        let (hay, keys) = (hayv.bytes(), keysv.bytes());
        let m = keys.len() / w;
        let mut r = longs(m);
        search::bin(c::pool(), w, is_float != 0, is_signed != 0, right != 0, hay, None, (hay.len() / w) as i64, &keys[..w * m], None, m,
                    search::i64s(r.bytes_mut()));
        r.into()
    }











    /// Spec: `runStarts w float hay` is the ascending indices `i` where `key hay[i]` differs from `key hay[i-1]`, with `0`
    /// first and the element count last, as `Int64`s. An empty payload answers `,0`.
    fn qlean_search_run_starts(w: usize, is_float: u8, hayv: B) -> O {
        let o = Blocks::dense(hayv.bytes(), w);
        starts(o.n, |out| search::run_starts(&o, w, is_float != 0, out))
    }



    /// Spec: `runStartsBits n bits` is `runStarts` over `n` booleans packed LSB first, a byte past the end reading `0` as
    /// `Column.bitAt` does.
    fn qlean_search_run_starts_bits(n: usize, bitsv: B) -> O { starts(n, |out| search::run_starts_bits(n, bitsv.bytes(), out)) }




}


export! {












}
/// `binRows` over a haystack dense or encoded: `bounds` and `gids` are `Int64`s, `order` 64-bit rows (empty: none).
pub fn bin_rows(w: usize, is_float: bool, is_signed: bool, right: bool, hay: &[u8], enc: Option<&Coc>, keysv: B, orderv: B, boundsv: B, gidsv: B, miss: u64) -> O {
    fn words<'a>(v: B<'a>) -> &'a [i64] { let b = v.bytes(); pod::cast::<i64>(&b[..b.len() / 8 * 8]).expect("qlean bin_rows: a bounds or gids array is misaligned") }
    let keys = keysv.bytes();
    let m = keys.len() / w;
    let mut r = longs(m);
    search::bin_rows(c::pool(), w, is_float, is_signed, right, hay, enc, &keys[..w * m], orderv.bytes(), words(boundsv), words(gidsv), miss as i64, m,
                     search::i64s(r.bytes_mut()));
    r.into()
}
/// `needles ? hay` (`bits` false: `out` is `8 * m` bytes of `Int64`s) or `needles in hay` (bits, `out` zeroed) for symbol
/// columns: through the haystack's kept hash where it is an interned dictionary that keeps one (`m` probes, no table built),
/// else `search::sym_search`.
pub fn sym_search(bits: bool, nb: B, no: B, hb: B, ho: B, out: &mut [u8]) {
    let (nd, h) = (syms_of(nb, no), syms_of(hb, ho));
    let (m, n) = (nd.count(), h.count());
    if m == 0 { return }
    let kept = sd_kept(hb, ho, |probe| for j in 0..m { search::sym_put(bits, out, n, j, probe(nd.at(j))) });
    if kept.is_none() { search::sym_search(bits, &nd, &h, out) }
}
/// The operand `operand w metadata pack n`: the payload `pack` when `metadata` is empty, and `Coc.decode w metadata pack n`
/// otherwise.
pub fn opnd_of<'a>(who: &str, mv: B<'a>, pv: B<'a>, n: usize, w: usize) -> Blocks<'a> {
    if mv.bytes().is_empty() { return Blocks::dense(pv.bytes(), w) }
    let c = view(who, mv, pv, n);
    Blocks::new(Src::For(c), c.meta.n)
}
