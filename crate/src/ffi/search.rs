//! search.c's Lean exports that moved: the finds, the membership and run-start walks over ids and bits, the operand
//! searches, the Frame-of-Reference equality walks, the id mask, and the index cell, an external object holding a value's
//! index. Each unboxes its arguments, allocates the answer and makes one call into `search.rs`, which owns the loops.
//! Lean passes `Int64` and `UInt64` as C's `uint64_t`.
#![deny(unsafe_code)]
use crate::coc::Coc;
use crate::exports::coc::{meta, view};
use crate::ffi::{sarray_room, syms_of};
use crate::exports::reduce::elems;
use crate::lean::{B, Class, Ext, Io, O, Once, SArr, Slot, apply, box_usize_o, boxed, export};
use crate::search::{Kind, Opnd, Src};
use crate::{c, ids, pod, search};

/// The needle as the signed key of a column of `w`-byte elements (`coc_needle`: its low `w` bytes, sign-extended).
fn key(w: usize, needle: u64) -> i64 { search::sext(needle, w) }

/// The operand `operand w metadata pack n`: the payload `pack` when `metadata` is empty, and `Coc.decode w metadata pack n`
/// otherwise.
fn opnd_of<'a>(who: &str, mv: B<'a>, pv: B<'a>, n: usize, w: usize) -> Opnd<'a> {
    if mv.bytes().is_empty() { return Opnd::dense(pv.bytes(), w) }
    let c = view(who, mv, pv, n);
    Opnd { n: c.meta.n, src: Src::Enc(c) }
}
/// `x ? h` (`member` false, `Int64`s) or `x in h` (bits) at the key type `kd`, over the pool.
fn probe(kd: Kind, h: &Opnd, x: &Opnd, member: bool) -> O {
    let mut r = SArr::new(1, if member { x.n.div_ceil(8) } else { x.n * 8 });
    search::search(c::pool(), kd, h, x, member, r.bytes_mut());
    r.into()
}
/// The encoded column `metadata`, `pack` and `n` name, or `None` where `metadata` is empty and the operand is the payload.
fn enc<'a>(who: &str, mv: B<'a>, pv: B<'a>, n: usize) -> Option<Coc<'a>> { (!mv.bytes().is_empty()).then(|| view(who, mv, pv, n)) }
/// `binRows` over a haystack dense or encoded: `bounds` and `gids` are `Int64`s, `order` 64-bit rows (empty: none).
fn bin_rows(w: usize, is_float: bool, is_signed: bool, right: bool, hay: &[u8], enc: Option<&Coc>, keysv: B, orderv: B, boundsv: B, gidsv: B, miss: u64) -> O {
    fn words<'a>(v: B<'a>) -> &'a [i64] { let b = v.bytes(); pod::cast::<i64>(&b[..b.len() / 8 * 8]).expect("qlean bin_rows: a bounds or gids array is misaligned") }
    let keys = keysv.bytes();
    let m = keys.len() / w;
    let mut r = longs(m);
    search::bin_rows(c::pool(), w, is_float, is_signed, right, hay, enc, &keys[..w * m], orderv.bytes(), words(boundsv), words(gidsv), miss as i64, m,
                     search::i64s(r.bytes_mut()));
    r.into()
}
/// A run-starts answer: `f` writes the starts and the terminator into room for `n + 1` and answers how many it wrote; the array
/// is allocated at that room and sized to the count in place (the run count is not known before the pass).
fn starts(n: usize, f: impl FnOnce(&mut [i64]) -> usize) -> O {
    let mut r = SArr::with_capacity(1, 0, (n + 1) * 8);
    let g = f(pod::cast_mut(r.capacity_mut()).expect("qlean run_starts: the answer array is misaligned"));
    sarray_room(r.into(), g * 8)
}
/// An answer of `m` `Int64`s, to be written whole.
fn longs(m: usize) -> SArr { SArr::new(1, m * 8) }

/// `IndexCell.ready` lives in `QLean/Value.lean`, below every kernel the index is built from, so the builder reaches
/// it through this slot: `Kernel.Index` registers `Index.build` at module initialisation. A slot rather than a
/// forward-declared `@[export]` because each precompiled module is its own shared object, and `Value`'s would not
/// load with the symbol unresolved.
static BUILDER: Slot = Slot::new();
static EXTENDER: Slot = Slot::new();

/// `IndexCell`: the `Option Index` once built (empty before), and the bare value until then. A cell is built when it
/// is made; `v` is kept where no builder was registered yet -- a value made while the modules initialise -- and for a
/// keyed table's key, and is built on its first lookup. `ix` is set once, by compare-and-swap, so two racing builds
/// keep one answer and drop the other.
struct Cell { v: Option<O>, ix: Once, a: u8 }
impl Ext for Cell {
    fn foreach(&self, f: B<'_>) {
        if let Some(v) = &self.v { drop(apply(f.to_owned(), [v.borrow().to_owned()])) }
        if let Some(ix) = self.ix.get() { drop(apply(f.to_owned(), [ix.to_owned()])) }
    }
}
static CELL: Class<Cell> = Class::new();

/// The index `c` holds, built now if `c` was made before a builder was registered; `none` (box 0) when there is
/// nothing to build from.
fn ready(cell: B, c: &Cell) -> O {
    if let Some(ix) = c.ix.get() { return ix.to_owned() }
    let (Some(f), Some(v)) = (BUILDER.get(), &c.v) else { return boxed(0) };
    let built = apply(f.to_owned(), [boxed(c.a as usize), v.borrow().to_owned()]);
    if cell.is_mt() { built.mark_mt() }
    c.ix.set(built).to_owned()
}

export! {
    /// Spec: `remapIds map n w wout ids` is `map` read at each element's id, at the new dictionary's width; `map` and the
    /// answer are ids of the new dictionary, read and written at `wout`, the argument is at `w`.
    fn qlean_search_remap_ids(mapv: B, n: usize, w: usize, wout: usize, idsv: B) -> O {
        let (ids, w, wout) = (idsv.bytes(), w as u32, wout as u32);
        let n = n.min(ids::ids_avail(ids.len(), w));
        let mut r = SArr::new(1, ids::ids_bytes(n, wout));
        r.bytes_mut().fill(0); // sub-byte fields are or-ed in, and the tail bits must be zero (`Column.packIds`)
        search::remap_ids(c::pool(), ids, n, w, mapv.bytes(), wout, r.bytes_mut());
        r.into()
    }

    /// Spec: `findIds n w ids needle` is `findScalar` over an interned column's ids: the least element holding `needle`,
    /// and `n` when none does.
    fn qlean_search_find_ids(n: usize, w: usize, idsv: B, needle: usize) -> usize { search::find_ids(n, w as u32, idsv.bytes(), needle) }

    /// Spec: `longsByIds vals nvals n w ids` is `vals` read at each element's id, as little-endian `Int64`s, and `0` where
    /// the id is past `vals`.
    fn qlean_search_longs_by_ids(valsv: B, nvals: usize, n: usize, w: usize, idsv: B) -> O {
        let (ids, w) = (idsv.bytes(), w as u32);
        let mut r = longs(n.min(ids::ids_avail(ids.len(), w)));
        search::longs_by_ids(elems(valsv), nvals, w, ids, search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `belowBits vals m n` is bit `j` set exactly when the `j`th `Int64` of `vals` is below `n`.
    fn qlean_search_below_bits(valsv: B, m: usize, n: usize) -> O {
        let mut r = SArr::new(1, m.div_ceil(8));
        search::below_bits(elems(valsv), m, n, r.bytes_mut());
        r.into()
    }

    /// Spec: `runStartsIds n w ids` is `runStarts` over an interned column's ids; the dictionary is distinct, so two
    /// elements are equal exactly when their ids are.
    fn qlean_search_run_starts_ids(n: usize, w: usize, idsv: B) -> O {
        let (ids, w) = (idsv.bytes(), w as u32);
        let n = n.min(ids::ids_avail(ids.len(), w));
        starts(n, |out| search::run_starts_ids(n, w, ids, out))
    }

    /// Spec: `matchBytes w float a b` is `QAtom.identical` element by element over two dense payloads.
    fn qlean_match_bytes(w: usize, is_float: u8, av: B, bv: B) -> u8 { search::match_bytes(w, is_float != 0, av.bytes(), bv.bytes()) as u8 }

    /// Spec: `foRMatch w am ap an bm bp bn` is `matchBytes w false` over the two operands' bytes.
    fn qlean_coc_match(w: usize, amv: B, apv: B, an: usize, bmv: B, bpv: B, bn: usize) -> u8 {
        search::coc_match(&opnd_of("qlean_coc_match", amv, apv, an, w), &opnd_of("qlean_coc_match", bmv, bpv, bn, w), w) as u8
    }

    /// Spec: `findVec w float hay ndl` is `findScalar w float hay` at each element of `ndl`, as `Int64`s.
    fn qlean_search_find_vec(w: usize, is_float: u8, hay: B, ndl: B) -> O {
        let kd = search::kind_of(w, is_float != 0, "find_vec"); // before dividing by `w`
        probe(kd, &Opnd::dense(hay.bytes(), w), &Opnd::dense(ndl.bytes(), w), false)
    }

    /// Spec: `memberVec w float xs hay` is bit `i` set exactly when `findScalar w float hay xs[i]` is below `hay.size / w`,
    /// packed LSB first with the tail bits of the last byte zero.
    fn qlean_search_member_vec(w: usize, is_float: u8, xs: B, hay: B) -> O {
        let kd = search::kind_of(w, is_float != 0, "member_vec");
        probe(kd, &Opnd::dense(hay.bytes(), w), &Opnd::dense(xs.bytes(), w), true)
    }

    /// Spec: `foRFindVec w hm hp hn nm np nn` is `findVec w false (operand w hm hp hn) (operand w nm np nn)`; no float key,
    /// as `Column.encodes` is q's signed integral types.
    fn qlean_coc_find_vec(w: usize, hm: B, hp: B, hn: usize, nm: B, np: B, nn: usize) -> O {
        let kd = search::kind_of(w, false, "coc_find_vec");
        probe(kd, &opnd_of("qlean_coc_find_vec", hm, hp, hn, w), &opnd_of("qlean_coc_find_vec", nm, np, nn, w), false)
    }

    /// Spec: `foRMemberVec w xm xp xn hm hp hn` is `memberVec w false (operand w xm xp xn) (operand w hm hp hn)`.
    fn qlean_coc_member_vec(w: usize, xm: B, xp: B, xn: usize, hm: B, hp: B, hn: usize) -> O {
        let kd = search::kind_of(w, false, "coc_member_vec");
        probe(kd, &opnd_of("qlean_coc_member_vec", hm, hp, hn, w), &opnd_of("qlean_coc_member_vec", xm, xp, xn, w), true)
    }

    /// Spec: `findIdsVec hw hay hn nw ndl nn` is `findVec` at `idKeyWidth hw nw` bytes over both id payloads repacked there
    /// (nothing is repacked: a block of ids is restored at a time).
    fn qlean_search_find_ids_vec(hw: usize, hay: B, hn: usize, nw: usize, ndl: B, nn: usize) -> O {
        let (h, x) = (Opnd::ids(hay.bytes(), hn, hw as u32), Opnd::ids(ndl.bytes(), nn, nw as u32));
        probe(search::kind_of(search::ids_key_width(hw, nw), false, "find_ids_vec"), &h, &x, false)
    }

    /// Spec: `memberIdsVec xw xs xn hw hay hn` is `memberVec` at `idKeyWidth xw hw` bytes over both id payloads repacked there.
    fn qlean_search_member_ids_vec(xw: usize, xs: B, xn: usize, hw: usize, hay: B, hn: usize) -> O {
        let (x, h) = (Opnd::ids(xs.bytes(), xn, xw as u32), Opnd::ids(hay.bytes(), hn, hw as u32));
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

    /// Spec: `binBits n hay m ndl right` is `binBytes 1 false false right` over the two bitmaps expanded to a byte an element.
    fn qlean_search_bin_bits(n: usize, hayv: B, m: usize, ndlv: B, right: u8) -> O {
        let mut r = longs(m);
        search::bin_bits(n, hayv.bytes(), ndlv.bytes(), m, right != 0, search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `memberBits m xs n hay` is bit `i` set exactly when `findBit n hay (Column.bitAt xs i)` is below `n`.
    fn qlean_search_member_bits(m: usize, xs: B, n: usize, hay: B) -> O {
        let mut r = SArr::new(1, m.div_ceil(8));
        search::member_bits(m, xs.bytes(), n, hay.bytes(), r.bytes_mut());
        r.into()
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

    /// Spec: `foRFind w needle metadata pack n` is `findScalar w false (Coc.decode w metadata pack n) needle`.
    fn qlean_coc_find_scalar(w: usize, needle: u64, mv: B, pv: B, n: usize) -> usize { search::coc_find(&view("qlean_coc_find_scalar", mv, pv, n), key(w, needle)) }

    /// Spec: `foRSpan w needle metadata n` is the number of blocks whose [base, maxv] holds the needle, read off the
    /// metadata alone.
    fn qlean_coc_span(w: usize, needle: u64, mv: B, n: usize) -> usize { search::coc_span(&meta("qlean_coc_span", mv, n), key(w, needle)) }

    /// Spec: `foRRows w needle metadata pack n` is every row of `Coc.decode` equal to the needle, ascending, as
    /// little-endian `Int64`s.
    fn qlean_coc_rows_eq(w: usize, needle: u64, mv: B, pv: B, n: usize) -> O {
        let rows = search::coc_rows_eq(&view("qlean_coc_rows_eq", mv, pv, n), key(w, needle));
        let mut r = SArr::new(1, rows.len() * 8);
        r.bytes_mut().copy_from_slice(pod::bytes(&rows));
        r.into()
    }

    /// Spec: `maskByIds mask nmask ids` is bit `i` set exactly when the element's id is inside `nmask` and `mask` has
    /// that bit.
    fn qlean_search_mask_by_ids(maskv: B, nmask: usize, n: usize, w: usize, idsv: B) -> O {
        let (ids, w) = (idsv.bytes(), w as u32);
        let n = n.min(ids::ids_avail(ids.len(), w));
        let mut r = SArr::new(1, n.div_ceil(8));
        search::mask_by_ids(maskv.bytes(), nmask, n, w, ids, r.bytes_mut());
        r.into()
    }

    /// Spec: `matchSyms ba oa bb ob` is `Column.symKey` equal at every index.
    fn qlean_match_syms(bav: B, oav: B, bbv: B, obv: B) -> u8 { search::match_syms(&syms_of(bav, oav), &syms_of(bbv, obv)) as u8 }

    /// Spec: `matchIds da doa ia db dob ib` is `Column.symKey` equal at every position, the ids read through their own
    /// dictionaries.
    fn qlean_search_match_ids(n: usize, m: usize, dav: B, doav: B, iav: B, dbv: B, dobv: B, ibv: B) -> u8 {
        search::match_ids(n, m, &syms_of(dav, doav), iav.bytes(), &syms_of(dbv, dobv), ibv.bytes()) as u8
    }

    /// Spec: `matchSymsIds b o n d dof ids` is `Column.symKey` equal at every position, element `i` of the blob against
    /// entry `ids[i]` of the dictionary; an id past the dictionary reads the empty symbol.
    fn qlean_search_match_syms_ids(bv: B, ov: B, n: usize, dv: B, dofv: B, idsv: B) -> u8 {
        search::match_syms_ids(&syms_of(bv, ov), n, &syms_of(dv, dofv), idsv.bytes()) as u8
    }

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

    /// Spec: `binOperands w float signed right hm hp hn km kp kn` is `binBytes w float signed right (operandBytes w hm hp hn)
    /// (operandBytes w km kp kn)`: either side where it lies. An encoded side is a signed integral column.
    fn qlean_bin_operands(w: usize, is_float: u8, is_signed: u8, right: u8, hm: B, hp: B, hn: usize, km: B, kp: B, kn: usize) -> O {
        let (h, k) = (enc("qlean_bin_operands", hm, hp, hn), enc("qlean_bin_operands", km, kp, kn));
        let n = h.as_ref().map_or(hp.bytes().len() / w, |c| c.meta.n);
        let m = k.as_ref().map_or(kp.bytes().len() / w, |c| c.meta.n);
        let mut r = longs(m);
        let (hay, keys) = (if h.is_some() { &[][..] } else { hp.bytes() }, if k.is_some() { &[][..] } else { &kp.bytes()[..w * m] });
        search::bin(c::pool(), w, is_float != 0, is_signed != 0, right != 0, hay, h.as_ref(), n as i64, keys, k.as_ref(), m, search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `binWide w right hay keys` is `binBytes`' halving with the element compared as `w` bytes in address order
    /// (`QAtom.identical`'s `cmpBytes`, q's order on a `guid`).
    fn qlean_search_bin_wide(w: usize, right: u8, hayv: B, keysv: B) -> O {
        let mut r = longs(keysv.bytes().len() / w);
        search::bin_wide(w, right != 0, hayv.bytes(), keysv.bytes(), search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `foRBin w right metadata pack n keys` is `binBytes w false true right (Coc.decode w metadata pack n) keys`, the
    /// halving reading the encoded column where it lies.
    fn qlean_coc_bin(w: usize, right: u8, mv: B, pv: B, n: usize, keysv: B) -> O {
        let (c, keys) = (view("qlean_coc_bin", mv, pv, n), keysv.bytes());
        let m = keys.len() / w;
        let mut r = longs(m);
        search::bin(c::pool(), w, false, true, right != 0, &[], Some(&c), c.meta.n as i64, &keys[..w * m], None, m, search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `binIds right vals n w ids keys` is `binBytes 8 false true right (longsByIds vals (vals.size / 8) n w ids) keys`:
    /// the same halving over an interned column, `vals` one `Int64` rank per dictionary entry; the ids are trusted to name
    /// entries of `vals`.
    fn qlean_search_bin_ids(right: u8, valsv: B, n: usize, w: usize, idsv: B, keysv: B) -> O {
        let (ids, w) = (idsv.bytes(), w as u32);
        let n = n.min(ids::ids_avail(ids.len(), w));
        let mut r = longs(keysv.bytes().len() / 8);
        search::bin_ids(right != 0, valsv.bytes(), n, w, &ids[..ids::ids_bytes(n, w)], keysv.bytes(), search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `findSortedBytes w float signed hay keys` is, for each element `k` of `keys`, the least index whose `ordKey`
    /// equals `k`'s and `hay.size / w` where there is none, as `Int64`s: `findVec`'s answer read off a sorted haystack.
    fn qlean_search_find_sorted(w: usize, is_float: u8, is_signed: u8, hayv: B, keysv: B) -> O {
        let (hay, keys) = (hayv.bytes(), keysv.bytes());
        let m = keys.len() / w;
        let mut r = longs(m);
        search::find_sorted(c::pool(), w, is_float != 0, is_signed != 0, hay, None, (hay.len() / w) as i64, &keys[..w * m], m,
                            search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `memberSortedBytes w float signed xs hay` is `findSortedBytes`' answer below the count, a bit an element of `xs`,
    /// LSB first and the tail bits of the last byte left zero.
    fn qlean_search_member_sorted(w: usize, is_float: u8, is_signed: u8, xsv: B, hayv: B) -> O {
        let (hay, xs) = (hayv.bytes(), xsv.bytes());
        let m = xs.len() / w;
        let mut r = SArr::new(1, m.div_ceil(8));
        search::member_sorted(c::pool(), w, is_float != 0, is_signed != 0, hay, None, (hay.len() / w) as i64, &xs[..w * m], m, r.bytes_mut());
        r.into()
    }

    /// Spec: `foRFindSorted w metadata pack n keys` is `findSortedBytes w false true (Coc.decode w metadata pack n) keys`.
    fn qlean_coc_find_sorted(w: usize, mv: B, pv: B, n: usize, keysv: B) -> O {
        let (c, keys) = (view("qlean_coc_find_sorted", mv, pv, n), keysv.bytes());
        let m = keys.len() / w;
        let mut r = longs(m);
        search::find_sorted(c::pool(), w, false, true, &[], Some(&c), c.meta.n as i64, &keys[..w * m], m, search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `foRMemberSorted w xs metadata pack n` is `memberSortedBytes w false true xs (Coc.decode w metadata pack n)`.
    fn qlean_coc_member_sorted(w: usize, xsv: B, mv: B, pv: B, n: usize) -> O {
        let (c, xs) = (view("qlean_coc_member_sorted", mv, pv, n), xsv.bytes());
        let m = xs.len() / w;
        let mut r = SArr::new(1, m.div_ceil(8));
        search::member_sorted(c::pool(), w, false, true, &[], Some(&c), c.meta.n as i64, &xs[..w * m], m, r.bytes_mut());
        r.into()
    }

    /// Spec: `binRows w float signed right hay keys order bounds gids miss` is, for each element `k` of `keys`, the right row
    /// the halving names inside group `g = gids[j]` over `[bounds[g], bounds[g+1])` reading `hay` through `order` (empty: the
    /// position is the row); `miss` where `gids` has no entry `j`, `g` names no group, or the group holds nothing at or
    /// before `k`.
    fn qlean_search_bin_rows(w: usize, is_float: u8, is_signed: u8, right: u8, hayv: B, keysv: B, orderv: B, boundsv: B, gidsv: B, miss: u64) -> O {
        bin_rows(w, is_float != 0, is_signed != 0, right != 0, hayv.bytes(), None, keysv, orderv, boundsv, gidsv, miss)
    }

    /// Spec: `foRBinRows w right metadata pack n keys order bounds gids miss` is `binRows w false true right (Coc.decode w
    /// metadata pack n) keys order bounds gids miss`.
    fn qlean_coc_bin_rows(w: usize, right: u8, mv: B, pv: B, n: usize, keysv: B, orderv: B, boundsv: B, gidsv: B, miss: u64) -> O {
        bin_rows(w, false, true, right != 0, &[], Some(&view("qlean_coc_bin_rows", mv, pv, n)), keysv, orderv, boundsv, gidsv, miss)
    }

    /// Spec: `runStarts w float hay` is the ascending indices `i` where `key hay[i]` differs from `key hay[i-1]`, with `0`
    /// first and the element count last, as `Int64`s. An empty payload answers `,0`.
    fn qlean_search_run_starts(w: usize, is_float: u8, hayv: B) -> O {
        let o = Opnd::dense(hayv.bytes(), w);
        starts(o.n, |out| search::run_starts(&o, w, is_float != 0, out))
    }

    /// Spec: `foRRunStarts w metadata pack n` is `runStarts w false (Coc.decode w metadata pack n)`, the pack read a block at
    /// a time.
    fn qlean_coc_run_starts(w: usize, mv: B, pv: B, n: usize) -> O {
        let o = opnd_of("qlean_coc_run_starts", mv, pv, n, w);
        starts(o.n, |out| search::run_starts(&o, w, false, out))
    }

    /// Spec: `runStartsSyms blob offs` is `runStarts` over a symbol payload: the run starts of the bytes `Column.symBytes`
    /// points at, with the symbol count last.
    fn qlean_search_run_starts_syms(blobv: B, offsv: B) -> O {
        let s = syms_of(blobv, offsv);
        starts(s.count(), |out| search::run_starts_syms(&s, out))
    }

    /// Spec: `runStartsBits n bits` is `runStarts` over `n` booleans packed LSB first, a byte past the end reading `0` as
    /// `Column.bitAt` does.
    fn qlean_search_run_starts_bits(n: usize, bitsv: B) -> O { starts(n, |out| search::run_starts_bits(n, bitsv.bytes(), out)) }

    /// `Index.register`: the builder and the extender, kept for the life of the process. Lean 4.28 passes an `IO`
    /// extern no world argument (the generated C calls `qlean_index_register(f, g)`).
    fn qlean_index_register(f: O, g: O) -> O {
        BUILDER.set(f.persist());
        EXTENDER.set(g.persist());
        Io::ok(boxed(0))
    }

    /// Spec: a cell for `v` under the mark `a`, its index built now, as q builds it when it applies the mark; `v` is
    /// kept to build from on the first lookup while no builder is registered, and always under `0`, a keyed table's
    /// key: that index is no attribute, and its build (~20ms at 1M rows, one hash per key column and per fold) would
    /// otherwise be paid by every keying nothing looks up.
    fn qlean_ixcell_new(a: u8, v: O) -> O {
        match BUILDER.get() {
            Some(f) if a != 0 => CELL.alloc(Cell { v: None, ix: Once::with(apply(f.to_owned(), [boxed(a as usize), v])), a }),
            _ => CELL.alloc(Cell { v: Some(v), ix: Once::new(), a }),
        }
    }

    /// Spec: the index the cell holds, built now if the cell was made before a builder was registered.
    fn qlean_ixcell_ready(cell: B) -> O { ready(cell, cell.external(&CELL)) }

    /// Spec: a cell for `v` under `cell`'s mark, `v` being `cell`'s value with the rows `amended` changed and rows
    /// appended from `n` on: its index is `cell`'s edited and extended by the registered extender, and built over `v`
    /// only where `cell` holds none to extend.
    fn qlean_ixcell_extend(cell: B, v: O, n: usize, amended: B) -> O {
        let c = cell.external(&CELL);
        let ix = ready(cell, c);
        let Some(g) = EXTENDER.get().filter(|_| ix.borrow().tag() != 0) else { drop(ix); return qlean_ixcell_new(c.a, v) };
        let old = ix.borrow().field(0).to_owned();
        drop(ix);
        let a = boxed(c.a as usize);
        CELL.alloc(Cell { v: None, ix: Once::with(apply(g.to_owned(), [a, old, v, box_usize_o(n), amended.to_owned()])), a: c.a })
    }
}

/// An index table of `bytes` bytes, every slot empty and no rows hashed.
fn table(bytes: usize) -> SArr {
    let mut r = SArr::new(1, bytes);
    search::ix_init(pod::cast_mut(r.bytes_mut()).expect("qlean index: the slots are misaligned"));
    r
}
/// The words of a table `r` fresh and held alone.
fn slots(r: &mut SArr) -> &mut [u64] { pod::cast_mut(r.bytes_mut()).expect("qlean index: the slots are misaligned") }
/// The words of a table other values may share (`ix_room`'s claim made it this value's to write past its rows).
fn shared(t: &O) -> &mut [u64] { pod::cast_mut(t.shared_bytes_mut()).expect("qlean index: the slots are misaligned") }
/// A symbol column as the hash reads it: the blob and offsets, and the ids an interned column's elements name.
fn ixsyms<'a>(blob: B<'a>, offs: B<'a>, ids: B<'a>, w: usize, interned: u8) -> search::IxSyms<'a> {
    search::IxSyms { s: syms_of(blob, offs), ids: ids.bytes(), w: w as u32, interned: interned != 0 }
}
/// The elements an index lookup or build reads: at most what the payload holds.
fn avail(n: usize, p: B, w: usize) -> usize { n.min(ids::ids_avail(p.bytes().len(), w as u32)) }
/// The slots `t` (owned, hashing `base` rows) as a table the caller may write rows `base` to `keys` into: itself where it is
/// large enough and still hashes exactly `base` rows -- every value sharing it reads only its own rows, so the claim is all
/// that is needed, and a loop of one-row appends copies nothing -- and otherwise a table of the capacity `keys` needs,
/// rehashed from the slots below `base` alone: where another value has claimed past `base`, its rows are not this value's.
fn room(t: O, base: usize, keys: usize) -> O {
    if search::ix_claim(pod::cast_mut(t.shared_bytes_mut()).expect("qlean index: the slots are misaligned"), base, keys) { return t }
    // twice what is needed, so a loop of one-row appends rehashes a logarithmic number of times
    let mut r = table(search::ix_bytes(2 * keys));
    search::ix_rehash(slots(&mut r), elems(t.borrow()), base, keys);
    r.into()
}

export! {
    /// Spec: slots hashing the `n` keys `id_at` reads at `bits` from `keys` to the least position of each.
    fn qlean_index_hash_build(bits: usize, keysv: B, n: usize) -> O {
        let n = avail(n, keysv, bits);
        let mut r = table(search::ix_bytes(search::ix_distinct(keysv.bytes(), bits as u32, n)));
        search::ix_build(slots(&mut r), keysv.bytes(), bits as u32, n);
        r.into()
    }

    /// Spec: each of the `m` needles `id_at` reads at `bits` from `ndl`, its position in the slots, `miss` where they hold
    /// none, as little-endian `Int64`s.
    fn qlean_index_hash_find(slotsv: B, bits: usize, ndl: B, m: usize, miss: usize) -> O {
        let mut r = longs(m);
        assert!(m <= ids::ids_avail(ndl.bytes().len(), bits as u32), "qlean: index lookup of {m} needles over a payload of {} bytes", ndl.bytes().len());
        search::ix_find(elems(slotsv), ndl.bytes(), bits as u32, miss, search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `qlean_index_hash_build` over the `n` symbols of a symbol column, a key equal exactly where the symbols are: the
    /// blob `(blob, offs)` itself, or, `interned`, its entries at the `n` ids at `w` bits in `ids`.
    fn qlean_index_hash_build_syms(blobv: B, offsv: B, idsv: B, w: usize, n: usize, interned: u8) -> O {
        let v = ixsyms(blobv, offsv, idsv, w, interned);
        let n = n.min(if interned != 0 { ids::ids_avail(idsv.bytes().len(), w as u32) } else { v.s.count() });
        let mut r = table(search::ix_bytes(search::ix_distinct_syms(&v, n)));
        search::ix_build_syms(slots(&mut r), &v, n);
        r.into()
    }

    /// Spec: `qlean_index_hash_find` at the symbols of the needle blob `(nb, no)` over the slots of the symbol column
    /// `qlean_index_hash_build_syms` read with the same `hb ho hids hw interned`.
    fn qlean_index_hash_find_syms(slotsv: B, hb: B, ho: B, hids: B, hw: usize, interned: u8, nb: B, no: B, miss: usize) -> O {
        let nd = syms_of(nb, no);
        let mut r = longs(nd.count());
        search::ix_find_syms(elems(slotsv), &ixsyms(hb, ho, hids, hw, interned), &nd, miss, search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `vals` read at each of the `n` ids `id_at` reads at `w` from `ids`, as little-endian `Int64`s: an answer decided
    /// per dictionary entry carried to the elements of an interned column.
    fn qlean_index_by_ids(valsv: B, n: usize, w: usize, idsv: B) -> O {
        assert!(n <= ids::ids_avail(idsv.bytes().len(), w as u32), "qlean: {n} ids over a payload of {} bytes", idsv.bytes().len());
        let mut r = longs(n);
        search::ix_by_ids(elems(valsv), w as u32, idsv.bytes(), search::i64s(r.bytes_mut()));
        r.into()
    }

    /// Spec: `slots`, hashing a column's first `base` rows, with the `m` keys `id_at` reads at `bits` from `keys` added as
    /// rows `base` on; a key already held keeps its least position.
    fn qlean_index_hash_extend(slotsv: O, bits: usize, keysv: B, base: usize, m: usize) -> O {
        assert!(m <= ids::ids_avail(keysv.bytes().len(), bits as u32), "qlean: index extension by {m} keys over a payload of {} bytes", keysv.bytes().len());
        let r = room(slotsv, base, base + m);
        search::ix_extend(shared(&r), keysv.bytes(), bits as u32, base, m);
        r
    }

    /// Spec: `qlean_index_hash_extend` over a symbol column of `n` rows read as `qlean_index_hash_build_syms` reads it,
    /// `slots` hashing its first `base`.
    fn qlean_index_hash_extend_syms(slotsv: O, blobv: B, offsv: B, idsv: B, w: usize, base: usize, n: usize, interned: u8) -> O {
        let v = ixsyms(blobv, offsv, idsv, w, interned);
        let have = if interned != 0 { ids::ids_avail(idsv.bytes().len(), w as u32) } else { v.s.count() };
        assert!(n <= have && base <= n, "qlean: index extension of rows {base}..{n} over a column of {have}");
        let r = room(slotsv, base, n);
        search::ix_extend_syms(shared(&r), &v, base, n);
        r
    }

    /// Spec: the `na` words of `a` and the `nb` words of `b`, each plus `add`, merged: `b`'s word `j` goes before `a`'s word
    /// `i` exactly when `ins[j] < i` -- `ins` is `bin`'s answer, nondecreasing, the last word of `a` at or below `b`'s -- so
    /// equal keys keep `a` first. An empty `a` reads word `i` as `i`, an empty `b` word `j` as `na + j`.
    fn qlean_index_splice(insv: B, av: B, bv: B, na: usize, nb: usize, add: u64) -> O {
        let (a, b) = ((!av.bytes().is_empty()).then(|| elems(av)), (!bv.bytes().is_empty()).then(|| elems(bv)));
        let ins: &[i64] = elems(insv);
        assert!(ins.len() >= nb && a.is_none_or(|a| a.len() >= na) && b.is_none_or(|b| b.len() >= nb), "qlean: index splice of {na} and {nb} words past its payloads");
        let mut r = longs(na + nb);
        search::ix_splice(&ins[..nb], a, b, add, pod::cast_mut(r.bytes_mut()).expect("qlean index: the answer is misaligned"));
        r.into()
    }

    /// Spec: each needle's row read off two indices, `base` over rows below `n` and the tail's counted from `n`: `pb`'s word
    /// where it is below `n`, and otherwise `qb`'s plus `n`, as little-endian `Int64`s.
    fn qlean_index_pick(pbv: B, qbv: B, n: u64) -> O {
        let (pb, qb) = (elems(pbv), elems(qbv));
        assert!(pb.len() == qb.len(), "qlean: index pick of {} and {} needles", pb.len(), qb.len());
        let mut r = longs(pb.len());
        search::ix_pick(pb, qb, n, pod::cast_mut(r.bytes_mut()).expect("qlean index: the answer is misaligned"));
        r.into()
    }

    /// Spec: each needle's row off an edited index (`Index.edit`): `pb`'s word, the base's row, where it is below `total` and
    /// not one of the sorted rows `d`; `qb`'s word `q` read as `d[q]`, `total` past `d`; the least of the two. Where `pb`'s row
    /// is one of `d` and below `d[q]`, the base's next row may be the answer, which this cannot see: such a needle's word is
    /// the overlay's row, the caller takes the least of it and the base's first row not amended, and their positions follow
    /// the `m` answers.
    fn qlean_index_unedit(pbv: B, qbv: B, dv: B, total: u64) -> O {
        let (pb, qb) = (elems(pbv), elems(qbv));
        assert!(pb.len() == qb.len(), "qlean: index unedit of {} and {} needles", pb.len(), qb.len());
        let mut r = SArr::with_capacity(1, 0, 2 * pb.len() * 8);
        let left = search::ix_unedit(pb, qb, elems(dv), total, pod::cast_mut(r.capacity_mut()).expect("qlean index: the answer is misaligned"));
        sarray_room(r.into(), left * 8)
    }

    /// Spec: the first row of the runs `p` to `e` of an index (`lo`, `hi`, each ending in the row count) that is not among
    /// the sorted words `d`, `miss` where every one is. A run's rows ascend and the runs are in row order, so the walk passes
    /// only rows of `d` before it stops.
    fn qlean_index_first_clean(lov: B, hiv: B, p: usize, e: usize, dv: B, miss: u64) -> u64 {
        search::ix_first_clean(elems(lov), elems(hiv), p, e, elems(dv), miss)
    }

    /// Spec: the ascending rows of one value off two parts of an index: `a`'s words that are not among the sorted words `d`,
    /// and `b`'s words `w` read as `d[w]` where `d` has any, else as `w + add`, merged in ascending order.
    fn qlean_index_unedit_rows(av: B, bv: B, dv: B, add: u64) -> O {
        let (a, b) = (elems(av), elems(bv));
        let mut r = SArr::with_capacity(1, 0, (a.len() + b.len()) * 8);
        let o = search::ix_unedit_rows(a, b, elems(dv), add, pod::cast_mut(r.capacity_mut()).expect("qlean index: the answer is misaligned"));
        sarray_room(r.into(), o * 8)
    }

    /// Spec: `Kernel.Index.runRows`: the rows of runs `p..e` of an index, its `lo` and `hi` each ending in the row count,
    /// which is not a run.
    fn qlean_index_rows(lo: B, hi: B, p: usize, e: usize) -> O {
        let (l, h): (&[i64], &[i64]) = (elems(lo), elems(hi));
        let mut r = longs(search::ix_rows_len(l, h, p, e));
        search::ix_rows(l, h, p, e, search::i64s(r.bytes_mut()));
        r.into()
    }
}
