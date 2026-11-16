//! search.c's Lean exports that moved: the finds, the membership and run-start walks over ids and bits, the operand
//! searches, the Frame-of-Reference equality walks, the id mask, and the index cell, an external object holding a value's
//! index. Each unboxes its arguments, allocates the answer and makes one call into `search.rs`, which owns the loops.
//! Lean passes `Int64` and `UInt64` as C's `uint64_t`.
#![deny(unsafe_code)]
use crate::exports::coc::{meta, view};
use crate::exports::reduce::elems;
use alloc::vec;
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
        let mut starts = vec![0i64; n + 1]; // the run count is not known before the pass
        let g = search::run_starts_ids(n, w, ids, &mut starts);
        let mut r = longs(g);
        r.bytes_mut().copy_from_slice(pod::bytes(&starts[..g]));
        r.into()
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
