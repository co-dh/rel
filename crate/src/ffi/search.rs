//! search.c's Lean exports that moved: the scalar find, the Frame-of-Reference equality walks, the id mask, and the
//! index cell, an external object holding a value's index. Each unboxes its arguments, allocates the answer and makes one
//! call into `search.rs`, which owns the loops. Lean passes `Int64` and `UInt64` as C's `uint64_t`.
#![deny(unsafe_code)]
use crate::coc::{Coc, Meta};
use crate::lean::{B, Class, Ext, Io, O, Once, SArr, Slot, apply, box_usize_o, boxed, export};
use crate::{ids, os, pod, search};

/// coc.h `coc_meta_view` over `mv`, the count cut to what its blocks hold. Metadata too short for a block is no blocks and
/// is never read, as C's view over it (`COC_META_NBLK` 0).
fn meta<'a>(mv: B<'a>, n: usize) -> Meta<'a> {
    let m = mv.bytes();
    if m.len() < 33 { return Meta { base: &[], maxv: &[], off: &[], bsum: &[], width: &[], sumnul: 0, sumn: 0, n: 0, nblk: 0, mblk: 0 } }
    Meta::new(m, n).unwrap_or_else(|| panic!("qlean search: {} bytes of Frame of Reference metadata are not {} aligned blocks", m.len(), m.len() / 33))
}
/// coc.h `coc_view`: `meta` and the pack and patch list after it; a tail whose header does not size it is a bug and aborts.
fn coc_view<'a>(mv: B<'a>, pv: B<'a>, n: usize) -> Coc<'a> {
    let (m, pack) = (meta(mv, n), pv.bytes());
    Coc::attach(m, pack).unwrap_or_else(|| {
        let said = os::eprint(format_args!("qlean: a Frame of Reference pack of {} bytes whose residuals end at {} holds no patch list of {} blocks after them\n", pack.len(), m.res_end(), m.mblk));
        said.expect("qlean: the Frame of Reference pack message did not reach stderr");
        os::exit(1)
    })
}
/// The needle as the signed key of a column of `w`-byte elements (`coc_needle`: its low `w` bytes, sign-extended).
fn key(w: usize, needle: u64) -> i64 { search::sext(needle, w) }

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
    /// Spec: `findScalar w float hay needle` is the least `i < hay.size / w` whose key equals `needle`'s, and
    /// `hay.size / w` when there is none.
    fn qlean_search_find_scalar(w: usize, is_float: u8, hay: B, needle: u64) -> usize { search::find_scalar(w, is_float != 0, hay.bytes(), needle) }

    /// Spec: `foRFind w needle metadata pack n` is `findScalar w false (Coc.decode w metadata pack n) needle`.
    fn qlean_coc_find_scalar(w: usize, needle: u64, mv: B, pv: B, n: usize) -> usize { search::coc_find(&coc_view(mv, pv, n), key(w, needle)) }

    /// Spec: `foRSpan w needle metadata n` is the number of blocks whose [base, maxv] holds the needle, read off the
    /// metadata alone.
    fn qlean_coc_span(w: usize, needle: u64, mv: B, n: usize) -> usize { search::coc_span(&meta(mv, n), key(w, needle)) }

    /// Spec: `foRRows w needle metadata pack n` is every row of `Coc.decode` equal to the needle, ascending, as
    /// little-endian `Int64`s.
    fn qlean_coc_rows_eq(w: usize, needle: u64, mv: B, pv: B, n: usize) -> O {
        let rows = search::coc_rows_eq(&coc_view(mv, pv, n), key(w, needle));
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
