//! search.c's Lean exports that moved: the index cell, an external object holding a value's index.
#![deny(unsafe_code)]
use crate::lean::{B, Class, Ext, Io, O, Once, Slot, apply, box_usize_o, boxed, export};

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
