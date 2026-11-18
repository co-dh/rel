import Rel.Kernel.Coc

/-! `scatter`, the primitive that writes data to computed positions (`doc/rel-architecture.zh.typ` §4):
`out[ix[k]] = e[k]` over `n` cells that start as `fill`. Its inputs and its answer are `packed`, read as `Enc.raw` reads
a 64-bit column, so the kernel moves raw words and the caller's type narrows them.

An index `≥ n` is an error naming it, never dropped (owner, PLAN 6.5): a composition that discards a row sends it to a
spare cell and cuts that cell off (WHERE, `doc/rel-kernels.md`). The `k` in the name is temporary: `Kernel.scan`
(`Driver.lean`) already names the driver; 6.11 renames. -/

namespace Rel.Kernel
open Ext.Enc

/-- The `m` raw words of a `packed` argument, as `Enc.raw` reads a 64-bit column, or why it does not hold them: its
layout error (`Enc.packedErr`), or a form other than `packed`, which no kernel of design §4 reads. `m` is a parameter
because `packed` stores no count: its blocks bound it only to a multiple of `2 ^ lg`. -/
def packedWords (what : String) (m : USize) (e : Enc) : Except String (Array UInt64) :=
  match e with
  | .packed lg bases widths payload => match packedErr lg bases widths payload m.toNat with
    | some err => .error s!"{what}: {err}"
    | none => .ok (Ext.Enc.raw .long m e)
  | _ => .error s!"{what}: constructor {e.ctorIdx} is not packed"

/-- `n` cells, each `fill` until row `k` writes `es[k]` at `is[k]`, rows in order, so the last row naming a cell is the
one it keeps. The first row whose index is not below `n` is the error. -/
def scatterWords (is es : Array UInt64) (n : Nat) (fill : UInt64) : Except String (Array UInt64) :=
  (List.range is.size).foldlM (init := Array.replicate n fill) fun o k =>
    let i := is[k]?.getD 0
    if i.toNat < n then .ok (o.setIfInBounds i.toNat (es[k]?.getD 0))
    else .error s!"scatter: index {i} at row {k} is not below n = {n}"

/-- `scatter` over `m` rows of `ix` and `e` into `n` cells: `scatterWords` of their words, encoded as
`Coc.packedOf` at `lgEnc`, which `crate/src/pack.rs`'s `encode` writes. The first error in the order `ix`, `e`, the
rows is the answer. -/
@[extern "qlean_k_scatter"]
def kscatter (m : USize) (ix e : @& Enc) (n : USize) (fill : UInt64) : Except String Enc := do
  let o ← scatterWords (← packedWords "scatter: ix" m ix) (← packedWords "scatter: e" m e) n.toNat fill
  -- `ofNat32`, not the literal `8`, whose `toNat` is `8 % 2 ^ numBits` and stops `decide` at the opaque `numBits`
  pure (Coc.packedOf Column.lgEnc (USize.ofNat32 8 (by decide)) (o.foldl (init := .empty) fun acc w => Column.pushBits acc w 8))

end Rel.Kernel
