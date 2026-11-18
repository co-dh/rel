import Rel.Kernel.Coc

/-! `scatter`, the primitive that writes data to computed positions (`doc/rel-architecture.zh.typ` §4):
`out[ix[k]] = e[k]` over `n` cells that start as `fill`. Its inputs and its answer are `foR`, read as `Enc.raw` reads
a 64-bit column, so the kernel moves raw words and the caller's type narrows them.

An index `≥ n` is an error naming it, never dropped (owner, PLAN 6.5): a composition that discards a row sends it to a
spare cell and cuts that cell off (WHERE, `doc/rel-kernels.md`). The `k` in the name is temporary: `Kernel.scan`
(`Driver.lean`) already names the driver; 6.11 renames. -/

namespace Rel.Kernel
open Ext.Enc

/-- The `m` raw words of a `foR` argument, as `Enc.raw` reads a 64-bit column, or why it does not hold them: a layout
`Coc.foRStd` refuses at `m`, or a form other than `foR`, which no kernel of design §4 reads. -/
def foRWords (what : String) (m : USize) (e : Enc) : Except String (Array UInt64) :=
  match e with
  | .foR md pk => if Column.lgOk md && Coc.foRStd m md pk then .ok (Ext.Enc.raw .long m e)
    else .error s!"{what}: foR: {Column.nblk md} blocks of 2^{Column.lgAt md} and a {pk.size}-byte pack are not the layout of {m} elements"
  | _ => .error s!"{what}: constructor {e.ctorIdx} is not foR"

/-- Words as a `foR` answer of 8-byte elements, `foRWords`' converse: `Coc.encodeAt` at `lgEnc`, which
`qlean_coc_encode` writes (`exports::scan::for_words`). -/
def wordsFoR (ws : Array UInt64) : Enc :=
  -- `ofNat32`, not the literal `8`, whose `toNat` is `8 % 2 ^ numBits` and stops `decide` at the opaque `numBits`
  let p := Coc.encodeAt Column.lgEnc (USize.ofNat32 8 (by decide)) (ws.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
  .foR p.1 p.2

/-- `n` cells, each `fill` until row `k` writes `es[k]` at `is[k]`, rows in order, so the last row naming a cell is the
one it keeps. The first row whose index is not below `n` is the error. -/
def scatterWords (is es : Array UInt64) (n : Nat) (fill : UInt64) : Except String (Array UInt64) :=
  (List.range is.size).foldlM (init := Array.replicate n fill) fun o k =>
    let i := is[k]?.getD 0
    if i.toNat < n then .ok (o.setIfInBounds i.toNat (es[k]?.getD 0))
    else .error s!"scatter: index {i} at row {k} is not below n = {n}"

/-- `scatter` over `m` rows of `ix` and `e` into `n` cells: `scatterWords` of their words, encoded by `Coc.encode` at
8 bytes, every cache filled. The first error in the order `ix`, `e`, the rows is the answer. -/
@[extern "qlean_k_scatter"]
def kscatter (m : USize) (ix e : @& Enc) (n : USize) (fill : UInt64) : Except String Enc := do
  let o ← scatterWords (← foRWords "scatter: ix" m ix) (← foRWords "scatter: e" m e) n.toNat fill
  -- `ofNat32`, not the literal `8`, whose `toNat` is `8 % 2 ^ numBits` and stops `decide` at the opaque `numBits`
  let r := Coc.encode (USize.ofNat32 8 (by decide)) (o.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
  pure (.foR r.1 r.2)

end Rel.Kernel
