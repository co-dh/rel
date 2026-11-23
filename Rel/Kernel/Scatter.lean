module

public import Rel.Kernel.Coc
public import Rel.Kernel.Op

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `scatter`, the primitive that writes data to computed positions (`doc/rel-architecture.zh.typ` §4):
`out[ix[k]] := op(out[ix[k]], e[k])` in row order over `n` cells that start as `fill`; `op = .last` is the plain write
`out[ix[k]] = e[k]`, the last row winning. Its inputs and its answer are `foR`, read as `Enc.raw` reads
a 64-bit column, so the kernel moves raw words and the caller's type narrows them.

An index `≥ n` is an error naming it, never dropped (owner, PLAN 6.5): a composition that discards a row sends it to a
spare cell and cuts that cell off (WHERE, `doc/rel-kernels.md`). The `k` in the name is temporary: `Kernel.scan`
(`Driver.lean`) already names the driver; 6.11 renames. -/

namespace Rel.Kernel
open Ext.Enc

/-- Whether `e` is an argument every kernel reads at `m` rows: a `foR` column in the writers' layout (`Coc.foRStd`) with a
stored `lg` the layout admits, or `pos`. It reads the metadata and the pack's size only, never an element, so a caller
that asks only this calls it and not `foRWords`, whose answer is every word decoded in Lean. -/
@[simp] def foROk (m : USize) : Enc → Bool
  | .foR md pk => Column.lgOk md && Coc.foRStd m md pk
  | .pos => true
  | _ => false

/-- The `m` raw words of an argument `foROk` admits, as `Enc.raw` reads a 64-bit column, or why it does not hold them: a
layout `Coc.foRStd` refuses at `m`, or a form other than `foR` and `pos`, which no kernel of design §4 reads. `pos` is
word `i = i` at every `m` (PLAN 6.13): the kernel's loop index. -/
def foRWords (what : String) (m : USize) (e : Enc) : Except String (Array UInt64) :=
  if foROk m e then .ok (Ext.Enc.raw .i64 m e) else .error (match e with
    | .foR md pk => s!"{what}: foR: {Column.nblk md} blocks of 2^{Column.lgAt md} and a {pk.size}-byte pack are not the layout of {m} elements"
    | _ => s!"{what}: constructor {e.ctorIdx} is not foR")

/-- Whether `e` holds a null (`atom+1`'s `1`, in band): a `foR` block flagged (`Column.nulAt`). It reads one width byte
a block and no element (owner decision F: only a block holding a null is flagged), so a kernel moves null flags only
for an argument that has them and a column with none costs what it did. -/
def hasNul : Enc → Bool
  | .foR md _ => (Array.range (Column.nblk md)).any (Column.nulAt md)
  | _ => false

/-- `hasNul` of a `foR` column is false exactly when no block is flagged. -/
theorem hasNul_foR_false {md pk : ByteArray} :
    hasNul (.foR md pk) = false ↔ ∀ b < Column.nblk md, Column.nulAt md b = false := by
  rw [← Bool.not_eq_true, hasNul, Array.any_eq_true]
  simp only [Array.size_range, Array.getElem_range, not_exists, not_and, Bool.not_eq_true]

/-- The null flag of each of `e`'s `m` rows as a word, `1` at a null (`Column.foRNul`, tested on the block) and `0`
elsewhere: what a kernel moves, gathers and compares beside the row's word (`foRWords`), so the flag is part of the
value. Every row of `pos` is `0`. -/
def foRNuls (m : USize) : Enc → Array UInt64
  | .foR md pk => let st := Column.blockStarts md
    (Array.range m.toNat).map fun i => if Column.foRNul md pk st i then 1 else 0
  | _ => Array.replicate m.toNat 0

/-- The first null row of `e`'s `m` rows as the error `{what}: row k is null`, for an argument whose type has no `1`:
an index of `gather` or `scatter` names a row, and a null names none. -/
def noNul (what : String) (m : USize) (e : Enc) : Except String Unit :=
  if hasNul e then match (foRNuls m e).findIdx? (· != 0) with
    | some k => .error s!"{what}: row {k} is null, and a null names no row"
    | none => .ok ()
  else .ok ()

/-- Words as a `foR` answer of 8-byte elements, `foRWords`' converse: the extern `Coc.encode` (`Coc.encodeAt` at
`lgEnc`), which `qlean_coc_encode` writes (`exports::scan::for_words`). `nul` is `encode`'s null bitmap, row `i` null
where `Column.bitAt nul i` (its word then unread); empty, the default, for a column with none. -/
def wordsFoR (ws : Array UInt64) (nul : ByteArray := .empty) : Enc :=
  -- `ofNat32`, not the literal `8`, whose `toNat` is `8 % 2 ^ numBits` and stops `decide` at the opaque `numBits`;
  -- the extern, not its body: the body's width search is quadratic in a block and costs minutes on a wide column
  let p := Coc.encode (USize.ofNat32 8 (by decide)) (ws.foldl (init := .empty) fun acc w => Column.pushBits acc w 8) nul
  .foR p.1 p.2

/-- The flag words `ns` (`foRNuls`' form) as `wordsFoR`'s null bitmap, one bit a row, set where the flag is not `0`:
`packOf`, the one bit packer, so `bitAt_packOf` reads it back. -/
def nulMap (ns : Array UInt64) : ByteArray := packOf ns.size fun i => ns[i]?.getD 0 != 0

/-- `n` cells, each `fill` until row `k` combines `es[k]` into the cell `is[k]`: the cell becomes `op.eval cell es[k]`,
rows in order. Overwrite is `op = .last` (the last row naming a cell is the one it keeps), a sum `.add`. The first row
whose index is not below `n`, or whose `op.eval` fails (named with the row), is the error. -/
def scatterWords (op : Op) (is es : Array UInt64) (n : Nat) (fill : UInt64) : Except String (Array UInt64) :=
  (List.range is.size).foldlM (init := Array.replicate n fill) fun (o : Array UInt64) (k : Nat) =>
    let i : UInt64 := is[k]?.getD 0
    if i.toNat < n then
      match op.eval (o[i.toNat]?.getD 0) (es[k]?.getD 0) with
      | .ok v => .ok (o.setIfInBounds i.toNat v)
      | .error s => .error s!"scatter: {s} at row {k}"
    else .error s!"scatter: index {i} at row {k} is not below n = {n}"

/-- `scatter` over `m` rows of `ix` and `e` into `n` cells under `op`: `scatterWords` of their words, encoded by
`Coc.encode` at 8 bytes, every cache filled. A null of `e` is a value like any other: under `.last` its flag moves with
it (`foRNuls` scattered the same way, a cell keeping the flag of the row it keeps, a `fill` cell none); any other op
has no answer at a null and refuses its first null row. An op reading its divisor from the cell (`Op.readsDivisor`)
is refused first where a row exists: the kernel finds a failing row from `e` alone. After that, the first error in
the order `ix`, `e`, a null index, a null under an op other than `.last`, the rows is the answer. -/
@[extern "qlean_k_scatter"]
def kscatter (op : @& Op) (m : USize) (ix e : @& Enc) (n : USize) (fill : UInt64) : Except String Enc :=
  if op.readsDivisor && m != 0 then throw "scatter: rdiv and rmod divide by the cell, which no row test sees" else do
  let is ← foRWords "scatter: ix" m ix
  let es ← foRWords "scatter: e" m e
  noNul "scatter: ix" m ix
  match op with | .last => pure () | _ => noNul s!"scatter: e under op {op.ctorIdx}" m e
  let o ← scatterWords op is es n.toNat fill
  let nul ← if hasNul e then nulMap <$> scatterWords .last is (foRNuls m e) n.toNat 0 else pure .empty
  -- `ofNat32`, not the literal `8`, whose `toNat` is `8 % 2 ^ numBits` and stops `decide` at the opaque `numBits`
  let r := Coc.encode (USize.ofNat32 8 (by decide)) (o.foldl (init := .empty) fun acc w => Column.pushBits acc w 8) nul
  pure (.foR r.1 r.2)

end Rel.Kernel
