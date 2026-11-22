import Rel.Kernel.Asc
import Rel.Kernel.Scan

/-! `gather`, the kernel that reads data at computed positions (`doc/rel-architecture.zh.typ` §4): `out[i] = e[ix[i]]`.
It is an optimisation, not a primitive: its Lean body is the design's composition of the primitives — concatenate
`(j, e[j])` and `(ix[i], i)`, sort (`asc`), fill the values forward (`scan`), write each back to `i` (`scatter`) — and
`crate/src/gather.rs` is the fused form, one read per row; `Rel.Verify.gatherWords_eq` says they agree.

An index `≥ n` is an error naming it, never a fill (PLAN 6.6, as `kscatter`). The `k` in the name is temporary, as
`kscan`'s and `kscatter`'s; 6.11 renames. -/

namespace Rel.Kernel
open Ext.Enc

/-- A row of `gather`'s concatenation: `(key, tag, idx)`, then the value. Source row `j` is `(j, 0, j, e[j])` and
query row `i` is `(ix[i], 1, i, 0)`, so a source sorts right before the queries that name it. -/
abbrev GatherRow := Nat × Nat × Nat × UInt64

/-- The `asc` step: the rows through `kasc`'s grade (`ascGrade`) on the columns `key` and `tag`. No `idx` column,
because the grade is stable and the concatenation already lists the rows of one `(key, tag)` in `idx` order. -/
def gatherAsc (R : List GatherRow) : List GatherRow :=
  (ascGrade R.length [(R.map (·.1.toUInt64)).toArray, (R.map (·.2.1.toUInt64)).toArray]).map (R[·]?.getD default)

/-- `gather`'s concatenation: a source row per word of `es`, then a query row per word of `is`. -/
def gatherRows (is es : Array UInt64) : List GatherRow :=
  (List.range es.size).map (fun j => (j, 0, j, es[j]?.getD 0)) ++
    (List.range is.size).map fun i => ((is[i]?.getD 0).toNat, 1, i, 0)

/-- `out[i] = es[is[i]]` as the design's composition. The first index not below `es.size` is the error; otherwise the
concatenation is sorted by key (`asc`), its values filled forward from each source row (`kscanRow` with no column to
fold, the source rows starting the segments), and each query row's value written to its `i` (`scatterWords`), every
source row to the spare cell `is.size`, which is then cut off (WHERE, `doc/rel-kernels.md`). -/
def gatherWords (is es : Array UInt64) : Except String (Array UInt64) :=
  match (List.range is.size).find? fun k => es.size ≤ (is[k]?.getD 0).toNat with
  | some k => .error s!"gather: index {is[k]?.getD 0} at row {k} is not below n = {es.size}"
  | none => do
    let L := gatherAsc (gatherRows is es)
    let F ← (List.range L.length).foldlM (kscanRow .first (L.map fun r => if r.2.1 = 0 then (1 : UInt64) else 0).toArray
      (L.map (·.2.2.2)).toArray []) #[]
    let o ← scatterWords .last (L.map fun r => UInt64.ofNat (if r.2.1 = 0 then is.size else r.2.2.1)).toArray F (is.size + 1) 0
    pure (o.extract 0 is.size)

/-- `gather` of `m` indices `ix` into `n` words `e`, both `foR`: `gatherWords` of their words (`foRWords`), encoded
as `foR` by `Coc.encodeAt` at `lgEnc` over 8-byte elements, caches included. The first error in the order `ix`, `e`,
the indices is the answer.

The Rust (`crate/src/gather.rs`) reads `e` by address on the encoded column, and decodes the source once when
#idx ≥ #src and the source is not flat (approved 2026-11-18: the decode is O(n) ≤ the O(m) output, and a flat column
already reads in one load). -/
@[extern "qlean_k_gather"]
def kgather (m : USize) (ix : @& Enc) (n : USize) (e : @& Enc) : Except String Enc := do
  let is ← foRWords "gather: ix" m ix
  let es ← foRWords "gather: e" n e
  noNul "gather: ix" m ix
  -- a null of `e` is a value: its flag (`foRNuls`) is gathered by the same indices as its word
  let o ← gatherWords is es
  wordsFoR o <$> if hasNul e then nulMap <$> gatherWords is (foRNuls n e) else pure .empty

end Rel.Kernel
