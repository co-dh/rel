import Rel.Kernel.Scan
import Rel.Kernel.Scatter

/-! `distinct` (design §4): on rows whose equal ones are contiguous (a sorted input), the position of the first row of
each run of equal rows, in input order. It is an optimisation kernel, so its Lean body is the design's composition of
the two primitives, `scan` (adjacent compare) then `scatter` (compact), each by the word model its own kernel runs:
`kscanRow`'s row fold and `scatterWords`. The Rust is the fused form. Its columns and its answer are `foR`, read as
`Enc.raw` reads a 64-bit column. The `k` in the name is temporary, as for `kscan`; 6.11 renames. -/

namespace Rel.Kernel
open Ext.Enc

/-- `distinct` on the `n` words of each column of `xs`: the number `k` of runs and the `k` words holding each run's
first row. Every step is a scan but the last, which scatters:
- `ne` of each column and the column one row back (row 0 reads itself, so it compares equal), every row a segment;
- `or` of those, seeded by row 0's `1`: a row's word is `1` exactly where it starts a run;
- `add` of the starts, seeded by `0 - 1` at row 0: a row's word is the index of its run;
- `last`, segments at the starts and seeded by the row numbers: a row's word is its run's first row;
- the run start into cell run index, `k` cells: every row of a run writes the same word, so the order of writes is
  immaterial and no row is dropped. -/
def distinctWords (n : Nat) (xs : List (Array UInt64)) : Except String (Nat × Array UInt64) := do
  let one := Array.replicate n (1 : UInt64)
  let ds ← xs.mapM fun x => (List.range n).foldlM (kscanRow .ne one x [Array.ofFn (n := x.size) fun i => x[i.1 - 1]?.getD 0]) #[]
  let st ← (List.range n).foldlM (kscanRow .or one (Array.ofFn (n := n) fun i => if i.1 = 0 then 1 else 0) ds) #[]
  let ix ← (List.range n).foldlM (kscanRow .add #[] (Array.replicate n (0 - 1)) [st]) #[]
  let fst ← (List.range n).foldlM (kscanRow .last st (Array.ofFn (n := n) fun i => i.1.toUInt64) []) #[]
  let k := (ix.back?.map (·.toNat + 1)).getD 0
  (k, ·) <$> scatterWords ix fst k 0

/-- **The distinct kernel** (design §4, `distinct_first` + `distinct_cover`): the run starts of the `n` rows of `es`,
each column a `foR` read as `Enc.raw` reads a 64-bit one, as the count `k` of runs and the `foR` of their `k`
positions that `Coc.encode` writes at 8 bytes. `k` is in the answer because the header, not `foR`, holds a count. A
column that is not a standard `foR` of `n` elements is the error, naming its place in `es`. -/
@[extern "qlean_k_distinct"]
def kdistinct (n : USize) (es : @& List Enc) : Except String (Nat × Enc) := do
  let (k, o) ← distinctWords n.toNat (← es.zipIdx.mapM fun p => foRWords s!"distinct: es[{p.2}]" n p.1)
  pure (k, wordsFoR o)

end Rel.Kernel
