import Rel.Kernel.Gather

/-! `kgather`'s `decide`-beside-`#guard` pairs: each `example` evaluates the Lean body (the composition), each `#guard` the
Rust export `qlean_k_gather` (the fused form), against one literal. -/

namespace Rel.Kernel.GatherTest
open Ext.Enc

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` as the `foR` column the kernels answer (`wordsFoR`). -/
def col (xs : List UInt64) : Enc := wordsFoR xs.toArray

/-- An answer as its error, or its metadata and pack bytes (equal to `col`'s of the expected words, caches included),
through `.data.toList`, a projection: `ByteArray.toList` is well-founded recursion the kernel unfolds a byte at a time. -/
def view : Except String Enc → String ⊕ (List UInt8 × List UInt8)
  | .error s => .inl s
  | .ok (.foR md pk) => .inr (md.data.toList, pk.data.toList)
  | .ok _ => .inl "not foR"

-- rows read `e` at 2, 0, 2, 3
example : view (kgather (u 4) (col [2, 0, 2, 3]) (u 4) (col [10, 11, 12, 13])) = view (.ok (col [12, 10, 12, 13])) := by
  decide +kernel
#guard view (kgather (u 4) (col [2, 0, 2, 3]) (u 4) (col [10, 11, 12, 13])) == view (.ok (col [12, 10, 12, 13]))

-- an index `≥ n` is the error, named with its row, never a fill
def past : String ⊕ (List UInt8 × List UInt8) := .inl "gather: index 3 at row 1 is not below n = 3"
example : view (kgather (u 3) (col [1, 3, 9]) (u 3) (col [1, 2, 3])) = past := by decide +kernel
#guard view (kgather (u 3) (col [1, 3, 9]) (u 3) (col [1, 2, 3])) == past

-- a `foR` whose blocks do not cover the count, named by the argument it came in
def short : String ⊕ (List UInt8 × List UInt8) := .inl "gather: ix: foR: 1 blocks of 2^10 and a 128-byte pack are not the layout of 2000 elements"
example : view (kgather (u 2000) (col [0, 1]) (u 2) (col [0, 1])) = short := by decide +kernel
#guard view (kgather (u 2000) (col [0, 1]) (u 2) (col [0, 1])) == short

-- `pos` (PLAN 6.13) as either argument: the positions, read as the loop index. G1: `ix = pos` at `m = n` answers `e`,
-- at `m < n` the first `m` rows of `e`, at `m > n` row `n` is the error
example : view (kgather (u 4) .pos (u 4) (col [10, 11, 12, 13])) = view (.ok (col [10, 11, 12, 13])) := by decide +kernel
#guard view (kgather (u 4) .pos (u 4) (col [10, 11, 12, 13])) == view (.ok (col [10, 11, 12, 13]))
example : view (kgather (u 2) .pos (u 4) (col [10, 11, 12, 13])) = view (.ok (col [10, 11])) := by decide +kernel
#guard view (kgather (u 2) .pos (u 4) (col [10, 11, 12, 13])) == view (.ok (col [10, 11]))
def posPast : String ⊕ (List UInt8 × List UInt8) := .inl "gather: index 3 at row 3 is not below n = 3"
example : view (kgather (u 4) .pos (u 3) (col [1, 2, 3])) = posPast := by decide +kernel
#guard view (kgather (u 4) .pos (u 3) (col [1, 2, 3])) == posPast
-- G2: `e = pos` answers `ix`, once every index is below `n`
example : view (kgather (u 4) (col [2, 0, 2, 3]) (u 4) .pos) = view (.ok (col [2, 0, 2, 3])) := by decide +kernel
#guard view (kgather (u 4) (col [2, 0, 2, 3]) (u 4) .pos) == view (.ok (col [2, 0, 2, 3]))
example : view (kgather (u 3) (col [1, 3, 9]) (u 3) .pos) = past := by decide +kernel
#guard view (kgather (u 3) (col [1, 3, 9]) (u 3) .pos) == past

-- past a block of `2 ^ 10`, `#guard` only (encoding that many rows is more than `decide +kernel` reduces): the Lean
-- side is the body's `gatherWords` run compiled, the `#guard` the Rust. Sources: one with patches (every 97th word an
-- outlier) and one flat (one width); indices: a run of 600 into the second block, then scattered, the positions, and
-- one past `n` in the second block
def patched : Array UInt64 :=
  (Array.range 1500).map fun i => (if i % 97 = 5 then i * 1000003 else 1000 + i * 7919 % 8000).toUInt64
def flat : Array UInt64 := (Array.range 1500).map fun i => (i * 7919 % 4096).toUInt64
def idx : Array UInt64 := (Array.range 1100).map fun k => (if k < 600 then 1024 + k % 400 else k * 2654435761 % 1500).toUInt64
def til (n : Nat) : Array UInt64 := (Array.range n).map Nat.toUInt64
def want (r : Except String (Array UInt64)) : String ⊕ (List UInt8 × List UInt8) := view (wordsFoR <$> r)
#guard [patched, flat].all fun s =>
  view (kgather (u 1100) (col idx.toList) (u 1500) (col s.toList)) == want (gatherWords idx s) &&
  view (kgather (u 1100) .pos (u 1500) (col s.toList)) == want (gatherWords (til 1100) s) &&
  view (kgather (u 1100) (col (idx.setIfInBounds 1050 1504).toList) (u 1500) (col s.toList)) ==
    want (gatherWords (idx.setIfInBounds 1050 1504) s)
#guard view (kgather (u 1100) (col idx.toList) (u 1500) .pos) == want (gatherWords idx (til 1500))

-- an index reading whole blocks of `e` in order (3000 rows: the positions, `.pos`, and the first two blocks swapped)
-- answers them by moving, patched `e` or flat: the Rust against `gatherWords`, compiled
def swp : Array UInt64 := (Array.range 3000).map fun k => (if k < 1024 then k + 1024 else if k < 2048 then k - 1024 else k).toUInt64
def patched3 : Array UInt64 :=
  (Array.range 3000).map fun i => (if i % 97 = 5 then i * 1000003 else 1000 + i * 7919 % 8000).toUInt64
def flat3 : Array UInt64 := (Array.range 3000).map fun i => (i * 7919 % 4096).toUInt64
#guard [patched3, flat3].all fun s =>
  view (kgather (u 3000) .pos (u 3000) (col s.toList)) == want (gatherWords (til 3000) s) &&
  view (kgather (u 3000) (col (til 3000).toList) (u 3000) (col s.toList)) == want (gatherWords (til 3000) s) &&
  view (kgather (u 3000) (col swp.toList) (u 3000) (col s.toList)) == want (gatherWords swp s)

/-- `xs` with the rows `ns` null (`1+atom`, in band), as `wordsFoR` writes it; a null row's word is never read. -/
def ncol (xs : List UInt64) (ns : List Nat) : Enc :=
  wordsFoR xs.toArray (Column.packIds 1 xs.length fun i => (ns.contains i).toNat)

-- a null of `e` is a value: rows 0 and 2 read `e`'s null at 1, row 1 reads 5 (rq17c: before, the null read as 7)
example : view (kgather (u 3) (col [1, 0, 1]) (u 2) (ncol [5, 0] [1])) = view (.ok (ncol [0, 5, 0] [0, 2])) := by
  decide +kernel
#guard view (kgather (u 3) (col [1, 0, 1]) (u 2) (ncol [5, 0] [1])) == view (.ok (ncol [0, 5, 0] [0, 2]))

-- a null index names no row: the error, after both layouts
def nulIx : String ⊕ (List UInt8 × List UInt8) := .inl "gather: ix: row 1 is null, and a null names no row"
example : view (kgather (u 2) (ncol [0, 0] [1]) (u 2) (col [5, 6])) = nulIx := by decide +kernel
#guard view (kgather (u 2) (ncol [0, 0] [1]) (u 2) (col [5, 6])) == nulIx

end Rel.Kernel.GatherTest
