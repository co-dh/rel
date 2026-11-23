module

public import Rel.Kernel.Scatter

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `bitrows`, the one fused kernel beside the five (owner decision 2026-11-19, `doc/rel-architecture.zh.typ` §4): over
a bit matrix, row `r` of the answer folds a segment of its rows, by `∨` for `R ≫ S` and by `∧` for `R \ S`. A bit
matrix is a `u1` `foR` column of `na · w` rows and its width `w`, nothing else; `Tab.compBits` and `Tab.ldivBits`
(`Rel/Run/Bits.lean`) are the compositions that choose it. -/

namespace Rel.Kernel
open Ext.Enc

/-- `kbitrows` past its layout checks, on the words `es` (`g` segment ends), `is` (`ni` row numbers) and `ms`
(`na · w` bits, each word's bit 0): the first segment out of order, then the first row number `≥ na`, is the error;
else answer bit `r·w + j`, the fold of bit `is[k]·w + j` of `ms` over `k` in segment `r`, as a `u1` `foR`. -/
def bitRowsOf (all : Bool) (w na ni g : Nat) (es is ms : Array UInt64) : Except String Enc := do
  let lo := fun r => if r = 0 then 0 else (es[r - 1]?.getD 0).toNat
  let hi := fun r => (es[r]?.getD 0).toNat
  (List.range g).forM fun r => unless lo r ≤ hi r ∧ hi r ≤ ni do
    throw s!"bitrows: segment {r} ends at {hi r}, not in [{lo r}, {ni}]"
  (List.range ni).forM fun k => let i := is[k]?.getD 0
    unless i.toNat < na do throw s!"bitrows: idx {i} at row {k} is not below na = {na}"
  let b := fun i =>
    let ks := List.range' (lo (i / w)) (hi (i / w) - lo (i / w))
    let on := fun k => (ms[(is[k]?.getD 0).toNat * w + i % w]?.getD 0) % 2 == 1
    if all then ks.all on else ks.any on
  -- `ofNat32`, not the literal `1`, whose `toNat` is `1 % 2 ^ numBits` and stops `decide` at the opaque `numBits`
  let r := Coc.encodeAt Column.lgEnc (USize.ofNat32 1 (by decide))
    ⟨(Array.range (g * w)).map fun i => if b i then 1 else 0⟩ false
  pure (.foR r.1 r.2)

/-- **The bit-row kernel**: `m` a `u1` `foR` of `na · w` bits (row `i` at bits `[i·w, (i+1)·w)`), `idx` `ni` row
numbers each below `na`, `ends` `g` segment ends, nondecreasing and at most `ni` (segment `r` is
`[ends[r-1], ends[r])`, `ends[-1] = 0`). Answer bit `r·w + j` is the `∨` (`all = false`; an empty segment `0`) or the
`∧` (`all = true`; an empty segment `1`) over `k` in segment `r` of bit `idx[k]·w + j` of `m`: `g · w` bits as a
`u1` `foR` (`Coc.encodeAt lgEnc 1 _ false`, a mixed block its bitmap). Each count is an argument because an `Enc`
carries none (as `kscatter`'s `m`, `n`). The error, in this order: `na · w` or `g · w` not below `2^32`; `ends`, `idx`,
`m` not of their layout (`foRWords`, `m` a `foR` alone); then `bitRowsOf`'s. The bound is `2^32`, not `USize.size`:
every platform's `USize` holds it (`USize.le_size`) and `decide` reduces it, and a matrix is chosen at `≤ 2^27` bits. -/
@[extern "qlean_k_bitrows"]
def kbitrows (all : Bool) (w na ni g : USize) (ends idx m : @& Enc) : Except String Enc := do
  if h : na.toNat * w.toNat < 2 ^ 32 ∧ g.toNat * w.toNat < 2 ^ 32 then
    let es ← foRWords "bitrows: ends" g ends
    let is ← foRWords "bitrows: idx" ni idx
    let ms ← match m with
      | .pos => throw s!"bitrows: m: constructor {m.ctorIdx} is not foR"
      | _ => foRWords "bitrows: m" (USize.ofNatLT _ (Nat.lt_of_lt_of_le h.1 USize.le_size)) m
    bitRowsOf all w.toNat na.toNat ni.toNat g.toNat es is ms
  else throw s!"bitrows: {na} or {g} rows of {w} bits reach 2^32"

end Rel.Kernel
