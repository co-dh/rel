import Rel.Kernel.BitRows
import Rel.Kernel.ScatterTest

/-! `kbitrows`' `decide`-beside-`#guard` pairs: each `example` evaluates the Lean body, each `#guard` the Rust export
`qlean_k_bitrows`, against one literal. -/

namespace Rel.Kernel.BitRowsTest
open Ext.Enc ScatterTest

/-- `bs` as a `u1` `foR` the way `kbitrows` writes one: `Coc.encodeAt lgEnc 1 _ false`, a mixed block its bitmap. -/
def enc1 (bs : List Bool) : Enc :=
  let r := Coc.encodeAt Column.lgEnc (u 1) ⟨(bs.map fun b => if b then (1 : UInt8) else 0).toArray⟩ false
  .foR r.1 r.2
/-- An expected answer as `view` shows it. -/
def bits (bs : List Bool) : String ⊕ (List UInt8 × List UInt8) := view (.ok (enc1 bs))

/-- Three rows of two bits, `10 01 11`, as `Coc.encode 8` of their words (patches and all) and as a bitmap. -/
def m3 : Enc := col [1, 0, 0, 1, 1, 1]
def m3b : Enc := enc1 [true, false, false, true, true, true]

-- `∨` over rows `0 1`, nothing, `2 2`: `11 00 11`; `∧`: `00 11 11`, the empty segment all ones
example : view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 2, 2]) m3) =
  bits [true, true, false, false, true, true] := by decide +kernel
#guard view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 2, 2]) m3) ==
  bits [true, true, false, false, true, true]
example : view (kbitrows true (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 2, 2]) m3) =
  bits [false, false, true, true, true, true] := by decide +kernel
#guard view (kbitrows true (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 2, 2]) m3) ==
  bits [false, false, true, true, true, true]
-- the bitmap form of the same matrix
example : view (kbitrows true (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 2, 2]) m3b) =
  bits [false, false, true, true, true, true] := by decide +kernel
#guard view (kbitrows true (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 2, 2]) m3b) ==
  bits [false, false, true, true, true, true]
-- no segment, and segments of no width: no bits
example : view (kbitrows false (u 2) (u 3) (u 0) (u 0) (col []) (col []) m3) = bits [] := by decide +kernel
#guard view (kbitrows false (u 2) (u 3) (u 0) (u 0) (col []) (col []) m3) == bits []
example : view (kbitrows true (u 0) (u 3) (u 0) (u 2) (col [0, 0]) (col []) (col [])) = bits [] := by decide +kernel
#guard view (kbitrows true (u 0) (u 3) (u 0) (u 2) (col [0, 0]) (col []) (col [])) == bits []

-- the errors, in the body's order: a layout, a segment out of order or past `ni`, a row number past `na`
def eEnds : String ⊕ (List UInt8 × List UInt8) := .inl "bitrows: ends: constructor 0 is not foR"
example : view (kbitrows false (u 2) (u 3) (u 4) (u 1) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩) (col [0, 1, 2, 2]) m3) =
  eEnds := by decide +kernel
#guard view (kbitrows false (u 2) (u 3) (u 4) (u 1) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩) (col [0, 1, 2, 2]) m3) ==
  eEnds
def eM : String ⊕ (List UInt8 × List UInt8) := .inl "bitrows: m: constructor 6 is not foR"
example : view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 2, 2]) .pos) = eM := by
  decide +kernel
#guard view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 2, 2]) .pos) == eM
def eOrd : String ⊕ (List UInt8 × List UInt8) := .inl "bitrows: segment 1 ends at 2, not in [3, 4]"
example : view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [3, 2, 4]) (col [0, 1, 2, 2]) m3) = eOrd := by
  decide +kernel
#guard view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [3, 2, 4]) (col [0, 1, 2, 2]) m3) == eOrd
def ePast : String ⊕ (List UInt8 × List UInt8) := .inl "bitrows: segment 2 ends at 5, not in [2, 4]"
example : view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [2, 2, 5]) (col [0, 1, 2, 2]) m3) = ePast := by
  decide +kernel
#guard view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [2, 2, 5]) (col [0, 1, 2, 2]) m3) == ePast
def eIdx : String ⊕ (List UInt8 × List UInt8) := .inl "bitrows: idx 3 at row 2 is not below na = 3"
example : view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 3, 2]) m3) = eIdx := by
  decide +kernel
#guard view (kbitrows false (u 2) (u 3) (u 4) (u 3) (col [2, 2, 4]) (col [0, 1, 3, 2]) m3) == eIdx
-- `na · w` at `2^32`, the first error
def eBig : String ⊕ (List UInt8 × List UInt8) := .inl "bitrows: 65536 or 0 rows of 65536 bits reach 2^32"
example : view (kbitrows false (u 65536) (u 65536) (u 0) (u 0) (col []) (col []) m3) = eBig := by decide +kernel
#guard view (kbitrows false (u 65536) (u 65536) (u 0) (u 0) (col []) (col []) m3) == eBig

/-- Block boundaries and a width not a multiple of 64: 30 rows of 100 bits (3000, three 1024-bit blocks), 50 row
numbers, 20 segments (the first ones empty) into 2000 bits. Encoding these is more than `decide +kernel` reduces, so
the Lean side of each pair is `bitRowsOf` run compiled on the same words, the `#guard` beside it the Rust. -/
def mw : List UInt64 := (List.range 3000).map fun i => if i * 7 % 11 < 4 then 1 else 0
def iw : List UInt64 := (List.range 50).map fun k => (k * 13 % 30).toUInt64
def ew : List UInt64 := (List.range 20).map fun r => (r * r / 8).toUInt64
def big (all : Bool) (m : Enc) : Except String Enc := kbitrows all (u 100) (u 30) (u 50) (u 20) (col ew) (col iw) m
def model (all : Bool) : String ⊕ (List UInt8 × List UInt8) := view (bitRowsOf all 100 30 50 20 ew.toArray iw.toArray mw.toArray)
#guard view (big false (col mw)) == model false
#guard view (big true (col mw)) == model true
#guard view (big false (enc1 (mw.map (· == 1)))) == model false
#guard view (big true (enc1 (mw.map (· == 1)))) == model true

end Rel.Kernel.BitRowsTest
