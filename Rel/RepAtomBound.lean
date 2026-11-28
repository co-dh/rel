module

import all Init.Data.Array.Basic
import all Init.Data.Nat.Fold

public import Rel.Lang.DfnLaw
public import Rel.KernelSpec.Encoding
public import Rel.RepCanon

@[expose] public section

/-! **Bounds on the rows of an encoded `i64` column, read from its header.** A `foR` payload with no patch list
(`pack.size ≤ blockStart md (nblk md)`: nothing after the last block's residuals) holds each element as its block's base
plus a residual of at most `ones (widthAt b)`, so every row lies in `[base, base + 2^w - 1]` of its block. A column of a
generated literal (`Gen.atom`) is read this way with no row decoded. -/

namespace Rel
open Kernel Lang

/-- A signed word plus an unsigned one, wrapping, is their sum when the sum is an `Int64`. -/
theorem add_toInt64 (b r : UInt64) (hl : -2 ^ 63 ≤ b.toInt64.toInt + r.toNat)
    (hh : b.toInt64.toInt + r.toNat < 2 ^ 63) : (b + r).toInt64.toInt = b.toInt64.toInt + r.toNat := by
  have h1 := UInt64.toNat_lt b
  have h2 := UInt64.toNat_lt r
  have h3 : (b + r).toNat = (b.toNat + r.toNat) % 2 ^ 64 := UInt64.toNat_add b r
  have e : ∀ c : UInt64, c.toInt64.toInt = if c.toNat < 2 ^ 63 then (c.toNat : Int) else (c.toNat : Int) - 2 ^ 64 :=
    fun c => by
    show BitVec.toInt c.toBitVec = _
    rw [BitVec.toInt_eq_toNat_cond]
    have h : c.toBitVec.toNat = c.toNat := rfl
    rw [h]; split <;> split <;> omega
  rw [e (b + r)]
  rw [e b] at hl hh ⊢
  split at hl <;> split at hh <;> split <;> omega

/-- Without a patch list, a `foR` element is its block's base plus a residual of at most `ones w`. -/
theorem foRBits_bound (md pk : ByteArray) (i : Nat) (hp : pk.size ≤ Column.blockStart md (Column.nblk md)) :
    ∃ r : UInt64, r.toNat ≤ (Column.ones (Column.widthAt md (i / Column.blk md))).toNat ∧
      Column.foRBits md pk #[] i = Column.baseAt md (i / Column.blk md) + r := by
  refine ⟨Column.resAt pk (Column.blockStart md (i / Column.blk md)) (Column.widthAt md (i / Column.blk md))
    (i % Column.blk md), Verify.resAt_le_ones _ _ _ _, ?_⟩
  simp [Column.foRBits, Column.foRExc, Column.foRFrame, hp]

/-- A `foR` `i64` element is `foRBits` of its header and payload read as an `Int64`: the one reading the bound and the
equality of two literals' rows both go through. -/
theorem Arr.get_foR_eq {n : USize} (x : Arr .i64 n) {md pk : ByteArray} (hx : x.enc = .foR md pk) (i : Fin n.toNat) :
    x.get i = (Column.foRBits md pk #[] i.1).toInt64 := by
  rw [Arr.get_i64, hx]
  have hraw : (Enc.raw .i64 n (.foR md pk))[i.1]?.getD 0 = Column.foRBits md pk #[] i.1 := by
    simp [Enc.raw, QAtomicType.width, foRBits_starts]
  rw [hraw]

/-- **Every row of a `foR` `i64` column lies in `[lo, hi]`** when each block's base and base plus `ones w` do: the
condition `hb` reads only the header (`baseAt`, `widthAt` per block), and `hp` says the payload has no patch list. -/
theorem Arr.get_foR_bound {n : USize} (x : Arr .i64 n) {md pk : ByteArray} (hx : x.enc = .foR md pk)
    (hp : pk.size ≤ Column.blockStart md (Column.nblk md)) (lo hi : Int) (hl : -2 ^ 63 ≤ lo) (hh : hi < 2 ^ 63)
    (hb : ∀ b < Column.nblk md, lo ≤ (Column.baseAt md b).toInt64.toInt ∧
      (Column.baseAt md b).toInt64.toInt + (Column.ones (Column.widthAt md b)).toNat ≤ hi) (i : Fin n.toNat) :
    lo ≤ (x.get i).toInt ∧ (x.get i).toInt ≤ hi := by
  have hw := x.wf
  rw [hx] at hw
  have hlt : i.1 / Column.blk md < Column.nblk md := Nat.div_lt_of_lt_mul (by
    have := hw.2.2.1; have := i.2; have := Nat.mul_comm (Column.blk md) (Column.nblk md); omega)
  obtain ⟨r, hr, he⟩ := foRBits_bound md pk i.1 hp
  obtain ⟨h1, h2⟩ := hb _ hlt
  rw [Arr.get_foR_eq x hx i, he]
  have := add_toInt64 (Column.baseAt md (i.1 / Column.blk md)) r (by omega) (by omega)
  rw [this]; omega

/-- A generated `i64` literal (`Gen.atom`, header text `m`, pack text `p`) whose header `md` says it is well formed with no
flagged block is the `foR` column of its two texts. -/
theorem Lang.Gen.atom_enc {n : USize} {m p : List String} {hw : QAtomicType.i64.width.isSome = true}
    (hn : n.toNat ≤ Column.blk (Gen.unhex m) * Column.nblk (Gen.unhex m)) (hl : Column.lgOk (Gen.unhex m) = true)
    (hN : (Array.range (Column.nblk (Gen.unhex m))).any (Column.nulAt (Gen.unhex m)) = false) :
    (Gen.atom .i64 n m p hw).1.enc = .foR (Gen.unhex m) (Gen.unhex p) := by
  have hw' : Enc.WF .i64 n (.foR (Gen.unhex m) (Gen.unhex p)) := by
    refine ⟨by decide, fun h => absurd h (by decide), hn, hl, fun b hb hnul => ?_⟩
    have : (Array.range (Column.nblk (Gen.unhex m))).any (Column.nulAt (Gen.unhex m)) = true :=
      Array.any_eq_true.2 ⟨b, by simpa using hb, by simpa using hnul⟩
    rw [hN] at this; exact absurd this (by decide)
  rw [Gen.atom_eq rfl hw' (fun _ _ _ h => nomatch h) hN hw]; rfl

/-- `Arr.get_foR_bound` at a generated literal: every row lies in `[lo, hi]` if each block's range does. Every hypothesis
reads `md`, and `p` only by its size, so a header is checked without the pack. -/
theorem Lang.Gen.atom_get_bound {n : USize} {m p : List String} {md : ByteArray} (hm : Gen.unhex m = md)
    (hn : n.toNat ≤ Column.blk md * Column.nblk md) (hl : Column.lgOk md = true)
    (hN : (Array.range (Column.nblk md)).any (Column.nulAt md) = false)
    (hp : (Gen.unhex p).size ≤ Column.blockStart md (Column.nblk md)) (lo hi : Int)
    (hlo : -2 ^ 63 ≤ lo) (hhi : hi < 2 ^ 63)
    (hb : ∀ b < Column.nblk md, lo ≤ (Column.baseAt md b).toInt64.toInt ∧
      (Column.baseAt md b).toInt64.toInt + (Column.ones (Column.widthAt md b)).toNat ≤ hi)
    (i : Fin n.toNat) :
    lo ≤ ((Gen.atom .i64 n m p).1.get i).toInt ∧ ((Gen.atom .i64 n m p).1.get i).toInt ≤ hi := by
  subst hm
  exact Arr.get_foR_bound _ (Lang.Gen.atom_enc hn hl hN) hp lo hi hlo hhi hb i

/-- **A row of one generated literal is a row of another** when some position `j` of the first has the same `foRBits` as
position `i` of the second: the search is over `Nat` positions below `n.toNat`, so a decision procedure on the two
headers and packs settles it once `n.toNat` is a literal. -/
theorem Lang.Gen.atom_row_mem {n n0 : USize} {m p m0 p0 : List String} {hw : QAtomicType.i64.width.isSome = true}
    {hw0 : QAtomicType.i64.width.isSome = true}
    (hn : n.toNat ≤ Column.blk (Gen.unhex m) * Column.nblk (Gen.unhex m)) (hl : Column.lgOk (Gen.unhex m) = true)
    (hN : (Array.range (Column.nblk (Gen.unhex m))).any (Column.nulAt (Gen.unhex m)) = false)
    (hn0 : n0.toNat ≤ Column.blk (Gen.unhex m0) * Column.nblk (Gen.unhex m0)) (hl0 : Column.lgOk (Gen.unhex m0) = true)
    (hN0 : (Array.range (Column.nblk (Gen.unhex m0))).any (Column.nulAt (Gen.unhex m0)) = false)
    (i : Nat) (hi : i < n0.toNat)
    (h : ∃ j, j < n.toNat ∧
      Column.foRBits (Gen.unhex m) (Gen.unhex p) #[] j = Column.foRBits (Gen.unhex m0) (Gen.unhex p0) #[] i) :
    ∃ j : Fin n.toNat, (Gen.atom .i64 n m p hw).1.get j = (Gen.atom .i64 n0 m0 p0 hw0).1.get ⟨i, hi⟩ := by
  obtain ⟨j, hj, h⟩ := h
  refine ⟨⟨j, hj⟩, ?_⟩
  rw [Arr.get_foR_eq _ (Lang.Gen.atom_enc hn hl hN), Arr.get_foR_eq _ (Lang.Gen.atom_enc hn0 hl0 hN0)]
  exact congrArg UInt64.toInt64 h

/-- The header of the range literal `-10…20`: one block of 31 elements, residual width 5, no null. -/
def rangeMd : ByteArray :=
  ⟨#[246, 255, 255, 255, 255, 255, 255, 255, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 155, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 128, 31, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 5]⟩

set_option maxRecDepth 100000 in
theorem unhex_rangeMd : Gen.unhex
    ["f6ffffffffffffff140000000000000000000000000000009b00000000000000", "00000000000000801f000000000000000a0000000000000005"] =
    rangeMd := by
  have hb : ∀ {a b : ByteArray}, a.data.toList = b.data.toList → a = b := fun {a b} h => by
    cases a; cases b; simp_all
  apply hb; rw [Lang.Gen.unhex_toList]; with_unfolding_all rfl

theorem rangeMd_nblk : Column.nblk rangeMd = 1 := by decide +kernel
theorem rangeMd_blk : Column.blk rangeMd = 1024 := by decide +kernel
theorem rangeMd_lgOk : Column.lgOk rangeMd = true := by decide +kernel
theorem rangeMd_nul : (Array.range (Column.nblk rangeMd)).any (Column.nulAt rangeMd) = false := by decide +kernel
theorem rangeMd_start : Column.blockStart rangeMd (Column.nblk rangeMd) = 640 := by decide +kernel
theorem rangeMd_rows : ∀ b < Column.nblk rangeMd, -10 ≤ (Column.baseAt rangeMd b).toInt64.toInt ∧
    (Column.baseAt rangeMd b).toInt64.toInt + (Column.ones (Column.widthAt rangeMd b)).toNat ≤ 21 := by
  decide +kernel

/-- The range literal `-10…20`, for any pack `p` of at most the block's 640 bytes: every row lies in `[-10, 21]`, from the
header alone, with no row decoded. -/
example (p : List String) (hp : (Gen.unhex p).size ≤ 640) (i : Fin (USize.ofNat 31).toNat) :
    -10 ≤ ((Lang.Gen.atom .i64 (USize.ofNat 31)
      ["f6ffffffffffffff140000000000000000000000000000009b00000000000000", "00000000000000801f000000000000000a0000000000000005"]
      p).1.get i).toInt ∧ ((Lang.Gen.atom .i64 (USize.ofNat 31)
      ["f6ffffffffffffff140000000000000000000000000000009b00000000000000", "00000000000000801f000000000000000a0000000000000005"]
      p).1.get i).toInt ≤ 21 :=
  Lang.Gen.atom_get_bound unhex_rangeMd (by rw [rangeMd_nblk, rangeMd_blk, USize.toNat_ofNat']; rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide)
    rangeMd_lgOk rangeMd_nul (by rw [rangeMd_start]; exact hp) (-10) 21 (by decide) (by decide) rangeMd_rows i

end Rel
