module

public import Rel.KernelSpec.Encoding
public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Verify.Raw` the Rel kernels reach; `Rel.Verify.Raw` imports it. -/


open Rel.Ext

namespace Rel.Verify

open Rel

theorem toInt_toInt64 (x : UInt64) :
    x.toInt64.toInt = if x.toNat < 2 ^ 63 then (x.toNat : Int) else x.toNat - 2 ^ 64 := by
  rw [Int64.toInt, show x.toInt64.toBitVec = x.toBitVec from rfl, BitVec.toInt_eq_toNat_cond]
  simp only [UInt64.toNat_toBitVec]
  split <;> split <;> omega

/-- The low `w` bytes of `v` as a two's-complement number: what a signed `w`-byte element denotes. -/
def sx (w : Nat) (v : UInt64) : Int :=
  if v.toNat % 2 ^ (8 * w) < 2 ^ (8 * w - 1) then ((v.toNat % 2 ^ (8 * w) : Nat) : Int)
  else ((v.toNat % 2 ^ (8 * w) : Nat) : Int) - ((2 ^ (8 * w) : Nat) : Int)


theorem pairwise_map_range_iff {α : Type} (R : α → α → Prop) (f : Nat → α) (m : Nat) :
    ((List.range m).map f).Pairwise R ↔ ∀ i j, i < j → j < m → R (f i) (f j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.pairwise_append, ih]
    simp only [List.map_cons, List.map_nil, List.pairwise_singleton, List.mem_map, List.mem_range,
      List.mem_singleton, true_and]
    constructor
    · rintro ⟨h, hm⟩ i j hij hj
      by_cases hjm : j = m
      · subst hjm; exact hm _ ⟨i, hij, rfl⟩ _ rfl
      · exact h i j hij (by omega)
    · intro h
      exact ⟨fun i j hij hj => h i j hij (by omega), by
        rintro _ ⟨i, hi, rfl⟩ _ rfl; exact h i m hi (by omega)⟩

end Rel.Verify


namespace Rel.Verify

open Rel Rel.Column

theorem size_raw {t : QAtomicType} (n : USize) (e : Ext.Enc X) (hw : Enc.WF t n e) (hb : t ≠ .u1)
    (hs : t ≠ .sym) (hn : t ≠ .general) : (Enc.raw t n e).size = n.toNat := by
  cases e <;> cases t <;> simp_all [Enc.raw, Enc.WF, QAtomicType.width]

/-- `atomOfBits` at a type of width `w` reads only the low `8 * w` bits. -/
theorem atomOfBits_mod {t : QAtomicType} {w : Nat} (ht : t.width = some w) (hb : t ≠ .u1)
    (v : UInt64) : atomOfBits t (UInt64.ofNat (v.toNat % 2 ^ (8 * w))) (QAtomicType.ne_general_of_width ht) = atomOfBits t v (QAtomicType.ne_general_of_width ht) := by
  have h8 : (UInt64.ofNat (v.toNat % 2 ^ 8)).toUInt8 = v.toUInt8 := UInt8.toNat_inj.1 (by simp)
  have h16 : (UInt64.ofNat (v.toNat % 2 ^ 16)).toUInt16 = v.toUInt16 := UInt16.toNat_inj.1 (by simp)
  have h32 : (UInt64.ofNat (v.toNat % 2 ^ 32)).toUInt32 = v.toUInt32 := UInt32.toNat_inj.1 (by simp)
  cases t <;> simp [QAtomicType.width] at ht <;> subst ht <;>
    first | exact absurd rfl hb | exact absurd rfl hg | simp only [atomOfBits, Nat.reduceMul, h8, h16, h32, ofNat_toNat_mod64]



/-- `Array.extract`'s loop: `bs`, then up to `i` elements of `a` from `j`. Core's `Array.getElem?_extract`
carries `Classical.choice`, so the read is taken from the loop here. -/
theorem extract_loop_getElem? {α : Type} (a bs : Array α) (i j k : Nat) :
    (Array.extract.loop a i j bs)[k]? = if k < bs.size then bs[k]? else
      if k - bs.size < i then if j + (k - bs.size) < a.size then a[j + (k - bs.size)]? else none else none := by
  induction i generalizing j bs with
  | zero =>
    rw [show Array.extract.loop a 0 j bs = bs by unfold Array.extract.loop; split <;> rfl]
    by_cases hk : k < bs.size
    · rw [if_pos hk]
    · rw [if_neg hk, if_neg (Nat.not_lt_zero _), Array.getElem?_eq_none (by omega)]
  | succ i ih =>
    unfold Array.extract.loop
    split
    · rename_i h
      show (Array.extract.loop a i (j + 1) (bs.push a[j]))[k]? = _
      rw [ih, Array.size_push, getElem?_push]
      repeat' split
      all_goals first | rfl | (exfalso; omega) | (congr 1; omega) | (simp only [show j + (k - bs.size) = j by omega, Array.getElem?_eq_getElem h])
    · rename_i h
      by_cases hk : k < bs.size
      · rw [if_pos hk]
      · rw [if_neg hk, Array.getElem?_eq_none (by omega)]
        by_cases hi : k - bs.size < i + 1
        · rw [if_pos hi, if_neg (by omega)]
        · rw [if_neg hi]


theorem extract_getElem? {α : Type} (a : Array α) (s e k : Nat) :
    (a.extract s e)[k]? = if k < min e a.size - s then a[s + k]? else none := by
  unfold Array.extract
  have h0 : ∀ c, (Array.emptyWithCapacity (α := α) c).size = 0 := fun _ => rfl
  rw [extract_loop_getElem?, h0, if_neg (Nat.not_lt_zero _), Nat.sub_zero, Nat.sub_eq]
  by_cases hk : k < min e a.size - s
  · rw [if_pos hk, if_pos hk, if_pos (by rw [Nat.lt_sub_iff_add_lt, Nat.lt_min] at hk; omega)]
  · rw [if_neg hk, if_neg hk]


/-- **The foR round trip.** `Enc.raw` cannot tell `Coc.encodeAt` at any block size `2 ^ lg` the layout admits
(`6 ≤ lg ≤ 16`) from the dense payload it encodes, read at that payload's width `w`, at any count up to `x`'s: element
`i`'s base plus its residual is `x`'s element sign-extended (`foRBits_encode`), cut back to its `8 * w` bits. -/
theorem raw_encodeAt (t : QAtomicType) (w : Nat) (ht : t.width = some w) (hb : t ≠ .u1)
    (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (x : ByteArray) (n : USize) (hn : n.toNat ≤ x.size / w) :
    Enc.raw (X := X) t n (.foR (Kernel.Coc.encodeAt lg w.toUSize x).1 (Kernel.Coc.encodeAt lg w.toUSize x).2) =
      (Array.range n.toNat).map fun i => Column.bitsAt x (i * w) w := by
  have hw : 0 < w ∧ w ≤ 8 := by cases t <;> simp [QAtomicType.width] at ht ⊢ <;> omega
  rw [raw_foR t w ht hb]
  refine Array.ext (by simp) fun i h1 _ => ?_
  simp only [Array.getElem_map, Array.getElem_range]
  rw [foRBits_encode lg hlg w hw.1 hw.2 x i (by simp at h1; omega),
    show (Kernel.Coc.keyAt w x i).toUInt64.toNat % 2 ^ (8 * w) = (Column.bitsAt x (i * w) w).toNat from
      sext_bits w hw.1 hw.2 _ (bitsAt_lt _ _ _ hw.2), UInt64.ofNat_toNat]

/-- **The foR round trip of a nullable column** (`1+atom`): row `i` of `Coc.encodeAt` with the null rows `nul`, read
through `Column.foROpt` and cut to the payload's `8 * w` bits, is `none` at a null and `x`'s element elsewhere
(`foROpt_encode`). `raw_encodeAt` is its null-free case. `hbig` is `foROpt_encode`'s, at every row: only a column of
`2 ^ 64` rows or more, which carries no patch list, needs it. -/
theorem rawOpt_encodeAt (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (x nul : ByteArray)
    {patch : Bool} (n : Nat) (hn : n ≤ x.size / w)
    (hbig : 2 ^ 64 ≤ x.size / w → ∀ i < n, Column.bitAt nul i = false → (Kernel.Coc.keyAt w x i).toInt = 2 ^ 63 - 1 → ∀ j,
      i / 2 ^ lg * 2 ^ lg ≤ j → j < i / 2 ^ lg * 2 ^ lg + 2 ^ lg → j < x.size / w → Column.bitAt nul j = false) :
    (Array.range n).map (fun i => (Column.foROpt (Kernel.Coc.encodeAt lg w.toUSize x patch nul).1
      (Kernel.Coc.encodeAt lg w.toUSize x patch nul).2
      (Column.blockStarts (Kernel.Coc.encodeAt lg w.toUSize x patch nul).1) i).map
        fun v => UInt64.ofNat (v.toNat % 2 ^ (8 * w))) =
      (Array.range n).map fun i => if Column.bitAt nul i then none else some (Column.bitsAt x (i * w) w) := by
  refine Array.ext (by simp) fun i h1 _ => ?_
  simp only [Array.size_map, Array.size_range] at h1
  simp only [Array.getElem_map, Array.getElem_range]
  rw [foROpt_encode lg hlg w hw0 hw x nul i (by omega) fun h => hbig h i h1]
  cases Column.bitAt nul i
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_some]
    rw [show (Kernel.Coc.keyAt w x i).toUInt64.toNat % 2 ^ (8 * w) = (Column.bitsAt x (i * w) w).toNat from
      sext_bits w hw0 hw _ (bitsAt_lt _ _ _ hw), UInt64.ofNat_toNat]
  · simp only [↓reduceIte, Option.map_none]

end Rel.Verify
