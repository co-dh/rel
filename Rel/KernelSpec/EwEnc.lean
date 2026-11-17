import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Elementwise
import Rel.Kernel.Coc
import Rel.KernelSpec.Distinct
import Rel.Kernel.Structural
import Rel.Kernel.Value
import Rel.Kernel.Elementwise

/-! The part of `Rel.Verify.EwEnc` the Rel kernels reach; `Rel.Verify.EwEnc` imports it. -/


open Rel.Ext
namespace Rel.Verify

open Rel Rel.Kernel

theorem width_bounds (cls : UInt8) : 0 < Ew.width cls ∧ Ew.width cls ≤ 8 := by
  unfold Ew.width
  repeat' split
  all_goals decide

theorem toUSize_toNat_of_le8 (w : Nat) (hw : w ≤ 8) : w.toUSize.toNat = w := by
  rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize, h] <;> omega

/-- **The Frame-of-Reference round trip on a payload**: decoding what `Coc.encode` wrote gives the
    elements back, at the widths it packs (`1 < w`: `byte` and `char` stay dense). -/
theorem elemsW_decode_encode (w : Nat) (hw1 : 1 < w) (hw : w ≤ 8) (x : ByteArray) (n : USize)
    (hn : n.toNat = x.size / w) :
    elemsW w (Coc.decode w.toUSize (Coc.encode w.toUSize x).1 (Coc.encode w.toUSize x).2 n) = elemsW w x := by
  simp only [Coc.decode, Coc.elems, toUSize_toNat_of_le8 w hw, List.foldl_map]
  rw [elemsW_foldl_mod _ w (by omega) hw, hn]
  apply List.ext_getElem (by simp [elemsW])
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [elemsW, List.getElem_map, List.getElem_range]
  apply UInt64.toNat_inj.1
  have hlt : (Column.foRBits (Coc.encode w.toUSize x).1 (Coc.encode w.toUSize x).2
      (Column.blockStarts (Coc.encode w.toUSize x).1) i).toNat % 2 ^ (8 * w) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
  unfold Rel.Kernel.Coc.encode at hlt ⊢
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt, foRBits_encode_bits Rel.Column.lgEnc (by decide) w hw1 hw x i h1]

theorem eq_of_ite_some {α : Type} {c : Prop} [Decidable c] {x y : α}
    (h : (if c then some x else none) = some y) : x = y := by
  split at h
  · exact Option.some.inj h
  · cases h

theorem eq_of_ite_none {α : Type} {c : Prop} [Decidable c] {x y : α}
    (h : (if c then none else some x) = some y) : x = y := by
  split at h
  · cases h
  · exact Option.some.inj h

/-- An eight-byte encode, read back: what `foRShift`, `foRScale` and `foRValVV` answer. -/
theorem decode_of_encode8 {x m p : ByteArray} {n : USize} (h : Coc.encode 8 x = (m, p))
    (hn : n.toNat = x.size / 8) : elemsW 8 (Coc.decode 8 m p n) = elemsW 8 x := by
  rw [show m = _ from (congrArg Prod.fst h).symm, show p = _ from (congrArg Prod.snd h).symm]
  exact elemsW_decode_encode 8 (by decide) (by decide) x n hn

/-- **`Build.runEnc` encodes the chain's answer and nothing else**: read back at its element width,
    it is the dense `Build.run`. -/
theorem runEnc_elems (b : Ew.Build) (last : Ew.Stage) (n : USize) (w : Nat) (hw1 : 1 < w) (hw : w ≤ 8)
    (m : USize) (hm : m.toNat = (b.run last n).size / w) :
    elemsW w (Coc.decode w.toUSize (b.runEnc last n w.toUSize).1 (b.runEnc last n w.toUSize).2 m) =
      elemsW w (b.run last n) :=
  elemsW_decode_encode w hw1 hw _ m hm

/-- **`Enc.answer` on an encoded column** keeps it or decodes it: either way the same elements. -/
theorem answer_foR (t : QAtomicType) (w : Nat) (k : USize) (M P : ByteArray) (ht : t.width = some w) :
    Enc.answer (X := X) t k (.foR M P) = .foR M P ∨
      Enc.answer (X := X) t k (.foR M P) = .bytes (Coc.decode w.toUSize M P k) := by
  simp only [Enc.answer]
  split
  · exact .inl rfl
  · simp only [ht]
    split
    · exact .inl rfl
    · exact .inr (by simp [Enc.bytesOf, ht])

/-- **`Ew.val`, element by element**: element `i` is `valStep` of the two elements the shape reads at
    `i`, truncated to the class's width. -/
theorem val_spec (op cls shape : UInt8) (nul : Int64) (a b : ByteArray) (n : USize) :
    (Ew.val op cls shape nul a b n).size = Ew.width cls * n.toNat ∧
    elemsW (Ew.width cls) (Ew.val op cls shape nul a b n) = (List.range n.toNat).map fun i =>
      UInt64.ofNat ((Ew.valStep op cls nul.toUInt64 (Ew.elem cls a (Ew.shapeIdx shape i).1)
        (Ew.elem cls b (Ew.shapeIdx shape i).2)).toNat % 2 ^ (8 * Ew.width cls)) := by
  obtain ⟨h0, h8⟩ := width_bounds cls
  let g : Nat → UInt64 := fun i =>
    Ew.valStep op cls nul.toUInt64 (Ew.elem cls a (Ew.shapeIdx shape i).1) (Ew.elem cls b (Ew.shapeIdx shape i).2)
  exact ⟨(foldl_pushBits g _ h8 (List.range n.toNat) ByteArray.empty).1.trans (by simp),
    elemsW_foldl_mod g _ h0 h8 _⟩

theorem val_size8 (op shape : UInt8) (nul : Int64) (a b : ByteArray) (n : USize) :
    n.toNat = (Ew.val op Ew.i64 shape nul a b n).size / 8 := by
  rw [(val_spec op Ew.i64 shape nul a b n).1]
  exact (Nat.mul_div_cancel_left _ (by decide)).symm

/-- **`foRVal`** answers `val` over the two decoded operands, element by element. -/
theorem foRVal_spec (op cls : UInt8) (nul : Int64) (ma pa mb pb : ByteArray) (n : USize) :
    elemsW (Ew.width cls) (Ew.foRVal op cls nul ma pa mb pb n) = (List.range n.toNat).map fun i =>
      UInt64.ofNat ((Ew.valStep op cls nul.toUInt64
        (Ew.elem cls (Coc.decode (Ew.width cls).toUSize ma pa n) i)
        (Ew.elem cls (Coc.decode (Ew.width cls).toUSize mb pb n) i)).toNat % 2 ^ (8 * Ew.width cls)) :=
  (val_spec op cls Ew.vv nul _ _ n).2

/-- **`foRValAtom`** answers `val` over the decoded vector and the atom, on the side `shape` names. -/
theorem foRValAtom_spec (op cls shape : UInt8) (nul : Int64) (md pk : ByteArray) (n : USize) (atom : ByteArray)
    (hs : shape = Ew.va ∨ shape = Ew.av) :
    elemsW (Ew.width cls) (Ew.foRValAtom op cls shape nul md pk n atom) = (List.range n.toNat).map fun i =>
      UInt64.ofNat ((if shape == Ew.va
        then Ew.valStep op cls nul.toUInt64 (Ew.elem cls (Coc.decode (Ew.width cls).toUSize md pk n) i)
          (Ew.elem cls atom 0)
        else Ew.valStep op cls nul.toUInt64 (Ew.elem cls atom 0)
          (Ew.elem cls (Coc.decode (Ew.width cls).toUSize md pk n) i)).toNat % 2 ^ (8 * Ew.width cls)) := by
  rcases hs with rfl | rfl
  · exact (val_spec op cls Ew.va nul _ _ n).2
  · exact (val_spec op cls Ew.av nul _ _ n).2

/-- **`foRValVV`**, where it answers, encodes `val` over the two decoded operands. -/
theorem foRValVV_spec (op : UInt8) (ma pa mb pb : ByteArray) (n : USize) (m p : ByteArray)
    (h : Ew.foRValVV op ma pa mb pb n = some (m, p)) :
    elemsW 8 (Coc.decode 8 m p n) =
      elemsW 8 (Ew.val op Ew.i64 Ew.vv Int64.minValue (Coc.decode 8 ma pa n) (Coc.decode 8 mb pb n) n) := by
  unfold Ew.foRValVV at h
  dsimp only at h
  exact decode_of_encode8 (eq_of_ite_some h) (val_size8 _ _ _ _ _ _)

/-- **`foRShift`**, where it answers, encodes `k + x` (`k - x` when `neg`) over the decoded operand. -/
theorem foRShift_spec (neg : Bool) (k : Int64) (md pk : ByteArray) (n : USize) (m p : ByteArray)
    (h : Ew.foRShift neg k md pk n = some (m, p)) :
    elemsW 8 (Coc.decode 8 m p n) = elemsW 8 (if neg
      then Ew.val Ew.sub Ew.i64 Ew.av Int64.minValue (Column.pushBits ByteArray.empty k.toUInt64 8)
        (Coc.decode 8 md pk n) n
      else Ew.val Ew.add Ew.i64 Ew.va Int64.minValue (Coc.decode 8 md pk n)
        (Column.pushBits ByteArray.empty k.toUInt64 8) n) := by
  unfold Ew.foRShift at h
  dsimp only at h
  exact decode_of_encode8 (eq_of_ite_none h) (by split <;> exact val_size8 _ _ _ _ _ _)

/-- **`foRScale`**, where it answers, encodes `x * k` over the decoded operand. -/
theorem foRScale_spec (k : Int64) (md pk : ByteArray) (n : USize) (m p : ByteArray)
    (h : Ew.foRScale k md pk n = some (m, p)) :
    elemsW 8 (Coc.decode 8 m p n) = elemsW 8 (Ew.val Ew.mul Ew.i64 Ew.va Int64.minValue
      (Coc.decode 8 md pk n) (Column.pushBits ByteArray.empty k.toUInt64 8) n) := by
  unfold Ew.foRScale at h
  dsimp only at h
  exact decode_of_encode8 (eq_of_ite_some h) (val_size8 _ _ _ _ _ _)

/-- **`foRCmp`**: bit `i` is `cmpStep` of decoded element `i` against `v`. -/
theorem foRCmp_bitAt (op : UInt8) (v : Int64) (md pk : ByteArray) (n : USize) :
    (Ew.foRCmp op v md pk n).size = (n.toNat + 7) / 8 ∧
    ∀ i < 8 * ((n.toNat + 7) / 8), Column.bitAt (Ew.foRCmp op v md pk n) i =
      (decide (i < n.toNat) && Ew.cmpStep op Ew.i64 (Ew.elem Ew.i64 (Coc.decode 8 md pk n) i) v.toUInt64) := by
  obtain ⟨hs, hb⟩ := cmp_bitAt op Ew.i64 Ew.va (Coc.decode 8 md pk n) (Column.pushBits ByteArray.empty v.toUInt64 8) n
  have hv : Ew.elem Ew.i64 (Column.pushBits ByteArray.empty v.toUInt64 8) 0 = v.toUInt64 :=
    bitsAt_pushBits8 ByteArray.empty v.toUInt64
  refine ⟨hs, fun i hi => (hb i hi).trans ?_⟩
  rw [show Ew.shapeIdx Ew.va i = (i, 0) from rfl]
  dsimp only
  rw [hv]

/-- **`foRCmpVV`**: bit `i` is `cmpStep` of the two decoded elements `i`. -/
theorem foRCmpVV_bitAt (op : UInt8) (ma pa mb pb : ByteArray) (n : USize) :
    (Ew.foRCmpVV op ma pa mb pb n).size = (n.toNat + 7) / 8 ∧
    ∀ i < 8 * ((n.toNat + 7) / 8), Column.bitAt (Ew.foRCmpVV op ma pa mb pb n) i =
      (decide (i < n.toNat) && Ew.cmpStep op Ew.i64 (Ew.elem Ew.i64 (Coc.decode 8 ma pa n) i)
        (Ew.elem Ew.i64 (Coc.decode 8 mb pb n) i)) :=
  cmp_bitAt op Ew.i64 Ew.vv _ _ n

theorem shiftBytes_size (w : USize) (hw : w.toNat ≤ 8) (fill : UInt64) (k : Int64) (b : ByteArray) :
    (shiftBytes w fill k b).size = w.toNat * (b.size / w.toNat) :=
  (foldl_pushBits _ _ hw (List.range (b.size / w.toNat)) ByteArray.empty).1.trans (by simp)

/-- **`shiftFoR`** encodes `shiftBytes` over the decoded column. -/
theorem shiftFoR_spec (ew : Nat) (hw1 : 1 < ew) (hw : ew ≤ 8) (md pk : ByteArray) (n : USize) (k : Int64)
    (fill : UInt64) :
    elemsW ew (Coc.decode ew.toUSize (shiftFoR ew.toUSize md pk n k fill).1 (shiftFoR ew.toUSize md pk n k fill).2 n) =
      elemsW ew (shiftBytes ew.toUSize fill k (Coc.decode ew.toUSize md pk n)) := by
  have hwt := toUSize_toNat_of_le8 ew hw
  refine elemsW_decode_encode ew hw1 hw _ n ?_
  rw [shiftBytes_size _ (by omega), (decodeW ew.toUSize (by omega) md pk n).1, hwt,
    Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]

end Rel.Verify

/-- info: 'Rel.Verify.elemsW_decode_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.elemsW_decode_encode

/-- info: 'Rel.Verify.width_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms Rel.Verify.width_bounds

/-- info: 'Rel.Verify.toUSize_toNat_of_le8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.toUSize_toNat_of_le8

/-- info: 'Rel.Verify.eq_of_ite_some' does not depend on any axioms -/
#guard_msgs in
#print axioms Rel.Verify.eq_of_ite_some

/-- info: 'Rel.Verify.eq_of_ite_none' does not depend on any axioms -/
#guard_msgs in
#print axioms Rel.Verify.eq_of_ite_none

/-- info: 'Rel.Verify.decode_of_encode8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.decode_of_encode8

/-- info: 'Rel.Verify.shiftBytes_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.shiftBytes_size

/-- info: 'Rel.Verify.shiftFoR_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.shiftFoR_spec

-- `Classical.choice` below is each statement's, not its proof's: `Ew.val`, `Ew.cmpStep`, `Build.run`
-- (a chain names every engine), `Enc.answer` (ALP) and `Eval.arithAtoms` all name a `Float` decode.

/-- info: 'Rel.Verify.runEnc_elems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.runEnc_elems

/-- info: 'Rel.Verify.answer_foR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.answer_foR

/-- info: 'Rel.Verify.val_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_spec

/-- info: 'Rel.Verify.val_size8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_size8

/-- info: 'Rel.Verify.foRVal_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.foRVal_spec

/-- info: 'Rel.Verify.foRValAtom_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.foRValAtom_spec

/-- info: 'Rel.Verify.foRValVV_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.foRValVV_spec

/-- info: 'Rel.Verify.foRShift_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.foRShift_spec

/-- info: 'Rel.Verify.foRScale_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.foRScale_spec

/-- info: 'Rel.Verify.foRCmp_bitAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.foRCmp_bitAt

/-- info: 'Rel.Verify.foRCmpVV_bitAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.foRCmpVV_bitAt
