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



end Rel.Verify

/-- info: 'Rel.Verify.elemsW_decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-- info: 'Rel.Verify.decode_of_encode8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.decode_of_encode8


