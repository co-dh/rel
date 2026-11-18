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



-- `Classical.choice` below is each statement's, not its proof's: `Ew.val`, `Ew.cmpStep`, `Build.run`
-- (a chain names every engine), `Enc.answer` (ALP) and `Eval.arithAtoms` all name a `Float` decode.


/-- info: 'Rel.Verify.answer_foR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.answer_foR

/-- info: 'Rel.Verify.val_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_spec

/-- info: 'Rel.Verify.val_size8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_size8




/-- info: 'Rel.Verify.foRShift_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.foRShift_spec



