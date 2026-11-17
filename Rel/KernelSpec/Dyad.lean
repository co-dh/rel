import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Distinct
import Rel.Kernel.Value
import Rel.Kernel.Elementwise

/-! The part of `Rel.Verify.Dyad` the Rel kernels reach; `Rel.Verify.Dyad` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel

/-- `Ew.val` at `i64` against one long atom: element `i` is `intStep` of element `i` and the atom. -/
theorem val_i64_va (op : UInt8) (nul : Int64) (b : ByteArray) (c : UInt64) (n : Nat) (hn : n < USize.size) :
    elemsW 8 (Ew.val op Ew.i64 Ew.va nul b (atomBytes Ew.i64 c) n.toUSize) =
      (List.range n).map fun i =>
        (Ew.intStep op nul (Column.bitsAt b (i * 8) 8).toInt64 c.toInt64).toUInt64 := by
  rw [← elemsW_foldl (fun i => (Ew.intStep op nul (Column.bitsAt b (i * 8) 8).toInt64 c.toInt64).toUInt64)
    8 (by decide) (by decide) (List.range n) (fun _ _ => UInt64.toNat_lt _)]
  unfold Ew.val
  rw [USize.toNat_ofNat_of_lt' hn]
  congr 2; funext acc i
  show Column.pushBits acc (Ew.valStep op Ew.i64 nul.toUInt64 (Column.bitsAt b (i * 8) 8)
    (Column.bitsAt (Column.pushBits ByteArray.empty c 8) ByteArray.empty.size 8)) 8 = _
  rw [bitsAt_pushBits8]; rfl

/-- `Ew.val` at `i64` on two long vectors: element `i` is `intStep` of the two elements `i`. -/
theorem val_i64_vv (op : UInt8) (nul : Int64) (a b : ByteArray) (n : Nat) (hn : n < USize.size) :
    elemsW 8 (Ew.val op Ew.i64 Ew.vv nul a b n.toUSize) =
      (List.range n).map fun i =>
        (Ew.intStep op nul (Column.bitsAt a (i * 8) 8).toInt64 (Column.bitsAt b (i * 8) 8).toInt64).toUInt64 := by
  rw [← elemsW_foldl (fun i => (Ew.intStep op nul (Column.bitsAt a (i * 8) 8).toInt64
    (Column.bitsAt b (i * 8) 8).toInt64).toUInt64) 8 (by decide) (by decide) (List.range n)
    (fun _ _ => UInt64.toNat_lt _)]
  unfold Ew.val
  rw [USize.toNat_ofNat_of_lt' hn]
  rfl

/-- q's `x div k` on longs: floored, `0N` for a null operand or a zero divisor. -/
theorem val_idiv_va (b : ByteArray) (c : UInt64) (n : Nat) (hn : n < USize.size) :
    elemsW 8 (Ew.val Ew.idiv Ew.i64 Ew.va Int64.minValue b (atomBytes Ew.i64 c) n.toUSize) =
      (List.range n).map fun i =>
        let x := (Column.bitsAt b (i * 8) 8).toInt64
        let y := c.toInt64
        (if x == Int64.minValue || y == Int64.minValue || y == 0 then Int64.minValue
         else Int64.ofInt (Int.fdiv x.toInt y.toInt)).toUInt64 := by
  rw [val_i64_va _ _ _ _ _ hn]; rfl

/-- q's `x mod k` on longs: the floored remainder, `0N` for a null operand or a zero divisor. -/
theorem val_imod_va (b : ByteArray) (c : UInt64) (n : Nat) (hn : n < USize.size) :
    elemsW 8 (Ew.val Ew.imod Ew.i64 Ew.va Int64.minValue b (atomBytes Ew.i64 c) n.toUSize) =
      (List.range n).map fun i =>
        let x := (Column.bitsAt b (i * 8) 8).toInt64
        let y := c.toInt64
        (if x == Int64.minValue || y == Int64.minValue || y == 0 then Int64.minValue
         else Int64.ofInt (Int.fmod x.toInt y.toInt)).toUInt64 := by
  rw [val_i64_va _ _ _ _ _ hn]; rfl

/-- q's `x * k` on longs: wrapping, `0N` for a null operand. -/
theorem val_mul_va (b : ByteArray) (c : UInt64) (n : Nat) (hn : n < USize.size) :
    elemsW 8 (Ew.val Ew.mul Ew.i64 Ew.va Int64.minValue b (atomBytes Ew.i64 c) n.toUSize) =
      (List.range n).map fun i =>
        let x := (Column.bitsAt b (i * 8) 8).toInt64
        let y := c.toInt64
        (if x == Int64.minValue || y == Int64.minValue then Int64.minValue else x * y).toUInt64 := by
  rw [val_i64_va _ _ _ _ _ hn]; rfl

/-- q's `x + y` on two long vectors: wrapping, `0N` where either element is null. -/
theorem val_add_vv (a b : ByteArray) (n : Nat) (hn : n < USize.size) :
    elemsW 8 (Ew.val Ew.add Ew.i64 Ew.vv Int64.minValue a b n.toUSize) =
      (List.range n).map fun i =>
        let x := (Column.bitsAt a (i * 8) 8).toInt64
        let y := (Column.bitsAt b (i * 8) 8).toInt64
        (if x == Int64.minValue || y == Int64.minValue then Int64.minValue else x + y).toUInt64 := by
  rw [val_i64_vv _ _ _ _ _ hn]; rfl

end Rel.Verify

/-- info: 'Rel.Verify.val_i64_va' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_i64_va

/-- info: 'Rel.Verify.val_i64_vv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_i64_vv

/-- info: 'Rel.Verify.val_idiv_va' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_idiv_va

/-- info: 'Rel.Verify.val_imod_va' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_imod_va

/-- info: 'Rel.Verify.val_mul_va' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_mul_va

/-- info: 'Rel.Verify.val_add_vv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.val_add_vv
