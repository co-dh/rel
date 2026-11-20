import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.Kernel.Value
import Rel.Kernel.Elementwise
import Rel.Kernel.Eval.Val

/-! The part of `Rel.Verify.Elementwise` the Rel kernels reach; `Rel.Verify.Elementwise` imports it. -/


namespace Rel.Verify

open Rel

open Rel.Kernel in
/-- **`packOf`'s bitmap**: bit `i` is set exactly when `i < n` and `f i`, so the last byte's tail is
    zero. `Ew.cmp`, `Ew.bit` and `shiftBits` are each this fold. -/
theorem packOf_bitAt (n : Nat) (f : Nat → Bool) :
    (packOf n f).size = (n + 7) / 8 ∧
    ∀ i < 8 * ((n + 7) / 8), Column.bitAt (packOf n f) i = (decide (i < n) && f i) := by
  let C : Nat → Bool := fun i => decide (i < n) && f i
  let B : Nat → UInt8 := fun k =>
    (List.range 8).foldl (fun byte t => if C (k * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte) 0
  have hf : packOf n f = (List.range ((n + 7) / 8)).foldl (fun acc k => acc.push (B k)) ByteArray.empty := rfl
  obtain ⟨hs, -, hg⟩ := foldl_push8 B (List.range ((n + 7) / 8)) ByteArray.empty
  rw [hf]
  refine ⟨by simpa using hs, fun i hi => ?_⟩
  have h := hg (i / 8) (by simp; omega)
  simp only [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at h
  have hm8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  show Column.bitAt _ i = C i
  simp only [Column.bitAt, h, Option.getD_some]
  rw [bit_eq_testBit _ _ hm8, foldl_setBit _ _ (fun t ht => List.mem_range.1 ht), UInt8.toNat_zero,
    Nat.zero_testBit, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, -, ht⟩
    rw [Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨e, hc⟩ := ht
    subst e
    rwa [Nat.mul_comm, Nat.div_add_mod] at hc
  · intro hc
    refine ⟨i % 8, List.mem_range.2 hm8, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, Nat.mul_comm, Nat.div_add_mod]
    exact ⟨rfl, hc⟩

open Rel.Kernel in
/-- **`Ew.cmp`'s bitmap**: bit `i` is set exactly when `i < n` and `cmpStep` holds of the two elements
    the shape reads at `i`, so the last byte's tail is zero. -/
theorem cmp_bitAt (op cls shape : UInt8) (a b : ByteArray) (n : USize) :
    (Ew.cmpBitmap op cls shape a b n).size = (n.toNat + 7) / 8 ∧
    ∀ i < 8 * ((n.toNat + 7) / 8), Column.bitAt (Ew.cmpBitmap op cls shape a b n) i =
      (decide (i < n.toNat) && Ew.cmpStep op cls (Ew.elem cls a (Ew.shapeIdx shape i).1)
        (Ew.elem cls b (Ew.shapeIdx shape i).2)) :=
  packOf_bitAt n.toNat fun i =>
    Ew.cmpStep op cls (Ew.elem cls a (Ew.shapeIdx shape i).1) (Ew.elem cls b (Ew.shapeIdx shape i).2)

open Rel.Kernel in
/-- **`Ew.bit`'s bitmap**: bit `i` is set exactly when `i < n` and `bitStep` holds of the two bits the
    shape reads at `i`. -/
theorem Ew.bit_bitAt (op shape : UInt8) (a b : ByteArray) (n : USize) :
    (Ew.bitBitmap op shape a b n).size = (n.toNat + 7) / 8 ∧
    ∀ i < 8 * ((n.toNat + 7) / 8), Column.bitAt (Ew.bitBitmap op shape a b n) i =
      (decide (i < n.toNat) && Ew.bitStep op (Column.bitAt a (Ew.shapeIdx shape i).1)
        (Column.bitAt b (Ew.shapeIdx shape i).2)) :=
  packOf_bitAt n.toNat fun i =>
    Ew.bitStep op (Column.bitAt a (Ew.shapeIdx shape i).1) (Column.bitAt b (Ew.shapeIdx shape i).2)

/-! ### `Ew.intStep` verb by verb
Each is proved by reducing `intStep` at its verb (`show`), never by unfolding it under `simp`/`rw`: the unfolded body
carries the `panic!` of its last branch, and a proof term holding it is a panic site of the `panic` gate. Cite these
instead of `Ew.intStep`. -/

open Rel.Kernel

theorem Ew.intStep_add (nul x y : Int64) : Ew.intStep Ew.add nul x y = if x = nul ∨ y = nul then nul else x + y := by
  show (if x == nul || y == nul then nul else x + y) = _; simp only [Bool.or_eq_true, beq_iff_eq]
theorem Ew.intStep_sub (nul x y : Int64) : Ew.intStep Ew.sub nul x y = if x = nul ∨ y = nul then nul else x - y := by
  show (if x == nul || y == nul then nul else x - y) = _; simp only [Bool.or_eq_true, beq_iff_eq]
theorem Ew.intStep_mul (nul x y : Int64) : Ew.intStep Ew.mul nul x y = if x = nul ∨ y = nul then nul else x * y := by
  show (if x == nul || y == nul then nul else x * y) = _; simp only [Bool.or_eq_true, beq_iff_eq]
theorem Ew.intStep_fill (nul x y : Int64) : Ew.intStep Ew.fill nul x y = if y = nul then x else y := by
  show (if y == nul then x else y) = _; simp only [beq_iff_eq]
theorem Ew.intStep_lesser (nul x y : Int64) : Ew.intStep Ew.lesser nul x y = if x < y then x else y := rfl
theorem Ew.intStep_greater (nul x y : Int64) : Ew.intStep Ew.greater nul x y = if y < x then x else y := rfl
theorem Ew.intStep_idiv (nul x y : Int64) : Ew.intStep Ew.idiv nul x y =
    if x = nul ∨ y = nul ∨ y = 0 then nul else Int64.ofInt (Int.fdiv x.toInt y.toInt) := by
  show (if x == nul || y == nul || y == 0 then nul else Int64.ofInt (Int.fdiv x.toInt y.toInt)) = _
  simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]
theorem Ew.intStep_imod (nul x y : Int64) : Ew.intStep Ew.imod nul x y =
    if x = nul ∨ y = nul ∨ y = 0 then nul else Int64.ofInt (Int.fmod x.toInt y.toInt) := by
  show (if x == nul || y == nul || y == 0 then nul else Int64.ofInt (Int.fmod x.toInt y.toInt)) = _
  simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]

end Rel.Verify

-- `Classical.choice` is the statement's: `Ew.cmpStep` names `Float.ofBits` (via `ord64`, `ord32`,
-- `QAtom.tolerant`), an opaque whose `Inhabited` witness is choice; the proof adds none.
/-- info: 'Rel.Verify.cmp_bitAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.cmp_bitAt

/-- info: 'Rel.Verify.packOf_bitAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.packOf_bitAt

/-- info: 'Rel.Verify.Ew.bit_bitAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.Ew.bit_bitAt


namespace Rel.Verify

open Rel Rel.Eval

-- `general` has no atom, so each constructor below takes `h : t ≠ .general`; it is implicit here
-- because the term on the left already carries it.
@[simp] theorem nullAtom_type (t : QAtomicType) {h : t ≠ .general} : (nullAtom t h).type = t := by
  cases t <;> first | exact absurd rfl h | rfl

end Rel.Verify
