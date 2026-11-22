import Rel.KernelSpec.Encoding
import Rel.Kernel.Value
import Rel.Kernel.Scan

/-! The part of `Rel.Verify.Distinct` the Rel kernels reach; `Rel.Verify.Distinct` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel

/-- A fold of `w`-byte writes reads back as the values written, each truncated to `8 * w` bits. -/
theorem elemsW_foldl_mod {E : Type} (g : E → UInt64) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (l : List E) :
    elemsW w (l.foldl (fun acc e => Column.pushBits acc (g e) w) ByteArray.empty) =
      l.map fun e => UInt64.ofNat ((g e).toNat % 2 ^ (8 * w)) := by
  obtain ⟨hs, -, hb⟩ := foldl_pushBits g w hw l ByteArray.empty
  have hs' : (l.foldl (fun acc e => Column.pushBits acc (g e) w) ByteArray.empty).size / w = l.length := by
    rw [hs, show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Nat.mul_div_cancel_left _ hw0]
  apply List.ext_getElem (by rw [elemsW, List.length_map, List.length_range, hs', List.length_map])
  intro j h1 h2
  rw [List.length_map] at h2
  have e := hb j h2
  rw [show ByteArray.empty.size + w * j = j * w by
    rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Nat.mul_comm]] at e
  simp only [elemsW, List.getElem_map, List.getElem_range]
  exact e

/-- Elements pushed at `w` bytes, each fitting in `w` bytes, read back as themselves. -/
theorem elemsW_foldl {E : Type} (g : E → UInt64) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (l : List E)
    (hg : ∀ e ∈ l, (g e).toNat < 2 ^ (8 * w)) :
    elemsW w (l.foldl (fun acc e => Column.pushBits acc (g e) w) ByteArray.empty) = l.map g := by
  rw [elemsW_foldl_mod g w hw0 hw l]
  exact List.map_congr_left fun e he => by rw [Nat.mod_eq_of_lt (hg e he), UInt64.ofNat_toNat]

/-- info: 'Rel.Verify.elemsW_foldl_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms elemsW_foldl_mod
#print axioms elemsW_foldl

end Rel.Verify


namespace Rel.Verify

open Rel Rel.Kernel
open Rel.Kernel.Scan (Kind)


end Rel.Verify
