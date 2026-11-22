import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Group
import Rel.KernelSpec.Distinct
import Rel.Kernel.Structural
import Rel.Kernel.Value

/-! The part of `Rel.Verify.Structural` the Rel kernels reach; `Rel.Verify.Structural` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel






/-- **`tilLongs` is `til n`**: read back as eight-byte elements, the answer is `0, 1, …, n - 1`. -/
theorem tilLongs_spec (n : USize) : (elemsW 8 (tilLongs n)).map UInt64.toNat = List.range n.toNat := by
  unfold tilLongs
  rw [elemsW_foldl (fun i => (Int64.ofNat i).toUInt64) 8 (by decide) (by decide) _ (fun e _ => UInt64.toNat_lt _),
    List.map_map]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.length_range] at h2
  simp only [List.getElem_map, List.getElem_range, Function.comp]
  rw [show (Int64.ofNat j).toUInt64 = UInt64.ofNat j from rfl, UInt64.toNat_ofNat_of_lt' (by have := usize_lt n; exact Nat.lt_trans h2 this)]

end Rel.Verify

#print axioms Rel.Verify.tilLongs_spec
