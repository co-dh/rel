import Rel.KernelSpec.Search
import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Group
import Rel.KernelSpec.Ids
import Rel.Kernel.Sort
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.KernelSpec.Distinct
import Rel.Kernel.Scan

/-! The part of `Rel.Verify.BinWin` the Rel kernels reach; `Rel.Verify.BinWin` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel
open Rel.Kernel.Scan (Kind)

/-- **`bin` answers the last element not above the needle**: over `n` elements whose `ordKey`s ascend,
element `j` of the answer, read as an `Int64`, is `r - 1` for the `r` elements whose key is at most
needle `j`'s, none from `r` on being so. -/
theorem binBytes_last (w : USize) (float signed : Bool) (hay keys : ByteArray) (hn : hay.size / w.toNat < 2 ^ 63)
    (hsort : ∀ i j, i ≤ j → j < hay.size / w.toNat →
      ordKey w.toNat float signed (Column.bitsAt hay (i * w.toNat) w.toNat)
        ≤ ordKey w.toNat float signed (Column.bitsAt hay (j * w.toNat) w.toNat))
    (j : Nat) (hj : j < keys.size / w.toNat) :
    ∃ r, r ≤ hay.size / w.toNat ∧
      (Column.bitsAt (binBytes w float signed false hay keys) (8 * j) 8).toInt64.toInt = (r : Int) - 1 ∧
      (∀ i, i < r → ordKey w.toNat float signed (Column.bitsAt hay (i * w.toNat) w.toNat)
        ≤ ordKey w.toNat float signed (Column.bitsAt keys (j * w.toNat) w.toNat)) ∧
      (∀ i, r ≤ i → i < hay.size / w.toNat → ordKey w.toNat float signed (Column.bitsAt keys (j * w.toNat) w.toNat)
        < ordKey w.toNat float signed (Column.bitsAt hay (i * w.toNat) w.toNat)) := by
  have hs := binStep_spec w.toNat float signed false hay
    (ordKey w.toNat float signed (Column.bitsAt keys (j * w.toNat) w.toNat)) _ hsort
  refine ⟨_, hs.1, ?_, fun i hi => by simpa using hs.2.1 i hi,
    fun i h1 h2 => UInt64.lt_iff_toNat_lt.2 (by
      have := hs.2.2 i h1 h2; simp only [Bool.false_eq_true, ↓reduceIte, UInt64.le_iff_toNat_le] at this; omega)⟩
  have := hs.1
  rw [bitsAt_binBytes w float signed false hay keys j hj, Int64.toInt64_toUInt64]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact Int64.toInt_ofInt_of_le (by omega) (by omega)

/-- **`groupSizes` counts each group's rows**: entry `g` is how many of the ids read back are `g`. -/
theorem groupSizes_spec (ng w n : USize) (gid : ByteArray) :
    ids (Order.groupSizes ng w n gid) =
      (List.range ng.toNat).map fun g => (idsW w.toNat n.toNat gid).countP (· == g) := by
  rw [Order.groupSizes, ids_indices]
  · exact List.map_congr_left fun g _ => by rw [idsW, List.countP_map]; rfl
  · intro c hc'
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hc'
    exact Nat.lt_of_le_of_lt (Nat.le_trans List.countP_le_length
      (by rw [List.length_range]; exact idsCap_le _ _ _)) (usize_lt n)

end Rel.Verify
#print axioms Rel.Verify.binBytes_last
#print axioms Rel.Verify.groupSizes_spec


namespace Rel.Verify

open Rel Rel.Kernel
open Rel.Kernel.Scan (Kind)

/-- At an integral kind `ordKey` is the kernel's sort key, signed exactly at the signed widths. -/
theorem ordKey_keyAt {k : Kind} {s : Bool}
    (hk : (k = .u8 ∨ k = .c8) ∧ s = false ∨ (k = .i16 ∨ k = .i32 ∨ k = .i64) ∧ s = true) (b : ByteArray)
    (i : Nat) : ordKey k.width false s (Column.bitsAt b (i * k.width) k.width) = Order.keyAt k b i := by
  have hw := kind_width k
  have hm := toNat_and_mask hw.1 hw.2 (Column.bitsAt b (i * k.width) k.width)
  rw [Nat.mod_eq_of_lt (bitsAt_lt _ _ _ hw.2)] at hm
  have hm := UInt64.toNat_inj.1 hm
  rcases hk with ⟨hk | hk, rfl⟩ | ⟨hk | hk | hk, rfl⟩ <;> subst hk <;>
    simp only [ordKey, Bool.false_eq_true, ↓reduceIte, hm] <;> rfl

end Rel.Verify
#print axioms Rel.Verify.ordKey_keyAt
