import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.Kernel.Value
import Rel.Kernel.Elementwise

/-! The part of `Rel.Verify.Chain` the Rel kernels reach; `Rel.Verify.Chain` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel


/-- A left fold of `++` over records of one size `m`: its size, the prefix untouched, and byte `j` of
record `k` at `m * k + j` past the prefix. -/
theorem foldl_append_get (m : Nat) (L : List ByteArray) (hL : ∀ x ∈ L, x.size = m) (a : ByteArray) :
    (L.foldl (· ++ ·) a).size = a.size + m * L.length ∧
    (∀ i < a.size, (L.foldl (· ++ ·) a)[i]? = a[i]?) ∧
    ∀ k (hk : k < L.length), ∀ j < m, (L.foldl (· ++ ·) a)[a.size + (m * k + j)]? = L[k][j]? := by
  induction L generalizing a with
  | nil => exact ⟨by simp, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | cons x L ih =>
    have hx := hL x (by simp)
    obtain ⟨hs, hp, hg⟩ := ih (fun y hy => hL y (by simp [hy])) (a ++ x)
    have hax : (a ++ x).size = a.size + m := by rw [ByteArray.size_append, hx]
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨by rw [hs, hax, Nat.mul_succ]; omega,
      fun i hi => by rw [hp i (by omega), ba_append_left _ _ _ hi], fun k hk j hj => ?_⟩
    cases k with
    | zero =>
      rw [hp _ (by omega), Nat.mul_zero, Nat.zero_add, ba_append_right, List.getElem_cons_zero]
    | succ k =>
      rw [List.getElem_cons_succ, ← hg k (by simp at hk; omega) j hj, hax,
        show a.size + (m * (k + 1) + j) = a.size + m + (m * k + j) by rw [Nat.mul_succ]; omega]

/-- A one-byte read is the byte. -/
theorem bitsAt_one (b : ByteArray) (o : Nat) : Column.bitsAt b o 1 = (b[o]?.getD 0).toUInt64 := by
  rw [Column.bitsAt_succ]; simp [Column.bitsAt]






theorem width_pos_le (cls : UInt8) : 0 < Ew.width cls ∧ Ew.width cls ≤ 8 := by
  unfold Ew.width; repeat' split
  all_goals omega


end Rel.Verify
