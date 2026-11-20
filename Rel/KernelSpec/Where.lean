import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.Kernel.Elementwise
import Rel.KernelSpec.Raw

/-! The part of `Rel.Verify.Where` the Rel kernels reach; `Rel.Verify.Where` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel




/-- A fold over a filter is a fold that skips. -/
theorem foldl_filter {α β : Type} (p : α → Bool) (f : β → α → β) (l : List α) (a : β) :
    (l.filter p).foldl f a = l.foldl (fun acc x => if p x then f acc x else acc) a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    cases h : p x <;> simp only [List.filter_cons, h, List.foldl_cons, ih, ↓reduceIte, Bool.false_eq_true]

/-- The elements a dense fold reads at class `cls`, in order: `Ew.signed`'s value of each. -/
def denseElems (cls : UInt8) (b : ByteArray) : List Int64 :=
  (List.range (b.size / Ew.width cls)).map fun i => Ew.signed cls (Ew.elem cls b i)

/-- q's `f/` over a list of elements: `Over.step` folded from `seed`, with `nul` dropped first except
at `all` and `any`. Every reduction kernel, dense, encoded or bitmap, is stated as this. -/
def overList (op : Coc.Over) (nul seed : Int64) (xs : List Int64) : Int64 :=
  (xs.filter fun x => op.boolCast || x != nul).foldl op.step seed


/-- A wrapping sum is the integer sum, wrapped once. Stated through `toInt` and `bmod` because core's
`Int64.ofInt_toInt` brings `Classical.choice`. -/
theorem foldl_add_int64 (l : List Int64) (a : Int64) :
    (l.foldl (· + ·) a).toInt = (a.toInt + (l.map Int64.toInt).sum).bmod (2 ^ 64) := by
  induction l generalizing a with
  | nil =>
    -- `toInt_add` at `0 + a` rather than core's `Int64.toInt_bmod`, which brings `Classical.choice`
    have h := Int64.toInt_add 0 a
    rw [Int64.zero_add, Int64.toInt_zero, Int.zero_add] at h
    rw [List.foldl_nil, List.map_nil, List.sum_nil, Int.add_zero]; exact h
  | cons x l ih =>
    rw [List.foldl_cons, ih, Int64.toInt_add, Int.bmod_add_bmod, List.map_cons, List.sum_cons, Int.add_assoc]


end Rel.Verify


namespace Rel.Verify
open Rel Rel.Kernel

/-- `whereBits`' list: below `n`, ascending, and exactly the indices whose bit is set. -/
theorem whereBits_indices (n : Nat) (bits : ByteArray) :
    ((List.range n).filter (Column.bitAt bits)).Pairwise (· < ·) ∧
    ∀ i, i ∈ (List.range n).filter (Column.bitAt bits) ↔ i < n ∧ Column.bitAt bits i = true :=
  -- `pairwise_map_range_iff` rather than core's `List.pairwise_lt_range`, which brings `Classical.choice`
  ⟨List.Pairwise.filter _ (by simpa using (pairwise_map_range_iff (· < ·) id n).mpr fun _ _ h _ => h),
    fun i => by simp [List.mem_filter, List.mem_range]⟩

end Rel.Verify
