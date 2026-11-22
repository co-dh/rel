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




end Rel.Verify


namespace Rel.Verify
open Rel Rel.Kernel


end Rel.Verify
