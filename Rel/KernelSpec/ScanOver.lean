import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.Kernel.Scan
import Rel.KernelSpec.Where
import Rel.Kernel.Value

/-! The part of `Rel.Verify.ScanOver` the Rel kernels reach; `Rel.Verify.ScanOver` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel Rel.Kernel.Scan

/-- `scanStep` folded over the first `n` indices: the pushed bytes are the accumulator after each
element, in order, and the accumulator is the null-skipping step folded over the elements read. -/
theorem foldl_scanStep {α : Type} (w : Nat) (rd : Nat → UInt64) (isNull : UInt64 → Bool)
    (step : α → UInt64 → α) (emit : α → UInt64) (seed : α) (n : Nat) :
    (List.range n).foldl (scanStep w rd isNull step emit) (ByteArray.empty, seed) =
      (((List.range n).map fun j =>
          ((List.range (j + 1)).map rd).foldl (fun a x => if isNull x then a else step a x) seed).foldl
          (fun acc a => Column.pushBits acc (emit a) w) ByteArray.empty,
        ((List.range n).map rd).foldl (fun a x => if isNull x then a else step a x) seed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, scanStep]





end Rel.Verify
