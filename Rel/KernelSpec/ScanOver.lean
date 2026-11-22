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

/-- **The scan engine**, at every seed and step: output `j` is the low `8 * w` bits of `emit` at the
step folded from `seed` over elements `0 … j`, a null leaving the accumulator where it was. -/
theorem scanOf_get {α : Type} (n w : Nat) (hw : w ≤ 8) (rd : Nat → UInt64) (isNull : UInt64 → Bool)
    (seed : α) (step : α → UInt64 → α) (emit : α → UInt64) (j : Nat) (hj : j < n) :
    Column.bitsAt (scanOf n w rd isNull seed step emit) (j * w) w =
      UInt64.ofNat ((emit (((List.range (j + 1)).map rd).foldl
        (fun a x => if isNull x then a else step a x) seed)).toNat % 2 ^ (8 * w)) := by
  unfold scanOf
  rw [foldl_scanStep]
  obtain ⟨-, -, hg⟩ := foldl_pushBits emit w hw ((List.range n).map fun j =>
    ((List.range (j + 1)).map rd).foldl (fun a x => if isNull x then a else step a x) seed) ByteArray.empty
  have h := hg j (by simpa using hj)
  simp only [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, List.getElem_map, List.getElem_range] at h
  rw [Nat.mul_comm, h]

/-- `intScan`, the integral body of `scan`, is the engine at a seed, step and writer that do not
depend on the payload or the count: its elements are `Kind.bitsAt`, and `Kind.isNull` is what it
skips. With `scanOf_get` this is every verb's answer over a dense payload. -/
theorem intScan_scanOf (v : Scan.Verb) (k : Kind) (w : Nat) (hi lo nl : Int64) :
    ∃ (seed : Int64) (step : Int64 → UInt64 → Int64) (emit : Int64 → UInt64), ∀ (b : ByteArray) (m : Nat),
      intScan v k b m w hi lo nl = scanOf m w (k.bitsAt b) k.isNull seed step emit := by
  cases v <;> exact ⟨_, _, _, fun _ _ => rfl⟩



end Rel.Verify
