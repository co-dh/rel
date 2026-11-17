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

/-- **`intScan` over `Coc.decode`**, which is `scanFoR` at every integral layout, at every verb:
output `j` is the step folded from the seed over the first `j + 1` elements `foRBits` decodes, each
truncated to the layout's width, a null leaving the accumulator where it was. -/
theorem intScan_foR (v : Scan.Verb) (k : Kind) (hk : k ≠ .bit) (w : Nat) (hw : w ≤ 8) (hi lo nl : Int64) :
    ∃ (seed : Int64) (step : Int64 → UInt64 → Int64) (emit : Int64 → UInt64),
      ∀ (n : USize) (md pk : ByteArray), ∀ j < n.toNat,
        Column.bitsAt (intScan v k (Coc.decode k.width.toUSize md pk n)
            (min n.toNat (k.avail (Coc.decode k.width.toUSize md pk n))) w hi lo nl) (j * w) w =
          UInt64.ofNat ((emit (((List.range (j + 1)).map fun i =>
            UInt64.ofNat ((Column.foRBits md pk (Column.blockStarts md) i).toNat % 2 ^ (8 * k.width))).foldl
              (fun a x => if k.isNull x then a else step a x) seed)).toNat % 2 ^ (8 * w)) := by
  obtain ⟨seed, step, emit, h⟩ := intScan_scanOf v k w hi lo nl
  refine ⟨seed, step, emit, fun n md pk j hj => ?_⟩
  have hkw : k.width.toUSize.toNat ≤ 8 ∧ 0 < k.width.toUSize.toNat ∧ k.width.toUSize.toNat = k.width := by
    cases k <;> simp only [Kind.width, Nat.toUSize, USize.toNat_ofNat'] <;>
      rcases System.Platform.numBits_eq with h | h <;> simp [h]
  have hav : ∀ b, k.avail b = b.size / k.width := by
    intro b; cases k <;> first | exact absurd rfl hk | rfl
  have hrd : ∀ b i, k.bitsAt b i = Column.bitsAt b (i * k.width) k.width := by
    intro b i; cases k <;> first | exact absurd rfl hk | rfl
  obtain ⟨hs, hg⟩ := decodeW k.width.toUSize hkw.1 md pk n
  rw [hkw.2.2] at hs hg
  have hm : (List.range (j + 1)).map (k.bitsAt (Coc.decode k.width.toUSize md pk n)) =
      (List.range (j + 1)).map fun i =>
        UInt64.ofNat ((Column.foRBits md pk (Column.blockStarts md) i).toNat % 2 ^ (8 * k.width)) :=
    List.map_congr_left fun i hi => by
      rw [hrd, hg i (Nat.lt_of_lt_of_le (List.mem_range.1 hi) hj)]
  rw [h, hav, hs, Nat.mul_div_cancel_left _ (hkw.2.2 ▸ hkw.2.1), Nat.min_self, scanOf_get _ _ hw _ _ _ _ _ _ hj, hm]

/-- **`Coc.over`**, at every verb: `overList` from `Over.seed` over the `n` elements `foRBits`
decodes, read as `Int64`. -/
theorem over_eq (op : Coc.Over) (nul : Int64) (md pk : ByteArray) (n : USize) :
    Coc.over op nul md pk n =
      overList op nul (op.seed nul)
        ((List.range n.toNat).map fun i => (Column.foRBits md pk (Column.blockStarts md) i).toInt64) := by
  rw [overList, foldl_filter, List.foldl_map]
  simp only [Coc.over, Coc.elems, List.foldl_map]
  congr 1
  funext acc i
  cases op.boolCast <;> cases h : ((Column.foRBits md pk (Column.blockStarts md) i).toInt64 == nul) <;>
    simp only [h, bne, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.true_or,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte]

end Rel.Verify
