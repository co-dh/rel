import QLean.RelPart.Verify.Encoding
import QLean.RelPart.Kernel.Coc
import QLean.RelPart.Kernel.Reduce
import QLean.RelPart.Value
import QLean.RelPart.Kernel.Search
import QLean.RelPart.Kernel.Elementwise

/-! The part of `QLean.Verify.Where` the Rel kernels reach; `QLean.Verify.Where` imports it. -/


namespace QLean.Verify
open QLean QLean.Kernel

/-- `whereBits n bits` is eight bytes per set bit below `n`, and long `j` is the `j`-th of them. -/
theorem whereBits_spec (n : USize) (bits : ByteArray) :
    (whereBits n bits).size = 8 * ((List.range n.toNat).filter (Column.bitAt bits)).length ∧
    ∀ j (h : j < ((List.range n.toNat).filter (Column.bitAt bits)).length),
      (Column.bitsAt (whereBits n bits) (j * 8) 8).toNat = ((List.range n.toNat).filter (Column.bitAt bits))[j] := by
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun i : Nat => (Int64.ofNat i).toUInt64) 8 (Nat.le_refl 8)
    ((List.range n.toNat).filter (Column.bitAt bits)) ByteArray.empty
  refine ⟨by simpa [whereBits] using hs, fun j hj => ?_⟩
  have h := hg j hj
  have hl : ((List.range n.toNat).filter (Column.bitAt bits))[j] < n.toNat :=
    List.mem_range.mp (List.mem_filter.mp (List.getElem_mem hj)).1
  have hn : n.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le n.toNat_lt_size USize.size_le
  rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add] at h
  simp only [whereBits]
  rw [Nat.mul_comm j, h]
  rw [show 8 * 8 = 64 from rfl, ofNat_toNat_mod64]
  exact Nat.mod_eq_of_lt (Nat.lt_trans hl hn)

/-- `gatherBytes` at a width up to eight holds one element per index, and element `j` is the source's
element `idx[j]` — the index read unsigned — when that is below the source's count, and the low `w`
bytes of `fill` otherwise, which is where a negative index and `0N` go too (`gatherAt`). -/
theorem gatherBytes_spec (w : USize) (hw : w.toNat ≤ 8) (fill : UInt64) (src idx : ByteArray) :
    (gatherBytes w fill src idx).size = w.toNat * (idx.size / 8) ∧
    ∀ j < idx.size / 8, Column.bitsAt (gatherBytes w fill src idx) (j * w.toNat) w.toNat =
      if (Column.bitsAt idx (j * 8) 8).toNat < src.size / w.toNat
      then Column.bitsAt src ((Column.bitsAt idx (j * 8) 8).toNat * w.toNat) w.toNat
      else UInt64.ofNat (fill.toNat % 2 ^ (8 * w.toNat)) := by
  let G : Nat → UInt64 := fun j => match gatherAt (src.size / w.toNat) idx j with
    | some i => Column.bitsAt src (i * w.toNat) w.toNat
    | none => fill
  have hf : gatherBytes w fill src idx =
      (List.range (idx.size / 8)).foldl (fun acc j => Column.pushBits acc (G j) w.toNat) ByteArray.empty := by
    simp only [gatherBytes]
    congr 1
    funext acc j
    simp only [G]
    rcases gatherAt (src.size / w.toNat) idx j with _ | i <;> simp [hw]
  obtain ⟨hs, -, hg⟩ := foldl_pushBits G w.toNat hw (List.range (idx.size / 8)) ByteArray.empty
  rw [hf]
  refine ⟨by simpa using hs, fun j hj => ?_⟩
  have h := hg j (by simpa using hj)
  simp only [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at h
  rw [Nat.mul_comm j, h]
  simp only [G, gatherAt]
  by_cases hi : (Column.bitsAt idx (j * 8) 8).toNat < src.size / w.toNat
  · simp only [hi, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (bitsAt_lt _ _ _ hw), UInt64.ofNat_toNat]
  · simp only [hi, ↓reduceIte]

/-- **`gatherBytes` at `whereBits`' indices** holds, at `j`, the source element at the `j`-th set bit, when
every set bit is below the source's count. -/
theorem gatherBytes_whereBits (w : USize) (hw : w.toNat ≤ 8) (fill : UInt64) (src : ByteArray) (n : USize)
    (bits : ByteArray) (hL : ∀ i ∈ (List.range n.toNat).filter (Column.bitAt bits), i < src.size / w.toNat) :
    (gatherBytes w fill src (whereBits n bits)).size =
        w.toNat * ((List.range n.toNat).filter (Column.bitAt bits)).length ∧
    ∀ j (h : j < ((List.range n.toNat).filter (Column.bitAt bits)).length),
      Column.bitsAt (gatherBytes w fill src (whereBits n bits)) (j * w.toNat) w.toNat =
        Column.bitsAt src (((List.range n.toNat).filter (Column.bitAt bits))[j] * w.toNat) w.toNat := by
  obtain ⟨hs, hj⟩ := whereBits_spec n bits
  obtain ⟨gs, gj⟩ := gatherBytes_spec w hw fill src (whereBits n bits)
  have hc : (whereBits n bits).size / 8 = ((List.range n.toNat).filter (Column.bitAt bits)).length := by
    rw [hs, Nat.mul_div_cancel_left _ (by decide)]
  rw [hc] at gs gj
  exact ⟨gs, fun j h => by rw [gj j h, hj j h, if_pos (hL _ (List.getElem_mem h))]⟩

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

/-- `overBytes`, at every verb: `overList` from the dense seed over the elements. -/
theorem overBytes_eq (op : Coc.Over) (cls : UInt8) (nul : Int64) (b : ByteArray) :
    overBytes op cls nul b = overList op nul (op.denseSeed cls nul) (denseElems cls b) := by
  rw [overList, foldl_filter, denseElems, List.foldl_map]
  simp only [overBytes]
  congr 1
  funext acc i
  cases op.boolCast <;> cases h : (Ew.signed cls (Ew.elem cls b i) == nul) <;>
    simp only [h, bne, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.true_or,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte]

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

/-- `sum` over a dense payload: the elements that are not `nul`, added as integers and wrapped to 64
bits once. -/
theorem overBytes_add (cls : UInt8) (nul : Int64) (b : ByteArray) :
    (overBytes .add cls nul b).toInt =
      ((((denseElems cls b).filter (· != nul)).map Int64.toInt).sum).bmod (2 ^ 64) := by
  rw [overBytes_eq, overList]
  have hs : Coc.Over.denseSeed .add cls nul = 0 := by simp [Coc.Over.denseSeed, Coc.Over.seed]
  have hst : Coc.Over.step .add = (· + ·) := rfl
  rw [hs, hst, foldl_add_int64, Int64.toInt_zero, Int.zero_add]
  simp [Coc.Over.boolCast]

end QLean.Verify
