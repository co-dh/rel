import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.KernelSpec.Gather
import Rel.Kernel.Structural
import Rel.KernelSpec.Alp
import Rel.Kernel.Value

/-! The part of `Rel.Verify.AlpConcat` the Rel kernels reach; `Rel.Verify.AlpConcat` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel

/-- An ALP element is no wider than the blob's element size: an exception is read at it and a
decimal of a `real` column is narrowed to four bytes. -/
theorem alpBits_lt (M P a : ByteArray) (s : Array Nat) (i : Nat) :
    (Column.alpBits M P a s i).toNat < 2 ^ (8 * Column.alpEsz a) := by
  unfold Column.alpBits
  split
  · exact bitsAt_lt _ _ _ (by unfold Column.alpEsz; split <;> decide)
  · unfold Column.alpDec Column.alpEsz
    cases Column.alpF32 a
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact UInt64.toNat_lt _
    · simp only [↓reduceIte, UInt32.toNat_toUInt64]; exact Nat.lt_of_lt_of_le (UInt32.toNat_lt _) (by decide)

/-- **`Coc.alpDecode` at the blob's element size reads back `Column.alpBits`**, the ALP counterpart
of `decodeW`: element `i` of the decode is stored element `i`, every bit of it. -/
theorem elemsW_alpDecode_alpBits (M P a : ByteArray) (n w : USize) (hw : w.toNat = Column.alpEsz a) :
    elemsW w.toNat (Coc.alpDecode w M P a n) =
      (List.range n.toNat).map (Column.alpBits M P a (Column.blockStarts M)) := by
  have hw8 : Column.alpEsz a ≤ 8 := by unfold Column.alpEsz; split <;> decide
  have hw0 : 0 < Column.alpEsz a := by unfold Column.alpEsz; split <;> decide
  rw [elemsW_alpDecode w (by omega) (by omega)]
  simp only [Coc.alpElems, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [hw, Nat.mod_eq_of_lt (alpBits_lt _ _ _ _ _), UInt64.ofNat_toNat]

/-- **The ALP round trip on the decoded words**, at either element width: decoding what
`Coc.alpEncodeAt f32 x` wrote, at `x`'s element count, gives `x`'s words. -/
theorem elemsW_alpDecode_alpEncodeAt (f32 : Bool) (w : Nat) (hw : (if f32 then 4 else 8) = w) (x : ByteArray)
    (hx : x.size / w < 2 ^ 32) :
    elemsW w (Coc.alpDecode w.toUSize (Coc.alpEncodeAt f32 x).1 (Coc.alpEncodeAt f32 x).2.1
      (Coc.alpEncodeAt f32 x).2.2 (x.size / w).toUSize) = elemsW w x := by
  obtain ⟨hf, hrt⟩ := alpBits_alpEncodeAt f32 Column.lgEnc (by decide) w hw x hx
  have hw8 : w ≤ 8 := by subst hw; cases f32 <;> decide
  have hwU : w.toUSize.toNat = w :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw8 (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  have hN : (x.size / w).toUSize.toNat = x.size / w := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hx USize.le_size)
  have rd := elemsW_alpDecode_alpBits (Coc.alpEncodeAt f32 x).1 (Coc.alpEncodeAt f32 x).2.1
    (Coc.alpEncodeAt f32 x).2.2 (x.size / w).toUSize w.toUSize (by rw [hwU]; unfold Column.alpEsz; rw [hf, hw])
  rw [hwU, hN] at rd
  rw [rd, elemsW]
  exact List.map_congr_left fun i hi => hrt i (List.mem_range.1 hi)

/-- The `w`-byte elements of a join are the parts', when the first part ends on an element. -/
theorem elemsW_append (w : Nat) (hw : 0 < w) (a b : ByteArray) (ha : a.size % w = 0) :
    elemsW w (a ++ b) = elemsW w a ++ elemsW w b := by
  obtain ⟨q, hq⟩ : ∃ q, a.size = q * w := ⟨a.size / w, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ha)).symm⟩
  have hqa : a.size / w = q := by rw [hq, Nat.mul_div_cancel _ hw]
  have hs : (a ++ b).size / w = q + b.size / w := by
    rw [ByteArray.size_append, hq, Nat.mul_comm, Nat.mul_add_div hw]
  apply List.ext_getElem (by simp only [elemsW, List.length_append, List.length_map, List.length_range, hs, hqa])
  intro i h1 h2
  simp only [elemsW, List.length_map, List.length_range, hs] at h1
  by_cases hi : i < q
  · rw [List.getElem_append_left (by simp only [elemsW, List.length_map, List.length_range, hqa]; exact hi)]
    simp only [elemsW, List.getElem_map, List.getElem_range]
    have : i * w + w ≤ q * w := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    exact bitsAt_shift _ _ _ _ w fun t ht => ba_append_left _ _ _ (by omega)
  · rw [List.getElem_append_right (by simp only [elemsW, List.length_map, List.length_range, hqa]; omega)]
    simp only [elemsW, List.getElem_map, List.getElem_range, List.length_map, List.length_range, hqa]
    have : (i - q) * w + q * w = i * w := by rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    exact bitsAt_shift _ _ _ _ w fun t ht => by
      rw [show i * w + t = a.size + ((i - q) * w + t) by omega, ba_append_right]

/-- A left fold of joins, read in `w`-byte elements, is its parts' elements in order, when every part
ends on an element. `concatBytes` is this fold. -/
theorem elemsW_foldl_append (w : Nat) (hw : 0 < w) (parts : List ByteArray) (acc : ByteArray)
    (ha : acc.size % w = 0) (hp : ∀ p ∈ parts, p.size % w = 0) :
    elemsW w (parts.foldl (· ++ ·) acc) = elemsW w acc ++ (parts.map (elemsW w)).flatten := by
  induction parts generalizing acc with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih _ (by rw [ByteArray.size_append, Nat.add_mod, ha, hp p (by simp)]; simp)
      (fun r hr => hp r (by simp [hr])), elemsW_append w hw acc p ha]
    simp [List.append_assoc]

/-- **`concatALP` read back**: the answer's flag is the join's width, and its decode at the joined
count is every part's stored elements, part after part. Each part is read at its own count, the one
stored at bytes `8k`–`8k+7` of `ns`, and must be of the join's width; the joined count is under
`2 ^ 32`, the bound `exc_off` stores at. -/
theorem elemsW_concatALP (ew : USize) (ns : ByteArray) (metas packs alps : Array ByteArray) (m : Nat)
    (hm : m = min (ns.size / 8) (min metas.size (min packs.size alps.size)))
    (hf : ∀ k < m, Column.alpF32 alps[k]! = (ew == 4)) (hn : ∀ k < m, (Column.bitsAt ns (8 * k) 8).toNat < USize.size)
    (hx : ((List.range m).map fun k => (Column.bitsAt ns (8 * k) 8).toNat).sum < 2 ^ 32) :
    Column.alpF32 (concatALP ew ns metas packs alps).2.2 = (ew == 4) ∧
    elemsW (if ew == 4 then 4 else 8) (Coc.alpDecode (if ew == 4 then 4 else 8) (concatALP ew ns metas packs alps).1
      (concatALP ew ns metas packs alps).2.1 (concatALP ew ns metas packs alps).2.2
      ((List.range m).map fun k => (Column.bitsAt ns (8 * k) 8).toNat).sum.toUSize) =
      ((List.range m).map fun k => (List.range (Column.bitsAt ns (8 * k) 8).toNat).map
        (Column.alpBits metas[k]! packs[k]! alps[k]! (Column.blockStarts metas[k]!))).flatten := by
  have hwE : (if ew == 4 then (4 : USize) else 8) = (if ew == 4 then 4 else 8 : Nat).toUSize := by split <;> rfl
  rw [hwE]
  generalize hwN : (if ew == 4 then 4 else 8 : Nat) = w
  have hw0 : 0 < w := by rw [← hwN]; split <;> decide
  have hw8 : w ≤ 8 := by rw [← hwN]; split <;> decide
  have hwU : w.toUSize.toNat = w :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw8 (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  -- each part: its size and its words
  have hD : ∀ k < m, (Coc.alpDecode w.toUSize metas[k]! packs[k]! alps[k]! (Column.bitsAt ns (8 * k) 8).toNat.toUSize).size = w * (Column.bitsAt ns (8 * k) 8).toNat ∧
      elemsW w (Coc.alpDecode w.toUSize metas[k]! packs[k]! alps[k]! (Column.bitsAt ns (8 * k) 8).toNat.toUSize) =
        (List.range (Column.bitsAt ns (8 * k) 8).toNat).map (Column.alpBits metas[k]! packs[k]! alps[k]! (Column.blockStarts metas[k]!)) := by
    intro k hk
    have hnk : (Column.bitsAt ns (8 * k) 8).toNat.toUSize.toNat = (Column.bitsAt ns (8 * k) 8).toNat := USize.toNat_ofNat_of_lt' (hn k hk)
    refine ⟨?_, ?_⟩
    · rw [alpDecode_eq, (foldl_pushBits id _ (by rw [hwU]; exact hw8) _ ByteArray.empty).1]
      simp only [Coc.alpElems, List.length_map, List.length_range, hnk, hwU]
      exact Nat.zero_add _
    · have := elemsW_alpDecode_alpBits metas[k]! packs[k]! alps[k]! (Column.bitsAt ns (8 * k) 8).toNat.toUSize w.toUSize
        (by rw [hwU]; unfold Column.alpEsz; rw [hf k hk, hwN])
      rwa [hwU, hnk] at this
  -- the join
  obtain ⟨X, hX⟩ : ∃ X, X = concatBytes ((Array.range m).map fun k =>
      Coc.alpDecode w.toUSize metas[k]! packs[k]! alps[k]! (Column.bitsAt ns (8 * k) 8).toNat.toUSize) := ⟨_, rfl⟩
  have he : concatALP ew ns metas packs alps = Coc.alpEncodeAt (ew == 4) X := by
    rw [hX, hm, ← hwN, ← hwE]; rfl
  have hXw : elemsW w X = ((List.range m).map fun k => (List.range (Column.bitsAt ns (8 * k) 8).toNat).map
      (Column.alpBits metas[k]! packs[k]! alps[k]! (Column.blockStarts metas[k]!))).flatten := by
    rw [hX, concatBytes, ← Array.foldl_toList, elemsW_foldl_append w hw0 _ _ (Nat.zero_mod _) (fun p hp => by
      rw [Array.toList_map, toList_range, List.mem_map] at hp
      obtain ⟨k, hk, rfl⟩ := hp
      rw [(hD k (List.mem_range.1 hk)).1, Nat.mul_mod_right])]
    rw [Array.toList_map, toList_range, List.map_map]
    simp only [elemsW, show ByteArray.empty.size = 0 from rfl, Nat.zero_div, List.range_zero, List.map_nil,
      List.nil_append]
    congr 1
    exact List.map_congr_left fun k hk => (hD k (List.mem_range.1 hk)).2
  have hXN : X.size / w = ((List.range m).map fun k => (Column.bitsAt ns (8 * k) 8).toNat).sum := by
    have := congrArg List.length hXw
    simp only [elemsW, List.length_map, List.length_range, List.length_flatten, List.map_map] at this
    rw [this]; congr 1
    exact List.map_congr_left fun k _ => by simp
  rw [he]
  refine ⟨(alpBits_alpEncodeAt (ew == 4) Column.lgEnc (by decide) w hwN X (by rw [hXN]; exact hx)).1, ?_⟩
  rw [← hXN, elemsW_alpDecode_alpEncodeAt (ew == 4) w hwN X (by rw [hXN]; exact hx), hXw]

end Rel.Verify
