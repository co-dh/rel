import Rel.Kernel.Driver
import Rel.KernelSpec.Alp
import Rel.KernelSpec.Search

open Rel.Ext

/-! The driver law of coc plan step 4: `ofRaw` written at `t` reads back through `Enc.raw` as the elements it was
handed, whichever form `Enc.answer` leaves the payload in, when each is below `2 ^ (8 * w)`; and each driver's answer,
read back the same way, is what its docstring says. `raw` reads every form zero-extended (`raw_lt`), so the range is
the whole hypothesis. -/

namespace Rel.Kernel
open Column

/-- A fixed-width type's width is one to eight bytes, two or more where it is Frame-of-Reference encoded and four or
eight where it is ALP encoded. -/
theorem width_cases (t : QAtomicType) (w : Nat) (ht : t.width = some w) :
    1 ≤ w ∧ w ≤ 8 ∧ (encodes t = true → 1 < w) ∧ (alpEncodes t = true → w = 4 ∨ w = 8) := by
  cases t <;> simp_all [QAtomicType.width, encodes, alpEncodes] <;> subst ht <;> decide

/-- `Enc.answer` leaves a dense payload dense, ALP encoded, or Frame-of-Reference encoded. -/
theorem answer_bytes (t : QAtomicType) (w : Nat) (ht : t.width = some w) (n : USize) (b : ByteArray) :
    Enc.answer (X := Empty) t n (.bytes b) = .bytes b ∨
    (alpEncodes t = true ∧ Enc.answer (X := Empty) t n (.bytes b) =
      .alp (Coc.alpEncodeAt (w == 4) b).1 (Coc.alpEncodeAt (w == 4) b).2.1 (Coc.alpEncodeAt (w == 4) b).2.2) ∨
    (encodes t = true ∧ Enc.answer (X := Empty) t n (.bytes b) =
      .foR (Coc.encode w.toUSize b).1 (Coc.encode w.toUSize b).2) := by
  cases t <;> simp only [QAtomicType.width, Option.some.injEq, reduceCtorEq] at ht <;> subst ht <;>
    simp only [Enc.answer, QAtomicType.width, alpEncodes, encodes, Coc.encodeBelow, Coc.alpEncodeBelow64,
      Coc.alpEncodeBelow32, Coc.alpEncode64, Coc.alpEncode32] <;>
    (repeat' split) <;> simp_all

/-- `dense`'s element `i` read back at `w` bytes is `xs[i]` on its low `8 * w` bits (`Verify.foldl_pushBits`). -/
theorem dense_bits (w : Nat) (hw : w ≤ 8) (xs : Array UInt64) :
    (dense w xs).size = w * xs.size ∧
    ∀ i (h : i < xs.size), bitsAt (dense w xs) (i * w) w = UInt64.ofNat (xs[i].toNat % 2 ^ (8 * w)) := by
  obtain ⟨hs, -, hb⟩ := Verify.foldl_pushBits id w hw xs.toList .empty
  simp only [id, ByteArray.size_empty, Nat.zero_add, Array.length_toList, Array.getElem_toList,
    Array.foldl_toList] at hs hb
  exact ⟨by rw [dense, hs], fun i h => by rw [dense, Nat.mul_comm, hb i h]⟩

/-- The raw elements of a boolean `bits` column are `0` or `1`. -/
theorem raw_boolean_le (n : USize) (e : Enc) : ∀ v ∈ e.raw .u1 n, v ≤ 1 := by
  intro v hv
  cases e <;> simp only [Enc.raw, Array.mem_map, Array.mem_range, Array.not_mem_empty] at hv
  obtain ⟨i, -, rfl⟩ := hv; split <;> decide

/-- **The rule `Enc.raw` keeps**: an element of a `w`-byte type is below `2 ^ (8 * w)`, in every form. -/
theorem raw_lt (t : QAtomicType) (w : Nat) (ht : t.width = some w) (n : USize) (e : Enc) :
    ∀ v ∈ e.raw t n, v.toNat < 2 ^ (8 * w) := by
  obtain ⟨hw1, hw8, -, -⟩ := width_cases t w ht
  have hM : 2 ^ (8 * w) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hmod : ∀ x : UInt64, (UInt64.ofNat (x.toNat % 2 ^ (8 * w))).toNat < 2 ^ (8 * w) := fun x => by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hM)]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  intro v hv
  by_cases hb : t = .u1
  · subst hb
    exact Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.1 (raw_boolean_le n e v hv))
      (Nat.lt_of_lt_of_le (show (1 : UInt64).toNat < 2 ^ 8 by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  cases e with
  | bytes b =>
    rw [Verify.raw_bytes t w ht hb] at hv; obtain ⟨i, -, rfl⟩ := Array.mem_map.1 hv; exact Verify.bitsAt_lt _ _ _ hw8
  | foR M P => rw [Verify.raw_foR t w ht hb] at hv; obtain ⟨i, -, rfl⟩ := Array.mem_map.1 hv; exact hmod _
  | alp M P a => rw [Verify.raw_alp t w ht hb] at hv; obtain ⟨i, -, rfl⟩ := Array.mem_map.1 hv; exact hmod _
  | _ => cases t <;> simp_all [Enc.raw, QAtomicType.width]

/-- **The driver law**: `ofRaw t n xs` read back by `Enc.raw` at `t` is `xs`, each element below `2 ^ (8 * w)` — a
boolean's being `0`/`1`, and an ALP type's column below `2 ^ 32` elements (`Verify.alpBits_alpEncodeAt`). -/
theorem raw_ofRaw (t : QAtomicType) (w : Nat) (ht : t.width = some w) (n : USize) (xs : Array UInt64)
    (hn : xs.size = n.toNat) (hr : ∀ v ∈ xs, v.toNat < 2 ^ (8 * w)) (hbool : t = .u1 → ∀ v ∈ xs, v ≤ 1)
    (h32 : alpEncodes t = true → n.toNat < 2 ^ 32) :
    (ofRaw t n xs).raw t n = xs := by
  obtain ⟨hw1, hw8, hfor, halp⟩ := width_cases t w ht
  by_cases hb : t = .u1
  · subst hb
    simp only [ofRaw, Enc.raw]
    apply Array.ext (by simp [hn])
    intro i h1 h2
    have hx := hbool rfl xs[i] (Array.getElem_mem _)
    have hp := Verify.idAt_packIds_sub (w := 1) (n := n.toNat) (i := i)
      (f := fun i => (xs[i]?.getD 0).toNat) (.inl rfl) (by simpa using h1) (by
        simp only [Array.getElem?_eq_getElem h2, Option.getD_some]; exact Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.1 hx) (by decide))
    rw [Verify.idAt_one] at hp
    simp only [Array.getElem_map, Array.getElem_range]
    simp only [Array.getElem?_eq_getElem h2, Option.getD_some] at hp
    split at hp <;> rename_i hc <;> simp only [hc] <;> apply UInt64.toNat_inj.1 <;> simp [← hp]
  have hof : ofRaw t n xs = Enc.answer t n (.bytes (dense w xs)) := by
    cases t <;> simp_all [ofRaw, QAtomicType.width]
  obtain ⟨hds, hdb⟩ := dense_bits w hw8 xs
  have hdn : (dense w xs).size / w = n.toNat := by rw [hds, ← hn, Nat.mul_div_cancel_left _ (by omega)]
  -- every form reads element `i` back as the dense bits
  obtain ⟨g, hg, hgi⟩ : ∃ g : Nat → UInt64, (ofRaw t n xs).raw t n = (Array.range n.toNat).map g ∧
      ∀ i < n.toNat, g i = bitsAt (dense w xs) (i * w) w := by
    rw [hof]
    rcases answer_bytes t w ht n (dense w xs) with e | ⟨ha, e⟩ | ⟨he, e⟩ <;> rw [e]
    · exact ⟨_, Verify.raw_bytes t w ht hb n _, fun i _ => rfl⟩
    · refine ⟨_, Verify.raw_alp t w ht hb n _ _ _, fun i hi => ?_⟩
      have := (Verify.alpBits_alpEncodeAt (w == 4) lgEnc (by decide) w
        (by rcases halp ha with rfl | rfl <;> rfl) (dense w xs) (by rw [hdn]; exact h32 ha)).2 i (by omega)
      rw [this, Nat.mod_eq_of_lt (Verify.bitsAt_lt _ _ _ hw8), UInt64.ofNat_toNat]
    · exact ⟨_, Verify.raw_foR t w ht hb n _ _, fun i hi => by
        exact (congrArg UInt64.ofNat (Verify.foRBits_encode_bits lgEnc (by decide) w (hfor he) hw8 _ i (by omega))).trans
          UInt64.ofNat_toNat⟩
  rw [hg]
  apply Array.ext (by simp [hn])
  intro i h1 h2
  simp only [Array.getElem_map, Array.getElem_range]
  rw [hgi i (by simpa using h1), hdb i (by simpa using h2), Nat.mod_eq_of_lt (hr _ (Array.getElem_mem _)),
    UInt64.ofNat_toNat]

/-- `map`: element `i` of the answer is `f` of element `i` of every source, where each such is below `2 ^ (8 * w)`. -/
theorem raw_map (s t : QAtomicType) (w : Nat) (ht : t.width = some w) (n : USize) (f : List UInt64 → UInt64)
    (es : List Enc) (hr : ∀ i < n.toNat, (f (es.map fun e => (e.raw s n)[i]?.getD 0)).toNat < 2 ^ (8 * w))
    (hbool : t = .u1 → ∀ l, f l ≤ 1) (h32 : alpEncodes t = true → n.toNat < 2 ^ 32) :
    (map s t n f es).raw t n = (Array.range n.toNat).map fun i => f (es.map fun e => (e.raw s n)[i]?.getD 0) := by
  rw [map, raw_ofRaw t w ht n _ (by simp)
    (fun v hv => by obtain ⟨i, hi, rfl⟩ := Array.mem_map.1 hv; exact hr i (Array.mem_range.1 hi))
    (fun hb v hv => by obtain ⟨i, -, rfl⟩ := Array.mem_map.1 hv; exact hbool hb _) h32]

/-- `fold` is the left fold over the source's raw elements in position order. -/
theorem fold_raw {α : Type} (s : QAtomicType) (n : USize) (step : α → UInt64 → α) (seed : α) (e : Enc) :
    fold s n step seed e = (e.raw s n).toList.foldl step seed := by
  rw [fold, Array.foldl_toList]

/-- The prefix fold `scan` runs: from `(a, out)`, it appends the fold of each nonempty prefix of `l` to `out`. -/
theorem foldl_scan (step : UInt64 → UInt64 → UInt64) (l : List UInt64) (a : UInt64) (out : Array UInt64) :
    (l.foldl (fun (p : UInt64 × Array UInt64) v => (step p.1 v, p.2.push (step p.1 v))) (a, out)).2.toList =
      out.toList ++ (List.range l.length).map fun i => (l.take (i + 1)).foldl step a := by
  induction l generalizing a out with
  | nil => simp
  | cons v l ih => rw [List.foldl_cons, ih, List.length_cons, List.range_succ_eq_map]; simp

/-- `scan`: element `i` of the answer is `step` folded over the source's first `i + 1` raw elements from `seed`, where
each such is below `2 ^ (8 * w)`; the source holds `n` raw elements at `s`. -/
theorem raw_scan (s t : QAtomicType) (w : Nat) (ht : t.width = some w) (n : USize)
    (step : UInt64 → UInt64 → UInt64) (seed : UInt64) (e : Enc) (hs : (e.raw s n).size = n.toNat)
    (hr : ∀ i < n.toNat, (((e.raw s n).toList.take (i + 1)).foldl step seed).toNat < 2 ^ (8 * w))
    (hbool : t = .u1 → ∀ a v, step a v ≤ 1) (h32 : alpEncodes t = true → n.toNat < 2 ^ 32) :
    ((scan s t n step seed e).raw t n).toList =
      (List.range n.toNat).map fun i => ((e.raw s n).toList.take (i + 1)).foldl step seed := by
  have hl := foldl_scan step (e.raw s n).toList seed #[]
  rw [Array.foldl_toList] at hl
  simp only [List.nil_append, Array.length_toList] at hl
  have hsz : ((e.raw s n).foldl (fun (p : UInt64 × Array UInt64) v => (step p.1 v, p.2.push (step p.1 v)))
      (seed, #[])).2.size = n.toNat := by rw [← Array.length_toList, hl]; simp [hs]
  rw [scan, raw_ofRaw t w ht n _ hsz (fun v hv => ?_) (fun hb v hv => ?_) h32, hl, hs]
  · rw [← Array.mem_toList_iff, hl] at hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact hr i (by simpa [hs] using hi)
  · rw [← Array.mem_toList_iff, hl] at hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    cases hc : ((e.raw s n).toList.take (i + 1)).reverse with
    | nil => (simp_all [List.mem_range]) <;> omega
    | cons v l =>
      rw [← List.reverse_reverse ((e.raw s n).toList.take (i + 1)), hc, List.reverse_cons, List.foldl_append]
      exact hbool hb _ _

/-- `permute`: the answer's elements are the source's at the positions `ix`, `fill` past its end, `fill` below
`2 ^ (8 * w)` as every raw element is (`raw_lt`). -/
theorem raw_permute (s : QAtomicType) (w : Nat) (hs : s.width = some w) (n m : USize) (ix : Array Nat)
    (fill : UInt64) (e : Enc) (hm : ix.size = m.toNat) (hr : fill.toNat < 2 ^ (8 * w)) (hbool : s = .u1 → fill ≤ 1)
    (h32 : alpEncodes s = true → m.toNat < 2 ^ 32) :
    (permute s n m ix fill e).raw s m = ix.map fun j => (e.raw s n)[j]?.getD fill := by
  rw [permute, raw_ofRaw s w hs m _ (by simp [hm]) (fun v hv => ?_) (fun hb v hv => ?_) h32]
  · obtain ⟨j, -, rfl⟩ := Array.mem_map.1 hv
    cases h : (e.raw s n)[j]? with
    | none => exact hr
    | some v => exact raw_lt s w hs n e v (Array.mem_of_getElem? h)
  · obtain ⟨j, -, rfl⟩ := Array.mem_map.1 hv
    subst hb
    cases h : (e.raw .u1 n)[j]? with
    | none => exact hbool rfl
    | some v => exact raw_boolean_le n e v (Array.mem_of_getElem? h)

end Rel.Kernel
