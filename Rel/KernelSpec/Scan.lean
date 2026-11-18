import Rel.Kernel.Scan
import Rel.KernelSpec.Ids
import Rel.KernelSpec.Search

open Rel.Ext

/-! The scan primitive's law (design §4, `raw_scan`; `raw_kscan` until 6.11 takes the name back from the driver's): an
answer `kscan` returns is the segmented prefix fold of `Op.eval` over the raw rows of its columns, cut to the answer
type's width. -/

namespace Rel.Kernel
open Column

theorem rawAll_ok {t : QAtomicType} {n : USize} {e : Enc} {a : Array UInt64} (h : rawAll t n e = .ok a) :
    a = e.raw t n ∧ a.size = n.toNat := by
  unfold rawAll at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem mapM_rawAll {s : QAtomicType} {n : USize} :
    ∀ {es : List Enc} {cs : List (Array UInt64)}, es.mapM (rawAll s n) = .ok cs →
      cs = es.map (·.raw s n) ∧ ∀ e ∈ es, (e.raw s n).size = n.toNat
  | [], cs, h => by cases h; simp
  | e :: es, cs, h => by
    rw [List.mapM_cons] at h
    cases ha : rawAll s n e with
    | error m => rw [ha] at h; cases h
    | ok a =>
      cases hb : es.mapM (rawAll s n) with
      | error m => rw [ha, hb] at h; cases h
      | ok bs =>
        rw [ha, hb] at h; cases h
        obtain ⟨rfl, hs⟩ := rawAll_ok ha
        obtain ⟨rfl, hr⟩ := mapM_rawAll hb
        exact ⟨rfl, by simpa [hs] using hr⟩

/-- `kscan`'s row fold: from no rows, it answers one word a row, row `i`'s being `op` folded over the other columns'
row `i` from the carry `kscanRow` picks. -/
theorem foldlM_kscanRow (op : Op) (g seed : Array UInt64) (xs : List (Array UInt64)) :
    ∀ (m : Nat) (out : Array UInt64), (List.range m).foldlM (kscanRow op g seed xs) #[] = .ok out →
      out.size = m ∧ ∀ i (hi : i < out.size), xs.foldlM (fun a x => op.eval a (x[i]?.getD 0))
        (if 0 < i ∧ g[i]?.getD 0 = 0 then out[i - 1]?.getD 0 else seed[i]?.getD 0) = .ok out[i] := by
  intro m
  induction m with
  | zero => intro out h; cases h; exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | succ m ih =>
    intro out h
    rw [List.range_succ, List.foldlM_append] at h
    cases hm : (List.range m).foldlM (kscanRow op g seed xs) #[] with
    | error e => rw [hm] at h; cases h
    | ok mid =>
      obtain ⟨hs, hrow⟩ := ih mid hm
      cases ha : xs.foldlM (fun a x => op.eval a (x[m]?.getD 0))
          (if 0 < m ∧ g[m]?.getD 0 = 0 then mid[m - 1]?.getD 0 else seed[m]?.getD 0) with
      | error e => simp [hm, kscanRow, ha, bind, Except.bind, Functor.map, Except.map] at h
      | ok a =>
        simp only [hm, kscanRow, ha, bind, Except.bind, List.foldlM_cons, List.foldlM_nil, Functor.map, Except.map,
          pure, Except.pure] at h
        cases h
        refine ⟨by simp [hs], fun i hi => ?_⟩
        simp only [Array.size_push] at hi
        -- the carry at row `i ≤ m` reads row `i - 1 < m`, which the push leaves as it was
        have hc : (if 0 < i ∧ g[i]?.getD 0 = 0 then (mid.push a)[i - 1]?.getD 0 else seed[i]?.getD 0) =
            (if 0 < i ∧ g[i]?.getD 0 = 0 then mid[i - 1]?.getD 0 else seed[i]?.getD 0) := by
          by_cases h0 : 0 < i
          · simp only [Array.getElem?_push, show i - 1 ≠ mid.size by omega, if_false]
          · simp [h0]
        rw [hc]
        by_cases him : i < m
        · rw [Array.getElem_push_lt (by omega)]; exact hrow i (by omega)
        · obtain rfl : i = m := by omega
          subst hs
          rw [Array.getElem_push_eq]; exact ha

/-- **`raw_scan`** (design §4): an answer of `kscan` read back at its type `t` of `w` bytes is the word sequence `out`
of one word a row, each cut to `t`'s width (a boolean's to its low bit), where row `i` of `out` is `op` folded over the
columns after the first at row `i`, from the previous row's word, or from the first column's row `i` where `seg` starts
a segment there (row 0 always); every column held `n` raw words. -/
theorem raw_kscan (op : Op) (s t : QAtomicType) (w : Nat) (ht : t.width = some w) (n : USize) (seg : Enc)
    (es : List Enc) (e : Enc) (h : kscan op s t n seg es = .ok e) :
    (seg.raw .u1 n).size = n.toNat ∧ (∀ x ∈ es, (x.raw s n).size = n.toNat) ∧
    ∃ c cs, es = c :: cs ∧ ∃ out : Array UInt64, out.size = n.toNat ∧
      e.raw t n = out.map (fun v => UInt64.ofNat (v.toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) ∧
      ∀ i (hi : i < out.size), (cs.map (·.raw s n)).foldlM (fun a x => op.eval a (x[i]?.getD 0))
        (if 0 < i ∧ (seg.raw .u1 n)[i]?.getD 0 = 0 then out[i - 1]?.getD 0 else (c.raw s n)[i]?.getD 0) =
          .ok out[i] := by
  unfold kscan at h
  cases hg : rawAll .u1 n seg with
  | error m => simp [hg, bind, Except.bind] at h
  | ok g =>
    obtain ⟨rfl, hgs⟩ := rawAll_ok hg
    cases hc : es.mapM (rawAll s n) with
    | error m => simp [hg, hc, bind, Except.bind] at h
    | ok cs =>
      obtain ⟨rfl, hsz⟩ := mapM_rawAll hc
      cases es with
      | nil => simp [hg, hc, bind, Except.bind] at h
      | cons c es =>
        cases hf : (List.range n.toNat).foldlM (kscanRow op (seg.raw .u1 n) (c.raw s n)
            (es.map (·.raw s n))) #[] with
        | error m => simp [hg, hc, hf, bind, Except.bind] at h
        | ok out =>
          obtain ⟨hos, hrow⟩ := foldlM_kscanRow _ _ _ _ _ _ hf
          simp only [hg, hc, hf, bind, Except.bind, List.map_cons, ht, pure, Except.pure] at h
          refine ⟨hgs, hsz, c, es, rfl, out, hos, ?_, hrow⟩
          by_cases hb : t = .u1
          · subst hb
            simp only [if_true] at h
            cases h
            apply Array.ext (by simp [Enc.raw, hos])
            intro i h1 h2
            have hi : i < n.toNat := by simpa [hos] using h2
            have hget : out[i]? = some out[i] := Array.getElem?_eq_getElem (by simpa using h2)
            have hp := Verify.idAt_packIds_sub (w := 1) (n := n.toNat) (i := i)
              (f := fun i => (out[i]?.getD 0).toNat % 2) (.inl rfl) hi (Nat.mod_lt _ (by decide))
            rw [Verify.idAt_one] at hp
            simp only [hget, Option.getD_some] at hp
            simp only [if_true, Enc.raw, Array.getElem_map, Array.getElem_range]
            apply UInt64.toNat_inj.1
            split at hp <;> rename_i hbit <;> simp only [hbit] <;> simp [← hp]
          · simp only [hb, if_false] at h
            cases h
            -- the words, encoded whole at 8 bytes, read back exactly (`foRBits_encode`), then cut to `t`'s width
            have h8 : USize.ofNat32 8 (by decide) = (8 : Nat).toUSize := USize.toNat_inj.mp (by
              rcases System.Platform.numBits_eq with h | h <;> simp [h])
            generalize hX : out.foldl (init := ByteArray.empty) (fun acc w => Column.pushBits acc w 8) = X
            obtain ⟨hxs, -, hxg⟩ := Verify.foldl_pushBits (fun v => v) 8 (by decide) out.toList ByteArray.empty
            rw [Array.foldl_toList, hX] at hxs hxg
            simp only [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Array.length_toList] at hxs hxg
            rw [Verify.raw_foR t w ht hb]
            apply Array.ext (by simp [hos])
            intro i h1 h2
            have hi : i < out.size := by simpa [hos] using h1
            have hu : Coc.unbias 8 (Coc.keyAt 8 X i) = out[i] := by
              have h1 := Verify.unbias_keyAt 8 (by decide) (by decide) X i
              rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), Nat.mul_comm, hxg i (by simpa using hi),
                Verify.ofNat_toNat_mod64, Array.getElem_toList] at h1
              exact UInt64.toNat_inj.mp h1
            simp only [Array.getElem_map, Array.getElem_range, hb, if_false, h8, Coc.encode]
            rw [Verify.foRBits_encode Column.lgEnc (by decide) 8 (by decide) (by decide) X i (by rw [hxs]; omega), hu]

end Rel.Kernel

/-- info: 'Rel.Kernel.raw_kscan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Kernel.raw_kscan
