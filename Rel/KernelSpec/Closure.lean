import Rel.KernelSpec.Alp
import Rel.KernelSpec.Scan
import Rel.KernelSpec.Scatter
import Rel.KernelSpec.KGather
import Rel.KernelSpec.KSeen

/-! The closure law (PLAN 6.14): a column a kernel answers is a column, `Ext.Enc.WF` at the type and length its body
determines, and a column every kernel reads, `Enc.Valid`. Every one of the five answers `wordsFoR` of its words
(`kscan` and `kscatter` spell it `Coc.encode` at 8 bytes, the same term), so `wordsFoR_closed` carries the law and each
kernel's theorem only names its words and their count. A composition's success is then a chain of these laws. -/

namespace Rel.Kernel
open Ext.Enc

/-- The arguments `foRWords` reads at `n` rows, its test stated as a proposition: a `foR` column in the writers' layout
(`Coc.foRStd`) with a stored `lg` the layout admits, or `pos`. `foRWords_valid` is its reading, `Enc.Valid.wf` what it
gives `Ext.Enc.WF`. -/
def Enc.Valid (n : USize) : Enc → Prop
  | .foR md pk => Column.lgOk md = true ∧ Coc.foRStd n md pk = true
  | .pos => True
  | _ => False

end Rel.Kernel

namespace Rel.Verify
open Rel.Kernel Ext.Enc

/-- **The reader accepts exactly a valid column**: `foRWords` answers the raw words of what `Enc.Valid` admits, and
an error at everything else. -/
theorem foRWords_valid (what : String) (m : USize) (e : Enc) :
    (Enc.Valid m e → foRWords what m e = .ok (raw .i64 m e)) ∧ ∀ ws, foRWords what m e = .ok ws → Enc.Valid m e := by
  have hv : foROk m e = true ↔ Enc.Valid m e := by cases e <;> simp [Enc.Valid]
  unfold foRWords
  refine ⟨fun h => by rw [if_pos (hv.2 h)], fun ws h => ?_⟩
  split at h
  · exact hv.1 ‹_›
  · cases h

/-- A valid `foR` column is `Ext.Enc.WF` at every fixed-width type, a boolean one where every element but a null is `0` or `1`:
`Coc.foRStd`'s block count covers the `n` elements, the layout part of `Ext.Enc.WF`. -/
theorem _root_.Rel.Kernel.Enc.Valid.wf {t : QAtomicType} {n : USize} {md pk : ByteArray} (h : Enc.Valid n (.foR md pk))
    (ht : t.width.isSome) (hu : t = .u1 → ∀ i < n.toNat, ∀ v, Column.foROpt md pk (Column.blockStarts md) i = some v → v.toNat < 2) :
    Ext.Enc.WF t n (.foR md pk : Enc) := by
  obtain ⟨hlg, hs⟩ := h
  have hF := (foRStd_iff.1 hs).nblk
  have hb := blk_pos md
  have hle : n.toNat ≤ Column.blk md * Column.nblk md := by
    rw [hF]
    have := Nat.div_add_mod (n.toNat + Column.blk md - 1) (Column.blk md)
    have := Nat.mod_lt (n.toNat + Column.blk md - 1) hb
    omega
  cases t <;> simp only [Ext.Enc.WF] <;>
    first | exact ⟨ht, hu, hle, hlg⟩ | exact ⟨ht, fun _ => hu rfl, hle, hlg⟩ | exact ⟨ht, hle, hlg⟩ | (simp [QAtomicType.width] at ht)

/-- **A kernel's answer is a column, null flags or not**: `wordsFoR ws nul`, at the `ws.size` rows it holds, is valid
(every kernel reads it), holds that many words, reads back through `Column.foROpt` as `none` at a null
(`Column.bitAt nul`) and `ws` elsewhere (`foROpt_encode`, whose `hbig` is the hypothesis of that conjunct), and is
`Ext.Enc.WF` at every fixed-width type, a boolean one where every word but a null's is `0` or `1`. -/
theorem wordsFoR_nul (ws : Array UInt64) (nul : ByteArray) {n : USize} (hn : n.toNat = ws.size) :
    Enc.Valid n (wordsFoR ws nul) ∧ (raw .i64 n (wordsFoR ws nul)).size = n.toNat ∧
      (∀ md pk, wordsFoR ws nul = .foR md pk → ∀ i (hi : i < ws.size),
        (2 ^ 32 ≤ ws.size → Column.bitAt nul i = false → ws[i] = 9223372036854775807 → ∀ j,
          i / 2 ^ Column.lgEnc * 2 ^ Column.lgEnc ≤ j → j < i / 2 ^ Column.lgEnc * 2 ^ Column.lgEnc + 2 ^ Column.lgEnc →
          j < ws.size → Column.bitAt nul j = false) →
        Column.foROpt md pk (Column.blockStarts md) i = if Column.bitAt nul i then none else some ws[i]) ∧
      ∀ {t : QAtomicType}, t.width.isSome → (t = .u1 → ∀ i (h : i < ws.size), Column.bitAt nul i = false → ws[i] < 2) →
        Ext.Enc.WF t n (wordsFoR ws nul) := by
  have h8 : USize.ofNat32 8 (by decide) = (8 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp [h])
  have hlg : 6 ≤ Column.lgEnc ∧ Column.lgEnc ≤ 16 := ⟨by decide, by decide⟩
  obtain ⟨hxs, -, hxg⟩ := foldl_pushBits (fun v => v) 8 (by decide) ws.toList ByteArray.empty
  rw [Array.foldl_toList] at hxs hxg
  simp only [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Array.length_toList] at hxs hxg
  unfold wordsFoR Coc.encode
  simp only [h8]
  generalize ws.foldl (init := ByteArray.empty) (fun acc w => Column.pushBits acc w 8) = X at hxs hxg
  have hnX : n.toNat = X.size / 8 := by rw [hxs, hn]; omega
  -- key `i` of `X` is word `i`
  have hkey : ∀ i (hi : i < ws.size), (Coc.keyAt 8 X i).toUInt64 = ws[i] := fun i hi => by
    have h1 : (Coc.keyAt 8 X i).toUInt64.toNat % 2 ^ (8 * 8) = (Column.bitsAt X (i * 8) 8).toNat :=
      sext_bits 8 (by decide) (by decide) _ (bitsAt_lt _ _ _ (by decide))
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), Nat.mul_comm, hxg i (by simpa using hi), ofNat_toNat_mod64,
      Array.getElem_toList] at h1
    exact UInt64.toNat_inj.mp h1
  have hopt : ∀ i (hi : i < ws.size), (2 ^ 32 ≤ ws.size → Column.bitAt nul i = false → ws[i] = 9223372036854775807 →
      ∀ j, i / 2 ^ Column.lgEnc * 2 ^ Column.lgEnc ≤ j → j < i / 2 ^ Column.lgEnc * 2 ^ Column.lgEnc + 2 ^ Column.lgEnc →
        j < ws.size → Column.bitAt nul j = false) →
      Column.foROpt (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).1
        (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).2
        (Column.blockStarts (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).1) i =
        if Column.bitAt nul i then none else some ws[i] := fun i hi hb => by
    rw [foROpt_encode Column.lgEnc hlg 8 (by decide) (by decide) X nul i (by omega) fun h32 hni hk j a b c =>
      hb (by omega) hni (by rw [← hkey i hi, Int64.toInt_inj.1 (hk.trans (by decide : (2 : Int) ^ 63 - 1 = (9223372036854775807 : Int64).toInt))]; decide) j a b (by omega),
      hkey i hi]
  have hV : Enc.Valid n (.foR (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).1
      (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).2) := by
    have hl := (nblk_encode Column.lgEnc hlg 8 (by decide) (by decide) X (patch := true) (nul := nul)).2.2
    refine ⟨by unfold Column.lgOk; rw [hl]; decide, foRStd_iff.2 (hnX ▸ foRWF_encodeAt Column.lgEnc hlg 8 (by omega) X)⟩
  refine ⟨hV, by rw [raw_foR .i64 8 rfl (by decide)]; simp, fun md pk he i hi hb => ?_,
    fun ht hu => Enc.Valid.wf hV ht fun h1 i hi v hv => ?_⟩
  · injection he with h1 h2; subst h1 h2; exact hopt i hi hb
  · have hi' : i < ws.size := by omega
    rw [hopt i hi' fun _ hni hk => absurd (hu h1 i hi' hni) (by rw [hk]; decide)] at hv
    split at hv; · cases hv
    rename_i hni
    obtain rfl := Option.some.inj hv
    exact UInt64.lt_iff_toNat_lt.1 (hu h1 i hi' (by simpa using hni))

/-- **A kernel's answer is a column**: `wordsFoR ws`, at the `ws.size` rows it holds, is valid (every kernel reads
it), reads back as `ws` (so the next kernel reads the words this one wrote), and is `Ext.Enc.WF` at every fixed-width type,
a boolean one where every word is `0` or `1`. -/
theorem wordsFoR_closed (ws : Array UInt64) {n : USize} (hn : n.toNat = ws.size) :
    Enc.Valid n (wordsFoR ws) ∧ raw .i64 n (wordsFoR ws) = ws ∧
      ∀ {t : QAtomicType}, t.width.isSome → (t = .u1 → ∀ i (h : i < ws.size), ws[i] < 2) → Ext.Enc.WF t n (wordsFoR ws) := by
  obtain ⟨hV, -, hopt, hwf⟩ := wordsFoR_nul ws .empty hn
  have h0 := bitAt_empty
  refine ⟨hV, ?_, fun ht hu => hwf ht fun h1 i hi _ => hu h1 i hi⟩
  obtain ⟨md, pk, hE⟩ : ∃ md pk, wordsFoR ws = .foR md pk := ⟨_, _, rfl⟩
  rw [hE, raw_foR .i64 8 rfl (by decide)]
  refine Array.ext (by simp [hn]) fun i h1 h2 => ?_
  have h := hopt md pk hE i h2 fun _ _ _ j _ _ _ => h0 j
  rw [h0, if_neg Bool.false_ne_true] at h
  unfold Column.foROpt at h; split at h; · cases h
  simp only [Array.getElem_map, Array.getElem_range]
  rw [Option.some.inj h, ofNat_toNat_mod64]

/-- `scatterWords` answers its `n` cells. -/
theorem scatterWords_size {op : Op} {is es : Array UInt64} {n : Nat} {fill : UInt64} {o : Array UInt64}
    (h : scatterWords op is es n fill = .ok o) : o.size = n := by
  unfold scatterWords at h
  generalize List.range is.size = l at h
  have ha : (Array.replicate n fill).size = n := by simp
  generalize Array.replicate n fill = a at h ha
  induction l generalizing a with
  | nil => cases h; exact ha
  | cons k t ih =>
    rw [List.foldlM_cons] at h
    dsimp only at h
    split at h
    · split at h
      · exact ih _ h (by simp [ha])
      · cases h
    · cases h

/-- **`kscan` closes**: its answer is valid at its `n` rows and `Ext.Enc.WF` at its answer type `t`. -/
theorem kscan_closed {op : Op} {rev : Bool} {s t : QAtomicType} {n : USize} {seg : Option Enc} {es : List Enc}
    {pre post : List (Op × UInt64)} {r : Enc × Option UInt64} (h : kscan op rev s t n seg es pre post = .ok r) :
    Enc.Valid n r.1 ∧ Ext.Enc.WF t n r.1 := by
  unfold kscan at h
  by_cases hd : ((pre ++ post).any fun p => p.1 == .div || p.1 == .mod) = true
  · simp [hd, bind, Except.bind] at h
  simp only [hd, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i out₀ hf
  split at h; · cases h
  rename_i out hp
  have hos := (chainAll_ok hp).1.trans (foldlM_kscanRow _ _ _ _ _ _ hf).1
  split at h; · cases h
  rename_i ht
  simp only [Except.ok.injEq] at h
  subst h
  dsimp only
  have hW : (Array.map (fun v => if t = .u1 then v % 2 else v) (if rev = true then out.reverse else out)).size =
      n.toNat := by rw [Array.size_map]; split <;> simp [hos]
  have hc := wordsFoR_closed _ hW.symm
  refine ⟨hc.1, hc.2.2 (by simp [ht]) fun hu i hi => ?_⟩
  simp only [Array.getElem_map, hu, ↓reduceIte]
  exact UInt64.lt_iff_toNat_lt.2 (by rw [UInt64.toNat_mod]; exact Nat.mod_lt _ (by decide))

/-- **`kscatter` closes**: its answer holds `n` words, read back by `raw .i64`, valid and `Ext.Enc.WF` at every fixed-width
type but the boolean. -/
theorem kscatter_closed {op : Op} {m n : USize} {ix e o : Enc} {fill : UInt64}
    (h : kscatter op m ix e n fill = .ok o) :
    Enc.Valid n o ∧ (raw .i64 n o).size = n.toNat ∧ ∀ {t : QAtomicType}, t.width.isSome → t ≠ .u1 → Ext.Enc.WF t n o := by
  unfold kscatter at h
  simp only [bind, Except.bind] at h
  -- every `split` either refutes an error branch or cases the `op` match, whose branches both go on
  repeat' (split at h <;> try (cases h; done))
  all_goals
    change Except.ok (wordsFoR _ _) = _ at h
    simp only [Except.ok.injEq] at h
    subst h
    have hs := (scatterWords_size ‹scatterWords _ _ _ _ _ = .ok _›).symm
    exact ⟨(wordsFoR_nul _ _ hs).1, (wordsFoR_nul _ _ hs).2.1,
      fun ht hu => (wordsFoR_nul _ _ hs).2.2.2 ht fun h1 => absurd h1 hu⟩

/-- **`kgather` closes**: its answer holds `m` words, valid and `Ext.Enc.WF` at every fixed-width type but the boolean. -/
theorem kgather_closed {m n : USize} {ix e o : Enc} (h : kgather m ix n e = .ok o) :
    Enc.Valid m o ∧ (raw .i64 m o).size = m.toNat ∧ ∀ {t : QAtomicType}, t.width.isSome → t ≠ .u1 → Ext.Enc.WF t m o := by
  obtain ⟨hs, -, -, rfl⟩ := raw_kgather m ix n e o h
  have hm : m.toNat = (Array.map (fun i => (raw .i64 n e)[i.toNat]?.getD 0) (raw .i64 m ix)).size := by
    rw [Array.size_map, hs]
  exact ⟨(wordsFoR_nul _ _ hm).1, (wordsFoR_nul _ _ hm).2.1,
    fun ht hu => (wordsFoR_nul _ _ hm).2.2.2 ht fun h1 => absurd h1 hu⟩


end Rel.Verify
