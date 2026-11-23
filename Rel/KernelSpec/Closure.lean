module

public import Rel.KernelSpec.Alp
public import Rel.KernelSpec.Scan
public import Rel.KernelSpec.Gather
public import Rel.KernelSpec.Scatter
public import Rel.KernelSpec.KGather
public import Rel.KernelSpec.KSeen

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

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
    (ht : t.width.isSome) (hu : t = .u1 → ∀ i < n.toNat, ∀ v, Column.foROpt md pk (Column.blockStarts md) i = some v → v.toNat < 2)
    (hN : ∀ b < Column.nblk md, Column.nulAt md b = true → ∃ j < Column.blk md, b * Column.blk md + j < n.toNat ∧
      Column.foRNul md pk (Column.blockStarts md) (b * Column.blk md + j) = true) :
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
    first | exact ⟨ht, hu, hle, hlg, hN⟩ | exact ⟨ht, fun _ => hu rfl, hle, hlg, hN⟩ | exact ⟨ht, hle, hlg, hN⟩ |
      (simp [QAtomicType.width] at ht)

/-- **A kernel's answer is a column, null flags or not**: `wordsFoR ws nul least`, at the `ws.size` rows it holds, is valid
(every kernel reads it), holds that many words, reads back through `Column.foROpt` as `none` at a null
(`Column.bitAt nul`) and `ws` elsewhere (`foROpt_encode`, whose `hbig` the `USize` row count discharges), and is
`Ext.Enc.WF` at every fixed-width type, a boolean one where every word but a null's is `0` or `1`. `hle` is what makes
`least` the atom type's least key: every word that is not null is at or above it (`planBlock_nul`), which the default
`Int64.minValue` meets by itself. -/
theorem wordsFoR_nul (ws : Array UInt64) (nul : ByteArray) {n : USize} (hn : n.toNat = ws.size) (least : Int64 := Int64.minValue)
    (hle : ∀ i (hi : i < ws.size), Column.bitAt nul i = false → least.toInt ≤ ws[i].toInt64.toInt := by
      intro _ _ _; rw [Int64.toInt_minValue]; exact Int64.le_toInt _) :
    Enc.Valid n (wordsFoR ws nul least) ∧ (raw .i64 n (wordsFoR ws nul least)).size = n.toNat ∧
      (∀ md pk, wordsFoR ws nul least = .foR md pk → ∀ i (hi : i < ws.size),
        Column.foROpt md pk (Column.blockStarts md) i = if Column.bitAt nul i then none else some ws[i]) ∧
      ∀ {t : QAtomicType}, t.width.isSome → (t = .u1 → ∀ i (h : i < ws.size), Column.bitAt nul i = false → ws[i] < 2) →
        Ext.Enc.WF t n (wordsFoR ws nul least) := by
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
  have hleX : ∀ j < X.size / 8, Column.bitAt nul j = false → least.toInt ≤ (Coc.keyAt 8 X j).toInt := fun j hj hb => by
    have hj' : j < ws.size := by omega
    have : Coc.keyAt 8 X j = ws[j].toInt64 := by rw [← hkey j hj']; simp
    rw [this]; exact hle j hj' hb
  -- a `USize` count is below `2 ^ 64`, where the writer always patches, so `foROpt_encode`'s `hbig` is vacuous
  have hn64 : n.toNat < 2 ^ 64 := by have := n.toNat_lt_size; rcases USize.size_eq with h | h <;> omega
  have hopt : ∀ i (hi : i < ws.size),
      Column.foROpt (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul least).1
        (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul least).2
        (Column.blockStarts (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul least).1) i =
        if Column.bitAt nul i then none else some ws[i] := fun i hi => by
    rw [foROpt_encode Column.lgEnc hlg 8 (by decide) (by decide) X nul i (by omega) hleX fun h64 => absurd h64 (by omega),
      hkey i hi]
  have hV : Enc.Valid n (.foR (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul least).1
      (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul least).2) := by
    have hl := (nblk_encode Column.lgEnc hlg 8 (by decide) (by decide) X (patch := true) (nul := nul) (least := least)).2.2
    refine ⟨by unfold Column.lgOk; rw [hl]; decide, foRStd_iff.2 (hnX ▸ foRWF_encodeAt Column.lgEnc hlg 8 (by omega) X (patch := true) (nul := nul) (least := least) hleX)⟩
  refine ⟨hV, by rw [raw_foR .i64 8 rfl (by decide)]; simp, fun md pk he i hi => ?_,
    fun ht hu => Enc.Valid.wf hV ht (fun h1 i hi v hv => ?_) fun b hb hf => ?_⟩
  · injection he with h1 h2; subst h1 h2; exact hopt i hi
  rotate_left
  · -- a flagged block holds a row null in `nul` (`nulAt_encodeAt`), which reads back as the null
    obtain ⟨hnb, hbk, -⟩ := nblk_encode Column.lgEnc hlg 8 (by decide) (by decide) X (patch := true) (nul := nul)
    rw [hnb] at hb; rw [hbk]
    obtain ⟨j, hj, hjn, hjb⟩ := nulAt_encodeAt Column.lgEnc hlg 8 (by decide) (by decide) X nul b
      (mul_lt_of_lt_cdiv (Nat.two_pow_pos _) hb) hf
    refine ⟨j, hj, by omega, ?_⟩
    have h := hopt (b * 2 ^ Column.lgEnc + j) (by omega)
    rw [if_pos hjb] at h
    unfold Column.foROpt at h; split at h
    · assumption
    · cases h
  · have hi' : i < ws.size := by omega
    rw [hopt i hi'] at hv
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
  have h := hopt md pk hE i h2
  rw [h0, if_neg Bool.false_ne_true] at h
  unfold Column.foROpt at h; split at h; · cases h
  simp only [Array.getElem_map, Array.getElem_range]
  rw [Option.some.inj h, ofNat_toNat_mod64]

/-- **A column holds a null exactly where a row's flag is set**: `hasNul` reads the blocks' flags, and under
`Ext.Enc.WF` a flagged block holds a null row (owner decision F) while a null row's block is flagged (`foRNul`). So two
columns whose rows' flags agree up to a permutation agree on `hasNul`. -/
theorem hasNul_flags {t : QAtomicType} {n : USize} {e : Enc} (hw : Ext.Enc.WF t n e) :
    hasNul e = (foRNuls n e).any (· != 0) := by
  cases e with
  | foR md pk =>
    have hw' : n.toNat ≤ Column.blk md * Column.nblk md ∧ ∀ b < Column.nblk md, Column.nulAt md b = true →
        ∃ j < Column.blk md, b * Column.blk md + j < n.toNat ∧
          Column.foRNul md pk (Column.blockStarts md) (b * Column.blk md + j) = true := by
      cases t <;> simp only [Ext.Enc.WF] at hw <;> exact ⟨hw.2.2.1, hw.2.2.2.2⟩
    obtain ⟨hle, hN⟩ := hw'
    rw [Bool.eq_iff_iff, hasNul, foRNuls, Array.any_eq_true, Array.any_eq_true]
    simp only [List.mem_range, Array.size_map, Array.size_range, Array.getElem_map, Array.getElem_range]
    constructor
    · rintro ⟨b, hb, hf⟩
      obtain ⟨j, -, hjn, hjf⟩ := hN b hb hf
      exact ⟨_, hjn, by rw [hjf]; decide⟩
    · rintro ⟨i, hi, hf⟩
      have hf' : Column.foRNul md pk (Column.blockStarts md) i = true := by
        cases h : Column.foRNul md pk (Column.blockStarts md) i <;> simp_all
      refine ⟨i / Column.blk md, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hi hle), ?_⟩
      unfold Column.foRNul at hf'; simp only [Bool.and_eq_true] at hf'; exact hf'.1.1
  | _ =>
    simp only [hasNul, foRNuls]
    exact (Bool.eq_false_iff.2 fun h => by obtain ⟨i, hi, h⟩ := Array.any_eq_true.1 h; simp at h).symm

/-- A column holding no null flags none of its rows (`hasNul_flags`). -/
theorem foRNuls_plain {t : QAtomicType} {n : USize} {e : Enc} (hw : Ext.Enc.WF t n e) (hN : hasNul e = false)
    {i : Nat} (hi : i < n.toNat) : (foRNuls n e)[i]? = some 0 := by
  have hs : i < (foRNuls n e).size := by cases e <;> simp [foRNuls, hi]
  rw [hasNul_flags hw, Array.any_eq_false] at hN
  rw [Array.getElem?_eq_getElem hs]
  simpa using hN i hs

/-- **A kernel's answer reads back its null flags**: row `i` of `wordsFoR ws nul least` is flagged exactly where
`Column.bitAt nul i`. -/
theorem foRNuls_wordsFoR (ws : Array UInt64) (nul : ByteArray) {n : USize} (hn : n.toNat = ws.size) (i : Nat)
    (hi : i < ws.size) (least : Int64 := Int64.minValue)
    (hle : ∀ i (hi : i < ws.size), Column.bitAt nul i = false → least.toInt ≤ ws[i].toInt64.toInt := by
      intro _ _ _; rw [Int64.toInt_minValue]; exact Int64.le_toInt _) :
    (foRNuls n (wordsFoR ws nul least))[i]? = some (if Column.bitAt nul i then 1 else 0) := by
  obtain ⟨md, pk, hE⟩ : ∃ md pk, wordsFoR ws nul least = .foR md pk := ⟨_, _, rfl⟩
  have h := (wordsFoR_nul ws nul hn least hle).2.2.1 md pk hE i hi
  rw [hE]; unfold Column.foROpt at h
  simp only [foRNuls, Array.getElem?_map, Array.getElem?_range, show i < n.toNat by omega, if_true, Option.map_some]
  cases hb : Column.bitAt nul i <;> cases hf : Column.foRNul md pk (Column.blockStarts md) i <;> simp_all

/-- A column with no flagged block holds no null: `hasNul` reads the flags alone. -/
theorem hasNul_of_nulAt {md pk : ByteArray} (h : ∀ b < Column.nblk md, Column.nulAt md b = false) :
    hasNul (.foR md pk) = false := hasNul_foR_false.2 h

/-- A column with no flagged block has no null row: `foRNul` needs the row's block flagged. -/
theorem foRNul_of_plain {md pk : ByteArray} (h : hasNul (.foR md pk) = false) {i : Nat}
    (hi : i < Column.blk md * Column.nblk md) : Column.foRNul md pk (Column.blockStarts md) i = false := by
  rw [hasNul_foR_false] at h
  simp only [Column.foRNul, h _ (Nat.div_lt_of_lt_mul hi), Bool.false_and]

/-- A kernel's answer written with no null bitmap holds no null (`nulAt_encodeAt_empty`). -/
theorem hasNul_wordsFoR (ws : Array UInt64) : hasNul (wordsFoR ws) = false := by
  have h8 : USize.ofNat32 8 (by decide) = (8 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp [h])
  unfold wordsFoR Coc.encode
  rw [hasNul_foR_false]
  simp only [h8]
  intro b hb
  rw [nulAt_encodeAt_empty Column.lgEnc ⟨by decide, by decide⟩ 8 (by decide) (by decide) _ b hb]

/-- `raw_kgather` where the source holds no null: the answer is `wordsFoR` of the gathered words alone, so it reads
back as them (`wordsFoR_closed`). -/
theorem kgather_plain {m n : USize} {ix e o : Enc} (h : kgather m ix n e = .ok o) (hN : hasNul e = false) :
    o = wordsFoR ((raw .i64 m ix).map fun i => (raw .i64 n e)[i.toNat]?.getD 0) := by
  obtain ⟨-, -, -, rfl⟩ := raw_kgather m ix n e o h
  simp only [hN, Bool.false_eq_true, ↓reduceIte]

/-- A gather of a column with no null holds none (`kgather_plain`), as `kscatter_plain` for a scatter. -/
theorem kgather_noNul {m n : USize} {ix e o : Enc} (h : kgather m ix n e = .ok o) (hN : hasNul e = false) :
    hasNul o = false := by
  rw [kgather_plain h hN]; exact hasNul_wordsFoR _

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

/-- Discharges `kscanStream op es pre post = false` for an `op` that is a concrete constructor, or a conditional of two,
and for a chain with a step: the autoParam of every caller that maps or scans in lock-step. -/
macro "lockstep" : tactic => `(tactic| first | decide | (simp [kscanStream]; done) | (simp only [kscanStream]; split <;> (try (rename_i h; split at h)) <;> simp_all))

/-- Discharges `op.nulFold = none ∨ …` for an `op` that is a concrete constructor other than `min`/`max`: the autoParam `hF` of every caller that scans in lock-step (`kscan_lock_closed`). -/
macro "nulfree" : tactic => `(tactic| first | exact Or.inl rfl | (left; split <;> rfl))

/-- Only `first` reads its sources as a stream, so any other op closes with no hypothesis on its sources. -/
theorem kscanStream_ne {op : Op} (h : op ≠ .first) (es : List (USize × Enc)) (pre post : List (Op × UInt64)) :
    kscanStream op es pre post = false := by
  unfold kscanStream; split <;> simp_all

/-- **`kscanCols` flags no null row** where every source holds none: a lock-step call carries no flags, and a stream's are
the sources' `foRNuls`, all `0` (`hasNul_flags`). -/
theorem kscanCols_nul {op : Op} {s : QAtomicType} {n : USize} {es : List (USize × Enc)} {pre post : List (Op × UInt64)}
    {ws : List (Array UInt64)} {ns : List (Array UInt64)}
    (hS : kscanStream op es pre post = true → (∀ p ∈ es, hasNul p.2 = false) ∧ ∀ p ∈ es, Ext.Enc.WF s p.1 p.2)
    (hF : op.nulFold = none ∨ ∀ p ∈ es, hasNul p.2 = false)
    (h : kscanCols op s n es pre post = .ok (ws, ns)) : ns.any (·.any (· != 0)) = false := by
  by_cases hs : kscanStream op es pre post = true
  · obtain ⟨hN, hW⟩ := hS hs
    unfold kscanCols at h
    simp only [hs, if_true] at h
    cases hm : es.mapM (fun p => rawAll s p.1 p.2 >>= chainAll pre) with
    | error m => rw [hm] at h; simp [bind, Except.bind] at h
    | ok ws' =>
      rw [hm] at h; simp only [bind, Except.bind] at h
      by_cases hsum : ((es.map (·.1.toNat)).sum != n.toNat) = true
      · simp [hsum] at h
      · simp only [hsum, Bool.false_eq_true, if_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2, List.any_cons, List.any_nil, Bool.or_false]
        have key : ∀ (l : List (USize × Enc)) (a : Array UInt64), (∀ p ∈ l, hasNul p.2 = false) →
            (∀ p ∈ l, Ext.Enc.WF s p.1 p.2) → a.any (· != 0) = false →
            (l.foldl (fun a p => a ++ foRNuls p.1 p.2) a).any (· != 0) = false := by
          intro l
          induction l with
          | nil => intro a _ _ ha; exact ha
          | cons q l ih =>
            intro a hn hw ha
            refine ih _ (fun p hp => hn p (by simp [hp])) (fun p hp => hw p (by simp [hp])) ?_
            have hq := hn q (by simp)
            rw [hasNul_flags (hw q (by simp)), ← Bool.not_eq_true, Bool.not_eq_true] at hq
            rw [Array.any_append, ha, hq]; rfl
        exact key es #[] hN hW (by simp)
  · rw [Bool.not_eq_true] at hs
    obtain ⟨-, rfl, -⟩ := kscanCols_lock hs hF h
    simp

/-- **`kscan` closes**: its answer is valid at its `n` rows, `Ext.Enc.WF` at its answer type `t`, and holds no null
(written with no null bitmap). Only a stream (`kscanStream`) reads its sources' null flags, so only there must they hold
no null and be `Ext.Enc.WF` at `s`. -/
theorem kscan_closed {op : Op} {rev : Bool} {s t : QAtomicType} {n : USize} {seg : Option Enc}
    {es : List (USize × Enc)} {pre post : List (Op × UInt64)} {r : Enc × Option UInt64}
    (hS : kscanStream op es pre post = true → (∀ p ∈ es, hasNul p.2 = false) ∧ ∀ p ∈ es, Ext.Enc.WF s p.1 p.2)
    (hF : op.nulFold = none ∨ ∀ p ∈ es, hasNul p.2 = false)
    (h : kscan op rev s t n seg es pre post = .ok r) :
    Enc.Valid n r.1 ∧ Ext.Enc.WF t n r.1 ∧ hasNul r.1 = false := by
  unfold kscan at h
  by_cases hd : kscanRefuses op n es pre post = true
  · simp only [hd, ↓reduceIte] at h; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hd, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  rename_i cs hc
  split at h; · cases h
  rename_i c cs' ns
  have hns := kscanCols_nul hS hF hc
  split at h; · cases h
  rename_i out₀ hf
  split at h; · cases h
  rename_i out hp
  have hos := (chainAll_ok hp).1.trans (foldlM_kscanRow _ _ _ _ _ _ hf).1
  split at h; · cases h
  rename_i w' ht
  split at h; · cases h
  rename_i nl hnl
  simp only [Except.ok.injEq] at h
  subst h
  dsimp only
  simp only [hns, Bool.false_eq_true, if_false]
  have hW : (Array.map (fun v => if t = .u1 then v % 2 else v) (if rev = true then out.reverse else out)).size =
      n.toNat := by rw [Array.size_map]; split <;> simp [hos]
  have hc := wordsFoR_closed _ hW.symm
  refine ⟨hc.1, hc.2.2 (by simp [ht]) fun hu i hi => ?_, hasNul_wordsFoR _⟩
  simp only [Array.getElem_map, hu, ↓reduceIte]
  exact UInt64.lt_iff_toNat_lt.2 (by rw [UInt64.toNat_mod]; exact Nat.mod_lt _ (by decide))

/-- **`kscan` closes** where it is no stream (`kscanStream`): no hypothesis on its sources. -/
theorem kscan_lock_closed {op : Op} {rev : Bool} {s t : QAtomicType} {n : USize} {seg : Option Enc}
    {es : List (USize × Enc)} {pre post : List (Op × UInt64)} {r : Enc × Option UInt64}
    (hs : kscanStream op es pre post = false) (hF : op.nulFold = none ∨ ∀ p ∈ es, hasNul p.2 = false)
    (h : kscan op rev s t n seg es pre post = .ok r) :
    Enc.Valid n r.1 ∧ Ext.Enc.WF t n r.1 ∧ hasNul r.1 = false :=
  kscan_closed (fun h => absurd h (by rw [hs]; decide)) hF h

/-! A stream (`kscanStream`, no segment marks) over sources that may hold nulls: the answer is the sources' words joined
and their flags joined (`streamEnc`), and reads back each source's rows, null included. -/

/-- `e`'s `n` raw words at a fixed-width `s` are `n` of them where `Ext.Enc.WF` holds. -/
theorem raw_size_wf {s : QAtomicType} {n : USize} {e : Enc} (hs : s.width.isSome) (h : Ext.Enc.WF s n e) :
    (e.raw s n).size = n.toNat := by
  cases e with
  | foR md pk => cases s <;> simp_all [Ext.Enc.raw, QAtomicType.width]
  | pos => cases s <;> simp_all [Ext.Enc.WF, Ext.Enc.raw]
  | _ => cases s <;> simp_all [Ext.Enc.WF, QAtomicType.width]

/-- A source list of `Ext.Enc.WF` columns, read one after the other: each source's raw words, `chainAll []` being `pure`. -/
theorem mapM_raw_pairs {s : QAtomicType} (hs : s.width.isSome) :
    ∀ {es : List (USize × Enc)}, (∀ p ∈ es, Ext.Enc.WF s p.1 p.2) →
      es.mapM (fun p => rawAll s p.1 p.2 >>= chainAll []) = .ok (es.map fun p => p.2.raw s p.1)
  | [], _ => rfl
  | p :: es, h => by
    rw [List.mapM_cons, mapM_raw_pairs hs fun q hq => h q (by simp [hq])]
    have hr : rawAll s p.1 p.2 = .ok (p.2.raw s p.1) := by
      unfold rawAll; rw [if_pos (raw_size_wf hs (h p (by simp)))]
    simp [hr, chainAll_nil, bind, Except.bind, pure, Except.pure]

/-- `kscanRow .first` with no other column never fails. -/
theorem foldlM_first_ok (g seed : Array UInt64) (m : Nat) :
    ∃ out, (List.range m).foldlM (kscanRow .first g seed []) #[] = .ok out := by
  induction m with
  | zero => exact ⟨#[], rfl⟩
  | succ m ih =>
    obtain ⟨o, ho⟩ := ih
    refine ⟨o.push (if 0 < m ∧ g[m]?.getD 0 = 0 then o[m - 1]?.getD 0 else seed[m]?.getD 0), ?_⟩
    rw [List.range_succ, List.foldlM_append, ho]
    simp [kscanRow, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

/-- Where every row starts a segment (`g` nonzero) and no column is folded in, `kscan`'s row fold is the seed itself. -/
theorem foldlM_first {g seed : Array UInt64} {m : Nat} (hg : ∀ i < m, g[i]?.getD 0 ≠ 0) (hs : seed.size = m) :
    (List.range m).foldlM (kscanRow .first g seed []) #[] = .ok seed := by
  obtain ⟨o, ho⟩ := foldlM_first_ok g seed m
  obtain ⟨hos, hr⟩ := foldlM_kscanRow .first g seed [] m o ho
  rw [ho]; congr 1
  refine Array.ext (by omega) fun i h1 h2 => ?_
  have h := hr i h1
  simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
  rw [if_neg (fun h' => hg i (by omega) h'.2)] at h
  rw [← h]; simp [Array.getElem?_eq_getElem h2]

theorem foldl_append_start {α : Type} (L : List (Array α)) (a : Array α) :
    L.foldl (· ++ ·) a = a ++ L.foldl (· ++ ·) #[] := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => simp only [List.foldl_cons, Array.empty_append]; rw [ih (a ++ x), ih x, Array.append_assoc]

theorem foldl_append_size {α : Type} (L : List (Array α)) : (L.foldl (· ++ ·) #[]).size = (L.map (·.size)).sum := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.foldl_cons, Array.empty_append, List.map_cons, List.sum_cons]; rw [foldl_append_start]; simp [ih]

/-- Row `k` of source `j` is row `(sizes before j) + k` of the sources joined. -/
theorem foldl_append_get {α : Type} : ∀ (L : List (Array α)) (j k : Nat) (hj : j < L.length), k < L[j].size →
    (L.foldl (· ++ ·) #[])[((L.take j).map (·.size)).sum + k]? = L[j][k]?
  | x :: L, 0, k, _, hk => by
    simp only [List.foldl_cons, Array.empty_append]; rw [foldl_append_start]
    simp [Array.getElem?_append_left (show k < x.size from hk)]
  | x :: L, j+1, k, hj, hk => by
    simp only [List.foldl_cons, Array.empty_append]; rw [foldl_append_start]
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    rw [Nat.add_assoc, Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact foldl_append_get L j k (by simpa using hj) hk

/-- A stream's sources' raw words, one after the other. -/
def streamRaw (s : QAtomicType) (es : List (USize × Enc)) : Array UInt64 :=
  (es.map fun p => p.2.raw s p.1).foldl (· ++ ·) #[]

/-- A stream's sources' null flags, one after the other (`kscanCols`' second component). -/
def streamNul (es : List (USize × Enc)) : Array UInt64 := es.foldl (fun a p => a ++ foRNuls p.1 p.2) #[]

/-- A stream's answer type's reading of a word: a boolean's low bit. -/
def cutBit (t : QAtomicType) (v : UInt64) : UInt64 := if t = .u1 then v % 2 else v

/-- The column `kscan` writes for a stream: the words cut to `t`, the flags as `nulMap` where any is set. -/
def streamEnc (s t : QAtomicType) (es : List (USize × Enc)) : Enc :=
  wordsFoR ((streamRaw s es).map (cutBit t)) (if (streamNul es).any (· != 0) then nulMap (streamNul es) else .empty)

theorem streamRaw_size {s : QAtomicType} (hs : s.width.isSome) {es : List (USize × Enc)}
    (hW : ∀ p ∈ es, Ext.Enc.WF s p.1 p.2) : (streamRaw s es).size = (es.map (·.1.toNat)).sum := by
  unfold streamRaw
  rw [foldl_append_size, List.map_map]
  congr 1
  exact List.map_congr_left fun p hp => raw_size_wf hs (hW p hp)

theorem streamNul_eq (es : List (USize × Enc)) :
    streamNul es = (es.map fun p => foRNuls p.1 p.2).foldl (· ++ ·) #[] := by
  unfold streamNul; rw [List.foldl_map]

theorem streamNul_size (es : List (USize × Enc)) : (streamNul es).size = (es.map (·.1.toNat)).sum := by
  rw [streamNul_eq, foldl_append_size, List.map_map]
  congr 1
  exact List.map_congr_left fun p _ => foRNuls_size p.1 p.2

/-- **`kscan` of a stream** (`kscanStream`, no segment marks) is `streamEnc`: the sources' words joined and cut to `t`,
their flags joined. Its fold result is the last joined word. -/
theorem kscan_stream {s t : QAtomicType} {w : Nat} (ht : t.width = some w) (hs : s.width.isSome) {n : USize}
    {es : List (USize × Enc)} (hW : ∀ p ∈ es, Ext.Enc.WF s p.1 p.2) (hl : 1 < es.length)
    (hn : (es.map (·.1.toNat)).sum = n.toNat) :
    kscan .first false s t n none es = .ok (streamEnc s t es,
      (streamRaw s es).back?.map fun v => UInt64.ofNat (v.toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) := by
  have hst : kscanStream .first es [] [] = true := by simp [kscanStream, hl]
  have hrf : kscanRefuses .first n es [] [] = false := by simp [kscanRefuses, Op.readsDivisor]
  have hcols : kscanCols .first s n es [] [] = .ok ([streamRaw s es], [streamNul es]) := by
    unfold kscanCols
    rw [mapM_raw_pairs hs hW]
    simp [hst, hn, streamRaw, streamNul, bind, Except.bind, pure, Except.pure]
  have hg : segAll n none = .ok (Array.replicate n.toNat 1) := rfl
  have hRs := streamRaw_size hs hW
  have hNs := streamNul_size es
  have hgg : ∀ i < n.toNat, (Array.replicate n.toNat (1 : UInt64))[i]?.getD 0 ≠ 0 := fun i hi => by simp [hi]
  unfold kscan
  simp only [hrf, Bool.false_eq_true, bind, Except.bind, hg, hcols, ↓reduceIte,
    foldlM_first (seed := streamRaw s es) hgg (hRs.trans hn), foldlM_first (seed := streamNul es) hgg (hNs.trans hn),
    chainAll_nil, pure, Except.pure, ht, List.map_nil, Op.nulFold, Option.elim, List.headD_cons, List.drop_succ_cons,
    List.drop_zero, List.any_cons, List.any_nil, Bool.or_false]
  rfl

/-- Row `k` of source `j` of a stream, one array per source (`f`) of `p.1` rows, is row `(rows before j) + k` of the
sources joined. -/
theorem joined_get {β : Type} (f : USize × Enc → Array β) {es : List (USize × Enc)}
    (hf : ∀ p ∈ es, (f p).size = p.1.toNat) {j k : Nat} (hj : j < es.length) (hk : k < es[j].1.toNat) :
    ((es.map f).foldl (· ++ ·) #[])[((es.take j).map (·.1.toNat)).sum + k]? = (f es[j])[k]? := by
  have h := foldl_append_get (es.map f) j k (by simpa using hj) (by simpa [hf _ (List.getElem_mem hj)] using hk)
  rw [List.map_take, List.map_map] at h
  rw [show ((es.take j).map (·.1.toNat)) = (List.map ((·.size) ∘ f) (List.take j es)) from
    List.map_congr_left fun p hp => (hf p (List.mem_of_mem_take hp)).symm]
  simpa using h

/-- A stream's null map reads the flag it was built from: row `i` is null in `nulMap`, or in none at all, exactly where
the flag word is set. -/
theorem bitAt_stream {ns : Array UInt64} {i : Nat} (hi : i < ns.size) :
    Column.bitAt (if ns.any (· != 0) then nulMap ns else .empty) i = (ns[i]?.getD 0 != 0) := by
  split
  · rw [nulMap, bitAt_packOf _ _ _ hi]
  · rename_i h
    rw [Bool.not_eq_true] at h
    rw [Array.any_eq_false] at h
    simp [bitAt_empty, Array.getElem?_eq_getElem hi, h i hi]

/-- **`kscan` of a stream closes**, nulls and all: its answer is `streamEnc`, valid and `Ext.Enc.WF` at `t`, wherever every
source is `Ext.Enc.WF` at `s` and their rows sum to `n`. -/
theorem kscan_stream_closed {s t : QAtomicType} {w : Nat} (ht : t.width = some w) (hs : s.width.isSome) {n : USize}
    {es : List (USize × Enc)} (hW : ∀ p ∈ es, Ext.Enc.WF s p.1 p.2) (hl : 1 < es.length)
    (hn : (es.map (·.1.toNat)).sum = n.toNat) :
    kscan .first false s t n none es = .ok (streamEnc s t es,
      (streamRaw s es).back?.map fun v => UInt64.ofNat (v.toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) ∧
    Enc.Valid n (streamEnc s t es) ∧ Ext.Enc.WF t n (streamEnc s t es) := by
  have hsz : n.toNat = ((streamRaw s es).map (cutBit t)).size := by
    rw [Array.size_map, streamRaw_size hs hW, hn]
  obtain ⟨hV, -, -, hwf⟩ := wordsFoR_nul ((streamRaw s es).map (cutBit t)) (if (streamNul es).any (· != 0) then
    nulMap (streamNul es) else .empty) hsz
  refine ⟨kscan_stream ht hs hW hl hn, hV, hwf (by simp [ht]) fun hu i hi _ => ?_⟩
  simp only [Array.getElem_map, cutBit, hu, ↓reduceIte]
  exact UInt64.lt_iff_toNat_lt.2 (by rw [UInt64.toNat_mod]; exact Nat.mod_lt _ (by decide))

/-- **A stream's answer reads each source's rows, null included**: row `k` of source `j` is row `(rows before j) + k` of the
answer, read through `foROpt` as `none` where the source's flag (`foRNuls`) is set and as its raw word cut to `t` else. -/
theorem kscan_stream_get {s t : QAtomicType} (hs : s.width.isSome) {n : USize}
    {es : List (USize × Enc)} (hW : ∀ p ∈ es, Ext.Enc.WF s p.1 p.2)
    (hn : (es.map (·.1.toNat)).sum = n.toNat) {j k : Nat} (hj : j < es.length) (hk : k < es[j].1.toNat)
    {md pk : ByteArray} (he : streamEnc s t es = .foR md pk) :
    Column.foROpt md pk (Column.blockStarts md) (((es.take j).map (·.1.toNat)).sum + k) =
      if (foRNuls es[j].1 es[j].2)[k]?.getD 0 != 0 then none
      else some (cutBit t ((es[j].2.raw s es[j].1)[k]?.getD 0)) := by
  have hsz : n.toNat = ((streamRaw s es).map (cutBit t)).size := by
    rw [Array.size_map, streamRaw_size hs hW, hn]
  have hi : ((es.take j).map (·.1.toNat)).sum + k < n.toNat := by
    have h1 : ((es.map (·.1.toNat)).take j).sum + ((es.map (·.1.toNat)).drop j).sum = (es.map (·.1.toNat)).sum := by
      rw [← List.sum_append_nat, List.take_append_drop]
    rw [List.drop_eq_getElem_cons (by simpa using hj), List.sum_cons, List.getElem_map, ← List.map_take] at h1
    omega
  have hi' : ((es.take j).map (·.1.toNat)).sum + k < ((streamRaw s es).map (cutBit t)).size := hsz ▸ hi
  have h := (wordsFoR_nul ((streamRaw s es).map (cutBit t)) (if (streamNul es).any (· != 0) then
    nulMap (streamNul es) else .empty) hsz).2.2.1 md pk he _ hi'
  have e1 : (streamNul es)[((es.take j).map (·.1.toNat)).sum + k]? = (foRNuls es[j].1 es[j].2)[k]? := by
    rw [streamNul_eq]; exact joined_get (fun p => foRNuls p.1 p.2) (fun p _ => foRNuls_size _ _) hj hk
  have e2 : (streamRaw s es)[((es.take j).map (·.1.toNat)).sum + k]? = (es[j].2.raw s es[j].1)[k]? :=
    joined_get (fun p => p.2.raw s p.1) (fun p hp => raw_size_wf hs (hW p hp)) hj hk
  have hr : ((es.take j).map (·.1.toNat)).sum + k < (streamRaw s es).size := by simpa using hi'
  have hnn : ((es.take j).map (·.1.toNat)).sum + k < (streamNul es).size := by rw [streamNul_size, hn]; exact hi
  rw [h, bitAt_stream hnn, e1]
  have e3 : (streamRaw s es)[((es.take j).map (·.1.toNat)).sum + k] = (es[j].2.raw s es[j].1)[k]?.getD 0 := by
    rw [← e2, Array.getElem?_eq_getElem hr]; rfl
  simp only [Array.getElem_map, e3]

/-- **`kscatter` closes**: its answer holds `n` words, read back by `raw .i64`, valid and `Ext.Enc.WF` at every fixed-width
type but the boolean. -/
theorem kscatter_closed {op : Op} {m n : USize} {ix e o : Enc} {fill : UInt64}
    (h : kscatter op m ix e n fill = .ok o) :
    Enc.Valid n o ∧ (raw .i64 n o).size = n.toNat ∧ ∀ {t : QAtomicType}, t.width.isSome → t ≠ .u1 → Ext.Enc.WF t n o := by
  unfold kscatter at h
  split at h; · cases h
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

/-- A `kscatter` answer holds a null only where `e` does: with no null in `e` it is `wordsFoR` of its words alone. -/
theorem kscatter_plain {op : Op} {m n : USize} {ix e o : Enc} {fill : UInt64}
    (h : kscatter op m ix e n fill = .ok o) (hN : hasNul e = false) : hasNul o = false := by
  unfold kscatter at h
  split at h; · cases h
  simp only [hN, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> try (cases h; done))
  all_goals
    change Except.ok (wordsFoR _ _) = _ at h
    simp only [Except.ok.injEq] at h
    subst h
    exact hasNul_wordsFoR _

/-- **`kgather` closes**: its answer holds `m` words, valid and `Ext.Enc.WF` at every fixed-width type but the boolean. -/
theorem kgather_closed {m n : USize} {ix e o : Enc} (h : kgather m ix n e = .ok o) :
    Enc.Valid m o ∧ (raw .i64 m o).size = m.toNat ∧ ∀ {t : QAtomicType}, t.width.isSome → t ≠ .u1 → Ext.Enc.WF t m o := by
  obtain ⟨hs, -, -, rfl⟩ := raw_kgather m ix n e o h
  have hm : m.toNat = (Array.map (fun i => (raw .i64 n e)[i.toNat]?.getD 0) (raw .i64 m ix)).size := by
    rw [Array.size_map, hs]
  exact ⟨(wordsFoR_nul _ _ hm).1, (wordsFoR_nul _ _ hm).2.1,
    fun ht hu => (wordsFoR_nul _ _ hm).2.2.2 ht fun h1 => absurd h1 hu⟩

end Rel.Verify
