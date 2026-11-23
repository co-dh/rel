module

public import Rel.KernelSpec.Alp
public import Rel.KernelSpec.Scan
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

/-- **A kernel's answer is a column, null flags or not**: `wordsFoR ws nul`, at the `ws.size` rows it holds, is valid
(every kernel reads it), holds that many words, reads back through `Column.foROpt` as `none` at a null
(`Column.bitAt nul`) and `ws` elsewhere (`foROpt_encode`, whose `hbig` the `USize` row count discharges), and is
`Ext.Enc.WF` at every fixed-width type, a boolean one where every word but a null's is `0` or `1`. -/
theorem wordsFoR_nul (ws : Array UInt64) (nul : ByteArray) {n : USize} (hn : n.toNat = ws.size) :
    Enc.Valid n (wordsFoR ws nul) ∧ (raw .i64 n (wordsFoR ws nul)).size = n.toNat ∧
      (∀ md pk, wordsFoR ws nul = .foR md pk → ∀ i (hi : i < ws.size),
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
  -- a `USize` count is below `2 ^ 64`, where the writer always patches, so `foROpt_encode`'s `hbig` is vacuous
  have hn64 : n.toNat < 2 ^ 64 := by have := n.toNat_lt_size; rcases USize.size_eq with h | h <;> omega
  have hopt : ∀ i (hi : i < ws.size),
      Column.foROpt (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).1
        (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).2
        (Column.blockStarts (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).1) i =
        if Column.bitAt nul i then none else some ws[i] := fun i hi => by
    rw [foROpt_encode Column.lgEnc hlg 8 (by decide) (by decide) X nul i (by omega) fun h64 => absurd h64 (by omega),
      hkey i hi]
  have hV : Enc.Valid n (.foR (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).1
      (Coc.encodeAt Column.lgEnc (8 : Nat).toUSize X true nul).2) := by
    have hl := (nblk_encode Column.lgEnc hlg 8 (by decide) (by decide) X (patch := true) (nul := nul)).2.2
    refine ⟨by unfold Column.lgOk; rw [hl]; decide, foRStd_iff.2 (hnX ▸ foRWF_encodeAt Column.lgEnc hlg 8 (by omega) X)⟩
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

/-- **A kernel's answer reads back its null flags**: row `i` of `wordsFoR ws nul` is flagged exactly where
`Column.bitAt nul i`. -/
theorem foRNuls_wordsFoR (ws : Array UInt64) (nul : ByteArray) {n : USize} (hn : n.toNat = ws.size) (i : Nat)
    (hi : i < ws.size) :
    (foRNuls n (wordsFoR ws nul))[i]? = some (if Column.bitAt nul i then 1 else 0) := by
  obtain ⟨md, pk, hE⟩ : ∃ md pk, wordsFoR ws nul = .foR md pk := ⟨_, _, rfl⟩
  have h := (wordsFoR_nul ws nul hn).2.2.1 md pk hE i hi
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

/-- Only `first` reads its sources as a stream, so any other op closes with no hypothesis on its sources. -/
theorem kscanStream_ne {op : Op} (h : op ≠ .first) (es : List (USize × Enc)) (pre post : List (Op × UInt64)) :
    kscanStream op es pre post = false := by
  unfold kscanStream; split <;> simp_all

/-- **`kscanCols` flags no null row** where every source holds none: a lock-step call carries no flags, and a stream's are
the sources' `foRNuls`, all `0` (`hasNul_flags`). -/
theorem kscanCols_nul {op : Op} {s : QAtomicType} {n : USize} {es : List (USize × Enc)} {pre post : List (Op × UInt64)}
    {ws : List (Array UInt64)} {ns : Array UInt64}
    (hS : kscanStream op es pre post = true → (∀ p ∈ es, hasNul p.2 = false) ∧ ∀ p ∈ es, Ext.Enc.WF s p.1 p.2)
    (h : kscanCols op s n es pre post = .ok (ws, ns)) : ns.any (· != 0) = false := by
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
        rw [← h.2]
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
    obtain ⟨-, rfl, -⟩ := kscanCols_lock hs h
    simp

/-- **`kscan` closes**: its answer is valid at its `n` rows, `Ext.Enc.WF` at its answer type `t`, and holds no null
(written with no null bitmap). Only a stream (`kscanStream`) reads its sources' null flags, so only there must they hold
no null and be `Ext.Enc.WF` at `s`. -/
theorem kscan_closed {op : Op} {rev : Bool} {s t : QAtomicType} {n : USize} {seg : Option Enc}
    {es : List (USize × Enc)} {pre post : List (Op × UInt64)} {r : Enc × Option UInt64}
    (hS : kscanStream op es pre post = true → (∀ p ∈ es, hasNul p.2 = false) ∧ ∀ p ∈ es, Ext.Enc.WF s p.1 p.2)
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
  have hns := kscanCols_nul hS hc
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
    (hs : kscanStream op es pre post = false) (h : kscan op rev s t n seg es pre post = .ok r) :
    Enc.Valid n r.1 ∧ Ext.Enc.WF t n r.1 ∧ hasNul r.1 = false :=
  kscan_closed (fun h => absurd h (by rw [hs]; decide)) h

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
