module

public import Rel.Kernel.BitRows
public import Rel.KernelSpec.Scatter
public import Rel.KernelSpec.Encoding
public import Rel.KernelSpec.Chain
public import Rel.KernelSpec.Alp

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `kbitrows`' law (`doc/rel-architecture.zh.typ` §4, the bit-row kernel), on the words `Enc.raw` reads from its
arguments, from the body `bitRowsOf`. -/

namespace Rel.Verify
open Rel.Kernel Ext.Enc

/-- Every element of a list on which `forM` succeeds passes `f`. -/
private theorem forM_ok {ε α : Type} {f : α → Except ε PUnit} :
    ∀ {l : List α}, l.forM f = .ok () → ∀ x ∈ l, f x = .ok ()
  | [], _, _, hx => absurd hx List.not_mem_nil
  | a :: l, h, x, hx => by
    have h' : (f a >>= fun _ => l.forM f) = .ok () := h
    cases ha : f a with
    | error e => rw [ha] at h'; cases h'
    | ok u =>
      rw [ha] at h'
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact forM_ok h' x hx

/-- A check `unless c do throw e` that passes holds `c`. -/
private theorem ok_of_unless {ε : Type} {c : Prop} [Decidable c] {e : ε}
    (h : (if c then pure PUnit.unit else throw e : Except ε PUnit) = .ok ()) : c := by
  by_cases hc : c
  · exact hc
  · rw [if_neg hc] at h; cases h

/-- The `u1` `foR` `kbitrows` writes of the bits `f`: element `i` reads as `f i`, as `u1` and as `i64` alike. -/
private theorem raw_bitmap (f : Nat → Bool) (N : Nat) (n : USize) (hn : n.toNat = N) (i : Nat) (hi : i < N) {e : Enc}
    (he : e = .foR (Coc.encodeAt Column.lgEnc (USize.ofNat32 1 (by decide))
      ⟨(Array.range N).map fun i => if f i then 1 else 0⟩ false).1 (Coc.encodeAt Column.lgEnc (USize.ofNat32 1 (by decide))
      ⟨(Array.range N).map fun i => if f i then 1 else 0⟩ false).2) :
    (raw .u1 n e)[i]? = some (if f i then 1 else 0) ∧ (raw .i64 n e)[i]? = some (if f i then 1 else 0) := by
  subst he
  have h1 : USize.ofNat32 1 (by decide) = (1 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp)
  have hlg : 6 ≤ Column.lgEnc ∧ Column.lgEnc ≤ 16 := ⟨by decide, by decide⟩
  simp only [h1]
  generalize hX : (⟨(Array.range N).map fun i => if f i then (1 : UInt8) else 0⟩ : ByteArray) = X
  have hXs : X.size = N := by rw [← hX]; simp [ByteArray.size]
  have hXi : X[i]?.getD 0 = if f i then 1 else 0 := by
    rw [getElem?_pos X i (by omega), Option.getD_some, ByteArray.getElem_eq_getElem_data]
    subst hX; simp
  have hv := foRBits_encode Column.lgEnc hlg 1 (by decide) (by decide) X (patch := false) i (by rw [Nat.div_one]; omega)
  simp only [Coc.keyAt, Column.sext, beq_self_eq_true, if_true, Nat.mul_one, bitsAt_one, hXi] at hv
  rw [raw_foR .i64 8 rfl (by decide)]
  simp only [raw, Array.getElem?_map, Array.getElem?_range, hn, hi, if_true, Option.map_some, hv]
  constructor <;> split <;> decide

/-- **The bit-row law**: on the words `es` (`g` segment ends), `is` (`ni` row numbers) and `ms` (`na · w` words, each
read at bit 0) `kbitrows` reads, every segment `[lo r, hi r)` is in order and at most `ni`, every row number is below
`na`, and answer bit `r·w + j`, read as `u1` and as `i64` alike, is `1` exactly when bit `is[k]·w + j` of `ms` is set
for every (`all`) or some (`¬all`) `k` of segment `r`. -/
theorem raw_kbitrows {all : Bool} {w na ni g : USize} {ends idx m o : Enc}
    (h : kbitrows all w na ni g ends idx m = .ok o) :
    let es := raw .i64 g ends
    let is := raw .i64 ni idx
    let ms := raw .i64 (na * w) m
    let lo := fun r => if r = 0 then 0 else (es[r - 1]?.getD 0).toNat
    let hi := fun r => (es[r]?.getD 0).toNat
    let on := fun j k => (ms[(is[k]?.getD 0).toNat * w.toNat + j]?.getD 0) % 2 = 1
    (na * w).toNat = na.toNat * w.toNat ∧ (g * w).toNat = g.toNat * w.toNat ∧
    es.size = g.toNat ∧ is.size = ni.toNat ∧ ms.size = na.toNat * w.toNat ∧
    (∀ r < g.toNat, lo r ≤ hi r ∧ hi r ≤ ni.toNat) ∧ (∀ k < ni.toNat, (is[k]?.getD 0).toNat < na.toNat) ∧
    ∀ r < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .u1 (g * w) o)[r * w.toNat + j]? = some v ∧
      (raw .i64 (g * w) o)[r * w.toNat + j]? = some v ∧ v < 2 ∧
      (v = 1 ↔ if all then ∀ k, lo r ≤ k → k < hi r → on j k else ∃ k, lo r ≤ k ∧ k < hi r ∧ on j k) := by
  intro es is ms lo hi on
  have hU : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  unfold kbitrows at h
  split at h
  case isFalse => cases h
  rename_i hb
  have hnw : (na * w).toNat = na.toNat * w.toNat := by rw [USize.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  have hgw : (g * w).toNat = g.toNat * w.toNat := by rw [USize.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i es' hes
  split at h
  · cases h
  rename_i is' his
  split at h
  · cases h
  split at h
  · cases h
  rename_i ms' hms
  have hms' : foRWords "bitrows: m" (na * w) m = .ok ms' := by
    rw [← hms]; congr 1; exact USize.toNat_inj.mp (by rw [hnw]; rfl)
  obtain ⟨rfl, hes⟩ := foRWords_raw _ _ _ _ hes
  obtain ⟨rfl, his⟩ := foRWords_raw _ _ _ _ his
  obtain ⟨rfl, hms⟩ := foRWords_raw _ _ _ _ hms'
  rw [hnw] at hms
  unfold bitRowsOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i u1 hseg
  split at h
  · cases h
  rename_i u2 hidx
  cases h
  have hseg' : ∀ r < g.toNat, lo r ≤ hi r ∧ hi r ≤ ni.toNat := fun r hr =>
    ok_of_unless (forM_ok hseg r (List.mem_range.2 hr))
  have hidx' : ∀ k < ni.toNat, (is[k]?.getD 0).toNat < na.toNat := fun k hk =>
    ok_of_unless (forM_ok hidx k (List.mem_range.2 hk))
  refine ⟨hnw, hgw, hes, his, hms, hseg', hidx', fun r hr j hj => ?_⟩
  have hw0 : 0 < w.toNat := by omega
  have hrj : r * w.toNat + j < g.toNat * w.toNat := by
    have := Nat.mul_le_mul_right w.toNat (show r + 1 ≤ g.toNat by omega)
    rw [Nat.succ_mul] at this; omega
  have hdiv : (r * w.toNat + j) / w.toNat = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (r * w.toNat + j) % w.toNat = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  refine ⟨_, (raw_bitmap _ _ _ hgw _ hrj rfl).1, (raw_bitmap _ _ _ hgw _ hrj rfl).2,
    (by decide : ∀ b : Bool, (if b then (1 : UInt64) else 0) < 2) _, ?_⟩
  obtain ⟨hl, hh⟩ := hseg' r hr
  simp only [lo, hi, on, es, is, ms] at hl hh ⊢
  simp only [hdiv, hmod]
  rw [show ∀ b : Bool, ((if b then (1 : UInt64) else 0) = 1 ↔ b = true) by decide]
  cases all <;> simp only [Bool.false_eq_true, if_false, if_true, List.all_eq_true, List.any_eq_true,
    List.mem_range'_1, beq_iff_eq]
  · exact ⟨fun ⟨k, ⟨h1, h2⟩, h3⟩ => ⟨k, h1, by omega, h3⟩, fun ⟨k, h1, h2, h3⟩ => ⟨k, ⟨h1, by omega⟩, h3⟩⟩
  · exact ⟨fun H k h1 h2 => H k ⟨h1, by omega⟩, fun H k ⟨h1, h2⟩ => H k h1 (by omega)⟩

/-- **A bit matrix holds no null**: `kbitrows` writes it with no null bitmap (`nulAt_encodeAt_empty`). -/
theorem kbitrows_plain {all : Bool} {w na ni g : USize} {ends idx m o : Enc}
    (h : kbitrows all w na ni g ends idx m = .ok o) : hasNul o = false := by
  have h1 : USize.ofNat32 1 (by decide) = (1 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp)
  unfold kbitrows at h
  split at h
  case isFalse => cases h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  unfold bitRowsOf at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  cases h
  simp only [h1, hasNul, List.any_eq_false, List.mem_range]
  intro b hb
  rw [nulAt_encodeAt_empty Column.lgEnc ⟨by decide, by decide⟩ 1 (by decide) (by decide) _ b hb]; decide

end Rel.Verify
