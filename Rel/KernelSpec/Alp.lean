import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.Kernel.Value

/-! The part of `Rel.Verify.Alp` the Rel kernels reach; `Rel.Verify.Alp` imports it. -/


namespace Rel.Verify

open Rel

theorem range_split (lo hi n : Nat) (h1 : lo ≤ hi) (h2 : hi ≤ n) :
    List.range n = List.range lo ++ List.range' lo (hi - lo) ++ List.range' hi (n - hi) := by
  have a := List.range'_append (s := 0) (m := lo) (n := hi - lo) (step := 1)
  have b := List.range'_append (s := 0) (m := hi) (n := n - hi) (step := 1)
  rw [show 0 + 1 * lo = lo by omega, show lo + (hi - lo) = hi by omega] at a
  rw [show 0 + 1 * hi = hi by omega, show hi + (n - hi) = n by omega] at b
  rw [List.range_eq_range', List.range_eq_range', ← b, ← a]

theorem filter_lt_range (P : Nat → Bool) (n m : Nat) :
    ((List.range n).filter P).filter (fun y => decide (y < m)) = (List.range (min m n)).filter P := by
  by_cases h : n ≤ m
  · rw [Nat.min_eq_right h, List.filter_eq_self.2]
    intro a ha; rw [List.mem_filter, List.mem_range] at ha; exact decide_eq_true (by omega)
  · rw [Nat.min_eq_left (by omega), range_split m m n (Nat.le_refl _) (by omega), Nat.sub_self,
      List.range'_zero, List.append_nil, List.filter_append, List.filter_append]
    have e1 : ((List.range m).filter P).filter (fun y => decide (y < m)) = (List.range m).filter P :=
      List.filter_eq_self.2 fun a ha => by rw [List.mem_filter, List.mem_range] at ha; exact decide_eq_true ha.1
    have e2 : ((List.range' m (n - m)).filter P).filter (fun y => decide (y < m)) = [] :=
      filter_nil_of _ _ fun a ha => by
        rw [List.mem_filter, List.mem_range'_1] at ha; exact decide_eq_false (by omega)
    rw [e1, e2, List.append_nil]

/-- In `A ++ B ++ C`, an index lands in `B` exactly when its entry lies in `B`'s range. -/
theorem block_index (L A B C : List Nat) (hL : L = A ++ B ++ C) (lo hi : Nat)
    (hA : ∀ y ∈ A, y < lo) (hB : ∀ y ∈ B, lo ≤ y ∧ y < hi) (hC : ∀ y ∈ C, hi ≤ y)
    (k : Nat) (hk : k < L.length) :
    (A.length ≤ k ∧ k < A.length + B.length) ↔ (lo ≤ L[k] ∧ L[k] < hi) := by
  subst hL
  rw [List.getElem_append]
  split
  · next h1 =>
    rw [List.length_append] at h1
    rw [List.getElem_append]
    split
    · next h2 =>
      have := hA _ (List.getElem_mem h2)
      exact ⟨fun h => absurd h.1 (by omega), fun h => absurd h.1 (by omega)⟩
    · next h2 =>
      have := hB _ (List.getElem_mem (show k - A.length < B.length by omega))
      exact ⟨fun _ => this, fun _ => ⟨by omega, by omega⟩⟩
  · next h1 =>
    rw [List.length_append] at h1
    have := hC _ (List.getElem_mem (show k - (A ++ B).length < C.length by
      simp only [List.length_append] at hk ⊢; omega))
    exact ⟨fun h => absurd h.2 (by omega), fun h => absurd h.2 (by omega)⟩

theorem sum_blocks (K n m : Nat) :
    ((List.range m).map fun c => min (c * K + K) n - c * K).sum =
      min (m * K) n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append_nat, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [Nat.succ_mul]; omega

theorem foldl_max_lt (l : List Nat) (g : Nat → Nat) (m a : Nat) (ha : a < m) (hg : ∀ j, g j < m) :
    l.foldl (fun acc j => max acc (g j)) a < m := by
  induction l generalizing a with
  | nil => exact ha
  | cons y l ih => exact ih _ (Nat.max_lt.2 ⟨ha, hg y⟩)

/-- The integers `Coc.alpEncodeAt` hands to `Coc.encode`: each block's entries at eight bytes, a
block that is not the last holding `blk` of them. -/
theorem foldl_blocks (K : Nat) (B : Nat × Array (Option UInt64) → UInt64) (L : List (Nat × Array (Option UInt64)))
    (a : ByteArray) :
    (L.foldl (fun acc be => be.2.foldl (fun a d => Column.pushBits a (d.getD (B be)) 8) acc) a).size =
      a.size + 8 * (L.map (·.2.size)).sum ∧
    (∀ i < a.size, (L.foldl (fun acc be => be.2.foldl (fun a d => Column.pushBits a (d.getD (B be)) 8) acc) a)[i]? =
      a[i]?) ∧
    ((∀ c (h : c + 1 < L.length), L[c].2.size = K) →
      ∀ c (h : c < L.length) j (hj : j < L[c].2.size) v, L[c].2[j] = some v →
        Column.bitsAt (L.foldl (fun acc be => be.2.foldl (fun a d => Column.pushBits a (d.getD (B be)) 8) acc) a)
          (a.size + 8 * (c * K + j)) 8 = v) := by
  induction L generalizing a with
  | nil => simp
  | cons be L ih =>
    obtain ⟨is, ip, ir⟩ := foldl_pushBits (fun d => d.getD (B be)) 8 (by decide) be.2.toList a
    simp only [Array.foldl_toList, Array.length_toList] at is ip ir
    obtain ⟨hs, hp, hr⟩ := ih (be.2.foldl (fun a d => Column.pushBits a (d.getD (B be)) 8) a)
    simp only [List.foldl_cons, List.length_cons, List.map_cons, List.sum_cons]
    refine ⟨by rw [hs, is]; omega, fun i hi => by rw [hp i (by omega), ip i hi], ?_⟩
    intro hfull c hc j hj v hv
    cases c with
    | zero =>
      simp only [List.getElem_cons_zero] at hj hv
      rw [Nat.zero_mul, Nat.zero_add,
        Column.bitsAt_congr (be.2.foldl (fun a d => Column.pushBits a (d.getD (B be)) 8) a) _ (a.size + 8 * j) 8
          (fun k hk => hp _ (by omega)), ir j (by simpa using hj)]
      simp [hv]
    | succ c =>
      simp only [List.getElem_cons_succ] at hj hv
      have hb0 : be.2.size = K := by simpa using hfull 0 (by simp at hc ⊢; omega)
      have := hr (fun c' h' => by simpa using hfull (c' + 1) (by simp; omega)) c (by simp at hc; omega) j hj v hv
      rw [is, show a.size + 8 * be.2.size + 8 * (c * K + j) =
        a.size + 8 * ((c + 1) * K + j) by rw [hb0, Nat.add_mul, Nat.one_mul]; omega] at this
      exact this

theorem blocks_size (B : Nat × Array (Option UInt64) → UInt64) (bs : Array (Nat × Array (Option UInt64))) :
    (bs.foldl (fun acc be => be.2.foldl (fun a d => Column.pushBits a (d.getD (B be)) 8) acc) ByteArray.empty).size =
      8 * (bs.toList.map (·.2.size)).sum := by
  rw [← Array.foldl_toList, (foldl_blocks 0 B bs.toList ByteArray.empty).1,
    show ByteArray.empty.size = 0 from rfl, Nat.zero_add]

theorem blocks_read (K : Nat) (B : Nat × Array (Option UInt64) → UInt64) (bs : Array (Nat × Array (Option UInt64)))
    (hfull : ∀ c (h : c + 1 < bs.size), bs[c].2.size = K) (c : Nat) (hc : c < bs.size) (j : Nat)
    (hj : j < bs[c].2.size) (v : UInt64) (hv : bs[c].2[j] = some v) :
    Column.bitsAt (bs.foldl (fun acc be => be.2.foldl (fun a d => Column.pushBits a (d.getD (B be)) 8) acc)
      ByteArray.empty) (8 * (c * K + j)) 8 = v := by
  have := (foldl_blocks K B bs.toList ByteArray.empty).2.2 (fun c h => by simpa using hfull c (by simpa using h))
    c (by simpa using hc) j (by simpa using hj) v (by simpa using hv)
  rw [Array.foldl_toList, show ByteArray.empty.size = 0 from rfl, Nat.zero_add] at this
  exact this

/-- `Coc.encode`'s block count, the one `Column.alpSects` is laid out by. -/
theorem nblk_encode (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (x : ByteArray)
    {patch : Bool} :
    Column.nblk (Kernel.Coc.encodeAt lg w.toUSize x patch).1 = (x.size / w + 2 ^ lg - 1) / 2 ^ lg ∧
      Column.blk (Kernel.Coc.encodeAt lg w.toUSize x patch).1 = 2 ^ lg ∧ Column.lgAt (Kernel.Coc.encodeAt lg w.toUSize x patch).1 = lg := by
  have hwt : w.toUSize.toNat = w := by
    rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize, h] <;> omega
  unfold Kernel.Coc.encodeAt
  simp only [hwt]
  generalize x.size / w = n
  have hpb := fun b => planBlock_bounds lg w n hw (patch && decide (n < 2 ^ 32)) x b
  generalize (patch && decide (n < 2 ^ 32)) = pl at hpb ⊢
  generalize Kernel.Coc.planBlock lg w n pl x = blk at hpb ⊢
  have hMr := foRMeta_reads lg (Nat.lt_of_le_of_lt hlg.2 (by decide)) (Kernel.Coc.sumNul w) n
    ((Array.map blk (Array.range ((n + 2 ^ lg - 1) / 2 ^ lg))).map fun x =>
      (Kernel.Coc.unbias w x.1, Kernel.Coc.unbias w x.2.1, x.2.2.1, x.2.2.2.2)) (fun b h => by
      simp only [Array.size_map, Array.size_range] at h
      simp only [Array.getElem_map, getElem_range]
      exact Nat.lt_of_le_of_lt (hpb b (mul_lt_of_lt_cdiv (Nat.two_pow_pos lg) h)).2.2.1 (by decide))
  exact ⟨by rw [hMr.1]; simp, by rw [blk_of_lgAt _ (by rw [hMr.2.1]; exact hlg), hMr.2.1], hMr.2.1⟩

/-- A decimal the encoder accepted is one `Column.alpDec` turns back into the bits it came from:
`Coc.alpDat` answers `some d` only after comparing `alpDec d e f32` with them. -/
theorem alpDat_some (f32 : Bool) (x : UInt64) (e : Nat) (v : UInt64) (h : Kernel.Coc.alpDat f32 x e = some v) :
    Column.alpDec v e f32 = x := by
  unfold Kernel.Coc.alpDat at h; dsimp only at h
  split at h
  · split at h
    · next hb => obtain rfl := Option.some.inj h; exact beq_iff_eq.1 hb
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- What each reader of the alp blob answers on what `Coc.alpBlob` wrote, at the element width the
blob's flag declares. -/
theorem alpBlob_reads (f32 : Bool) (K : Nat) (hK : 0 < K ∧ K ≤ 65536) (w : Nat) (hw : (if f32 then 4 else 8) = w) (n : Nat) (x : ByteArray)
    (bs : Array (Nat × Array (Option UInt64))) (M : ByteArray) (exc : Array Nat)
    (hexc : exc = (Array.range n).filter fun i => ((bs[i / K]!).2[i % K]!).isNone)
    (hM : Column.nblk M = bs.size) (hn : n < 2 ^ 32) (he : ∀ b (h : b < bs.size), bs[b].1 < 256) :
    Column.alpF32 (Kernel.Coc.alpBlob f32 K w n x bs) = f32 ∧
    (∀ k (h : k < exc.size), Column.alpExcRaw (Kernel.Coc.alpBlob f32 K w n x bs) k =
      Column.bitsAt x (exc[k] * w) w) ∧
    (∀ b ≤ bs.size, Column.alpExcOff M (Kernel.Coc.alpBlob f32 K w n x bs) b =
      (exc.filter (· < b * K)).size) ∧
    (∀ k (h : k < exc.size), Column.alpExcPos M (Kernel.Coc.alpBlob f32 K w n x bs) k = exc[k] % K) ∧
    (∀ b (h : b < bs.size), Column.alpExpAt M (Kernel.Coc.alpBlob f32 K w n x bs) b = bs[b].1) ∧
    Column.alpNexc (Kernel.Coc.alpBlob f32 K w n x bs) = exc.size := by
  have hw8 : w ≤ 8 := by subst hw; cases f32 <;> decide
  have hen : exc.size ≤ n := by
    rw [hexc, ← Array.length_toList, Array.toList_filter, toList_range]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hA : Kernel.Coc.alpBlob f32 K w n x bs = Kernel.Coc.excBlob (if f32 then 1 else 0) K w bs.size x exc
      (bs.foldl (init := ByteArray.empty) fun acc be => acc.push be.1.toUInt8) := by subst hexc; rfl
  rw [hA]
  have W4 := foldl_push8 (fun be : Nat × Array (Option UInt64) => be.1.toUInt8) bs.toList ByteArray.empty
  rw [Array.foldl_toList] at W4
  generalize bs.foldl (init := ByteArray.empty) (fun acc be => acc.push be.1.toUInt8) = L at W4 ⊢
  -- the blob is an exception ladder read from its start
  obtain ⟨hc, hwd, hraw, hoff, hpos, hlast, -⟩ := excBlob_reads (if f32 then 1 else 0) K hK w hw8 bs.size x exc L
    (by omega) (Kernel.Coc.excBlob (if f32 then 1 else 0) K w bs.size x exc L) 0 (fun k _ => by rw [Nat.zero_add])
  simp only [Nat.zero_add] at hwd hraw hoff hpos hlast
  generalize Kernel.Coc.excBlob (if f32 then 1 else 0) K w bs.size x exc L = A at hc hwd hraw hoff hpos hlast ⊢
  have hf32 : Column.alpF32 A = f32 := by unfold Column.alpF32; rw [hwd]; cases f32 <;> decide
  have hesz : Column.alpEsz A = w := by unfold Column.alpEsz; rw [hf32, hw]
  have hnx : Column.alpNexc A = exc.size := hc
  refine ⟨hf32, fun k hk => ?_, fun b hb => ?_, fun k hk => ?_, fun b hb => ?_, hnx⟩
  · unfold Column.alpExcRaw; rw [hesz, hraw k hk]
  · unfold Column.alpExcOff; rw [hM, hnx, hesz, hoff b hb]
  · unfold Column.alpExcPos; rw [hM, hnx, hesz, hpos k hk]
  · unfold Column.alpExpAt; rw [hM, hnx, hesz]
    have e0 : ByteArray.empty.size = 0 := rfl
    have := W4.2.2 b (by simpa using hb)
    simp only [e0, Nat.zero_add, Array.getElem_toList] at this W4
    rw [hlast b (by rw [W4.1]; simpa using hb), this]
    simp [Nat.mod_eq_of_lt (he b hb)]

/-- **The ALP round trip, element by element on the bits**, at either element width — `alpEncode64`
is `f32 = false`, `alpEncode32` is `true`: the blob's flag is the one asked for, and element `i` of
`Coc.alpEncodeAt f32 x`, read by `Column.alpBits`, is element `i` of `x`. NaN payloads, signed zeros
and q's `0n`, `0w`, `-0w` included, since an exception is copied and a decimal was accepted only on
its bits. -/
theorem alpBits_alpEncodeAt (f32 : Bool) (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw : (if f32 then 4 else 8) = w) (x : ByteArray)
    (hx : x.size / w < 2 ^ 32) :
    let e := Kernel.Coc.alpEncodeAt f32 x lg
    Column.alpF32 e.2.2 = f32 ∧
    ∀ i < x.size / w, Column.alpBits e.1 e.2.1 e.2.2 (Column.blockStarts e.1) i = Column.bitsAt x (i * w) w := by
  show Column.alpF32 (Kernel.Coc.alpEncodeAt f32 x lg).2.2 = f32 ∧ ∀ i < x.size / w,
    Column.alpBits (Kernel.Coc.alpEncodeAt f32 x lg).1 (Kernel.Coc.alpEncodeAt f32 x lg).2.1
      (Kernel.Coc.alpEncodeAt f32 x lg).2.2 (Column.blockStarts (Kernel.Coc.alpEncodeAt f32 x lg).1) i = _
  unfold Kernel.Coc.alpEncodeAt
  simp only [hw]
  generalize hn : x.size / w = n at hx ⊢
  generalize hown : Array.map (fun i => Kernel.Coc.alpOwn f32 (Column.bitsAt x (i * w) w)) (Array.range n) = own
  generalize hbs : Array.map (fun b => Kernel.Coc.alpBlockOf f32 (2 ^ lg) w n b x own)
    (Array.range ((n + 2 ^ lg - 1) / 2 ^ lg)) = bs
  generalize hds : Array.foldl _ ByteArray.empty bs = ds
  rw [show Kernel.Coc.encodeAt lg 8 ds false = Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds false from rfl]
  have hKp : 0 < 2 ^ lg := Nat.two_pow_pos lg
  -- the blocks
  have hnb : bs.size = (n + 2 ^ lg - 1) / 2 ^ lg := by rw [← hbs]; simp
  have hbget : ∀ c (h : c < bs.size), bs[c] = Kernel.Coc.alpBlockOf f32 (2 ^ lg) w n c x own := by
    intro c h; subst hbs; simp only [Array.getElem_map, getElem_range]
  have hbl : ∀ c, (Kernel.Coc.alpBlockOf f32 (2 ^ lg) w n c x own).2.size =
      min (c * 2 ^ lg + 2 ^ lg) n - c * 2 ^ lg := by
    intro c; simp [Kernel.Coc.alpBlockOf]
  have hel : ∀ c (hc : c < bs.size) j (hj : j < bs[c].2.size), bs[c].2[j] =
      if (own[c * 2 ^ lg + j]! : Option Nat).isNone then none
      else Kernel.Coc.alpDat f32 (Column.bitsAt x ((c * 2 ^ lg + j) * w) w) bs[c].1 := by
    intro c hc j hj; subst hbs; simp only [Array.getElem_map, getElem_range, Kernel.Coc.alpBlockOf]
  have hown19 : ∀ k : Nat, (own[k]! : Option Nat).getD 0 < 19 := by
    intro k
    by_cases hk : k < own.size
    · simp only [getElem!_pos, hk]
      have : own[k] = Kernel.Coc.alpOwn f32 (Column.bitsAt x (k * w) w) := by
        subst hown; simp only [Array.getElem_map, getElem_range]
      rw [this]; unfold Kernel.Coc.alpOwn; split
      · decide
      · generalize hf : List.find? _ (List.range 19) = o
        cases o with
        | none => decide
        | some e => have := List.mem_of_find?_eq_some hf; simpa using this
    · rw [getElem!_def, Array.getElem?_eq_none (by omega)]; decide
  have hexp : ∀ c, (Kernel.Coc.alpBlockOf f32 (2 ^ lg) w n c x own).1 < 19 := by
    intro c; simp only [Kernel.Coc.alpBlockOf, ← Array.foldl_toList]
    exact foldl_max_lt _ _ 19 0 (by decide) (fun j => hown19 _)
  have hfull : ∀ c (h : c + 1 < bs.size), bs[c].2.size = 2 ^ lg := by
    intro c h; rw [hbget c (by omega), hbl]; rw [hnb] at h
    have := mul_lt_of_lt_cdiv hKp h; rw [Nat.succ_mul] at this; omega
  -- the decimals' pack
  have hdsz : ds.size = 8 * n := by
    rw [← hds, blocks_size, ← hbs, Array.toList_map, toList_range, List.map_map]
    simp only [Function.comp_def, hbl]
    rw [sum_blocks]; have := Nat.mod_add_div' (n + 2 ^ lg - 1) (2 ^ lg); have := Nat.mod_lt (n + 2 ^ lg - 1) hKp; omega
  have hM : Column.nblk (Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds false).1 = bs.size := by
    rw [(nblk_encode lg hlg 8 (by decide) (by decide) ds).1, hdsz, hnb, Nat.mul_div_cancel_left n (by decide)]
  -- the alp blob
  generalize hP : (fun i => ((bs[i / 2 ^ lg]!).2[i % 2 ^ lg]!).isNone) = P
  generalize hexc : (Array.range n).filter P = exc
  obtain ⟨hf32, hraw, hoff, hpos, hexpA, -⟩ := alpBlob_reads f32 (2 ^ lg) ⟨Nat.two_pow_pos lg, Nat.pow_le_pow_right (by decide) hlg.2⟩ w hw n x bs _ exc (by rw [← hexc, ← hP]) hM hx
    (fun b h => by rw [hbget b h]; exact Nat.lt_trans (hexp b) (by decide))
  refine ⟨hf32, fun i hi => ?_⟩
  have hib : i / 2 ^ lg < bs.size := by rw [hnb]; exact lt_cdiv hKp (by omega)
  have hjb : i % 2 ^ lg < bs[i / 2 ^ lg].2.size := by
    rw [hbget _ hib, hbl]; have := Nat.mod_add_div' i (2 ^ lg); have := Nat.mod_lt i hKp; omega
  have hfr : Column.foRBits (Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds false).1
      (Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds false).2
      (Column.blockStarts (Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds false).1) i = Column.bitsAt ds (i * 8) 8 := by
    apply UInt64.toNat_inj.1
    rw [← Nat.mod_eq_of_lt (UInt64.toNat_lt _),
      foRBits_encode_bits lg hlg 8 (by decide) (by decide) ds i (by rw [hdsz]; omega)]
  generalize Kernel.Coc.alpBlob f32 (2 ^ lg) w n x bs = A at hf32 hraw hoff hpos hexpA ⊢
  have hBMP := (nblk_encode lg hlg 8 (by decide) (by decide) ds (patch := false)).2.1
  generalize Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds false = MP at hfr hM hoff hpos hexpA hBMP ⊢
  have hPi : P i = (bs[i / 2 ^ lg].2[i % 2 ^ lg]).isNone := by
    rw [← hP]; simp only [getElem!_pos, hib, hjb]
  -- the exceptions of block `i / blk`, as a slice of the exception list
  have hL : exc.toList = (List.range n).filter P := by rw [← hexc, Array.toList_filter, toList_range]
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = i / 2 ^ lg * 2 ^ lg := ⟨_, rfl⟩
  obtain ⟨hi', hhi⟩ : ∃ hi', hi' = min (lo + 2 ^ lg) n := ⟨_, rfl⟩
  have l1 : lo ≤ i := by rw [hlo]; exact Nat.div_mul_le_self i _
  have l2 : i < hi' := by rw [hhi, hlo]; have := Nat.mod_add_div' i (2 ^ lg); have := Nat.mod_lt i hKp; omega
  have l3 : hi' ≤ n := by rw [hhi]; omega
  have hdec : exc.toList = (List.range lo).filter P ++ (List.range' lo (hi' - lo)).filter P ++
      (List.range' hi' (n - hi')).filter P := by
    rw [hL, range_split lo hi' n (by omega) l3, List.filter_append, List.filter_append]
  have hAB : (List.range hi').filter P = (List.range lo).filter P ++ (List.range' lo (hi' - lo)).filter P := by
    rw [range_split lo hi' hi' (by omega) (Nat.le_refl _), Nat.sub_self, List.range'_zero, List.append_nil,
      List.filter_append]
  have hA : ∀ y ∈ (List.range lo).filter P, y < lo := fun y hy => by
    rw [List.mem_filter, List.mem_range] at hy; exact hy.1
  have hB : ∀ y ∈ (List.range' lo (hi' - lo)).filter P, lo ≤ y ∧ y < hi' := fun y hy => by
    rw [List.mem_filter, List.mem_range'_1] at hy; exact ⟨hy.1.1, by omega⟩
  have hC : ∀ y ∈ (List.range' hi' (n - hi')).filter P, hi' ≤ y := fun y hy => by
    rw [List.mem_filter, List.mem_range'_1] at hy; exact hy.1.1
  have hc0 : Column.alpExcOff MP.1 A (i / 2 ^ lg) = ((List.range lo).filter P).length := by
    rw [hoff _ (Nat.le_of_lt hib), ← Array.length_toList, Array.toList_filter, hL, filter_lt_range, ← hlo,
      Nat.min_eq_left (by omega)]
  have hc1 : Column.alpExcOff MP.1 A (i / 2 ^ lg + 1) = ((List.range hi').filter P).length := by
    rw [hoff _ hib, ← Array.length_toList, Array.toList_filter, hL, filter_lt_range,
      show min ((i / 2 ^ lg + 1) * 2 ^ lg) n = hi' by rw [hhi, hlo, Nat.add_mul, Nat.one_mul]]
  have hlen : ((List.range hi').filter P).length ≤ exc.size := by
    rw [← Array.length_toList, hdec, hAB]; simp only [List.length_append]; omega
  have F1 : ∀ k', (List.range' ((List.range lo).filter P).length (((List.range hi').filter P).length -
      ((List.range lo).filter P).length)).find? (fun k => Column.alpExcPos MP.1 A k == i % 2 ^ lg) = some k' →
      ∃ h : k' < exc.size, exc[k'] = i := by
    intro k' hk'
    have hp := List.find?_some hk'
    have hm := List.mem_of_find?_eq_some hk'
    rw [List.mem_range'_1] at hm
    have hks : k' < exc.size := by omega
    refine ⟨hks, ?_⟩
    rw [hpos k' hks, beq_iff_eq] at hp
    have hbi := (block_index exc.toList _ _ _ hdec lo hi' hA hB hC k' (by simpa using hks)).1
      ⟨hm.1, by rw [hAB, List.length_append] at hm; omega⟩
    simp only [Array.getElem_toList] at hbi
    rw [hhi, hlo] at hbi
    have hd := Nat.div_eq_of_lt_le hbi.1 (by rw [Nat.succ_mul]; omega)
    have h1 := Nat.mod_add_div' exc[k'] (2 ^ lg); rw [hd] at h1; have h2 := Nat.mod_add_div' i (2 ^ lg); omega
  unfold Column.alpBits
  rw [hBMP]
  rw [show Column.alpExcAt MP.1 A (i / 2 ^ lg) (i % 2 ^ lg) =
      (List.range' ((List.range lo).filter P).length (((List.range hi').filter P).length -
        ((List.range lo).filter P).length)).find? (fun k => Column.alpExcPos MP.1 A k == i % 2 ^ lg) by
    unfold Column.alpExcAt; rw [hc0, hc1]]
  split
  · -- an exception: its stored bits
    next k' hk' =>
    obtain ⟨hks, hke⟩ := F1 k' hk'
    rw [hraw k' hks, hke]
  · -- no exception: the decimal the encoder checked
    next hk' =>
    have hnP : P i = false := by
      cases hPt : P i
      · rfl
      · exfalso
        have hmem : i ∈ exc.toList := by rw [hL, List.mem_filter, List.mem_range]; exact ⟨by omega, hPt⟩
        obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 hmem
        have hbi := (block_index exc.toList _ _ _ hdec lo hi' hA hB hC k hk).2
          ⟨by rw [hke]; exact l1, by rw [hke]; exact l2⟩
        rw [List.find?_eq_none] at hk'
        apply hk' k (by rw [List.mem_range'_1, hAB, List.length_append]; omega)
        rw [hpos k (by simpa using hk), beq_iff_eq, ← Array.getElem_toList, hke]
    rw [hPi] at hnP
    cases hv : (bs[i / 2 ^ lg]'hib).2[i % 2 ^ lg]'hjb with
    | none => rw [hv] at hnP; cases hnP
    | some v =>
      have hrd : Column.bitsAt ds (i * 8) 8 = v := by
        rw [← hds, show i * 8 = 8 * (i / 2 ^ lg * 2 ^ lg + i % 2 ^ lg) by rw [Nat.div_add_mod']; omega]
        exact blocks_read (2 ^ lg) _ bs hfull _ hib _ hjb v hv
      rw [hfr, hexpA _ hib, hf32, hrd]
      rw [hel _ hib _ hjb] at hv
      split at hv
      · cases hv
      · have := alpDat_some f32 _ _ v hv
        rwa [Nat.div_add_mod'] at this

/-- What the writers guarantee of a Frame-of-Reference column of `n` elements: one block per started
`blk` elements, a pack ending where its last block's residuals do or where the patch list its header
declares does, and no width past 64. -/
structure FoRWF (n : Nat) (md pk : ByteArray) : Prop where
  nblk : Column.nblk md = (n + Column.blk md - 1) / Column.blk md
  size : pk.size = Column.blockStart md (Column.nblk md)
    ∨ (Kernel.Coc.foRTail (Column.nblk md) pk (Column.blockStart md (Column.nblk md))).map
        (Column.blockStart md (Column.nblk md) + ·) = some pk.size
  width : ∀ b < Column.nblk md, Column.widthAt md b ≤ 64

end Rel.Verify


namespace Rel.Verify

open Rel

/-- **The runtime test is the writer's form**: `Kernel.Coc.foRStd` is `FoRWF`. -/
theorem foRStd_iff {n : USize} {md pk : ByteArray} : Kernel.Coc.foRStd n md pk = true ↔ FoRWF n.toNat md pk := by
  simp only [Kernel.Coc.foRStd, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

/-- **What the encoder writes is the writers' form**, at every element width a kernel is instantiated at and every
block size the layout admits, patched or not: the codec's half of the closure law, a column the codec answers is one
every kernel that reads `foR` through `Coc.foRStd` accepts. -/
theorem foRWF_encodeAt (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (x : ByteArray) {patch : Bool} :
    FoRWF (x.size / w) (Kernel.Coc.encodeAt lg w.toUSize x patch).1 (Kernel.Coc.encodeAt lg w.toUSize x patch).2 := by
  have hw0 : 0 < w := by omega
  have hw8 : w ≤ 8 := by omega
  have hwt : w.toUSize.toNat = w := by
    rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize, h] <;> omega
  have hBp : 0 < 2 ^ lg := Nat.two_pow_pos _
  have hB16 : 2 ^ lg ≤ 65536 := Nat.pow_le_pow_right (by decide) hlg.2
  unfold Kernel.Coc.encodeAt
  simp only [hwt]
  generalize x.size / w = n
  have hpb := fun b => planBlock_bounds lg w n hw8 (patch && decide (n < 2 ^ 32)) x b
  have h32 : (patch && decide (n < 2 ^ 32)) = true → n < 2 ^ 32 := fun h => by simp at h; exact h.2
  generalize (patch && decide (n < 2 ^ 32)) = pl at hpb h32 ⊢
  generalize Kernel.Coc.planBlock lg w n pl x = blk at hpb ⊢
  generalize hbs : Array.map blk (Array.range ((n + 2 ^ lg - 1) / 2 ^ lg)) = bs
  have hbsz : bs.size = (n + 2 ^ lg - 1) / 2 ^ lg := by rw [← hbs]; simp
  have hbget : ∀ b (h : b < bs.size), bs[b] = blk b := by
    intro b h; subst hbs; simp only [Array.getElem_map, getElem_range]
  have hMr := foRMeta_reads lg (Nat.lt_of_le_of_lt hlg.2 (by decide)) (Kernel.Coc.sumNul w) n
    (bs.map fun x => (Kernel.Coc.unbias w x.1, Kernel.Coc.unbias w x.2.1, x.2.2.1, x.2.2.2.2)) (fun b h => by
      simp only [Array.size_map] at h; simp only [Array.getElem_map]; rw [hbget b h]
      exact Nat.lt_of_le_of_lt (hpb b (mul_lt_of_lt_cdiv hBp (hbsz ▸ h))).2.2.1 (by decide))
  generalize Kernel.Coc.foRMeta lg (Kernel.Coc.sumNul w) n _ = M at hMr ⊢
  obtain ⟨hnb, hlgM, hMb⟩ := hMr
  have hBM : Column.blk M = 2 ^ lg := by rw [blk_of_lgAt M ⟨hlgM ▸ hlg.1, hlgM ▸ hlg.2⟩, hlgM]
  simp only [Array.size_map] at hnb hMb
  -- a patch list is written only with patching on, so below `2 ^ 32` elements
  have h32' : ∀ exc : Array Nat, exc = (Array.range n).filter (fun i => Kernel.Coc.outside
      (bs.getD (i / 2 ^ lg) default).2.2.2.1 (bs.getD (i / 2 ^ lg) default).2.2.2.2 (Kernel.Coc.keyAt w x i)) →
      exc.size ≠ 0 → exc.size < 2 ^ 32 := fun exc hexc h => by
    have hen : exc.size ≤ n := by
      rw [hexc, ← Array.length_toList, Array.toList_filter, toList_range]
      exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    cases hpl : pl
    · -- by cases on the list, not `List.eq_nil_iff_forall_not_mem`, which carries `Classical.choice`
      have he : exc.toList = [] := by
        cases hl : exc.toList with
        | nil => rfl
        | cons j t =>
          have hj : j ∈ exc.toList := hl ▸ List.mem_cons_self
          rw [hexc, Array.toList_filter, toList_range, List.mem_filter, List.mem_range] at hj
          have hb : j / 2 ^ lg < bs.size := hbsz ▸ lt_cdiv hBp hj.1
          have hk := ((hpb (j / 2 ^ lg) (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hj.1)).2.2.2.2 j
            (Nat.div_mul_le_self _ _) (by have := Nat.mod_add_div' j (2 ^ lg); have := Nat.mod_lt j hBp; omega)
            hj.1).2 hpl
          rw [show bs.getD (j / 2 ^ lg) default = bs[j / 2 ^ lg] by unfold Array.getD; rw [dif_pos hb]; rfl, hbget _ hb, hk] at hj; exact absurd hj.2 Bool.false_ne_true
      exact absurd (by rw [← Array.length_toList, he]; rfl) h
    · exact Nat.lt_of_le_of_lt hen (h32 hpl)
  generalize hexc : Array.filter (fun i => Kernel.Coc.outside (bs.getD (i / 2 ^ lg) default).2.2.2.1
      (bs.getD (i / 2 ^ lg) default).2.2.2.2 (Kernel.Coc.keyAt w x i)) (Array.range n) = exc
  have h32e := h32' exc hexc.symm
  have hfsz : (Array.map (fun x : Nat × Nat × UInt64 × Nat × Nat => (x.2.2.2.1 - x.1).toUInt64) bs).size =
      Column.nblk M := by simp [hnb]
  generalize Array.map (fun x : Nat × Nat × UInt64 × Nat × Nat => (x.2.2.2.1 - x.1).toUInt64) bs = fs at hfsz ⊢
  generalize (fs.any fun a => a != 0) = frm
  have hQ := pack_blockStart M (2 ^ lg) hBM bs (·.2.2.2.2) hnb (fun c h => by rw [(hMb c h).2]; simp)
    (fun (a : ByteArray × Nat) (e : Nat × Nat × UInt64 × Nat × Nat) =>
      (a.1 ++ Kernel.Coc.packRes (2 ^ lg) e.2.2.2.2 fun j => (if (decide (a.2 * 2 ^ lg + j < n) &&
        !Kernel.Coc.outside e.2.2.2.1 e.2.2.2.2 (Kernel.Coc.keyAt w x (a.2 * 2 ^ lg + j))) = true then
        Kernel.Coc.keyAt w x (a.2 * 2 ^ lg + j) - e.2.2.2.1 else 0).toUInt64, a.2 + 1))
    (fun m (e : Nat × Nat × UInt64 × Nat × Nat) j =>
      (if (decide (m * 2 ^ lg + j < n) && !Kernel.Coc.outside e.2.2.2.1 e.2.2.2.2
        (Kernel.Coc.keyAt w x (m * 2 ^ lg + j))) = true then
        Kernel.Coc.keyAt w x (m * 2 ^ lg + j) - e.2.2.2.1 else 0).toUInt64)
    (fun a m e => rfl)
  generalize (Array.foldl _ (ByteArray.empty, 0) bs).1 = pack at hQ ⊢
  refine ⟨by rw [hnb, hbsz, hBM], ?_, fun b hb => ?_⟩
  · split
    · left; rw [ByteArray.size_append, ← hQ.1]; rfl
    · next h0 =>
      right
      have hlast : (fs.foldl (init := ByteArray.empty) fun acc v => Column.pushBits acc v 8).size = 8 * bs.size := by
        rw [← Array.foldl_toList, (foldl_pushBits (fun v => v) 8 (by decide) fs.toList ByteArray.empty).1,
          Array.length_toList, hfsz, hnb]; simp
      obtain ⟨hc, hwd, -, -, -, -, -, hsz⟩ := excBlob_reads (w.toUInt64 ||| if frm = true then 256 else 0) (2 ^ lg)
        ⟨hBp, hB16⟩ w hw8 bs.size x exc
        (if frm = true then fs.foldl (init := ByteArray.empty) fun acc v => Column.pushBits acc v 8 else ByteArray.empty)
        (h32e h0) _ pack.size (fun k _ => ba_append_right _ _ _)
      have hW : ([1, 2, 4, 8].contains ((w.toUInt64 ||| if frm = true then 256 else 0).toNat % 256) &&
          decide ((w.toUInt64 ||| if frm = true then 256 else 0).toNat < 512)) = true ∧
          (w.toUInt64 ||| if frm = true then 256 else 0).toNat % 256 = w ∧
          (if (w.toUInt64 ||| if frm = true then 256 else 0).toNat < 256 then 0 else 8 * bs.size) =
            if frm = true then 8 * bs.size else 0 := by
        rcases hw with rfl | rfl | rfl | rfl <;> cases frm <;>
          exact ⟨by decide +kernel, by decide +kernel, by split <;> first | rfl | exact absurd ‹_› (by decide +kernel)⟩
      rw [← hQ.1, hnb]
      unfold Kernel.Coc.foRTail
      rw [hwd, hc, if_pos hW.1, Option.map_some, hW.2.1, hW.2.2, ByteArray.size_append, hsz]
      cases frm
      · simp
      · simp only [↓reduceIte, hlast]; rw [show (8 * bs.size + 7) / 8 * 8 = 8 * bs.size by omega]
  · rw [(hMb b (hnb ▸ hb)).2]; simp only [Array.getElem_map]; rw [hbget b (hnb ▸ hb)]
    exact (hpb b (mul_lt_of_lt_cdiv hBp (hbsz ▸ hnb ▸ hb))).2.2.1

end Rel.Verify
