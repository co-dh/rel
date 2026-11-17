import QLean.RelPart.Verify.Encoding
import QLean.RelPart.Kernel.Coc
import QLean.RelPart.Value

/-! The part of `QLean.Verify.Alp` the Rel kernels reach; `QLean.Verify.Alp` imports it. -/


namespace QLean.Verify

open QLean

/-- Five padded sections laid end to end, each read back at its own start. -/
theorem blob_get (pad : ByteArray → ByteArray) (hp : ∀ b k, k < b.size → (pad b)[k]? = b[k]?)
    (hs : ∀ b, b.size ≤ (pad b).size) (S0 S1 S2 S3 S4 : ByteArray) :
    (∀ k < S0.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[k]? = S0[k]?) ∧
    (∀ k < S1.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[(pad S0).size + k]? = S1[k]?) ∧
    (∀ k < S2.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[(pad S0).size + (pad S1).size + k]? =
      S2[k]?) ∧
    (∀ k < S3.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[(pad S0).size + (pad S1).size +
      (pad S2).size + k]? = S3[k]?) ∧
    (∀ k < S4.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[(pad S0).size + (pad S1).size +
      (pad S2).size + (pad S3).size + k]? = S4[k]?) := by
  have h0 := hs S0; have h1 := hs S1; have h2 := hs S2; have h3 := hs S3
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by omega)]
    exact hp _ _ hk
  · rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega), ba_append_right]
    exact hp _ _ hk
  · rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      show (pad S0).size + (pad S1).size + k = (pad S0 ++ pad S1).size + k by rw [ByteArray.size_append],
      ba_append_right]; exact hp _ _ hk
  · rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      show (pad S0).size + (pad S1).size + (pad S2).size + k = (pad S0 ++ pad S1 ++ pad S2).size + k by
        simp only [ByteArray.size_append],
      ba_append_right]; exact hp _ _ hk
  · rw [show (pad S0).size + (pad S1).size + (pad S2).size + (pad S3).size + k =
        (pad S0 ++ pad S1 ++ pad S2 ++ pad S3).size + k by simp only [ByteArray.size_append],
      ba_append_right]; exact hp _ _ hk

theorem range_split (lo hi n : Nat) (h1 : lo ≤ hi) (h2 : hi ≤ n) :
    List.range n = List.range lo ++ List.range' lo (hi - lo) ++ List.range' hi (n - hi) := by
  have a := List.range'_append (s := 0) (m := lo) (n := hi - lo) (step := 1)
  have b := List.range'_append (s := 0) (m := hi) (n := n - hi) (step := 1)
  rw [show 0 + 1 * lo = lo by omega, show lo + (hi - lo) = hi by omega] at a
  rw [show 0 + 1 * hi = hi by omega, show hi + (n - hi) = n by omega] at b
  rw [List.range_eq_range', List.range_eq_range', ← b, ← a]

/-- Core's `List.filter_eq_nil_iff`, which carries `Classical.choice`. -/
theorem filter_nil_of (p : Nat → Bool) (l : List Nat) (h : ∀ a ∈ l, p a = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.filter_cons, h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]; rfl

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
theorem nblk_encode (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (x : ByteArray) :
    Column.nblk (Kernel.Coc.encodeAt lg w.toUSize x).1 = (x.size / w + 2 ^ lg - 1) / 2 ^ lg ∧
      Column.blk (Kernel.Coc.encodeAt lg w.toUSize x).1 = 2 ^ lg := by
  have hwt : w.toUSize.toNat = w := by
    rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize, h] <;> omega
  unfold Kernel.Coc.encodeAt
  simp only [hwt]
  generalize x.size / w = n
  generalize hbs : Array.map (fun b => Kernel.Coc.blockOf (2 ^ lg) w n b x) (Array.range _) = bs
  have hbsz : bs.size = (n + 2 ^ lg - 1) / 2 ^ lg := by rw [← hbs]; simp
  have hbget : ∀ b (h : b < bs.size), bs[b] = Kernel.Coc.blockOf (2 ^ lg) w n b x := by
    intro b h; subst hbs; simp only [Array.getElem_map, getElem_range]
  have hbw : ∀ b (h : b < bs.size), bs[b].2.2.2 ≤ 64 := by
    intro b h; rw [hbget]
    exact (blockOf_bounds (2 ^ lg) w n b hw x (b * 2 ^ lg) (Nat.le_refl _) (by have := Nat.two_pow_pos lg; omega)
      (mul_lt_of_lt_cdiv (Nat.two_pow_pos lg) (hbsz ▸ h))).2.2
  generalize hM : Kernel.Coc.foRMeta lg (Kernel.Coc.sumNul w) n _ = M
  have hMr := foRMeta_reads lg (Nat.lt_of_le_of_lt hlg.2 (by decide)) (Kernel.Coc.sumNul w) n
    (bs.map fun (mn, mx, s, wd) => (Kernel.Coc.unbias w mn, Kernel.Coc.unbias w mx, s, wd))
    (fun b h => by simp only [Array.getElem_map]; exact Nat.lt_of_le_of_lt (hbw b (by simpa using h)) (by decide))
  rw [hM] at hMr
  exact ⟨by rw [hMr.1, Array.size_map, hbsz], by rw [blk_of_lgAt _ (by rw [hMr.2.1]; exact hlg), hMr.2.1]⟩

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

/-- `Coc.alpBlob`, its sections named and its padding characterised. -/
theorem alpBlob_eq (f32 : Bool) (K w n : Nat) (x : ByteArray) (bs : Array (Nat × Array (Option UInt64)))
    (exc : Array Nat)
    (hexc : exc = (Array.range n).filter fun i => ((bs[i / K]!).2[i % K]!).isNone) :
    ∃ pad : ByteArray → ByteArray, (∀ b k, k < b.size → (pad b)[k]? = b[k]?) ∧
      (∀ b, (pad b).size = (b.size + 7) / 8 * 8) ∧
      Kernel.Coc.alpBlob f32 K w n x bs =
        pad (Column.pushBits (Column.pushBits ByteArray.empty exc.size.toUInt64 8) (if f32 then 1 else 0) 8)
        ++ pad (exc.foldl (init := ByteArray.empty) fun acc i => Column.pushBits acc (Column.bitsAt x (i * w) w) w)
        ++ pad ((Array.range (bs.size + 1)).foldl (init := ByteArray.empty) fun acc b =>
             Column.pushBits acc (exc.filter (· < b * K)).size.toUInt64 4)
        ++ pad (exc.foldl (init := ByteArray.empty) fun acc i => Column.pushBits acc (i % K).toUInt64 2)
        ++ pad (bs.foldl (init := ByteArray.empty) fun acc be => acc.push be.1.toUInt8) := by
  subst hexc
  refine ⟨_, fun b k h => ?_, fun b => ?_, rfl⟩
  · exact ba_append_left _ _ _ h
  · show (b ++ ⟨Array.replicate ((8 - b.size % 8) % 8) 0⟩).size = _
    simp only [ByteArray.size_append]
    show b.size + (Array.replicate ((8 - b.size % 8) % 8) (0 : UInt8)).size = _
    rw [Array.size_replicate]; omega

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
  have hsz : ∀ p : Nat → Bool, (exc.filter p).size ≤ exc.size := fun p => by
    have := List.length_filter_le p exc.toList
    rw [← Array.toList_filter, Array.length_toList, Array.length_toList] at this; exact this
  have hen : exc.size ≤ n := by
    rw [hexc, ← Array.length_toList, Array.toList_filter, toList_range]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have e0 : ByteArray.empty.size = 0 := rfl
  obtain ⟨pad, hpg, hps, hA⟩ := alpBlob_eq f32 K w n x bs exc hexc
  rw [hA]
  generalize hS0 : Column.pushBits (Column.pushBits ByteArray.empty exc.size.toUInt64 8) (if f32 then 1 else 0) 8 = S0
  generalize hS1 : exc.foldl (init := ByteArray.empty)
    (fun acc i => Column.pushBits acc (Column.bitsAt x (i * w) w) w) = S1
  generalize hS2 : (Array.range (bs.size + 1)).foldl (init := ByteArray.empty)
    (fun acc b => Column.pushBits acc (exc.filter (· < b * K)).size.toUInt64 4) = S2
  generalize hS3 : exc.foldl (init := ByteArray.empty)
    (fun acc i => Column.pushBits acc (i % K).toUInt64 2) = S3
  generalize hS4 : bs.foldl (init := ByteArray.empty) (fun acc be => acc.push be.1.toUInt8) = S4
  -- each section's size and contents
  have X8 : (Column.pushBits ByteArray.empty exc.size.toUInt64 8).size = 8 := by rw [Column.pushBits_size, e0]
  have z0 : S0.size = 16 := by rw [← hS0, Column.pushBits_size, X8]
  have W1 := foldl_pushBits (fun i => Column.bitsAt x (i * w) w) w hw8 exc.toList ByteArray.empty
  rw [Array.foldl_toList, hS1, e0] at W1
  have z1 : S1.size = exc.size * w := by rw [W1.1, Array.length_toList, Nat.zero_add, Nat.mul_comm]
  have r1 : ∀ k (h : k < exc.size), Column.bitsAt S1 (w * k) w = Column.bitsAt x (exc[k] * w) w := by
    intro k hk
    have := W1.2.2 k (by simpa using hk)
    simp only [Nat.zero_add, Array.getElem_toList] at this
    rw [this, Nat.mod_eq_of_lt (bitsAt_lt _ _ _ hw8), UInt64.ofNat_toNat]
  have hS2' : S2 = (List.range (bs.size + 1)).foldl (init := ByteArray.empty)
      (fun acc b => Column.pushBits acc (exc.filter (· < b * K)).size.toUInt64 4) := by
    rw [← hS2, ← Array.foldl_toList, toList_range]
  have W2 := foldl_pushBits (fun b => (exc.filter (· < b * K)).size.toUInt64) 4 (by decide)
    (List.range (bs.size + 1)) ByteArray.empty
  rw [← hS2', e0] at W2
  have z2 : S2.size = 4 * (bs.size + 1) := by rw [W2.1, List.length_range, Nat.zero_add]
  have r2 : ∀ b ≤ bs.size, (Column.bitsAt S2 (4 * b) 4).toNat = (exc.filter (· < b * K)).size := by
    intro b hb
    have := W2.2.2 b (by simp; omega)
    rw [Nat.zero_add, List.getElem_range] at this
    rw [this]
    have := hsz (· < b * K)
    simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]; omega
  have W3 := foldl_pushBits (fun i => (i % K).toUInt64) 2 (by decide) exc.toList ByteArray.empty
  rw [Array.foldl_toList, hS3, e0] at W3
  have z3 : S3.size = 2 * exc.size := by rw [W3.1, Array.length_toList, Nat.zero_add]
  have r3 : ∀ k (h : k < exc.size), (Column.bitsAt S3 (2 * k) 2).toNat = exc[k] % K := by
    intro k hk
    have := W3.2.2 k (by simpa using hk)
    rw [Nat.zero_add] at this
    rw [this]
    have : exc[k] % K < 65536 := Nat.lt_of_lt_of_le (Nat.mod_lt _ hK.1) hK.2
    simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq, Array.getElem_toList]; omega
  have W4 := foldl_push8 (fun be : Nat × Array (Option UInt64) => be.1.toUInt8) bs.toList ByteArray.empty
  rw [Array.foldl_toList, hS4, e0] at W4
  have z4 : S4.size = bs.size := by rw [W4.1, Array.length_toList, Nat.zero_add]
  have r4 : ∀ b (h : b < bs.size), S4[b]? = some bs[b].1.toUInt8 := by
    intro b hb
    have := W4.2.2 b (by simpa using hb)
    rw [Nat.zero_add] at this
    simpa using this
  obtain ⟨g0, g1, g2, g3, g4⟩ := blob_get pad hpg (fun b => by rw [hps]; omega) S0 S1 S2 S3 S4
  have p0 : (pad S0).size = 16 := by rw [hps, z0]
  have p1 : (pad S1).size = (exc.size * w + 7) / 8 * 8 := by rw [hps, z1]
  have p2 : (pad S2).size = (4 * (bs.size + 1) + 7) / 8 * 8 := by rw [hps, z2]
  have p3 : (pad S3).size = (2 * exc.size + 7) / 8 * 8 := by rw [hps, z3]
  generalize pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4 = A at g0 g1 g2 g3 g4 ⊢
  -- the header
  have hnx : Column.alpNexc A = exc.size := by
    unfold Column.alpNexc
    rw [bitsAt_shift A S0 0 0 8 (fun k hk => by rw [Nat.zero_add]; exact g0 k (by omega)), ← hS0,
      bitsAt_shift _ (Column.pushBits ByteArray.empty exc.size.toUInt64 8) 0 0 8
        (fun k hk => Column.pushBits_getElem?_lt _ _ _ _ (by rw [X8]; omega))]
    have := Column.bitsAt_pushBits ByteArray.empty exc.size.toUInt64 8 (by decide)
    rw [e0] at this; rw [this]
    simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]; omega
  have hf32 : Column.alpF32 A = f32 := by
    unfold Column.alpF32
    rw [bitsAt_shift A S0 8 8 8 (fun k hk => g0 _ (by omega)), ← hS0]
    have := Column.bitsAt_pushBits (Column.pushBits ByteArray.empty exc.size.toUInt64 8) (if f32 then 1 else 0) 8
      (by decide)
    rw [X8] at this; rw [this]; cases f32 <;> decide
  have hesz : Column.alpEsz A = w := by unfold Column.alpEsz; rw [hf32, hw]
  refine ⟨hf32, fun k hk => ?_, fun b hb => ?_, fun k hk => ?_, fun b hb => ?_, hnx⟩
  · unfold Column.alpExcRaw; rw [hesz, ← r1 k hk]
    have hk' : w * k + w ≤ S1.size := by
      rw [z1, Nat.mul_comm exc.size, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hk
    exact bitsAt_shift A S1 _ _ w (fun t ht => by
      rw [← g1 (w * k + t) (by omega)]; congr 1; rw [p0, Nat.mul_comm k w]; omega)
  · unfold Column.alpExcOff; rw [hM, hnx, hesz, ← r2 b hb]; simp only [Column.alpSects]
    congr 1
    exact bitsAt_shift A S2 _ _ 4 (fun t ht => by
      rw [← g2 (4 * b + t) (by omega)]; congr 1; rw [p0, p1]; omega)
  · unfold Column.alpExcPos; rw [hM, hnx, hesz, ← r3 k hk]; simp only [Column.alpSects]
    congr 1
    exact bitsAt_shift A S3 _ _ 2 (fun t ht => by
      rw [← g3 (2 * k + t) (by omega)]; congr 1; rw [p0, p1, p2]; omega)
  · unfold Column.alpExpAt; rw [hM, hnx, hesz]; simp only [Column.alpSects]
    have := g4 b (by omega)
    rw [r4 b hb] at this
    have e : ∀ m, m = (pad S0).size + (pad S1).size + (pad S2).size + (pad S3).size + b →
        A[m]? = some bs[b].1.toUInt8 := fun m hm => hm ▸ this
    rw [e _ (by rw [p0, p1, p2, p3]; omega)]
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
  rw [show Kernel.Coc.encodeAt lg 8 ds = Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds from rfl]
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
  have hM : Column.nblk (Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds).1 = bs.size := by
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
  have hfr : Column.foRBits (Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds).1 (Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds).2
      (Column.blockStarts (Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds).1) i = Column.bitsAt ds (i * 8) 8 := by
    apply UInt64.toNat_inj.1
    rw [← Nat.mod_eq_of_lt (UInt64.toNat_lt _),
      foRBits_encode_bits lg hlg 8 (by decide) (by decide) ds i (by rw [hdsz]; omega)]
  generalize Kernel.Coc.alpBlob f32 (2 ^ lg) w n x bs = A at hf32 hraw hoff hpos hexpA ⊢
  have hBMP := (nblk_encode lg hlg 8 (by decide) (by decide) ds).2
  generalize Kernel.Coc.encodeAt lg (8 : Nat).toUSize ds = MP at hfr hM hoff hpos hexpA hBMP ⊢
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

end QLean.Verify


namespace QLean.Verify

open QLean

/-- **The runtime test is the writer's form**: `Kernel.Coc.foRStd` is `FoRWF`. -/
theorem foRStd_iff {n : USize} {md pk : ByteArray} : Kernel.Coc.foRStd n md pk = true ↔ FoRWF n.toNat md pk := by
  simp only [Kernel.Coc.foRStd, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

end QLean.Verify
