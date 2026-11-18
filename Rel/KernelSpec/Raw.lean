import Rel.KernelSpec.Encoding
import Rel.Kernel.Value

/-! The part of `Rel.Verify.Raw` the Rel kernels reach; `Rel.Verify.Raw` imports it. -/


open Rel.Ext

namespace Rel.Verify

open Rel

theorem toInt_toInt64 (x : UInt64) :
    x.toInt64.toInt = if x.toNat < 2 ^ 63 then (x.toNat : Int) else x.toNat - 2 ^ 64 := by
  rw [Int64.toInt, show x.toInt64.toBitVec = x.toBitVec from rfl, BitVec.toInt_eq_toNat_cond]
  simp only [UInt64.toNat_toBitVec]
  split <;> split <;> omega

/-- The low `w` bytes of `v` as a two's-complement number: what a signed `w`-byte element denotes. -/
def sx (w : Nat) (v : UInt64) : Int :=
  if v.toNat % 2 ^ (8 * w) < 2 ^ (8 * w - 1) then ((v.toNat % 2 ^ (8 * w) : Nat) : Int)
  else ((v.toNat % 2 ^ (8 * w) : Nat) : Int) - ((2 ^ (8 * w) : Nat) : Int)

/-- `sx` reads only the low `8 * w` bits, which are what a `w`-byte write keeps. -/
theorem sx_mod {w : Nat} (h8 : w ≤ 8) (v : UInt64) : sx w (UInt64.ofNat (v.toNat % 2 ^ (8 * w))) = sx w v := by
  have : v.toNat % 2 ^ (8 * w) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by omega))
  simp only [sx, UInt64.toNat_ofNat', Nat.mod_eq_of_lt this, Nat.mod_mod]

theorem pairwise_map_range_iff {α : Type} (R : α → α → Prop) (f : Nat → α) (m : Nat) :
    ((List.range m).map f).Pairwise R ↔ ∀ i j, i < j → j < m → R (f i) (f j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.pairwise_append, ih]
    simp only [List.map_cons, List.map_nil, List.pairwise_singleton, List.mem_map, List.mem_range,
      List.mem_singleton, true_and]
    constructor
    · rintro ⟨h, hm⟩ i j hij hj
      by_cases hjm : j = m
      · subst hjm; exact hm _ ⟨i, hij, rfl⟩ _ rfl
      · exact h i j hij (by omega)
    · intro h
      exact ⟨fun i j hij hj => h i j hij (by omega), by
        rintro _ ⟨i, hi, rfl⟩ _ rfl; exact h i m hi (by omega)⟩

end Rel.Verify


namespace Rel.Verify

open Rel Rel.Column

theorem size_raw {t : QAtomicType} (n : USize) (e : Ext.Enc X) (hw : Enc.WF t n e) (hb : t ≠ .boolean)
    (hs : t ≠ .symbol) (hn : t ≠ .general) : (Enc.raw t n e).size = n.toNat := by
  cases e <;> cases t <;> simp_all [Enc.raw, Enc.WF, QAtomicType.width]

/-- `atomOfBits` at a type of width `w` reads only the low `8 * w` bits. -/
theorem atomOfBits_mod {t : QAtomicType} {w : Nat} (ht : t.width = some w) (hb : t ≠ .boolean)
    (v : UInt64) : atomOfBits t (UInt64.ofNat (v.toNat % 2 ^ (8 * w))) (QAtomicType.ne_general_of_width ht) = atomOfBits t v (QAtomicType.ne_general_of_width ht) := by
  have h8 : (UInt64.ofNat (v.toNat % 2 ^ 8)).toUInt8 = v.toUInt8 := UInt8.toNat_inj.1 (by simp)
  have h16 : (UInt64.ofNat (v.toNat % 2 ^ 16)).toUInt16 = v.toUInt16 := UInt16.toNat_inj.1 (by simp)
  have h32 : (UInt64.ofNat (v.toNat % 2 ^ 32)).toUInt32 = v.toUInt32 := UInt32.toNat_inj.1 (by simp)
  cases t <;> simp [QAtomicType.width] at ht <;> subst ht <;>
    first | exact absurd rfl hb | exact absurd rfl hg | simp only [atomOfBits, Nat.reduceMul, h8, h16, h32, ofNat_toNat_mod64]



/-- `Array.extract`'s loop: `bs`, then up to `i` elements of `a` from `j`. Core's `Array.getElem?_extract`
carries `Classical.choice`, so the read is taken from the loop here. -/
theorem extract_loop_getElem? {α : Type} (a bs : Array α) (i j k : Nat) :
    (Array.extract.loop a i j bs)[k]? = if k < bs.size then bs[k]? else
      if k - bs.size < i then if j + (k - bs.size) < a.size then a[j + (k - bs.size)]? else none else none := by
  induction i generalizing j bs with
  | zero =>
    rw [show Array.extract.loop a 0 j bs = bs by unfold Array.extract.loop; split <;> rfl]
    by_cases hk : k < bs.size
    · rw [if_pos hk]
    · rw [if_neg hk, if_neg (Nat.not_lt_zero _), Array.getElem?_eq_none (by omega)]
  | succ i ih =>
    unfold Array.extract.loop
    split
    · rename_i h
      show (Array.extract.loop a i (j + 1) (bs.push a[j]))[k]? = _
      rw [ih, Array.size_push, getElem?_push]
      repeat' split
      all_goals first | rfl | (exfalso; omega) | (congr 1; omega) | (simp only [show j + (k - bs.size) = j by omega, Array.getElem?_eq_getElem h])
    · rename_i h
      by_cases hk : k < bs.size
      · rw [if_pos hk]
      · rw [if_neg hk, Array.getElem?_eq_none (by omega)]
        by_cases hi : k - bs.size < i + 1
        · rw [if_pos hi, if_neg (by omega)]
        · rw [if_neg hi]


theorem extract_getElem? {α : Type} (a : Array α) (s e k : Nat) :
    (a.extract s e)[k]? = if k < min e a.size - s then a[s + k]? else none := by
  unfold Array.extract
  have h0 : ∀ c, (Array.emptyWithCapacity (α := α) c).size = 0 := fun _ => rfl
  rw [extract_loop_getElem?, h0, if_neg (Nat.not_lt_zero _), Nat.sub_zero, Nat.sub_eq]
  by_cases hk : k < min e a.size - s
  · rw [if_pos hk, if_pos hk, if_pos (by rw [Nat.lt_sub_iff_add_lt, Nat.lt_min] at hk; omega)]
  · rw [if_neg hk, if_neg hk]

/-- The bytes `[a, m)` of `s`, read at `o`, are `s` read at `a + o`, wherever the read ends by `m`. -/
theorem bitsAt_extract (s : ByteArray) {a m o w : Nat} (h : a + o + w ≤ m) :
    Column.bitsAt (s.extract a m) o w = Column.bitsAt s (a + o) w :=
  bitsAt_shift _ _ _ _ _ fun k hk => by
    rw [show (s.extract a m)[o + k]? = (s.extract a m).data[o + k]? from rfl, ByteArray.data_extract,
      extract_getElem?, show s[a + o + k]? = s.data[a + o + k]? from rfl]
    split
    · rw [Nat.add_assoc]
    · rw [Array.getElem?_eq_none (by have : s.data.size = s.size := rfl; omega)]

/-- `[a, m)` of `s`, `m` within `s`: `m - a` bytes, byte `k` being `s`'s byte `a + k`. -/
theorem extract_bytes (s : ByteArray) {a m : Nat} (hm : m ≤ s.size) :
    (s.extract a m).size = m - a ∧ ∀ k, a + k < m → (s.extract a m)[k]? = s[a + k]? := by
  have hs : s.data.size = s.size := rfl
  refine ⟨by rw [← ByteArray.size_data, ByteArray.data_extract, Array.size_extract]; omega, fun k hk => ?_⟩
  rw [show (s.extract a m)[k]? = (s.extract a m).data[k]? from rfl, ByteArray.data_extract, extract_getElem?,
    if_pos (by omega)]; rfl

/-- The prefix-sum fold `Enc.packedStarts` runs, from any `s` whose last entry is `v`: one entry per element, `s`
untouched, and entry `c` past `s`'s last being `v` plus `f` of the first `c` elements. -/
theorem foldl_starts (f : UInt8 → Nat) (l : List UInt8) (s : Array Nat) (v : Nat) (h0 : 0 < s.size)
    (hs : s[s.size - 1]? = some v) :
    (l.foldl (fun s w => s.push (s.back?.getD 0 + f w)) s).size = s.size + l.length ∧
    (∀ i < s.size, (l.foldl (fun s w => s.push (s.back?.getD 0 + f w)) s)[i]? = s[i]?) ∧
    ∀ c ≤ l.length, (l.foldl (fun s w => s.push (s.back?.getD 0 + f w)) s)[s.size - 1 + c]? =
      some (v + ((l.map f).take c).sum) := by
  induction l generalizing s v with
  | nil => exact ⟨rfl, fun _ _ => rfl, fun c hc => by simp at hc; subst hc; simpa using hs⟩
  | cons a l ih =>
    have hb : s.back?.getD 0 = v := by simp only [Array.back?, hs, Option.getD_some]
    obtain ⟨hz, hp, hg⟩ := ih (s.push (v + f a)) (v + f a) (by simp) (by simp)
    simp only [List.foldl_cons, hb]
    refine ⟨by rw [hz, Array.size_push, List.length_cons]; omega,
      fun i hi => by rw [hp i (by simp; omega), Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi],
      fun c hc => ?_⟩
    cases c with
    | zero =>
      rw [Nat.add_zero, hp _ (by simp; omega), Array.getElem?_push_lt (by omega), ← Array.getElem?_eq_getElem, hs]
      simp
    | succ c =>
      have := hg c (by simp at hc; omega)
      rw [Array.size_push, Nat.add_sub_cancel] at this
      rw [show s.size - 1 + (c + 1) = s.size + c by omega, this]
      simp [Nat.add_assoc]

/-- **The packed round trip.** `Coc.packedOf` at any block size `2 ^ lg` the layout admits (`3 ≤ lg ≤ 16`) and any
element width `w ≤ 8`, at a count `n` up to `x`'s that keeps its block count, passes `packedErr` and unpacks to `x`'s
elements as the encoder measured them, `unbias ∘ keyAt`: sign-extended to 64 bits, a byte zero-extended. -/
theorem unpack_packedOf (lg : Nat) (hlg : 3 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw : w ≤ 8) (wU : USize)
    (hwU : wU.toNat = w) (x : ByteArray) (n : Nat) (hn : n ≤ x.size / w)
    (hnb : (n + 2 ^ lg - 1) / 2 ^ lg = (x.size / w + 2 ^ lg - 1) / 2 ^ lg)
    {l : UInt8} {B W P : ByteArray} (h : Kernel.Coc.packedOf (X := X) lg wU x = .packed l B W P) :
    Enc.packedErr l B W P n = none ∧
      Enc.unpack l B W P n = .ok ((Array.range n).map fun i => Kernel.Coc.unbias w (Kernel.Coc.keyAt w x i)) := by
  have hBp : 0 < 2 ^ lg := Nat.two_pow_pos _
  have h8 : 8 ∣ 2 ^ lg :=
    ⟨2 ^ (lg - 3), by rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add, Nat.add_sub_cancel' hlg.1]⟩
  have hl8 : lg.toUInt8.toNat = lg := by simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']; omega
  unfold Kernel.Coc.packedOf Kernel.Coc.encodeAt at h
  simp only [hwU] at h
  generalize hN : x.size / w = N at *
  generalize hbs : Array.map (fun b => Kernel.Coc.blockOf (2 ^ lg) w N b x) (Array.range _) = bs at h
  have hbsz : bs.size = (N + 2 ^ lg - 1) / 2 ^ lg := by rw [← hbs]; simp
  have hbget : ∀ b (h : b < bs.size), bs[b] = Kernel.Coc.blockOf (2 ^ lg) w N b x := by
    intro b h; subst hbs; simp only [Array.getElem_map, getElem_range]
  have hbw : ∀ b (h : b < bs.size), bs[b].2.2.2 ≤ 64 := by
    intro b h; rw [hbget]
    exact (blockOf_bounds (2 ^ lg) w N b hw x (b * 2 ^ lg) (Nat.le_refl _) (by omega)
      (mul_lt_of_lt_cdiv hBp (hbsz ▸ h))).2.2
  generalize hM : Kernel.Coc.foRMeta lg (Kernel.Coc.sumNul w) N _ = M at h
  have hMr := foRMeta_reads lg (Nat.lt_of_le_of_lt hlg.2 (by decide)) (Kernel.Coc.sumNul w) N
    (bs.map fun (mn, mx, s, wd) => (Kernel.Coc.unbias w mn, Kernel.Coc.unbias w mx, s, wd))
    (fun b h => by simp only [Array.getElem_map]; exact Nat.lt_of_le_of_lt (hbw b (by simpa using h)) (by decide))
  have hMs := foRMeta_size lg (Kernel.Coc.sumNul w) N
    (bs.map fun (mn, mx, s, wd) => (Kernel.Coc.unbias w mn, Kernel.Coc.unbias w mx, s, wd))
  rw [hM] at hMr hMs
  obtain ⟨hnbM, -, hMb⟩ := hMr
  simp only [Array.size_map] at hnbM hMb hMs
  rw [hnbM] at h
  injection h with hl hB hW hP
  subst hl hB hW
  rw [← Array.foldl_toList] at hP
  -- the three sections, read through the metadata they were cut from
  obtain ⟨hBs, hBg⟩ := extract_bytes M (a := 0) (m := 8 * bs.size) (by omega)
  obtain ⟨hWs, hWg⟩ := extract_bytes M (a := 32 * bs.size + 24) (m := 33 * bs.size + 24) (by omega)
  generalize hWd : M.extract (32 * bs.size + 24) (33 * bs.size + 24) = W at hWs hWg ⊢
  have hWb : ∀ c (hc : c < bs.size), (W[c]?.getD 0).toNat = bs[c].2.2.2 := fun c hc => by
    rw [hWg c (by omega)]
    simpa [Column.widthAt, hnbM] using (hMb c (by simpa using hc)).2
  have hbase : ∀ c (hc : c < bs.size),
      Column.bitsAt (M.extract 0 (8 * bs.size)) (8 * c) 8 = Kernel.Coc.unbias w bs[c].1 := fun c hc => by
    rw [bitsAt_extract M (by omega), Nat.zero_add, Nat.mul_comm, ← Column.baseAt]
    exact (hMb c (by simpa using hc)).1.trans (by simp)
  have hWl : W.data.size = bs.size := by rw [ByteArray.size_data, hWs]; omega
  have hWc : ∀ c (hc : c < W.data.size), (W.data[c]).toNat = bs[c].2.2.2 := fun c hc => by
    have := hWb c (hWl ▸ hc)
    rwa [show W[c]? = W.data[c]? from rfl, Array.getElem?_eq_getElem hc, Option.getD_some] at this
  -- block `c`'s residuals start at `off c`, the sum of the block sizes before it
  let off : Nat → Nat := fun c => ((W.data.toList.map fun w => 2 ^ lg * w.toNat / 8).take c).sum
  have hoff : ∀ c (hc : c < bs.size), off (c + 1) = off c + 2 ^ lg * bs[c].2.2.2 / 8 := fun c hc => by
    simp only [off]
    rw [List.take_add_one, List.sum_append_nat, List.getElem?_map, List.getElem?_eq_getElem (by simp; omega)]
    simp [hWc]
  let Q : Nat → Nat × Nat × UInt64 × Nat → ByteArray := fun m e => Kernel.Coc.packRes (2 ^ lg) e.2.2.2 fun j =>
    (if m * 2 ^ lg + j < N then Kernel.Coc.keyAt w x (m * 2 ^ lg + j) - e.1 else 0).toUInt64
  have key : ∀ f : ByteArray × Nat → Nat × Nat × UInt64 × Nat → ByteArray × Nat,
      (∀ a m e, f (a, m) e = (a ++ Q m e, m + 1)) → (List.foldl f (ByteArray.empty, 0) bs.toList).1 = P →
      P.size = off bs.size ∧ ∀ c (hc : c < bs.size), ∀ k < 2 ^ lg * bs[c].2.2.2 / 8, P[off c + k]? = (Q c bs[c])[k]? := by
    intro f hf hP; subst hP
    obtain ⟨a, b⟩ := pack_fold0 f Q hf off bs.toList (by simp [off])
      (fun i h => by rw [packRes_size]; simpa using hoff i (by simpa using h))
    exact ⟨a.trans (by simp), fun c hc k hk => (b c (by simpa using hc) k (by rw [packRes_size]; simpa using hk)).trans (by simp)⟩
  obtain ⟨hPs, hPg⟩ := key _ (by intro a m ⟨mn, mx, s, wd⟩; rfl) hP
  -- the starts `packedStarts` recomputes are those offsets
  obtain ⟨hSs, -, hSg⟩ := foldl_starts (fun w => 2 ^ lg * w.toNat / 8) W.data.toList #[0] 0 (by decide) (by simp)
  have hS : ∀ c ≤ bs.size, (Enc.packedStarts lg W)[c]? = some (off c) := fun c hc => by
    have := hSg c (by simp; omega)
    simpa [Enc.packedStarts, off] using this
  have hback : (Enc.packedStarts lg W).back?.getD 0 = off bs.size := by
    have hsz : (Enc.packedStarts lg W).size = bs.size + 1 := by
      simp only [Enc.packedStarts, ← Array.foldl_toList, hSs]; simp; omega
    simp only [Array.back?, hsz, Nat.add_sub_cancel, hS _ (Nat.le_refl _), Option.getD_some]
  have hne : W.data.toList.findIdx? (64 < ·.toNat) = none := List.findIdx?_eq_none_iff.2 fun y hy => by
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hy
    simp only [Array.getElem_toList, hWc, decide_eq_false_iff_not, Nat.not_lt]
    exact hbw c (by simp at hc; omega)
  have hE : Enc.packedErr lg.toUInt8 (M.extract 0 (8 * bs.size)) W P n = none := by
    unfold Enc.packedErr
    simp only [hl8, hne, hback, hPs, hBs, hWs]
    rw [if_neg, if_neg, if_neg, if_neg] <;> omega
  refine ⟨hE, ?_⟩
  unfold Enc.unpack
  rw [hE]
  simp only [hl8]
  congr 1
  apply Array.ext (by simp)
  intro i h1 _
  simp only [Array.getElem_map, Array.getElem_range]
  have hi : i < N := by simp at h1; omega
  have hblk : i / 2 ^ lg < bs.size := by rw [hbsz]; exact lt_cdiv hBp hi
  obtain ⟨hmn, hres, hwd⟩ := blockOf_bounds (2 ^ lg) w N (i / 2 ^ lg) hw x i
    (Nat.div_mul_le_self _ _) (by have := Nat.mod_add_div' i (2 ^ lg); have := Nat.mod_lt i hBp; omega) hi
  rw [← hbget _ hblk] at hmn hres hwd
  rw [hS _ (Nat.le_of_lt hblk), Option.getD_some, hWb _ hblk, hbase _ hblk,
    resAt_packRes (2 ^ lg) _ h8 hwd (fun j => (if i / 2 ^ lg * 2 ^ lg + j < N then
      Kernel.Coc.keyAt w x (i / 2 ^ lg * 2 ^ lg + j) - bs[i / 2 ^ lg].1 else 0).toUInt64) P _
      (fun k hk => hPg _ hblk k hk) _ (Nat.mod_lt _ hBp)]
  rw [Nat.div_add_mod', if_pos hi, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (show _ < 2 ^ 64 by have := keyAt_lt w hw x i; omega), Nat.mod_eq_of_lt hres,
    ← Nat.toUInt64_eq, unbias_add _ _ _ hmn]

/-- `Enc.raw` cannot tell `Coc.packedOf` from the dense payload it packs, read at that payload's width. -/
theorem raw_packedOf (t : QAtomicType) (w : Nat) (ht : t.width = some w) (hb : t ≠ .boolean)
    (lg : Nat) (hlg : 3 ≤ lg ∧ lg ≤ 16) (wU : USize) (hwU : wU.toNat = w) (x : ByteArray) (n : USize)
    (hn : n.toNat ≤ x.size / w) (hnb : (n.toNat + 2 ^ lg - 1) / 2 ^ lg = (x.size / w + 2 ^ lg - 1) / 2 ^ lg) :
    Enc.raw (X := X) t n (Kernel.Coc.packedOf lg wU x) = Enc.raw (X := X) t n (.bytes x) := by
  have hw : 0 < w ∧ w ≤ 8 := by cases t <;> simp [QAtomicType.width] at ht ⊢ <;> omega
  obtain ⟨l, B, W, P, h⟩ : ∃ l B W P, Kernel.Coc.packedOf (X := X) lg wU x = .packed l B W P := ⟨_, _, _, _, rfl⟩
  have hu := (unpack_packedOf lg hlg w hw.2 wU hwU x n.toNat hn hnb h).2
  have he : ∀ i, UInt64.ofNat ((Kernel.Coc.unbias w (Kernel.Coc.keyAt w x i)).toNat % 2 ^ (8 * w)) =
      Column.bitsAt x (i * w) w := fun i => by
    rw [unbias_keyAt w hw.1 hw.2, UInt64.ofNat_toNat]
  rw [h, raw_bytes t w ht hb]
  cases t <;> simp only [QAtomicType.width, Option.some.injEq, reduceCtorEq] at ht <;> first
    | exact absurd rfl hb
    | (subst ht; simp only [Enc.raw, hu, QAtomicType.width, Array.map_map, Function.comp_def, reduceCtorEq,
        if_false, he])
end Rel.Verify
