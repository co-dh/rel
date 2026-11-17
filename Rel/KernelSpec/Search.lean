import Rel.KernelSpec.Encoding
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.KernelSpec.Raw

/-! The part of `Rel.Verify.Search` the Rel kernels reach; `Rel.Verify.Search` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel

/-- `binStep`'s invariant: everything below `lo` passes the test, nothing from `hi` up to `n` does,
and the fuel covers the interval. The answer then sits between them with the same two facts. -/
theorem binStep_inv (w : Nat) (float signed right : Bool) (hay : ByteArray) (k : UInt64) (n : Nat)
    (hmono : ∀ i j, i ≤ j → j < n →
      (if right then ordKey w float signed (Column.bitsAt hay (j * w) w) < k
        else ordKey w float signed (Column.bitsAt hay (j * w) w) ≤ k) →
      (if right then ordKey w float signed (Column.bitsAt hay (i * w) w) < k
        else ordKey w float signed (Column.bitsAt hay (i * w) w) ≤ k)) :
    ∀ fuel lo hi, hi - lo ≤ fuel → lo ≤ hi → hi ≤ n →
      (∀ j, j < lo → (if right then ordKey w float signed (Column.bitsAt hay (j * w) w) < k
        else ordKey w float signed (Column.bitsAt hay (j * w) w) ≤ k)) →
      (∀ j, hi ≤ j → j < n → ¬ (if right then ordKey w float signed (Column.bitsAt hay (j * w) w) < k
        else ordKey w float signed (Column.bitsAt hay (j * w) w) ≤ k)) →
      binStep w float signed right hay ByteArray.empty k fuel lo hi ≤ n ∧
      (∀ j, j < binStep w float signed right hay ByteArray.empty k fuel lo hi →
        (if right then ordKey w float signed (Column.bitsAt hay (j * w) w) < k
          else ordKey w float signed (Column.bitsAt hay (j * w) w) ≤ k)) ∧
      (∀ j, binStep w float signed right hay ByteArray.empty k fuel lo hi ≤ j → j < n →
        ¬ (if right then ordKey w float signed (Column.bitsAt hay (j * w) w) < k
          else ordKey w float signed (Column.bitsAt hay (j * w) w) ≤ k)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi hf hlh hhn hlo hhi
    have he : hi = lo := by omega
    subst he
    exact ⟨hhn, hlo, hhi⟩
  | succ fuel ih =>
    intro lo hi hf hlh hhn hlo hhi
    have he : ByteArray.empty.isEmpty = true := rfl
    simp only [binStep, he, ↓reduceIte]
    split
    · have he : hi = lo := by omega
      subst he
      exact ⟨hhn, hlo, hhi⟩
    · by_cases ht : (if right = true
          then ordKey w float signed (Column.bitsAt hay ((lo + (hi - lo) / 2) * w) w) < k
          else ordKey w float signed (Column.bitsAt hay ((lo + (hi - lo) / 2) * w) w) ≤ k)
      · rw [if_pos ht]
        exact ih _ hi (by omega) (by omega) hhn
          (fun j hj => if hj' : j < lo then hlo j hj'
            else hmono j (lo + (hi - lo) / 2) (by omega) (by omega) ht) hhi
      · rw [if_neg ht]
        exact ih lo _ (by omega) (by omega) (by omega) hlo
          (fun j hj hjn hT => ht (hmono _ j hj hjn hT))

/-- **`binStep` at `binBytes`' arguments answers the partition point**: over `n` elements whose
`ordKey`s ascend, the answer `p` is at most `n`, every element below `p` passes the test, and none
from `p` on does. The fuel `n + 1` that `binBytes` passes is enough, since `n - 0 ≤ n + 1`. -/
theorem binStep_spec (w : Nat) (float signed right : Bool) (hay : ByteArray) (k : UInt64) (n : Nat)
    (hsort : ∀ i j, i ≤ j → j < n →
      ordKey w float signed (Column.bitsAt hay (i * w) w)
        ≤ ordKey w float signed (Column.bitsAt hay (j * w) w)) :
    binStep w float signed right hay ByteArray.empty k (n + 1) 0 n ≤ n ∧
    (∀ j, j < binStep w float signed right hay ByteArray.empty k (n + 1) 0 n →
      (if right then ordKey w float signed (Column.bitsAt hay (j * w) w) < k
        else ordKey w float signed (Column.bitsAt hay (j * w) w) ≤ k)) ∧
    (∀ j, binStep w float signed right hay ByteArray.empty k (n + 1) 0 n ≤ j → j < n →
      ¬ (if right then ordKey w float signed (Column.bitsAt hay (j * w) w) < k
        else ordKey w float signed (Column.bitsAt hay (j * w) w) ≤ k)) := by
  refine binStep_inv w float signed right hay k n ?_ (n + 1) 0 n (by omega) (by omega) (by omega)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h1 h2 => absurd h2 (by omega))
  intro i j hij hjn hT
  cases right with
  | true => simp only [↓reduceIte] at hT ⊢; exact UInt64.lt_of_le_of_lt (hsort i j hij hjn) hT
  | false => simp only [Bool.false_eq_true, ↓reduceIte] at hT ⊢; exact UInt64.le_trans (hsort i j hij hjn) hT

/-- Element `j` of `binBytes`' answer is `binStep`'s at key `j`: `p` for `binr`, `p - 1` for `bin`. -/
theorem bitsAt_binBytes (w : USize) (float signed right : Bool) (hay keys : ByteArray) (j : Nat)
    (hj : j < keys.size / w.toNat) :
    Column.bitsAt (binBytes w float signed right hay keys) (8 * j) 8 =
      (if right then
          (binStep w.toNat float signed right hay ByteArray.empty
            (ordKey w.toNat float signed (Column.bitsAt keys (j * w.toNat) w.toNat))
            (hay.size / w.toNat + 1) 0 (hay.size / w.toNat) : Int)
        else (binStep w.toNat float signed right hay ByteArray.empty
            (ordKey w.toNat float signed (Column.bitsAt keys (j * w.toNat) w.toNat))
            (hay.size / w.toNat + 1) 0 (hay.size / w.toNat) : Int) - 1).toInt64.toUInt64 := by
  have h := (foldl_pushBits (fun j => (if right then
          (binStep w.toNat float signed right hay ByteArray.empty
            (ordKey w.toNat float signed (Column.bitsAt keys (j * w.toNat) w.toNat))
            (hay.size / w.toNat + 1) 0 (hay.size / w.toNat) : Int)
        else (binStep w.toNat float signed right hay ByteArray.empty
            (ordKey w.toNat float signed (Column.bitsAt keys (j * w.toNat) w.toNat))
            (hay.size / w.toNat + 1) 0 (hay.size / w.toNat) : Int) - 1).toInt64.toUInt64)
    8 (by decide) (List.range (keys.size / w.toNat)) ByteArray.empty).2.2 j (by simpa using hj)
  rw [show 8 * 8 = 64 from rfl, ofNat_toNat_mod64] at h
  simpa [binBytes] using h

/-- `ordKey`'s mask at `w` bytes keeps the low `8 * w` bits. -/
theorem toNat_and_mask {w : Nat} (h1 : 1 ≤ w) (h8 : w ≤ 8) (v : UInt64) :
    (v &&& (if w == 8 then (0xffffffffffffffff : UInt64) else (2 ^ (8 * w) - 1).toUInt64)).toNat =
      v.toNat % 2 ^ (8 * w) := by
  -- the mask's 64 low bits by `decide`: `Nat.testBit_two_pow_sub_one` brings `Classical.choice`
  have hk : ∀ i, i < 64 → (2 ^ (8 * w) - 1).testBit i = decide (i < 8 * w) := by
    have hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8 := by omega
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hp : 2 ^ (8 * w) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpos := Nat.two_pow_pos (8 * w)
  have hm : (if w == 8 then (0xffffffffffffffff : UInt64) else (2 ^ (8 * w) - 1).toUInt64).toNat =
      2 ^ (8 * w) - 1 := by
    split
    · rename_i h; rw [beq_iff_eq.1 h]; rfl
    · rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hand : v.toNat &&& (2 ^ (8 * w) - 1) = v.toNat % 2 ^ (8 * w) := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_mod_two_pow]
    by_cases hi : i < 64
    · rw [hk i hi, Bool.and_comm]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le v.toNat_lt (Nat.pow_le_pow_right (by omega) (by omega))),
        Bool.false_and, Bool.and_false]
  rw [UInt64.toNat_and, hm, hand]

theorem ordKey_signed {w : Nat} (h1 : 1 ≤ w) (h8 : w ≤ 8) (v : UInt64) :
    ((ordKey w false true v).toNat : Int) = sx w v + ((2 ^ (8 * w - 1) : Nat) : Int) := by
  have hp : 2 ^ (8 * w) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpos := Nat.two_pow_pos (8 * w)
  have he : 2 ^ (8 * w) = 2 * 2 ^ (8 * w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have ht : (2 ^ (8 * w - 1) : Nat).toUInt64.toNat = 2 ^ (8 * w - 1) := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  simp only [ordKey, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_xor, toNat_and_mask h1 h8, ht]
  have hlt := Nat.mod_lt v.toNat hpos
  rw [xor_top (8 * w - 1) (v.toNat % 2 ^ (8 * w)) (by rw [show 8 * w - 1 + 1 = 8 * w by omega]; exact hlt)]
  unfold sx; split <;> omega

/-- The partition point of a sorted signed `w`-byte haystack, as the 8-byte answer's single element
read back as an index: below `2^63` elements the `Int64` the kernel writes holds it exactly. -/
theorem binBytes_signed {w : Nat} (h1 : 1 ≤ w) (h8 : w ≤ 8) (wU : USize) (hwU : wU.toNat = w)
    (right : Bool) (hay : ByteArray) (k : UInt64) (hn : hay.size / w < 2 ^ 63)
    (hsort : ∀ i j, i ≤ j → j < hay.size / w →
      sx w (Column.bitsAt hay (i * w) w) ≤ sx w (Column.bitsAt hay (j * w) w)) :
    ∃ r, r ≤ hay.size / w ∧
      (Column.bitsAt (binBytes wU false true right hay (Column.pushBits ByteArray.empty k w)) 0 8).toInt64.toInt
        = (if right then (r : Int) else (r : Int) - 1) ∧
      (∀ j, j < r → if right then sx w (Column.bitsAt hay (j * w) w) < sx w k
        else sx w (Column.bitsAt hay (j * w) w) ≤ sx w k) ∧
      (r < hay.size / w → if right then sx w k ≤ sx w (Column.bitsAt hay (r * w) w)
        else sx w k < sx w (Column.bitsAt hay (r * w) w)) := by
  have hks : (Column.pushBits ByteArray.empty k w).size / w = 1 := by
    rw [Column.pushBits_size, show ByteArray.empty.size = 0 from rfl, Nat.zero_add]; exact Nat.div_self (by omega)
  have hout := bitsAt_binBytes wU false true right hay (Column.pushBits ByteArray.empty k w) 0
    (by rw [hwU, hks]; omega)
  have hpb := Column.bitsAt_pushBits ByteArray.empty k w h8
  rw [show ByteArray.empty.size = 0 from rfl] at hpb
  rw [hwU, Nat.zero_mul, Nat.mul_zero, hpb] at hout
  have ok := ordKey_signed h1 h8
  have hk := ok (UInt64.ofNat (k.toNat % 2 ^ (8 * w)))
  rw [sx_mod h8] at hk
  have hs := binStep_spec w false true right hay (ordKey w false true (UInt64.ofNat (k.toNat % 2 ^ (8 * w))))
    (hay.size / w) (fun i j hij hjn => UInt64.le_iff_toNat_le.2 (by
      have := hsort i j hij hjn; have := ok (Column.bitsAt hay (i * w) w); have := ok (Column.bitsAt hay (j * w) w)
      omega))
  refine ⟨_, hs.1, ?_, fun j hj => ?_, fun hr => ?_⟩
  · have := hs.1
    rw [hout, Int64.toInt64_toUInt64]
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact Int64.toInt_ofInt_of_le (by omega) (by omega)
  · have hj' := hs.2.1 j hj
    have := ok (Column.bitsAt hay (j * w) w)
    cases right
    · simp only [Bool.false_eq_true, ↓reduceIte, UInt64.le_iff_toNat_le] at hj' ⊢; omega
    · simp only [↓reduceIte, UInt64.lt_iff_toNat_lt] at hj' ⊢; omega
  · have hr' := hs.2.2 _ (Nat.le_refl _) hr
    have := ok (Column.bitsAt hay (binStep w false true right hay ByteArray.empty
      (ordKey w false true (UInt64.ofNat (k.toNat % 2 ^ (8 * w)))) (hay.size / w + 1) 0 (hay.size / w) * w) w)
    cases right
    · simp only [Bool.false_eq_true, ↓reduceIte, UInt64.le_iff_toNat_le] at hr' ⊢; omega
    · simp only [↓reduceIte, UInt64.lt_iff_toNat_lt] at hr' ⊢; omega

/-- `runStarts`' answer read back as `Int64`s: `m` run starts and then the element count, strictly
ascending, the first `0` when there is an element, each below the count and a run start, and every run
start among them. Below `2^63` elements the `Int64` the kernel writes holds an index exactly. -/
theorem runStarts_spec (w : USize) (float : Bool) (hay : ByteArray) (h63 : hay.size / w.toNat < 2 ^ 63) :
    ∃ m, (runStarts w float hay).size = 8 * (m + 1) ∧
      (Column.bitsAt (runStarts w float hay) (8 * m) 8).toInt64.toInt = ((hay.size / w.toNat : Nat) : Int) ∧
      (∀ i j, i < j → j ≤ m → (Column.bitsAt (runStarts w float hay) (8 * i) 8).toInt64.toInt
        < (Column.bitsAt (runStarts w float hay) (8 * j) 8).toInt64.toInt) ∧
      (0 < hay.size / w.toNat → 0 < m ∧ (Column.bitsAt (runStarts w float hay) 0 8).toInt64.toInt = 0) ∧
      (∀ j, j < m → ∃ r : Nat, (Column.bitsAt (runStarts w float hay) (8 * j) 8).toInt64.toInt = (r : Int) ∧
        r < hay.size / w.toNat ∧ (r = 0 ∨ key w.toNat float hay r ≠ key w.toNat float hay (r - 1))) ∧
      (∀ r, r < hay.size / w.toNat → (r = 0 ∨ key w.toNat float hay r ≠ key w.toNat float hay (r - 1)) →
        ∃ j, j < m ∧ (Column.bitsAt (runStarts w float hay) (8 * j) 8).toInt64.toInt = (r : Int)) := by
  let p : Nat → Bool := fun i => i == 0 || key w.toNat float hay i != key w.toNat float hay (i - 1)
  have hp : ∀ r, p r = true ↔ (r = 0 ∨ key w.toNat float hay r ≠ key w.toNat float hay (r - 1)) := fun r => by
    simp only [p, Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  have hf : ∀ (l : List Nat) (acc : ByteArray),
      l.foldl (fun acc i => if p i then Column.pushBits acc i.toUInt64 8 else acc) acc =
        (l.filter p).foldl (fun acc i => Column.pushBits acc i.toUInt64 8) acc := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro acc; simp only [List.foldl_cons, List.filter_cons]
      cases h : p a <;> simp only [ite_true, Bool.false_eq_true, ite_false, List.foldl_cons, ih]
  generalize hn : hay.size / w.toNat = n at h63 ⊢
  have hout : runStarts w float hay =
      ((List.range n).filter p ++ [n]).foldl (fun acc i => Column.pushBits acc i.toUInt64 8) ByteArray.empty := by
    subst hn; rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hf]; rfl
  have hR : (List.range n).Pairwise (· < ·) := by
    simpa using (pairwise_map_range_iff (· < ·) id n).2 (fun i j h _ => h)
  have hF : ((List.range n).filter p).Pairwise (· < ·) := hR.filter p
  have hL : ((List.range n).filter p ++ [n]).Pairwise (· < ·) := List.pairwise_append.2 ⟨hF, by simp,
    fun a ha b hb => by
      rw [List.mem_singleton] at hb; rw [List.mem_filter, List.mem_range] at ha; rw [hb]; exact ha.1⟩
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun i : Nat => i.toUInt64) 8 (by decide)
    ((List.range n).filter p ++ [n]) ByteArray.empty
  rw [← hout, show ByteArray.empty.size = 0 from rfl] at hs hg
  have hv : ∀ j (h : j < ((List.range n).filter p ++ [n]).length),
      (Column.bitsAt (runStarts w float hay) (8 * j) 8).toInt64.toInt = (((List.range n).filter p ++ [n])[j] : Int) := by
    intro j h
    have hle : ((List.range n).filter p ++ [n])[j] ≤ n := by
      have hm := List.getElem_mem h
      rw [List.mem_append, List.mem_filter, List.mem_range, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Nat.le_of_lt hm.1
      · exact Nat.le_of_eq hm
    have ht : (((List.range n).filter p ++ [n])[j]).toUInt64.toNat = ((List.range n).filter p ++ [n])[j] := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have := hg j h
    rw [Nat.zero_add] at this
    rw [this, show 8 * 8 = 64 from rfl, ofNat_toNat_mod64, toInt_toInt64, ht, if_pos (by omega)]
  have hlen : ((List.range n).filter p ++ [n]).length = ((List.range n).filter p).length + 1 := by simp
  have hleft : ∀ j (h : j < ((List.range n).filter p).length),
      ((List.range n).filter p ++ [n])[j]'(by omega) = ((List.range n).filter p)[j] :=
    fun j h => List.getElem_append_left h
  refine ⟨((List.range n).filter p).length, by rw [hs, hlen]; omega, ?_, fun i j hij hj => ?_, fun h0 => ?_,
    fun j hj => ?_, fun r hr hr' => ?_⟩
  · rw [hv _ (by omega)]; simp
  · rw [hv i (by omega), hv j (by omega)]
    exact Int.ofNat_lt.2 (List.pairwise_iff_getElem.1 hL i j (by omega) (by omega) hij)
  · have h0m : 0 ∈ (List.range n).filter p := List.mem_filter.2 ⟨List.mem_range.2 h0, rfl⟩
    have hpos := List.length_pos_of_mem h0m
    obtain ⟨k, hk, hk0⟩ := List.getElem_of_mem h0m
    refine ⟨hpos, ?_⟩
    have := hv 0 (by omega)
    rw [Nat.mul_zero] at this
    rw [this, hleft 0 hpos]
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rw [hk0]; rfl
    · have := List.pairwise_iff_getElem.1 hF 0 k hpos hk hk'; omega
  · refine ⟨_, hv j (by omega), ?_⟩
    rw [hleft j hj]
    have hm := List.mem_filter.1 (List.getElem_mem hj)
    exact ⟨List.mem_range.1 hm.1, (hp _).1 hm.2⟩
  · obtain ⟨j, hj, hjr⟩ := List.getElem_of_mem (List.mem_filter.2 ⟨List.mem_range.2 hr, (hp r).2 hr'⟩)
    exact ⟨j, hj, by rw [hv j (by omega), hleft j hj, hjr]⟩

/-- A bitmap's run starts are the dense pass's over the same `n` booleans widened to one byte each,
so `runStarts_spec` describes `runStartsBits` too: the layout moves where a bit is read, not the runs. -/
theorem runStartsBits_dense (n : USize) (bits : ByteArray) :
    runStartsBits n bits = runStarts 1 false
      ⟨((List.range n.toNat).map fun i => if Column.bitAt bits i then 1 else 0).toArray⟩ := by
  -- a `List` and not `Array.range`: `Array.getElem_range` brings `Classical.choice`
  generalize hd : (⟨((List.range n.toNat).map fun i => if Column.bitAt bits i then 1 else 0).toArray⟩
    : ByteArray) = d
  have hs : d.size / (1 : USize).toNat = n.toNat := by
    subst hd; simp only [ByteArray.size, List.size_toArray, List.length_map, List.length_range]
    rw [USize.toNat_one, Nat.div_one]
  have hget : ∀ (l : List UInt8) i (h : i < l.length), (⟨l.toArray⟩ : ByteArray)[i]? = some l[i] :=
    fun l i h => by show (if h : i < l.length then some _ else none) = _; rw [dif_pos h]; rfl
  have hk : ∀ i, i < n.toNat → key (1 : USize).toNat false d i = if Column.bitAt bits i then 1 else 0 := by
    intro i hi; subst hd
    have he := hget ((List.range n.toNat).map fun i => if Column.bitAt bits i then 1 else 0) i
      (by simpa only [List.length_map, List.length_range] using hi)
    rw [List.getElem_map, List.getElem_range] at he
    simp [key, normalise, Column.bitsAt_succ, Column.bitsAt, he]
    cases Column.bitAt bits i <;> rfl
  have hb : ∀ i, i < n.toNat → (key (1 : USize).toNat false d i != key (1 : USize).toNat false d (i - 1)) =
      (Column.bitAt bits i != Column.bitAt bits (i - 1)) := fun i h => by
    rw [hk i h, hk (i - 1) (by omega)]
    cases Column.bitAt bits i <;> cases Column.bitAt bits (i - 1) <;> decide
  have hu : n.toNat.toUInt64 = n.toUInt64 := by
    apply UInt64.toNat_inj.1; simp [Nat.toUInt64_eq]
  unfold runStartsBits runStarts
  simp only [hs, hu]
  congr 1
  have hm : ∀ i ∈ List.range n.toNat, i < n.toNat := fun i h => List.mem_range.1 h
  generalize List.range n.toNat = l at hm
  generalize ByteArray.empty = acc
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [hb a (hm a (by simp))]
    exact ih (fun i h => hm i (by simp [h])) _

set_option maxRecDepth 20000 in
/-- An id at a one-bit lane is `bitAt`'s bit: `packIds 1` lays ids out LSB first, eight to a byte,
which is `Column.bits`' layout, and a read past the end is `0` in both. -/
theorem idAt_one (b : ByteArray) (i : Nat) : Column.idAt b 1 i = if Column.bitAt b i then 1 else 0 := by
  have hlen : (i * 1 + 1 + 7) / 8 - i * 1 / 8 = 1 := by omega
  have hp : 2 ^ i = 2 ^ (i % 8) * 2 ^ (8 * (i / 8)) := by rw [← Nat.pow_add]; congr 1; omega
  unfold Column.idAt Column.resAt Column.bitAt
  rw [hlen]
  simp only [List.range'_one, List.foldl_cons, List.foldl_nil, Nat.mul_one, Nat.zero_add]
  rw [hp, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)]
  generalize b[i / 8]?.getD 0 = x
  have hr : i % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize i % 8 = r at hr ⊢
  revert x
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  -- each bit position over the 256 bytes
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact fun ⟨⟨⟨v, hv⟩⟩⟩ => by revert v; decide

/-- **An interned column's run starts at a one-bit lane are the bitmap's**: the ids are `bitAt`'s bits
(`idAt_one`), so `runStartsIds` at width 1 compares the same pairs `runStartsBits` does, at every `n`. -/
theorem runStartsIds_one (n : USize) (b : ByteArray) : runStartsIds n 1 b = runStartsBits n b := by
  have h : ∀ i, (Column.idAt b (1 : USize).toNat i != Column.idAt b (1 : USize).toNat (i - 1)) =
      (Column.bitAt b i != Column.bitAt b (i - 1)) := fun i => by
    rw [USize.toNat_one, idAt_one, idAt_one]
    cases Column.bitAt b i <;> cases Column.bitAt b (i - 1) <;> rfl
  unfold runStartsIds runStartsBits
  simp only [h]

end Rel.Verify

/-- info: 'Rel.Verify.runStartsIds_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.runStartsIds_one
#guard Rel.Kernel.runStartsIds 100 1 (Rel.Column.packIds 1 100 fun i => i / 3 % 2) ==
  Rel.Kernel.runStartsBits 100 (Rel.Column.packIds 1 100 fun i => i / 3 % 2)
