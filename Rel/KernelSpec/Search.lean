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


end Rel.Verify
