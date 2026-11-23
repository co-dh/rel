module

public import Rel.KernelSpec.Encoding
public import Rel.Kernel.Value
public import Rel.Kernel.Search
public import Rel.KernelSpec.Raw

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

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






end Rel.Verify
