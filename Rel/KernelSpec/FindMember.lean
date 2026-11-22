import Rel.KernelSpec.Encoding
import Rel.Kernel.Value
import Rel.Kernel.Search

/-! The part of `Rel.Verify.FindMember` the Rel kernels reach; `Rel.Verify.FindMember` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel



theorem idxOf_lt_length {α : Type} [BEq α] [LawfulBEq α] (y : α) (l : List α) :
    l.idxOf y < l.length ↔ y ∈ l := by
  induction l with
  | nil => exact ⟨fun h => absurd h (Nat.not_lt_zero 0), fun h => nomatch h⟩
  | cons a l ih =>
    rw [List.idxOf_cons, List.length_cons, List.mem_cons]
    cases h : a == y
    · have hne : ¬ y = a := fun e => Bool.noConfusion ((beq_iff_eq.2 e.symm).symm.trans h)
      simp only [cond_false]
      rw [Nat.add_lt_add_iff_right, ih]
      exact ⟨Or.inr, fun o => o.elim (fun e => absurd e hne) id⟩
    · exact ⟨fun _ => Or.inl (beq_iff_eq.1 h).symm, fun _ => Nat.succ_pos _⟩



theorem bit_eq_testBit (x : UInt8) (j : Nat) (hj : j < 8) :
    ((x >>> j.toUInt8) &&& 1 == 1) = x.toNat.testBit j := by
  have hj8 : j.toUInt8.toNat % 8 = j := by
    have hjn : j.toUInt8.toNat = j := by simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega
    omega
  have key : ((x >>> j.toUInt8) &&& 1).toNat = x.toNat / 2 ^ j % 2 := by
    rw [UInt8.toNat_and, UInt8.toNat_shiftRight, hj8, UInt8.toNat_one, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq, ← key]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← UInt8.toNat_inj, UInt8.toNat_one]

theorem toNat_or_bit (c : UInt8) (j : Nat) (hj : j < 8) :
    (c ||| 1 <<< j.toUInt8).toNat = c.toNat ||| 2 ^ j := by
  have hj8 : j.toUInt8.toNat % 8 = j := by
    have hjn : j.toUInt8.toNat = j := by simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega
    omega
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [UInt8.toNat_or, UInt8.toNat_shiftLeft, hj8, UInt8.toNat_one, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hp (by decide))]

/-- A byte built by setting bit `t` wherever `c t` holds. -/
theorem foldl_setBit (c : Nat → Bool) (l : List Nat) (hl : ∀ t ∈ l, t < 8) (a : UInt8) (j : Nat) :
    (l.foldl (fun byte t => if c t then byte ||| (1 <<< t.toUInt8) else byte) a).toNat.testBit j =
      (a.toNat.testBit j || l.any fun t => decide (t = j) && c t) := by
  induction l generalizing a with
  | nil => simp
  | cons t l ih =>
    rw [List.foldl_cons, ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)), List.any_cons]
    cases hc : c t
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_or]
    · simp only [↓reduceIte, Bool.and_true]
      rw [toNat_or_bit _ _ (hl t List.mem_cons_self), Nat.testBit_or, Nat.testBit_two_pow, Bool.or_assoc]


end Rel.Verify
