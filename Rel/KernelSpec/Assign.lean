import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Group
import Rel.KernelSpec.Ids
import Rel.KernelSpec.Structural
import Rel.Kernel.Sort
import Rel.Kernel.Structural
import Rel.Kernel.Value

/-! The part of `Rel.Verify.Assign` the Rel kernels reach; `Rel.Verify.Assign` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel

/-- At a sub-byte lane `w` of `per = 8 / w` fields to a byte, `Column.resAt` at element `i` is field
`i % per` of byte `i / per`, `0` past the array. -/
theorem resAt_field (P : ByteArray) (w per i : Nat) (hw : w = 1 ∧ per = 8 ∨ w = 2 ∧ per = 4 ∨ w = 4 ∧ per = 2) :
    (Column.resAt P 0 w i).toNat = (P[i / per]?.getD 0).toNat / 2 ^ (i % per * w) % 2 ^ w := by
  have hp : 0 < per := by rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hr := Nat.mod_lt i hp
  have hi := Nat.div_add_mod' i per
  generalize i / per = q at hi ⊢
  generalize i % per = r at hi hr ⊢
  subst hi
  have h3 : (q * per + r) * w = 8 * q + r * w := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hw1 : 1 ≤ w := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hrw : r * w + w ≤ 8 := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have h1 : (q * per + r) * w / 8 = q := Nat.div_eq_of_lt_le (by rw [h3]; omega) (by rw [h3]; omega)
  have h2 : ((q * per + r) * w + w + 7) / 8 = q + 1 := Nat.div_eq_of_lt_le (by rw [h3]; omega) (by rw [h3]; omega)
  unfold Column.resAt
  rw [h2, h1, Nat.add_sub_cancel_left, List.range'_one]
  simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add]
  rw [h3, Nat.pow_add, Nat.mul_comm, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]
  have hlt : (P[q]?.getD 0).toNat / 2 ^ (r * w) % 2 ^ w < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [UInt64.zero_or, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]

/-- The write of field `r` of a packed byte: field `r` becomes `v`, every other field keeps its bits.
By `decide` over every byte, field and value. -/
theorem set_field (w per : Nat) (hw : w = 1 ∧ per = 8 ∨ w = 2 ∧ per = 4 ∨ w = 4 ∧ per = 2) :
    ∀ b < 256, ∀ r < per, ∀ v < 2 ^ w, ∀ r' < per,
      ((b.toUInt8 &&& ~~~((((1 : UInt8) <<< w.toUInt8) - 1) <<< (r * w).toUInt8)) |||
        v.toUInt8 <<< (r * w).toUInt8).toNat / 2 ^ (r' * w) % 2 ^ w =
        if r' = r then v else b / 2 ^ (r' * w) % 2 ^ w := by
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide +kernel

/-- `ByteArray.set!` replaces byte `p` when it is there and touches no other. -/
theorem set!_getElem? (a : ByteArray) (p j : Nat) (x : UInt8) :
    (a.set! p x)[j]? = if p = j ∧ p < a.size then some x else a[j]? := by
  rcases a with ⟨d⟩
  show (d.set! p x)[j]? = if p = j ∧ p < d.size then some x else d[j]?
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : p = j <;> by_cases h2 : p < d.size <;> simp_all

/-- info: 'Rel.Verify.resAt_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms resAt_field
/-- info: 'Rel.Verify.set_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms set_field
/-- info: 'Rel.Verify.set!_getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms set!_getElem?

end Rel.Verify
