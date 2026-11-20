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

/-- `scatterPacked`'s write of field `r` of a byte: field `r` becomes `v`, every other field keeps its bits.
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

/-- Symbol `i` of a blob `b` with offsets `o`, as the bytes between its offset and the next: its NUL included,
which is what `scatterSyms` copies. -/
def symBytes (b : ByteArray) (o : Array Nat) (i : Nat) : List UInt8 :=
  (b.data.toList.drop o[i]!).take (o[i + 1]! - o[i]!)

/-- A `copySlice` to the end of `dst` appends the bytes of `src` it reads, clamped to `src`. -/
theorem copySlice_end (src dst : ByteArray) (so len : Nat) :
    (src.copySlice so dst dst.size len).data.toList = dst.data.toList ++ (src.data.toList.drop so).take len := by
  apply List.ext_getElem?
  intro j
  show (dst.data.extract 0 dst.data.size ++ src.data.extract so (so + len) ++
      dst.data.extract (dst.data.size + min len (src.data.size - so)) dst.data.size).toList[j]? = _
  simp only [Array.getElem?_toList, Array.getElem?_append, extract_getElem?, Array.size_append, Array.size_extract,
    List.getElem?_append, List.getElem?_take, List.getElem?_drop, Array.length_toList]
  repeat' split
  all_goals
    first | rfl | (exfalso; omega) | (congr 1; omega) | exact (Array.getElem?_eq_none (by omega)).symm | exact Array.getElem?_eq_none (by omega)

/-- `(a.push x)[t]!`: `a`'s own below its size, `x` at it. -/
theorem push_get! (a : Array Nat) (x t : Nat) : (a.push x)[t]! = if t < a.size then a[t]! else if t = a.size then x else 0 := by
  simp only [getElem!_def, ← Array.getElem?_toList, Array.toList_push, List.getElem?_append, Array.length_toList]
  by_cases h : t < a.size
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    by_cases h2 : t = a.size
    · subst h2; rw [if_pos rfl, Nat.sub_self]; rfl
    · rw [if_neg h2, List.getElem?_eq_none (by rw [List.length_singleton]; omega)]; rfl

/-- One step of `scatterSyms`' fold: appending the bytes `s` to the blob and its new end to the offsets adds
symbol `j` as `s` and leaves every earlier symbol as it was. -/
theorem symBytes_push (ob ob' : ByteArray) (oo : Array Nat) (j : Nat) (s : List UInt8)
    (h1 : oo.size = j + 1) (h2 : oo[j]! = ob.size) (h3 : ∀ t ≤ j, oo[t]! ≤ ob.size)
    (hob : ob'.data.toList = ob.data.toList ++ s) :
    (oo.push ob'.size).size = j + 1 + 1 ∧ (oo.push ob'.size)[j + 1]! = ob'.size ∧
      (∀ t ≤ j + 1, (oo.push ob'.size)[t]! ≤ ob'.size) ∧ symBytes ob' (oo.push ob'.size) j = s ∧
      ∀ t < j, symBytes ob' (oo.push ob'.size) t = symBytes ob oo t := by
  have hl : ob'.size = ob.size + s.length := by
    have := congrArg List.length hob
    simp only [Array.length_toList, List.length_append] at this
    exact this
  have hl' : ob.data.toList.length = ob.size := Array.length_toList
  have old : ∀ t ≤ j, (oo.push ob'.size)[t]! = oo[t]! := fun t ht => by
    rw [push_get!, if_pos (show t < oo.size by omega)]
  have new : (oo.push ob'.size)[j + 1]! = ob'.size := by
    rw [push_get!, if_neg (show ¬ j + 1 < oo.size by omega), if_pos h1.symm]
  refine ⟨by rw [Array.size_push, h1], new, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · rcases Nat.lt_or_eq_of_le ht with ht | rfl
    · rw [old t (by omega)]; have := h3 t (by omega); omega
    · rw [new]; exact Nat.le_refl _
  · unfold symBytes
    rw [old j (Nat.le_refl _), new, h2, hob, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append, hl, Nat.add_sub_cancel_left, List.take_length]
  · unfold symBytes
    have := h3 t (by omega); have := h3 (t + 1) (by omega)
    rw [old t (by omega), old (t + 1) (by omega), hob, List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]

/-- info: 'Rel.Verify.resAt_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms resAt_field
/-- info: 'Rel.Verify.set_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms set_field
/-- info: 'Rel.Verify.set!_getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms set!_getElem?
/-- info: 'Rel.Verify.copySlice_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copySlice_end
/-- info: 'Rel.Verify.push_get!' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms push_get!
/-- info: 'Rel.Verify.symBytes_push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms symBytes_push

end Rel.Verify
