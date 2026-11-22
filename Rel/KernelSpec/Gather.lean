import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.KernelSpec.Distinct
import Rel.Kernel.Structural
import Rel.KernelSpec.Where
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.Kernel.Elementwise

/-! The part of `Rel.Verify.Gather` the Rel kernels reach; `Rel.Verify.Gather` imports it. -/


open Rel.Ext

namespace Rel.Verify
open Rel Rel.Kernel


/-- `Coc.decode`'s elements, each the encoded one's low `8 * w` bits. -/
theorem elemsW_decode (w : USize) (hw0 : 0 < w.toNat) (hw : w.toNat ≤ 8) (M P : ByteArray) (n : USize) :
    elemsW w.toNat (Coc.decode w M P n) = (Coc.elems M P n).map fun v => UInt64.ofNat (v.toNat % 2 ^ (8 * w.toNat)) :=
  elemsW_foldl_mod id w.toNat hw0 hw _

/-- `Coc.alpDecode` is the one `alpElems` fold at every width: at 4 and 8 the C decoder it calls is
specified as that fold. -/
theorem alpDecode_eq (w : USize) (M P a : ByteArray) (n : USize) :
    Coc.alpDecode w M P a n =
      (Coc.alpElems M P a n).foldl (fun acc v => Column.pushBits acc (id v) w.toNat) .empty := by
  unfold Coc.alpDecode
  split
  · rename_i h; rw [eq_of_beq h, show (4 : USize).toNat = 4 by simp]; rfl
  · split
    · rename_i h; rw [eq_of_beq h, show (8 : USize).toNat = 8 by simp]; rfl
    · rfl

/-- `Coc.alpDecode`'s elements, each `alpElems`' low `8 * w` bits. -/
theorem elemsW_alpDecode (w : USize) (hw0 : 0 < w.toNat) (hw : w.toNat ≤ 8) (M P a : ByteArray) (n : USize) :
    elemsW w.toNat (Coc.alpDecode w M P a n) =
      (Coc.alpElems M P a n).map fun v => UInt64.ofNat (v.toNat % 2 ^ (8 * w.toNat)) := by
  rw [alpDecode_eq]; exact elemsW_foldl_mod id w.toNat hw0 hw _



/-- **`bytesOf` reads what `raw` reads**: the dense payload a fixed-width kernel is handed is the column's elements
at its own width, `raw` reading every form zero-extended from `8 * w` bits. -/
theorem elemsW_bytesOf {t : QAtomicType} {w : Nat} (ht : t.width = some w) (hb : t ≠ .u1)
    (hw0 : 0 < w) (hw : w ≤ 8) (n : USize) (e : Ext.Enc X) (hxw : Enc.WF t n e)
    (src : ByteArray) (h : Enc.bytesOf t n e = some src) :
    elemsW w src = (Enc.raw t n e).toList := by
  have hwU : w.toUSize.toNat = w := USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  cases e with
  | foR M P =>
    simp only [Enc.bytesOf, ht, Option.map_some, Option.some.injEq] at h
    subst h
    have e := elemsW_decode w.toUSize (by omega) (by omega) M P n
    rw [hwU] at e
    rw [e, raw_foR t w ht hb, Array.toList_map, Array.toList_range, Coc.elems, List.map_map]; rfl
  | pos =>
    cases t <;> simp only [Enc.WF] at hxw
    simp only [QAtomicType.width, Option.some.injEq] at ht; subst ht
    simp only [Enc.bytesOf, Option.some.injEq] at h; subst h
    rw [List.foldl_map, elemsW_foldl_mod Nat.toUInt64 8 (by decide) (by decide)]
    simp only [Enc.raw, Array.toList_map, Array.toList_range, List.map_map]
    exact List.map_congr_left fun a _ => UInt64.toNat_inj.mp (by simp [UInt64.toNat_ofNat, Nat.mod_mod])
  | _ => simp [Enc.bytesOf] at h


/-- The byte `packOf` builds from eight flags, flag `t` at bit `t`. -/
def byteOf (l : List Bool) : UInt8 :=
  (List.range 8).foldl (init := (0 : UInt8)) fun b t => if l.getD t false then b ||| (1 <<< t.toUInt8) else b

theorem byteOf_bit : ∀ c0 c1 c2 c3 c4 c5 c6 c7 : Bool, ∀ s, s < 8 →
    ((byteOf [c0, c1, c2, c3, c4, c5, c6, c7] >>> s.toUInt8) &&& 1 == 1) =
      [c0, c1, c2, c3, c4, c5, c6, c7].getD s false := by
  decide +kernel

/-- **`packOf` read back**: bit `j` below `n` is `f j`. -/
theorem bitAt_packOf (n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n) : Column.bitAt (packOf n f) j = f j := by
  let g (k t : Nat) : Bool := k * 8 + t < n && f (k * 8 + t)
  let B (k : Nat) : UInt8 := byteOf [g k 0, g k 1, g k 2, g k 3, g k 4, g k 5, g k 6, g k 7]
  have hp : packOf n f = (List.range ((n + 7) / 8)).foldl (fun acc k => acc.push (B k)) ByteArray.empty := rfl
  obtain ⟨-, -, hb⟩ := foldl_push8 B (List.range ((n + 7) / 8)) ByteArray.empty
  have hk : j / 8 < (n + 7) / 8 := by
    have h1 := Nat.div_mul_le_self j 8
    exact (Nat.le_div_iff_mul_le (by decide)).2 (by rw [Nat.succ_mul]; omega)
  have e := hb (j / 8) (by rw [List.length_range]; exact hk)
  rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, List.getElem_range] at e
  have hs : j % 8 < 8 := Nat.mod_lt _ (by decide)
  have hg : ∀ s < 8, [g (j / 8) 0, g (j / 8) 1, g (j / 8) 2, g (j / 8) 3, g (j / 8) 4, g (j / 8) 5,
      g (j / 8) 6, g (j / 8) 7].getD s false = g (j / 8) s := by
    intro s hs; rcases s with _ | _ | _ | _ | _ | _ | _ | _ | s
    all_goals first | rfl | omega
  have hd : j / 8 * 8 + j % 8 = j := Nat.div_add_mod' j 8
  rw [Column.bitAt, hp, e, Option.getD_some, byteOf_bit _ _ _ _ _ _ _ _ _ hs, hg _ hs]
  simp only [g, hd, hj, decide_true, Bool.true_and]




/-- One symbol laid after a blob and its starts: the bytes, a NUL, and the next start. -/
def symStep (x : ByteArray × Array Nat) (k : ByteArray) : ByteArray × Array Nat :=
  ((x.1 ++ k).push 0, x.2.push (x.1.size + k.size + 1))

theorem ba_size_append (a b : ByteArray) : (a ++ b).size = a.size + b.size := by
  first
    | exact ByteArray.size_append
    | (show (a ++ b).data.size = a.data.size + b.data.size; rw [ByteArray.data_append, Array.size_append])

/-- Symbols laid one after another by `symStep`: what was there stays, and symbol `j` starts at the
`j`-th new start, ends one byte before the next, and holds its own bytes. -/
theorem foldl_symStep (ks : List ByteArray) (b : ByteArray) (o : Array Nat) (ho0 : 0 < o.size)
    (ho : o[o.size - 1]? = some b.size) :
    (∀ q < b.size, (ks.foldl symStep (b, o)).1[q]? = b[q]?) ∧
    (∀ q < o.size, (ks.foldl symStep (b, o)).2[q]? = o[q]?) ∧
    (ks.foldl symStep (b, o)).2.size = o.size + ks.length ∧
    ∀ j (hj : j < ks.length), ∃ lo, (ks.foldl symStep (b, o)).2[o.size - 1 + j]? = some lo ∧
      (ks.foldl symStep (b, o)).2[o.size + j]? = some (lo + ks[j].size + 1) ∧
      ∀ q < ks[j].size, (ks.foldl symStep (b, o)).1[lo + q]? = ks[j][q]? := by
  induction ks generalizing b o with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | cons k ks ih =>
    have hb' : ((b ++ k).push 0).size = b.size + k.size + 1 := by rw [ba_size_push, ba_size_append]
    have hos : (o.push (b.size + k.size + 1)).size = o.size + 1 := Array.size_push ..
    have hlast : (o.push (b.size + k.size + 1))[o.size]? = some (b.size + k.size + 1) := Array.getElem?_push_size
    have hpre : ∀ q < o.size, (o.push (b.size + k.size + 1))[q]? = o[q]? := fun q hq => (Array.getElem?_push_lt hq).trans (Array.getElem?_eq_getElem hq).symm
    obtain ⟨hB, hO, hS, hJ⟩ := ih ((b ++ k).push 0) (o.push (b.size + k.size + 1)) (by omega)
      (by rw [hos, Nat.add_sub_cancel, hlast, hb'])
    simp only [List.foldl_cons, List.length_cons]
    rw [show symStep (b, o) k = ((b ++ k).push 0, o.push (b.size + k.size + 1)) from rfl]
    have hB0 := hB
    refine ⟨fun q hq => ?_, fun q hq => ?_, by rw [hS, hos]; omega, ?_⟩
    · rw [hB0 q (by rw [hb']; omega), ba_push_getElem?, if_neg (by rw [ba_size_append]; omega), ba_append_left _ _ _ hq]
    · rw [hO q (by omega), hpre q hq]
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        refine ⟨b.size, ?_, ?_, fun q hq => ?_⟩
        · rw [hO _ (by omega), hpre _ (by omega), ho]
        · rw [hO _ (by omega), hlast]
        · rw [hB0 _ (by rw [hb']; omega), ba_push_getElem?, if_neg (by rw [ba_size_append]; omega), ba_append_right]
      | succ j =>
        obtain ⟨lo, h1, h2, h3⟩ := hJ j (by simpa using hj)
        rw [hos, Nat.add_sub_cancel] at h1
        rw [hos] at h2
        exact ⟨lo, by rw [show o.size - 1 + (j + 1) = o.size + j by omega]; exact h1,
          by rw [show o.size + (j + 1) = o.size + 1 + j by omega]; exact h2, h3⟩




/-- info: 'Rel.Verify.elemsW_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms elemsW_decode

/-- info: 'Rel.Verify.elemsW_alpDecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms elemsW_alpDecode



/-- info: 'Rel.Verify.elemsW_bytesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms elemsW_bytesOf


/-- info: 'Rel.Verify.byteOf_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms byteOf_bit

/-- info: 'Rel.Verify.bitAt_packOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bitAt_packOf





/-- info: 'Rel.Verify.ba_size_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ba_size_append

/-- info: 'Rel.Verify.foldl_symStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms foldl_symStep



end Rel.Verify
