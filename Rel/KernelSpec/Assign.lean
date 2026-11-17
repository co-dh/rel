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
/-- **`scatterPacked` keeps the last write below a byte**: at `w` = 1, 2 or 4 bits (a bitmap, sub-byte
ids), field `i` of the answer is the source field of the last index naming `i`, and `dst`'s field `i`
where no index does. The answer is `dst`'s size, an index past `dst` writing nothing. -/
theorem scatterPacked_sub (w per : Nat) (hw : w = 1 ∧ per = 8 ∨ w = 2 ∧ per = 4 ∨ w = 4 ∧ per = 2)
    (wb : USize) (hwb : wb.toNat = w) (dst idx src : ByteArray) (soff : USize) (bcast : Bool) :
    (scatterPacked wb dst idx src soff bcast).size = dst.size ∧
    ∀ i < dst.size * 8 / w, Column.resAt (scatterPacked wb dst idx src soff bcast) 0 w i =
      match ((List.range (idx.size / 8)).filter fun k => (Column.bitsAt idx (k * 8) 8).toNat == i).getLast? with
      | some k => Column.resAt src 0 w (soff.toNat + if bcast then 0 else k)
      | none => Column.resAt dst 0 w i := by
  have hper : 8 / w = per := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hp : 0 < per := by rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hpw : per * w = 8 := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hw0 : (w == 0) = false := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hw8 : ¬ 8 ≤ w := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  -- `s * 8 / w` fields: `i` among them exactly when its byte `i / per` is
  have hN : ∀ s i, i < s * 8 / w ↔ i / per < s := fun s i => by
    rw [← hpw, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by omega), Nat.div_lt_iff_lt_mul hp]
  unfold scatterPacked
  simp only [hwb, hw0, hw8, hper, Bool.false_eq_true, if_false]
  refine foldl_lastWrite ByteArray.size (· * 8 / w) (fun b i => Column.resAt b 0 w i) _
    (fun k => (Column.bitsAt idx (k * 8) 8).toNat)
    (fun k => Column.resAt src 0 w (soff.toNat + if bcast then 0 else k)) _ (fun acc k => ?_)
    (fun acc k _ i hi => ?_) dst
  · dsimp only
    split
    · rfl
    · simp only [ByteArray.set!, ByteArray.size, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  · dsimp only at hi ⊢
    split
    · rename_i hu
      rw [if_neg (by omega)]
    · rename_i hu
      have hv : (Column.resAt src 0 w (soff.toNat + if bcast then 0 else k)).toNat < 2 ^ w := by
        rw [resAt_field _ w per _ hw]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      generalize (Column.bitsAt idx (k * 8) 8).toNat = u at hu ⊢
      generalize Column.resAt src 0 w (soff.toNat + if bcast then 0 else k) = v at hv ⊢
      have hu' := (hN _ _).1 (Nat.lt_of_not_le hu)
      have hb := (acc.get! (u / per)).toNat_lt
      apply UInt64.toNat_inj.1
      rw [resAt_field _ w per i hw, set!_getElem?]
      by_cases hq : u / per = i / per
      · rw [if_pos ⟨hq, hu'⟩, Option.getD_some]
        have := set_field w per hw (acc.get! (u / per)).toNat hb (u % per) (Nat.mod_lt _ hp) v.toNat hv
          (i % per) (Nat.mod_lt _ hp)
        have e1 : (acc.get! (u / per)).toNat.toUInt8 = acc.get! (u / per) := by simp
        have e2 : v.toNat.toUInt8 = v.toUInt8 := by simp
        rw [e1, e2] at this
        rw [this]
        by_cases hui : u = i
        · subst hui; rw [if_pos rfl, if_pos rfl]
        · have hr : ¬ i % per = u % per := fun h => hui (by
            rw [← Nat.div_add_mod' u per, ← Nat.div_add_mod' i per, hq, h])
          rw [if_neg hr, if_neg hui, resAt_field _ w per i hw, get!_eq, hq]
      · rw [if_neg (fun h => hq h.1), if_neg (fun h => hq (congrArg (· / per) h)), resAt_field _ w per i hw]

/-- **`scatterPacked` keeps the last write at every lane width**, read as ids: of the `n` ids `dst` holds
(`idsCap`), id `i` of the answer is the source id of the last index naming `i`, and `dst`'s id `i` where no
index does. Width `0` stores nothing and writes nothing; `src` holds the ids read, one under `bcast`. -/
theorem scatterPacked_ids {W : Nat} (hW : W = 0 ∨ W = 1 ∨ W = 2 ∨ W = 4 ∨ W = 8 ∨ W = 16 ∨ W = 32 ∨ W = 64)
    (wb : USize) (hwb : wb.toNat = W) (dst idx src : ByteArray) (soff : USize) (bcast : Bool) (n : Nat)
    (hcap : Column.idsCap dst W n = n) (hsrc : (soff.toNat + if bcast then 1 else idx.size / 8) * (W / 8) ≤ src.size) :
    ∀ i < n, Column.idAt (scatterPacked wb dst idx src soff bcast) W i =
      match ((List.range (idx.size / 8)).filter fun k => (Column.bitsAt idx (k * 8) 8).toNat == i).getLast? with
      | some k => Column.idAt src W (soff.toNat + if bcast then 0 else k)
      | none => Column.idAt dst W i := by
  intro i hi
  have hn : W ≠ 0 → n ≤ dst.size * 8 / W := fun h => by
    unfold Column.idsCap at hcap; rw [if_neg h] at hcap; omega
  -- whole-byte lanes `8c`: `scatterPacked_spec`, each id `c` bytes
  have lane : ∀ c, 1 ≤ c → c ≤ 8 → W = 8 * c → Column.idAt (scatterPacked wb dst idx src soff bcast) W i =
      match ((List.range (idx.size / 8)).filter fun k => (Column.bitsAt idx (k * 8) 8).toNat == i).getLast? with
      | some k => Column.idAt src W (soff.toNat + if bcast then 0 else k)
      | none => Column.idAt dst W i := fun c hc hc8 hWc => by
    subst hWc
    have hi' : i < dst.size / c := by
      have := hn (by omega); rw [Nat.mul_comm 8 c, Nat.mul_div_mul_right _ _ (by decide)] at this; omega
    have hsrc' : (soff.toNat + if bcast then 1 else idx.size / 8) * c ≤ src.size := by
      rwa [Nat.mul_div_cancel_left _ (by decide)] at hsrc
    unfold Column.idAt
    rw [resAt_lane _ c i hc8, Nat.mul_comm c i, (scatterPacked_spec c hc wb hwb dst idx src soff bcast hsrc').2 i hi']
    generalize (List.filter _ _).getLast? = o
    cases o <;> simp only [resAt_lane _ c _ hc8, Nat.mul_comm c]
  rcases hW with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · generalize (List.filter _ _).getLast? = o
    cases o <;> simp [Column.idAt, Column.resAt]
  -- sub-byte lanes: `scatterPacked_sub`
  · unfold Column.idAt
    rw [(scatterPacked_sub 1 8 (by decide) wb hwb dst idx src soff bcast).2 i (by have := hn (by decide); omega)]
    generalize (List.filter _ _).getLast? = o
    cases o <;> rfl
  · unfold Column.idAt
    rw [(scatterPacked_sub 2 4 (by decide) wb hwb dst idx src soff bcast).2 i (by have := hn (by decide); omega)]
    generalize (List.filter _ _).getLast? = o
    cases o <;> rfl
  · unfold Column.idAt
    rw [(scatterPacked_sub 4 2 (by decide) wb hwb dst idx src soff bcast).2 i (by have := hn (by decide); omega)]
    generalize (List.filter _ _).getLast? = o
    cases o <;> rfl
  · exact lane 1 (by decide) (by decide) rfl
  · exact lane 2 (by decide) (by decide) rfl
  · exact lane 4 (by decide) (by decide) rfl
  · exact lane 8 (by decide) (by decide) rfl

/-- **`scatterIds` keeps the last write**: the `n` ids at `wa` bits, widened to `wb`, with `yids` written at
`idx` — id `i` of the answer is `yids`' id of the last index naming `i`, and the column's own id `i` where no
index does. `yids` holds the ids read, one under `bcast`. -/
theorem scatterIds_spec (wa wb n : USize)
    (hwa : wa.toNat = 0 ∨ wa.toNat = 1 ∨ wa.toNat = 2 ∨ wa.toNat = 4 ∨ wa.toNat = 8 ∨ wa.toNat = 16 ∨ wa.toNat = 32 ∨ wa.toNat = 64)
    (hwb : wb.toNat = 0 ∨ wb.toNat = 1 ∨ wb.toNat = 2 ∨ wb.toNat = 4 ∨ wb.toNat = 8 ∨ wb.toNat = 16 ∨ wb.toNat = 32 ∨ wb.toNat = 64)
    (hab : wa.toNat ≤ wb.toNat) (ids idx yids : ByteArray) (bcast : Bool)
    (hcap : Column.idsCap ids wa.toNat n.toNat = n.toNat)
    (hy : (if bcast then 1 else idx.size / 8) * (wb.toNat / 8) ≤ yids.size) :
    ∀ i < n.toNat, Column.idAt (scatterIds wa wb n ids idx yids bcast) wb.toNat i =
      match ((List.range (idx.size / 8)).filter fun k => (Column.bitsAt idx (k * 8) 8).toNat == i).getLast? with
      | some k => Column.idAt yids wb.toNat (if bcast then 0 else k)
      | none => Column.idAt ids wa.toNat i := by
  intro i hi
  have hy' : ((0 : USize).toNat + if bcast then 1 else idx.size / 8) * (wb.toNat / 8) ≤ yids.size := by
    rw [show (0 : USize).toNat = 0 from rfl, Nat.zero_add]; exact hy
  unfold scatterIds
  by_cases h : wa = wb
  · subst h
    rw [if_pos (show (wa == wa) = true from decide_eq_true rfl), scatterPacked_ids hwb wa rfl ids idx yids 0 bcast n.toNat hcap hy' i hi]
    simp only [show (0 : USize).toNat = 0 from rfl, Nat.zero_add]
  · rw [if_neg (show ¬ (wa == wb) = true from fun e => h (of_decide_eq_true e)), scatterPacked_ids hwb wb rfl _ idx yids 0 bcast n.toNat (idsCap_packIds _ _ hwb) hy' i hi]
    simp only [show (0 : USize).toNat = 0 from rfl, Nat.zero_add]
    generalize (List.filter _ _).getLast? = o
    cases o
    · exact idAt_packIds hwb hi (Nat.lt_of_lt_of_le (idAt_lt ids _ i (by rcases hwa with h | h | h | h | h | h | h | h <;> rw [h] <;> decide)) (Nat.pow_le_pow_right (by decide) hab))
    · rfl

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

/-- **`:` of symbols into an interned column keeps the last write**: where `hashConcat` resolves `y`'s
symbols against `x`'s dictionary `d` (`yids`, ids of the joined dictionary `db`), the answer is `x`'s `n` ids
widened to `db`'s width with `yids` written at `ix` — id `i` is `y`'s id of the last index naming `i`, and
`x`'s own id `i` where no index does. Assumed, not derived: `db` is no shorter than `d` (`hab`), `x` holds
its `n` ids (`hcap`), and `yids` holds the ids read (`hy`). -/
theorem assignSyms_interned (n : USize) (e : Enc) (ny : USize) (ye : Enc) (ix : ByteArray)
    (bcast : Bool) (hns : ¬ ∃ b o yb yo, e = .syms b o ∧ ye = .syms yb yo)
    {d ids yd yi db yids : ByteArray} {o yo dbo : Array Nat}
    (hc : Column.intern e = .enum d o ids) (hyc : Column.intern ye = .enum yd yo yi)
    (hh : hashConcat #[(0, d, o, .empty), (ny, yd, yo, yi)] = .ok (db, dbo, yids))
    (hab : Column.idWidth o ≤ Column.idWidth dbo) (hcap : Column.idsCap ids (Column.idWidth o) n.toNat = n.toNat)
    (hy : (if bcast then 1 else ix.size / 8) * (Column.idWidth dbo / 8) ≤ yids.size) :
    ∃ ids', assignSyms n e ny ye ix bcast = some (.enum db dbo ids') ∧
      ∀ i < n.toNat, Column.idAt ids' (Column.idWidth dbo) i =
        match ((List.range (ix.size / 8)).filter fun k => (Column.bitsAt ix (k * 8) 8).toNat == i).getLast? with
        | some k => Column.idAt yids (Column.idWidth dbo) (if bcast then 0 else k)
        | none => Column.idAt ids (Column.idWidth o) i := by
  have lane : ∀ o : Array Nat, (Column.idWidth o).toUSize.toNat = Column.idWidth o ∧
      ((Column.idWidth o).toUSize.toNat = 0 ∨ (Column.idWidth o).toUSize.toNat = 1 ∨
        (Column.idWidth o).toUSize.toNat = 2 ∨ (Column.idWidth o).toUSize.toNat = 4 ∨
        (Column.idWidth o).toUSize.toNat = 8 ∨ (Column.idWidth o).toUSize.toNat = 16 ∨
        (Column.idWidth o).toUSize.toNat = 32 ∨ (Column.idWidth o).toUSize.toNat = 64) := fun o => by
    have h := laneWidth_cases (Column.widthFor (o.size - 1 - 1))
    have e : (Column.idWidth o).toUSize.toNat = Column.idWidth o :=
      USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by unfold Column.idWidth Column.idWidthOf; omega) USize.le_size)
    rw [e]; unfold Column.idWidth Column.idWidthOf; exact ⟨rfl, h⟩
  obtain ⟨ea, ha⟩ := lane o
  obtain ⟨eb, hb⟩ := lane dbo
  refine ⟨scatterIds (Column.idWidth o).toUSize (Column.idWidth dbo).toUSize n ids ix yids bcast, ?_, ?_⟩
  · unfold assignSyms
    split
    · exact absurd ⟨_, _, _, _, rfl, rfl⟩ hns
    · simp only [hc, hyc, hh]
  · have := scatterIds_spec _ _ n ha hb (by rw [ea, eb]; exact hab) ids ix yids bcast
      (by rw [ea]; exact hcap) (by rw [eb]; exact hy)
    rw [ea, eb] at this
    exact this

/-- info: 'Rel.Verify.resAt_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms resAt_field
/-- info: 'Rel.Verify.set_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms set_field
/-- info: 'Rel.Verify.set!_getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms set!_getElem?
/-- info: 'Rel.Verify.scatterPacked_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scatterPacked_sub
/-- info: 'Rel.Verify.scatterPacked_ids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scatterPacked_ids
/-- info: 'Rel.Verify.scatterIds_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scatterIds_spec
/-- info: 'Rel.Verify.copySlice_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copySlice_end
/-- info: 'Rel.Verify.push_get!' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms push_get!
/-- info: 'Rel.Verify.symBytes_push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms symBytes_push
/-- info: 'Rel.Verify.assignSyms_interned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms assignSyms_interned

end Rel.Verify
