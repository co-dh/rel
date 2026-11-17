import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.KernelSpec.Distinct
import Rel.Kernel.Structural
import Rel.Kernel.Reduce
import Rel.KernelSpec.Where
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.Kernel.Elementwise

/-! The part of `Rel.Verify.Gather` the Rel kernels reach; `Rel.Verify.Gather` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel

/-- **`gatherBytes` read back**: element `j` is the source's element at index `j` read unsigned, or
`fill`, at the low `8 * w` bits. -/
theorem elemsW_gatherBytes (w : USize) (hw0 : 0 < w.toNat) (hw : w.toNat ≤ 8) (fill : UInt64)
    (src idx : ByteArray) :
    elemsW w.toNat (gatherBytes w fill src idx) = (elemsW 8 idx).map fun k =>
      UInt64.ofNat (((elemsW w.toNat src).getD k.toNat fill).toNat % 2 ^ (8 * w.toNat)) := by
  obtain ⟨hs, hg⟩ := gatherBytes_spec w hw fill src idx
  apply List.ext_getElem (by simp only [elemsW, List.length_map, List.length_range, hs,
    Nat.mul_div_cancel_left _ hw0])
  intro j h1 h2
  simp only [elemsW, List.length_map, List.length_range] at h2
  simp only [elemsW, List.getElem_map, List.getElem_range]
  rw [hg j h2, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : (Column.bitsAt idx (j * 8) 8).toNat < src.size / w.toNat
  · rw [if_pos hi, List.getElem?_range hi, Option.map_some, Option.getD_some,
      Nat.mod_eq_of_lt (bitsAt_lt _ _ _ hw), UInt64.ofNat_toNat]
  · rw [if_neg hi, List.getElem?_eq_none (by rw [List.length_range]; omega), Option.map_none, Option.getD_none]

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

theorem denseWidth_facts {t : QAtomicType} {w : Nat} (ht : denseWidth t = some w) :
    rowWidth t = some w ∧ t.width = some w ∧ t ≠ .boolean ∧ t ≠ .guid ∧ t ≠ .symbol ∧ 0 < w ∧ w ≤ 8 := by
  cases t <;> simp only [denseWidth, QAtomicType.width, reduceCtorEq, Option.some.injEq] at ht <;> subst ht <;>
    exact ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem foRColumn_some {t : QAtomicType} {k : USize} {e : Enc} {n : USize} {M P : ByteArray}
    (h : foRColumn t k e = some (n, M, P)) : k = n ∧ e = .foR M P := by
  cases e <;> simp [foRColumn] at h; obtain ⟨_, rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

/-- **`bytesOf` reads what `raw` reads**, at the low `8 * w` bits: the dense payload a fixed-width
kernel is handed is the column's elements at its own width. -/
theorem elemsW_bytesOf {t : QAtomicType} {w : Nat} (ht : t.width = some w) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) (hw0 : 0 < w) (hw : w ≤ 8) (n : USize) (e : Enc) (hxw : Enc.WF t n e)
    (src : ByteArray) (h : Enc.bytesOf t n e = some src) :
    elemsW w src = (Enc.raw t n e).toList.map fun v => UInt64.ofNat (v.toNat % 2 ^ (8 * w)) := by
  have hwU : w.toUSize.toNat = w := USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  cases e with
  | bytes b =>
    have hs : b.size = n.toNat * w := by cases t <;> simp_all [Enc.WF, QAtomicType.width]
    simp only [Enc.bytesOf, Option.some.injEq] at h
    subst h
    rw [raw_bytes t w ht hb hg, Array.toList_map, Array.toList_range, List.map_map, elemsW, hs,
      Nat.mul_div_cancel _ hw0]
    exact List.map_congr_left fun i _ => by
      simp only [Function.comp_def]; rw [Nat.mod_eq_of_lt (bitsAt_lt _ _ _ hw), UInt64.ofNat_toNat]
  | foR M P =>
    simp only [Enc.bytesOf, ht, Option.map_some, Option.some.injEq] at h
    subst h
    have e := elemsW_decode w.toUSize (by omega) (by omega) M P n
    rw [hwU] at e
    rw [e, raw_foR t w ht hb hg, Array.toList_map, Array.toList_range, Coc.elems]
  | alp M P a =>
    have hr : Enc.raw t n (.alp M P a) =
        (Array.range n.toNat).map (Column.alpBits M P a (Column.blockStarts M)) := by
      cases t <;> simp_all [Enc.raw]
    simp only [Enc.bytesOf, ht, Option.map_some, Option.some.injEq] at h
    subst h
    have e := elemsW_alpDecode w.toUSize (by omega) (by omega) M P a n
    rw [hwU] at e
    rw [e, hr, Array.toList_map, Array.toList_range, Coc.alpElems]
  | _ => simp [Enc.bytesOf] at h

/-- The index of a gather as eight-byte longs, read the way `raw` reads the index column. -/
theorem elemsW_index (m : USize) (ie : Enc) (hiw : Enc.WF .long m ie) (ix : ByteArray)
    (h : Enc.bytesOf .long m ie = some ix) : elemsW 8 ix = (Enc.raw .long m ie).toList := by
  rw [elemsW_bytesOf (t := .long) rfl (by decide) (by decide) (by decide) (by decide) m ie hiw ix h]
  exact (List.map_congr_left fun v _ => ofNat_toNat_mod64 v).trans (List.map_id _)

theorem gatherColumn_fixed_shape {t : QAtomicType} {w : Nat} (ht : denseWidth t = some w) (n : USize) (e : Enc)
    (m : USize) (ie c : Enc) (hxw : Enc.WF t n e)
    (h : gatherColumn t n e m ie = some c) :
    ∃ src ix, Enc.bytesOf t n e = some src ∧ Enc.bytesOf .long m ie = some ix ∧
      c = .bytes (gatherBytes w.toUSize ((nullBits t).getD 0) src ix) := by
  obtain ⟨hr, hw, hb, hg, hs, hw0, hw8⟩ := denseWidth_facts ht
  unfold gatherColumn at h
  rw [ht] at h
  split at h
  · rename_i w' n' sm sp m' im ip hw' hfx hfi
    obtain rfl := Option.some.inj hw'
    obtain ⟨rfl, hxe⟩ := foRColumn_some hfx
    obtain ⟨rfl, hie⟩ := foRColumn_some hfi
    cases Option.some.inj h
    exact ⟨Coc.decode w.toUSize sm sp n, Coc.decode 8 im ip m,
      by simp [Enc.bytesOf, hxe, hw], by simp only [Enc.bytesOf, hie]; rfl, rfl⟩
  · -- the `idx` thunk is a `let` ahead of the `match t, e`: inline it so `split` takes the match
    simp only at h
    split at h
    · exact absurd rfl hb
    · exact absurd rfl hs
    · exact absurd rfl hs
    · split at h
      · simp at h
      · rename_i hae
        cases hix : Enc.bytesOf .long m ie with
        | none => simp [hix] at h
        | some ix =>
          by_cases hz : ix.size < m.toNat * 8
          · simp [hix, hz] at h
          simp only [hix, hz, ↓reduceIte, Option.map_some, Option.some.injEq] at h
          subst h
          cases t <;> simp [Column.alpEncodes] at hae <;> simp [QAtomicType.width] at hw <;> subst hw <;>
            exact ⟨_, ix, rfl, rfl, by rw [gatherAlp, show Column.alpF32 _ = _ from hxw.2.2.2]; rfl⟩
    · simp only [hr] at h
      split at h
      · obtain rfl := Option.some.inj ‹some w = some _›
        obtain ⟨rfl, hxe⟩ := foRColumn_some ‹foRColumn t _ _ = some _›
        cases hix : Enc.bytesOf .long m ie with
        | none => simp [hix] at h
        | some ix =>
          by_cases hz : ix.size < m.toNat * 8
          · simp [hix, hz] at h
          simp only [hix, hz, ↓reduceIte, Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨_, ix, by simp [Enc.bytesOf, hxe, hw], rfl, rfl⟩
      · obtain rfl := Option.some.inj ‹some w = some _›
        split at h
        · cases hix : Enc.bytesOf .long m ie with
          | none => simp [hix] at h
          | some ix =>
            by_cases hz : ix.size < m.toNat * 8
            · simp [hix, hz] at h
            simp only [hix, hz, ↓reduceIte, Option.map_some, Option.some.injEq] at h
            subst h
            exact ⟨_, ix, ‹_›, rfl, rfl⟩
        · simp at h
      · simp at h

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

/-- **`gatherBits` read back**: bit `j` of the answer is bit `idx[j]` of the source, the index read
unsigned, or `false` — `boolean`'s null — where that is not below `n`. -/
theorem bitAt_gatherBits (n : USize) (b idx : ByteArray) (j : Nat) (hj : j < idx.size / 8) :
    Column.bitAt (gatherBits n b idx) j =
      if (Column.bitsAt idx (j * 8) 8).toNat < n.toNat then Column.bitAt b (Column.bitsAt idx (j * 8) 8).toNat
      else false := by
  rw [gatherBits, bitAt_packOf _ _ _ hj]; simp only [gatherAt]
  by_cases hi : (Column.bitsAt idx (j * 8) 8).toNat < n.toNat <;> simp only [hi, ↓reduceIte]

/-- **`gatherPacked` read back**: id `j` of the answer is id `idx[j]` of the source, the index read
unsigned, or `fill` — the empty symbol's id — where that is not below `n`; at an answer width every
id fits. -/
theorem idAt_gatherPacked (n w wout : USize) (fill : UInt64) (src idx : ByteArray)
    (hw : wout.toNat = 0 ∨ wout.toNat = 1 ∨ wout.toNat = 2 ∨ wout.toNat = 4 ∨ wout.toNat = 8 ∨
      wout.toNat = 16 ∨ wout.toNat = 32 ∨ wout.toNat = 64)
    (hv : ∀ i < n.toNat, Column.idAt src w.toNat i < 2 ^ wout.toNat) (hf : fill.toNat < 2 ^ wout.toNat)
    (j : Nat) (hj : j < idx.size / 8) :
    Column.idAt (gatherPacked n w wout fill src idx) wout.toNat j =
      if (Column.bitsAt idx (j * 8) 8).toNat < n.toNat then Column.idAt src w.toNat (Column.bitsAt idx (j * 8) 8).toNat
      else fill.toNat := by
  unfold gatherPacked
  rw [idAt_packIds hw hj ?_] <;> simp only [gatherAt] <;>
    by_cases hi : (Column.bitsAt idx (j * 8) 8).toNat < n.toNat <;> simp only [hi, ↓reduceIte] <;>
    first | exact hv _ hi | exact hf

/-- **`x@i` at an interned `symbol` column** gathers the ids and leaves the dictionary to
`gatherIds`: the answer holds as many elements as the index, and its ids are `gatherPacked` of the
source's at the index — which `idAt_gatherPacked` reads back. An empty index answers before this. -/
theorem gatherColumn_enum (n : USize) (dict : ByteArray) (dof : Array Nat) (ids : ByteArray) (m : USize) (ie c : Enc)
    (hiw : Enc.WF .long m ie) (hm : m ≠ 0)
    (h : gatherColumn .symbol n (.enum dict dof ids) m ie = some c) :
    ∃ ix inRange db dbo nids, elemsW 8 ix = (Enc.raw .long m ie).toList ∧
      gatherIds dict dof inRange (fun w wo e => gatherPacked n w wo e ids ix) = (db, dbo, nids) ∧
      c = .enum db dbo nids := by
  simp only [gatherColumn, denseWidth] at h
  rw [if_neg (by simpa using hm)] at h
  cases hfi : foRColumn .long m ie with
  | some s =>
    obtain ⟨m', im, ip⟩ := s
    obtain ⟨rfl, rfl⟩ := foRColumn_some hfi
    simp only [hfi, Option.some.injEq] at h
    generalize hG : gatherIds dict dof _ _ = G at h
    obtain ⟨db, dbo, nids⟩ := G
    simp only at h
    exact ⟨Coc.decode 8 im ip m, _, db, dbo, nids, elemsW_index _ _ hiw _ rfl, hG, h.symm⟩
  | none =>
    simp only [hfi] at h
    cases hix : Enc.bytesOf .long m ie with
    | none => simp [hix] at h
    | some ix =>
      by_cases hz : ix.size < m.toNat * 8
      · simp [hix, hz] at h
      simp only [hix, hz, ↓reduceIte, Option.map_some, Option.some.injEq] at h
      generalize hG : gatherIds dict dof _ _ = G at h
      obtain ⟨db, dbo, nids⟩ := G
      simp only at h
      exact ⟨ix, _, db, dbo, nids, elemsW_index m ie hiw ix hix, hG, h.symm⟩

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

/-- **`gatherSyms` read back**: the answer holds one symbol per index, and symbol `j` — the bytes
between its start and the NUL before the next — is the source's symbol at the index read unsigned,
or the empty symbol, `symbol`'s null, past the end. -/
theorem gatherSyms_spec (blob : ByteArray) (offs : Array Nat) (ix : ByteArray) :
    let key (j : Nat) : ByteArray := match gatherAt (offs.size - 1) ix j with
      | some i => blob.extract offs[i]! (offs[i + 1]! - 1)
      | none => ByteArray.empty
    (gatherSyms blob offs ix).2.size = ix.size / 8 + 1 ∧
    ∀ j < ix.size / 8, ∃ lo, (gatherSyms blob offs ix).2[j]? = some lo ∧
      (gatherSyms blob offs ix).2[j + 1]? = some (lo + (key j).size + 1) ∧
      ∀ q < (key j).size, (gatherSyms blob offs ix).1[lo + q]? = (key j)[q]? := by
  intro key
  have hg : gatherSyms blob offs ix = ((List.range (ix.size / 8)).map key).foldl symStep (ByteArray.empty, #[0]) := by
    rw [List.foldl_map]; rfl
  obtain ⟨-, -, hS, hJ⟩ := foldl_symStep ((List.range (ix.size / 8)).map key) ByteArray.empty #[0] (by decide) rfl
  rw [hg]
  refine ⟨by rw [hS]; simp [Nat.add_comm], fun j hj => ?_⟩
  obtain ⟨lo, h1, h2, h3⟩ := hJ j (by simpa using hj)
  simp only [List.getElem_map, List.getElem_range] at h2 h3
  exact ⟨lo, by simpa using h1, by simpa [Nat.add_comm] using h2, h3⟩

/-- **`x@i` at a `symbol` blob** answers a blob, its symbols those `gatherSyms_spec` reads back at
the index column's elements. -/
theorem gatherColumn_syms (n : USize) (blob : ByteArray) (offs : Array Nat) (m : USize) (ie c : Enc)
    (hiw : Enc.WF .long m ie) (h : gatherColumn .symbol n (.syms blob offs) m ie = some c) :
    ∃ ix, elemsW 8 ix = (Enc.raw .long m ie).toList ∧
      c = .syms (gatherSyms blob offs ix).1 (gatherSyms blob offs ix).2 := by
  simp only [gatherColumn, denseWidth] at h
  cases hix : Enc.bytesOf .long m ie with
  | none => simp [hix] at h
  | some ix =>
    by_cases hz : ix.size < m.toNat * 8
    · simp [hix, hz] at h
    simp only [hix, hz, ↓reduceIte, Option.map_some, Option.some.injEq] at h
    exact ⟨ix, elemsW_index m ie hiw ix hix, h.symm⟩

/-- info: 'Rel.Verify.elemsW_gatherBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms elemsW_gatherBytes

/-- info: 'Rel.Verify.elemsW_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms elemsW_decode

/-- info: 'Rel.Verify.elemsW_alpDecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms elemsW_alpDecode

/-- info: 'Rel.Verify.denseWidth_facts' depends on axioms: [propext] -/
#guard_msgs in #print axioms denseWidth_facts

/-- info: 'Rel.Verify.foRColumn_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms foRColumn_some

/-- info: 'Rel.Verify.elemsW_bytesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms elemsW_bytesOf

/-- info: 'Rel.Verify.gatherColumn_fixed_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gatherColumn_fixed_shape

/-- info: 'Rel.Verify.byteOf_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms byteOf_bit

/-- info: 'Rel.Verify.bitAt_packOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bitAt_packOf

/-- info: 'Rel.Verify.bitAt_gatherBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bitAt_gatherBits

/-- info: 'Rel.Verify.elemsW_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms elemsW_index

/-- info: 'Rel.Verify.idAt_gatherPacked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms idAt_gatherPacked

/-- info: 'Rel.Verify.gatherColumn_enum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gatherColumn_enum

/-- info: 'Rel.Verify.ba_size_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ba_size_append

/-- info: 'Rel.Verify.foldl_symStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms foldl_symStep

/-- info: 'Rel.Verify.gatherSyms_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms gatherSyms_spec

/-- info: 'Rel.Verify.gatherColumn_syms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gatherColumn_syms

end Rel.Verify
