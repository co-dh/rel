/-
  The RelRep core: a relation is a key and a value column of one length `n` over the positions
  `0 … n-1`, `R x y ↔ ∃ i, key.get i = x ∧ val.get i = y` — a tabulation, `key° ≫ val = R`.
  Columns are qlean's `Column`s in whatever encoding carries them; an element is read through
  `Column.get` (qlean's one-element reader over `bitsAt`/`bitAt`/`foRBits`/`symBytes`), never
  `Column.atoms`. Lists exist in proofs only (`toList`).
-/
import Rel.Kernel.Dep.Monadic
import Rel.KernelSpec.Alp
import Rel.KernelSpec.SymFind
import Rel.KernelSpec.Gather

open Rel.Ext

namespace Rel

open Rel Rel.Dep

/-- An element of a column of type `t`: qlean's `Carrier`, a `QValue` in a general list. -/
abbrev El := Carrier

/-- A vector of `n` elements of type `t`: qlean's typed vector, `QValue.WFAt` saying the header is `t`, `n`
    and `Enc.WF` that the payload agrees with it; a general list is `.gen xs`. q's attribute is the vector's
    own (codes 1 sorted, 2 unique, 3 parted, 4 grouped, with the `IndexCell` of its index), set by producers
    and read by consumers (§2.4). -/
abbrev Arr (t : QAtomicType) (n : USize) := {v : QValue // v.WFAt t n}

namespace Arr

variable {t : QAtomicType} {n : USize}

/-- The payload. The fallback is unreachable: `WFAt` holds only of a `vector`. -/
def enc (x : Arr t n) : Enc := match x.1 with | .vector _ _ e _ => e | _ => .gen #[]

/-- The attribute and index cell, `QValue.attrCell` of the vector. -/
def attrCell (x : Arr t n) : Option (UInt8 × IndexCell) := match x.1 with | .vector _ _ _ a => a | _ => none

/-- The payload agrees with the header. -/
theorem wf (x : Arr t n) : Enc.WF t n x.enc := by
  obtain ⟨v, h⟩ := x; cases v <;> first | exact h.2.2 | exact h.elim

-- Kept with no caller: the specification of `Arr` as a `List`, `Arr` the implementation, `List` for proofs.
/-- The vector is its header, its payload and its attribute: what a kernel matching `.vector t n e a` sees. -/
theorem val_eq (x : Arr t n) : x.1 = .vector t n x.enc x.attrCell := by
  obtain ⟨v, h⟩ := x; cases v <;> first | exact h.elim | (obtain ⟨rfl, rfl, -⟩ := h; rfl)

/-- `e` under the header `t`, `n` and the attribute `a`. -/
def mk (e : Enc) (h : Enc.WF t n e) (a : Option (UInt8 × IndexCell) := none) : Arr t n := ⟨.vector t n e a, rfl, rfl, h⟩

/-- A general list's payload is `gen` and holds its `n` elements. -/
theorem gen_size (x : Arr .general n) {xs : Array QValue} (hc : x.enc = .gen xs) : xs.size = n.toNat := by
  have hw := x.wf; rw [hc] at hw; exact hw

/-- Element `i`. At an atom type it is `Enc.get`'s atom at `i` read back at the index; the
    fallback, the atom of zero bits, is unreachable under `wf`, as is the general list's non-`gen` one. -/
def get (x : Arr t n) (i : Fin n.toNat) : El t :=
  match t, x with
  | .general, x => match hc : x.enc with
    | .gen xs => xs[i.1]'(by rw [gen_size x hc]; exact i.2)
    | _ => QValue.general #[] 0
  | t, x => ((Enc.get t n x.enc i).bind fun a => Carrier.of? t (.atom a)).getD default

/-- `get` at an atom type: `Enc.get`'s atom read back at `t`. -/
theorem get_ne (x : Arr t n) (i : Fin n.toNat) (h : t ≠ .general) :
    x.get i = ((Enc.get t n x.enc i).bind fun a => Carrier.of? t (.atom a)).getD default := by
  cases t <;> first | exact absurd rfl h | rfl

/-- The elements in position order, for proofs only. -/
def toList (x : Arr t n) : List (El t) := List.ofFn x.get

theorem length_toList (x : Arr t n) : x.toList.length = n.toNat := List.length_ofFn

-- Kept with no caller: the specification of `Arr` as a `List`, `Arr` the implementation, `List` for proofs.
theorem getElem_toList (x : Arr t n) (i : Nat) (h : i < x.toList.length) :
    x.toList[i] = x.get ⟨i, by rw [length_toList] at h; exact h⟩ := List.getElem_ofFn ..

/-- The list as a relation from its positions: `x i y ↔ x[j] = y` at the `j` with `Int64.ofNat j = i`. -/
def Holds (x : Arr t n) (i : Int64) (y : El t) : Prop := ∃ j : Fin n.toNat, Int64.ofNat j = i ∧ x.get j = y

theorem holds_iff_mem_zipIdx (x : Arr t n) (i : Int64) (y : El t) :
    x.Holds i y ↔ ∃ j, Int64.ofNat j = i ∧ (y, j) ∈ x.toList.zipIdx := by
  simp only [Holds, List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff, length_toList]
  constructor
  · rintro ⟨j, rfl, rfl⟩; exact ⟨j, rfl, j.2, by rw [getElem_toList]⟩
  · rintro ⟨j, rfl, h, rfl⟩; exact ⟨⟨j, h⟩, rfl, by rw [getElem_toList]⟩

/-- A kernel's answer as an `Arr`, the one way in: `WFAt` is decided (the header's two fields and
    `Enc.WF`), never assumed; `what` names the producer in the error. The vector is the kernel's, mark
    and all; a producer that knows an attribute applies it after. -/
def of (t : QAtomicType) (n : USize) (v : QValue) (what : String) : Except String (Arr t n) :=
  match v with
  | .vector t' n' e a => if h : t' = t ∧ n' = n ∧ Enc.WF t n e then .ok ⟨.vector t' n' e a, h⟩
    else .error s!"{what}: the kernel answered a payload that is not {n} well-formed elements of its type"
  | _ => .error s!"{what}: the kernel answered a value that is not a vector"

end Arr

/-- The group holding each of `n` positions under the offsets `o`: the last cut at or below it, `o bin til n`
    (`binBytes`). -/
def groupOf (o : ByteArray) (n : USize) : ByteArray := Kernel.binBytes 8 false true false o (Kernel.tilLongs n)

/-- `xs` as a dense long payload, eight bytes each: the literal columns of every module's checks. -/
def packLongs (xs : List Int64) : ByteArray := xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty

theorem packLongs_size (xs : List Int64) : (packLongs xs).size = 8 * xs.length := by
  suffices ∀ b : ByteArray, (xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) b).size = b.size + 8 * xs.length by
    simpa [packLongs] using this .empty
  induction xs with
  | nil => simp
  | cons x xs ih => intro b; rw [List.foldl_cons, ih, Column.pushBits_size, List.length_cons]; omega

/-- `encodeAt lg` records `lg` in its metadata: `foRMeta_reads` at the block widths `planBlock_bounds` caps
    at 64, the step `Verify.foRWF_encode` takes inside its proof. -/
theorem lgAt_encodeAt (lg : Nat) (hlg : lg < 2 ^ 64) (width : USize) (hw : width.toNat ≤ 8) (x : ByteArray)
    {patch : Bool} : Column.lgAt (Kernel.Coc.encodeAt lg width x patch).1 = lg := by
  have hKp : 0 < 2 ^ lg := Nat.two_pow_pos lg
  simp only [Kernel.Coc.encodeAt]
  generalize width.toNat = w at hw ⊢
  generalize x.size / w = n
  refine (Verify.foRMeta_reads lg hlg _ n _ fun b h => ?_).2.1
  simp only [Array.size_map, Array.size_range] at h
  simp only [Array.getElem_map, Verify.getElem_range]
  exact Nat.lt_of_le_of_lt (Verify.planBlock_bounds lg w n hw _ x b (Verify.mul_lt_of_lt_cdiv hKp h)).2.2.1
    (by decide)

/-- `encode`'s metadata passes `Enc.WF`'s `lgOk`: it is `encodeAt` at `Column.lgEnc`. -/
theorem lgOk_encode (width : USize) (hw : width.toNat ≤ 8) (x : ByteArray) :
    Column.lgOk (Kernel.Coc.encode width x).1 = true := by
  rw [Kernel.Coc.encode, Column.lgOk, lgAt_encodeAt _ (by decide) _ hw (patch := true)]; rfl

/-- A dense payload `b` of `n` longs Frame-of-Reference encoded is well formed at `n`: every long column the runtime
    builds (`longArr`), which `decide` cannot evaluate through `Coc.encode`. -/
theorem foRBytes_wf (b : ByteArray) {n : USize} (hn : b.size = 8 * n.toNat) : Enc.WF (X := Empty) .i64 n
    (.foR (Kernel.Coc.encode (8 : Nat).toUSize b).1 (Kernel.Coc.encode (8 : Nat).toUSize b).2) := by
  have h := Verify.nblk_encode Column.lgEnc (by decide) 8 (by decide) (by decide) b (patch := true)
  rw [hn] at h
  refine ⟨rfl, by simp, ?_, ?_⟩
  · show n.toNat ≤ Column.blk (Kernel.Coc.encodeAt Column.lgEnc (8 : Nat).toUSize b).1 *
      Column.nblk (Kernel.Coc.encodeAt Column.lgEnc (8 : Nat).toUSize b).1
    rw [h.1, h.2.1]; simp only [Column.lgEnc, Nat.reducePow]; omega
  · exact lgOk_encode _ (by rw [USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)]; exact Nat.le_refl 8) _

/-- Under `wf`, a long `bytes` column holds `b.size / 8` elements. -/
theorem Arr.n_long_bytes {m : USize} (x : Arr .i64 m) {b : ByteArray} (hc : x.enc = .bytes b) :
    b.size / 8 = m.toNat := by
  have hw := x.wf
  simp only [Enc.WF, hc, QAtomicType.width] at hw; omega

/-- Under `wf`, a long `bytes` column's element `i` is the eight bytes at `8i`, read as a long. -/
theorem Arr.get_long_bytes {m : USize} (x : Arr .i64 m) {b : ByteArray} (hc : x.enc = .bytes b) (i : Fin m.toNat) :
    x.get i = (Column.bitsAt b (i.1 * 8) 8).toInt64 := by
  rw [Arr.get_ne x i (by decide)]
  simp only [Enc.get, if_pos i.2, hc, QAtomicType.width]; rfl

-- Kept with no caller: the specification of `Arr` as a `List`, per payload form, `List` for proofs.
/-- Under `wf`, a long `bytes` column lists its eight-byte words, each read as a long. -/
theorem Arr.toList_long_bytes {m : USize} (x : Arr .i64 m) {b : ByteArray} (hc : x.enc = .bytes b) :
    x.toList = ((List.range m.toNat).map fun i => Column.bitsAt b (i * 8) 8).map UInt64.toInt64 := by
  apply List.ext_getElem (by rw [Arr.length_toList]; simp)
  intro i h1 h2
  rw [Arr.getElem_toList, Arr.get_long_bytes x hc]; simp

/-- `foRBits` with no hoisted table reads the start `blockStarts` holds (`blockStarts_get`), so
    `Column.get`'s `#[]` and the kernels' table are one decode. -/
theorem foRBits_starts (md pk : ByteArray) (i : Nat) :
    Column.foRBits md pk #[] i = Column.foRBits md pk (Column.blockStarts md) i := by
  have hs : (Column.blockStarts md).size = Column.nblk md + 1 := (Verify.blockStarts_fold md (Column.nblk md)).2.1
  unfold Column.foRBits
  by_cases h : i / Column.blk md ≤ Column.nblk md
  · simp [Verify.blockStarts_get md h]
  · simp [Array.getElem?_eq_none (show (Column.blockStarts md).size ≤ i / Column.blk md by omega)]

/-- Under `wf`, a long `foR` column's element `i` is its `foRBits` decode, read as a long. -/
theorem Arr.get_long_foR {m : USize} (x : Arr .i64 m) {md pk : ByteArray} (hc : x.enc = .foR md pk)
    (i : Fin m.toNat) : x.get i = (Column.foRBits md pk (Column.blockStarts md) i.1).toInt64 := by
  rw [Arr.get_ne x i (by decide), ← foRBits_starts]
  simp only [Enc.get, if_pos i.2, hc, QAtomicType.width]; rfl

/-- **The kernels' words are the elements**: element `i` of a long `foR` column is word `i` of `Enc.raw`, the word every
kernel reads (`foRWords`) and `Verify.wordsFoR_closed` says a kernel's answer reads back as, read as a long. -/
theorem Arr.get_raw_foR {m : USize} (x : Arr .i64 m) {md pk : ByteArray} (hc : x.enc = .foR md pk) (i : Fin m.toNat) :
    x.get i = ((Enc.raw .i64 m x.enc)[i.1]?.getD 0).toInt64 := by
  rw [Arr.get_long_foR x hc, hc, Verify.raw_foR .i64 8 rfl (by decide)]
  simp [i.2]

/-- A long payload's `n` words in position order: a `bytes` payload's eight-byte elements, a `foR` payload's
    `foRBits` decode. `none` at `alp`, whose decode has no law yet, and at the non-long constructors. -/
def longWords (n : USize) (e : Enc) : Option (List UInt64) :=
  match e with
  | .bytes b => some (Verify.elemsW 8 b)
  | .foR md pk => some ((List.range n.toNat).map (Column.foRBits md pk (Column.blockStarts md)))
  | _ => none

/-- Under `wf`, a long column lists its words, each read as a long: `toList_long_bytes` and the `foR` decode. -/
theorem Arr.toList_long {m : USize} (x : Arr .i64 m) {ws : List UInt64} (h : longWords m x.enc = some ws) :
    x.toList = ws.map UInt64.toInt64 := by
  unfold longWords at h
  cases hc : x.enc with
  | bytes b => rw [hc] at h; cases h; rw [Arr.toList_long_bytes x hc, Verify.elemsW, Arr.n_long_bytes x hc]
  | foR md pk =>
    rw [hc] at h; cases h
    apply List.ext_getElem (by rw [Arr.length_toList]; simp)
    intro i h1 h2; rw [Arr.getElem_toList, Arr.get_long_foR x hc]; simp
  | _ => all_goals (rw [hc] at h; cases h)

/-- Element `i` of a long column is word `i`, read as a long. -/
theorem Arr.get_long {m : USize} (x : Arr .i64 m) {ws : List UInt64} (h : longWords m x.enc = some ws)
    (i : Nat) (hi : i < m.toNat) (hw : i < ws.length) : x.get ⟨i, hi⟩ = ws[i].toInt64 := by
  rw [← Arr.getElem_toList x i (by rw [Arr.length_toList]; exact hi)]
  simp [Arr.toList_long x h]

/-- The dense payload a kernel reads off a long column that lists `longWords`: a `bytes` payload is
    itself, a `foR` one is handed over or decoded (`decodeW`) to the same words. -/
theorem Arr.dense_long {m : USize} (x : Arr .i64 m) {ws : List UInt64} (h : longWords m x.enc = some ws) :
    ∃ B, (x.enc = .bytes B ∨ ∃ md pk, x.enc = .foR md pk ∧
      B = Kernel.Coc.decode (8 : Nat).toUSize md pk m) ∧ Enc.bytesOf .i64 m x.enc = some B ∧
      Verify.elemsW 8 B = ws ∧ B.size / 8 = m.toNat := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  unfold longWords at h
  cases hc : x.enc with
  | bytes b =>
    rw [hc] at h; cases h
    exact ⟨b, .inl rfl, by simp only [Enc.bytesOf], rfl, Arr.n_long_bytes x hc⟩
  | foR md pk =>
    rw [hc] at h; cases h
    obtain ⟨hsz, hg⟩ := Verify.decodeW (8 : Nat).toUSize (by rw [h8]; decide) md pk m
    rw [h8] at hsz hg
    refine ⟨_, .inr ⟨md, pk, rfl, rfl⟩, by simp only [Enc.bytesOf, QAtomicType.width]; rfl,
      List.ext_getElem (by simp [Verify.elemsW, hsz]) fun i h1 _ => ?_, by rw [hsz]; omega⟩
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [hg i (by simpa [Verify.elemsW, hsz] using h1), Verify.ofNat_toNat_mod64]
  | _ => all_goals (rw [hc] at h; cases h)

/-- A dense long payload of `m` words Frame-of-Reference encoded lists them (`foRBits_encode_bits`). -/
theorem longWords_encode {m : USize} (b : ByteArray) (hm : b.size / 8 = m.toNat) :
    longWords m (.foR (Kernel.Coc.encode (8 : Nat).toUSize b).1 (Kernel.Coc.encode (8 : Nat).toUSize b).2) =
      some (Verify.elemsW 8 b) := by
  simp only [longWords, Verify.elemsW, ← hm]
  refine congrArg some (List.map_congr_left fun i hi => UInt64.toNat_inj.1 ?_)
  rw [← Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
  exact Verify.foRBits_encode_bits Column.lgEnc (by decide) 8 (by decide) (by decide) b i (List.mem_range.1 hi)

/-- A dense long answer lists its words whichever form `Enc.answer` leaves it in: dense, or encoded
    (`foRBits_encode_bits`). -/
theorem longWords_answer {m : USize} (b : ByteArray) (hm : b.size / 8 = m.toNat) :
    longWords m (Enc.answer .i64 m (.bytes b)) = some (Verify.elemsW 8 b) := by
  have ha : Enc.answer (X := Empty) .i64 m (.bytes b) = .bytes b ∨
      Enc.answer (X := Empty) .i64 m (.bytes b) =
      .foR (Kernel.Coc.encode (8 : Nat).toUSize b).1 (Kernel.Coc.encode (8 : Nat).toUSize b).2 := by
    simp only [Enc.answer, QAtomicType.width, show Column.alpEncodes .i64 = false from rfl,
      show Column.encodes .i64 = true from rfl, Kernel.Coc.encodeBelow]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  rcases ha with e | e
  · rw [e]; rfl
  · rw [e]; exact longWords_encode b hm

/-- A long column of `n` rows from the dense payload `b`: `Coc.encode` at 8 bytes, the encoder `wordsFoR` runs, so the
    column is `foR` where it is produced (decision M). A literal is packed and encoded here once; an old kernel's dense
    answer is encoded here at its exit, which goes with the old layer (W5). -/
def longArr {n : USize} (b : ByteArray) (h : b.size = 8 * n.toNat) : Arr .i64 n :=
  Arr.mk (.foR (Kernel.Coc.encode (8 : Nat).toUSize b).1 (Kernel.Coc.encode (8 : Nat).toUSize b).2) (foRBytes_wf b h)

/-- Element `i` of `longArr b` is the eight bytes at `8i`, read as a long, as `Arr.get_long_bytes` reads them. -/
theorem Arr.get_longArr {n : USize} (b : ByteArray) (h : b.size = 8 * n.toNat) (i : Fin n.toNat) :
    (longArr b h).get i = (Column.bitsAt b (i.1 * 8) 8).toInt64 := by
  rw [Arr.get_long _ (longWords_encode b (by omega)) i.1 i.2 (by simp [Verify.elemsW]; omega)]
  simp [Verify.elemsW]

/-- `longArr b` lists `b`'s eight-byte words, each read as a long. -/
theorem Arr.toList_longArr {n : USize} (b : ByteArray) (h : b.size = 8 * n.toNat) :
    (longArr b h).toList = ((List.range n.toNat).map fun i => Column.bitsAt b (i * 8) 8).map UInt64.toInt64 := by
  rw [Arr.toList_long _ (longWords_encode b (by omega)), Verify.elemsW, show b.size / 8 = n.toNat by omega]

/-- The column of `f` at the positions `0 … n-1`, packed by Lean with no kernel and no `List`: the reference
    beside a kernel whose count is checked. -/
def colFn (n : USize) (f : Fin n.toNat → Int64) : Arr .i64 n :=
  longArr ((Array.ofFn f).foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty) (by
    rw [← Array.foldl_toList]
    show (packLongs (Array.ofFn f).toList).size = 8 * n.toNat; rw [packLongs_size]; simp)

/-- `alpBits` with no hoisted table reads the start `blockStarts` holds, as `foRBits_starts`. -/
theorem alpBits_starts (md pk a : ByteArray) (i : Nat) :
    Column.alpBits md pk a #[] i = Column.alpBits md pk a (Column.blockStarts md) i := by
  unfold Column.alpBits; rw [foRBits_starts]

/-- A float column's words in position order, the bits each `float` holds: a `bytes` payload's eight-byte
    elements, an `alp` payload's `alpBits` decode. -/
def floatWords (n : USize) (e : Enc) : Option (List UInt64) :=
  match e with
  | .bytes b => some (Verify.elemsW 8 b)
  | .alp md pk a => some ((List.range n.toNat).map (Column.alpBits md pk a (Column.blockStarts md)))
  | _ => none

/-- Under `wf`, a float column lists its words. -/
theorem Arr.toList_float {m : USize} (x : Arr .f64 m) {ws : List UInt64} (h : floatWords m x.enc = some ws) :
    x.toList = ws := by
  unfold floatWords at h
  cases hc : x.enc with
  | bytes b =>
    rw [hc] at h; cases h
    have hb : b.size / 8 = m.toNat := by
      have hw := x.wf; simp only [Enc.WF, hc, QAtomicType.width] at hw; omega
    apply List.ext_getElem (by rw [Arr.length_toList, Verify.elemsW, List.length_map, List.length_range, hb])
    intro i h1 h2
    rw [Arr.length_toList] at h1
    rw [Arr.getElem_toList, Arr.get_ne x _ (by decide)]
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range, Enc.get, if_pos h1, hc, QAtomicType.width]
    rfl
  | alp md pk a =>
    rw [hc] at h; cases h
    apply List.ext_getElem (by rw [Arr.length_toList]; simp)
    intro i h1 h2
    rw [Arr.length_toList] at h1
    rw [Arr.getElem_toList, Arr.get_ne x _ (by decide)]
    simp only [List.getElem_map, List.getElem_range, Enc.get, if_pos h1, hc, QAtomicType.width, alpBits_starts]
    rfl
  | _ => all_goals (rw [hc] at h; cases h)

/-- The dense payload a kernel reads off a float column that lists `floatWords`: a `bytes` payload is
    itself, an `alp` one is decoded (`alpDecode64`) to the same words. -/
theorem Arr.dense_float {m : USize} (x : Arr .f64 m) {ws : List UInt64} (h : floatWords m x.enc = some ws) :
    ∃ B, (x.enc = .bytes B ∨ ∃ md pk a, x.enc = .alp md pk a ∧
      B = Kernel.Coc.alpDecode64 md pk a m) ∧ Verify.elemsW 8 B = ws ∧ B.size / 8 = m.toNat := by
  unfold floatWords at h
  cases hc : x.enc with
  | bytes b =>
    rw [hc] at h; cases h
    have hw := x.wf
    simp only [Enc.WF, hc, QAtomicType.width] at hw
    exact ⟨b, .inl rfl, rfl, by omega⟩
  | alp md pk a =>
    rw [hc] at h; cases h
    have e : Verify.elemsW 8 (Kernel.Coc.alpDecode64 md pk a m) =
        (Kernel.Coc.alpElems md pk a m).map fun v => UInt64.ofNat (v.toNat % 2 ^ (8 * 8)) :=
      Verify.elemsW_foldl_mod id 8 (by decide) (by decide) _
    rw [Kernel.Coc.alpElems, List.map_map, show 8 * 8 = 64 from rfl] at e
    refine ⟨_, .inr ⟨md, pk, a, rfl, rfl⟩, ?_, ?_⟩
    · rw [e]; exact List.map_congr_left fun i _ => Verify.ofNat_toNat_mod64 _
    · have := congrArg List.length e
      simpa [Verify.elemsW] using this
  | _ => all_goals (rw [hc] at h; cases h)

/-- A dense float answer lists its words whichever form `Enc.answer` leaves it in: dense, or ALP
    encoded (`alpBits_alpEncodeAt`, below `2³²` elements). -/
theorem floatWords_answer {m : USize} (b : ByteArray) (h32 : b.size / 8 < 2 ^ 32) (hm : b.size / 8 = m.toNat) :
    floatWords m (Enc.answer .f64 m (.bytes b)) = some (Verify.elemsW 8 b) := by
  have ha : Enc.answer (X := Empty) .f64 m (.bytes b) = .bytes b ∨
      Enc.answer (X := Empty) .f64 m (.bytes b) =
      .alp (Kernel.Coc.alpEncode64 b).1 (Kernel.Coc.alpEncode64 b).2.1 (Kernel.Coc.alpEncode64 b).2.2 := by
    simp only [Enc.answer, QAtomicType.width, show Column.alpEncodes .f64 = true from rfl,
      Kernel.Coc.alpEncodeBelow64]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  unfold floatWords
  rcases ha with e | e
  · rw [e]
  · rw [e]; simp only [Verify.elemsW, ← hm]
    exact congrArg some (List.map_congr_left fun i hi => (Verify.alpBits_alpEncodeAt false Column.lgEnc (by decide) 8 rfl b h32).2 i (List.mem_range.1 hi))

/-- An `int` answer column, dense or encoded, lists its payload's four-byte words: `longWords_answer` at
    width four, the `foR` form read back by `foRBits_encode_bits`. -/
theorem toList_answer_int {m : USize} (x : Arr .i32 m) {b : ByteArray} (hm : b.size / 4 = m.toNat)
    (hc : x.enc = Enc.answer .i32 m (.bytes b)) :
    x.toList = (List.range m.toNat).map fun i => (Column.bitsAt b (i * 4) 4).toUInt32.toInt32 := by
  have ha : Enc.answer (X := Empty) .i32 m (.bytes b) = .bytes b ∨
      Enc.answer (X := Empty) .i32 m (.bytes b) =
      .foR (Kernel.Coc.encode (4 : Nat).toUSize b).1 (Kernel.Coc.encode (4 : Nat).toUSize b).2 := by
    simp only [Enc.answer, QAtomicType.width, show Column.alpEncodes .i32 = false from rfl,
      show Column.encodes .i32 = true from rfl, Kernel.Coc.encodeBelow]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  apply List.ext_getElem (by rw [Arr.length_toList]; simp)
  intro i h1 _
  have hn : i < m.toNat := by rw [Arr.length_toList] at h1; omega
  rw [Arr.getElem_toList, List.getElem_map, List.getElem_range, Arr.get_ne x _ (by decide)]
  rw [← hc] at ha
  rcases ha with e | e <;> simp only [Enc.get, if_pos hn, e, QAtomicType.width]
  · rfl
  · have hi : i < b.size / 4 := by omega
    show (Column.foRBits _ _ #[] i).toUInt32.toInt32 = _
    rw [foRBits_starts]
    congr 1
    apply UInt32.toNat_inj.1
    rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, Kernel.Coc.encode, Verify.foRBits_encode_bits Column.lgEnc (by decide) 4 (by decide) (by decide) b i hi,
      Nat.mod_eq_of_lt (Verify.bitsAt_lt _ _ _ (by decide))]

/-- Reading a word as a long loses nothing. -/
theorem toInt64_inj {x y : UInt64} (h : x.toInt64 = y.toInt64) : x = y := by
  simpa using congrArg Int64.toUInt64 h

/-- A boolean column's bitmap: `boolBits` reads one off the one form `Enc.WF .u1` admits, a `u1` `foR`. -/
def Alg.tagBits {n : USize} (x : Arr .u1 n) : ByteArray :=
  (Kernel.boolBits .u1 n x.enc).get (by
    have hw := x.wf; revert hw; cases x.enc <;> simp [Enc.WF, Kernel.boolBits])

/-- A boolean column's payload reads as its bitmap `tagBits`. -/
theorem Alg.enc_tagBits {n : USize} (x : Arr .u1 n) : Kernel.boolBits .u1 n x.enc = some (Alg.tagBits x) :=
  (Option.some_get _).symm

/-- Under `Enc.WF`, a boolean payload's element `j` is bit `j` of the bitmap `boolBits` reads: a
    `u1` `foR` element is `0` or `1`, so its low bit, which `bitsOfFoR` keeps, is whether it is nonzero. -/
theorem get_boolBits {n : USize} {e : Enc} (hw : Enc.WF .u1 n e) {b : ByteArray}
    (ht : Kernel.boolBits .u1 n e = some b) {j : Nat} (hj : j < n.toNat) :
    Enc.get .u1 n e j = some (.u1 (Column.bitAt b j)) := by
  revert ht hw
  cases e <;> simp only [Kernel.boolBits, Enc.WF, reduceCtorEq, false_implies, true_implies, implies_true, Option.some.injEq]
  · rename_i md pk
    rintro ⟨-, hl, hn, -⟩ rfl
    have h2 := hl j hj
    have hb : j < Column.blk md * Column.nblk md := Nat.lt_of_lt_of_le hj hn
    simp only [Enc.get, if_pos hj, QAtomicType.width, Kernel.bitsOfFoR, Verify.bitAt_packOf _ _ _ hj,
      foRBits_starts, decide_eq_true hb, Bool.true_and]
    generalize Column.foRBits md pk (Column.blockStarts md) j = v at h2
    rcases (show v.toNat = 0 ∨ v.toNat = 1 by omega) with h | h
    · obtain rfl : v = 0 := UInt64.toNat_inj.1 h; rfl
    · obtain rfl : v = 1 := UInt64.toNat_inj.1 h; rfl

/-- A boolean column's element `i` is bit `i` of its bitmap (`get_boolBits`). -/
theorem Arr.get_bool_bits {m : USize} (x : Arr .u1 m) {b : ByteArray}
    (ht : Kernel.boolBits .u1 m x.enc = some b) (i : Fin m.toNat) : x.get i = Column.bitAt b i.1 := by
  rw [Arr.get_ne x i (by decide), get_boolBits x.wf ht i.2]; rfl

/-- `Coc.bools` at a count `n` is a well formed boolean column of `n` rows: each element `0` or `1`
    (`foRBits_bools`), its blocks covering `n`, its `lg` the encoder's. -/
theorem wf_bools {X : Type} {n : USize} (p : Nat → Bool) :
    Ext.Enc.WF .u1 n (.foR (Kernel.Coc.bools n.toNat p).1 (Kernel.Coc.bools n.toNat p).2 : Ext.Enc X) := by
  have h1 : USize.ofNat32 1 (by decide) = (1 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp [h])
  obtain ⟨hs, -⟩ := Verify.packIds_bytes 1 n.toNat (fun i => (p i).toNat) (by decide) (by decide)
  simp only [Nat.mul_one] at hs
  obtain ⟨hn, hk, -⟩ := Verify.nblk_encode Column.lgEnc (by decide) 1 (by decide) (by decide)
    (Column.packIds 8 n.toNat fun i => (p i).toNat) (patch := false)
  refine ⟨rfl, fun _ i hi => ?_, ?_, ?_⟩
  · rw [foRBits_bools _ _ hi]; cases p i <;> decide
  · rw [show Kernel.Coc.bools n.toNat p = _ from congrArg (fun w => Kernel.Coc.encodeAt Column.lgEnc w _ false) h1, hn, hk, hs]
    simp only [Nat.div_one, Nat.one_mul, Column.lgEnc, Nat.reducePow]; omega
  · rw [Kernel.Coc.bools, Column.lgOk, lgAt_encodeAt Column.lgEnc (by decide) (USize.ofNat32 1 (by decide)) (by simp)]; rfl

/-- **A boolean writer's column reads as its bitmap**: `boolBits` of `Coc.bools n` of a `packOf n f`'s bits is that
    `packOf`. Every writer's bitmap body (`cmpBitmap`, `bitBitmap`, `member*Bitmap`) is a `packOf`, so this one read
    serves them all, and `get_boolBits` then reads the column's elements off the bitmap's `*_bitAt` lemma. -/
theorem boolBits_bools {n : USize} (f : Nat → Bool) :
    Kernel.boolBits .u1 n (.foR (Kernel.Coc.bools n.toNat (Column.bitAt (Kernel.packOf n.toNat f))).1
      (Kernel.Coc.bools n.toNat (Column.bitAt (Kernel.packOf n.toNat f))).2 : Enc) = some (Kernel.packOf n.toNat f) := by
  have hb := (wf_bools (X := Unit) (n := n) (Column.bitAt (Kernel.packOf n.toNat f))).2.2.1
  have hf : ∀ i < n.toNat, Column.bitAt (Kernel.packOf n.toNat f) i = f i := fun i hi => Verify.bitAt_packOf _ _ _ hi
  generalize Column.bitAt (Kernel.packOf n.toNat f) = P at hb hf ⊢
  simp only [Kernel.boolBits, Kernel.bitsOfFoR, Option.some.injEq]
  -- `packOf` reads `f` only below `n`, where the column's element is `f`'s bit
  have e : ∀ g : Nat → Bool, Kernel.packOf n.toNat g = Kernel.packOf n.toNat fun i => decide (i < n.toNat) && g i :=
    fun g => by simp only [Kernel.packOf, Bool.and_self_left]
  rw [e, e f]; congr 1; funext i
  by_cases hi : i < n.toNat
  · simp only [hi, decide_true, Bool.true_and, foRBits_bools _ _ hi, hf i hi, decide_eq_true (Nat.lt_of_lt_of_le hi hb)]
    cases f i <;> decide
  · simp [hi]

/-- **A boolean writer's column, bit by bit**: below `n`, the bitmap `boolBits` reads off `Coc.bools` of `n` rows is
    the predicate it encodes (`foRBits_bools`). Every writer's `*_bitAt` lemma states its predicate; this composes. -/
theorem bitAt_bools {N : Nat} {n : USize} (p : Nat → Bool) (hN : N = n.toNat) {i : Nat} (hi : i < n.toNat) :
    Column.bitAt (Kernel.bitsOfFoR (Kernel.Coc.bools N p).1 (Kernel.Coc.bools N p).2 n) i = p i := by
  subst hN
  have hb := Nat.lt_of_lt_of_le hi (wf_bools (X := Unit) (n := n) p).2.2.1
  simp only [Kernel.bitsOfFoR, Verify.bitAt_packOf _ _ _ hi, foRBits_bools _ _ hi, hb, decide_true, Bool.true_and]
  cases p i <;> decide

/-- **A bitmap kernel's answer, read back**: element `j < n` of the column `Coc.boolsOf n g` writes is bit `j` of
    `g` (`get_boolBits`, `bitAt_bools`). -/
theorem get_boolsOf {n : USize} (g : ByteArray) {j : Nat} (hj : j < n.toNat) :
    Enc.get .u1 n (.foR (Kernel.Coc.boolsOf n g).1 (Kernel.Coc.boolsOf n g).2 : Enc) j =
      some (.u1 (Column.bitAt g j)) := by
  show Enc.get .u1 n
    (.foR (Kernel.Coc.bools n.toNat (Column.bitAt g)).1 (Kernel.Coc.bools n.toNat (Column.bitAt g)).2) j = _
  rw [get_boolBits (wf_bools (Column.bitAt g)) rfl hj, bitAt_bools _ rfl hj]

/-- The boolean column of the `n` booleans `p`, as every boolean writer lays it out (`Coc.bools`). -/
def Arr.bools (n : USize) (p : Nat → Bool) : Arr .u1 n :=
  Arr.mk (.foR (Kernel.Coc.bools n.toNat p).1 (Kernel.Coc.bools n.toNat p).2) (wf_bools p)

theorem Ext.Enc.blank_WF {X : Type} (t : QAtomicType) (n : USize) : Ext.Enc.WF t n (Ext.Enc.blank (X := X) t n) := by
  cases t
  case u1 => exact wf_bools fun _ => false
  case sym =>
    have h0 : ∀ k, (Array.replicate (n.toNat + 1) 0)[k]! = 0 := fun k => by
      by_cases hk : k < n.toNat + 1
      · rw [getElem!_pos _ k (by simpa using hk)]; simp
      · rw [getElem!_neg _ k (by simpa using hk)]; rfl
    show (Array.replicate (n.toNat + 1) 0).size = n.toNat + 1 ∧
      SymsWF ByteArray.empty (Array.replicate (n.toNat + 1) 0) ∧
      ∀ i < n.toNat, (Column.symKey ByteArray.empty (Array.replicate (n.toNat + 1) 0) i).IsValidUTF8
    -- every entry is the empty bytes, which are valid
    exact ⟨by simp, ⟨by simp, h0 0, by rw [h0]; rfl, fun k _ => by rw [h0]; exact Nat.zero_le _,
      fun k _ => by rw [h0, h0]; exact Nat.le_refl _⟩,
      fun i _ => by simp only [Column.symKey, Column.symBytes, h0]; split <;> decide⟩
  all_goals simp [Ext.Enc.blank, Ext.Enc.WF, QAtomicType.width, ByteArray.size]

namespace Column
open Ext.Enc

/-- What `ofAtoms` builds is well formed: its header is the atoms' type and count, and each layout
holds exactly that many. Here, after `wf_bools`, because a boolean is a `u1` `foR`. -/
theorem ofAtoms_WF {X : Type} {t : QAtomicType} {as : Array QAtom} {e : Ext.Enc X} {hn : t ≠ .general}
    (h : ∀ a ∈ as, a.type = t) (hc : ofAtoms t as hn = some e) (hs : as.size < USize.size) :
    WF t as.size.toUSize e := by
  unfold ofAtoms at hc
  rw [if_pos (Array.all_eq_true'.mpr fun x hx => by simp [h x hx])] at hc
  have h0 : ∀ k, (ByteArray.emptyWithCapacity k).size = 0 := fun _ =>
    ByteArray.size_eq_zero_iff.mpr rfl
  match t, hn, h, hc with
  | .general, hn, _, _ => exact absurd rfl hn
  | .u1, _, _, hc =>
    cases hc
    have := wf_bools (X := X) (n := as.size.toUSize) fun i => (as[i]?.map boolOf).getD false
    rwa [USize.toNat_ofNat_of_lt' hs] at this
  | .sym, _, _, hc =>
    cases hc
    unfold WF; rw [USize.toNat_ofNat_of_lt' hs]
    show ((as.map utf8Of).foldl offStep (#[0], 0)).1.size = as.size + 1 ∧
      SymsWF ((as.map utf8Of).foldl blobStep ByteArray.empty) ((as.map utf8Of).foldl offStep (#[0], 0)).1 ∧
      ∀ i < as.size, (symKey ((as.map utf8Of).foldl blobStep ByteArray.empty)
        ((as.map utf8Of).foldl offStep (#[0], 0)).1 i).IsValidUTF8
    rw [← Array.foldl_toList blobStep, ← Array.foldl_toList offStep]
    refine ⟨by rw [foldl_offStep_size]; simp <;> omega, symsWF_folds _, fun i hi => ?_⟩
    -- every entry is a `String`'s `toUTF8`, or the empty bytes for a non-symbol
    rw [symKey_folds _ i (by simpa using hi), getElem!_pos _ i (by simpa using hi), Array.getElem_toList,
      Array.getElem_map]
    cases as[i] <;> first | exact String.isValidUTF8 _ | exact (by decide : ByteArray.empty.IsValidUTF8)
  | .u8, _, _, hc | .char, _, _, hc | .i16, _, _, hc | .i32, _, _, hc | .i64, _, _, hc
  | .f32, _, _, hc | .f64, _, _, hc | .i8, _, _, hc | .date, _, _, hc | .datetime, _, _, hc =>
    cases hc
    unfold WF; rw [USize.toNat_ofNat_of_lt' hs]
    simp only [WF, QAtomicType.width]
    rw [← Array.foldl_toList, foldl_pushBits_size, h0]; simp <;> omega

end Column

/-- The `str` bridge: bytes that are some string's UTF-8, read as a string the way `Column.get` reads a
    symbol (`fromUTF8?`, `""` at invalid bytes), write back out as themselves. -/
theorem str_bytes {B : ByteArray} (h : ∃ s : String, s.toUTF8.data.toList = B.data.toList) :
    ((String.fromUTF8? B).getD "").toUTF8.data.toList = B.data.toList := by
  obtain ⟨s, hs⟩ := h
  obtain rfl : s.toByteArray = B := ByteArray.ext (Array.ext' hs)
  simp only [String.fromUTF8?, s.isValidUTF8, dite_true, Option.getD_some]
  rfl

/-- A symbol payload's element `i`, read as `Enc.get` reads it, writes out as `symsOf`'s symbol `i`
    wherever that symbol is UTF-8. -/
theorem get_sym_bytes {n : USize} {e : Enc} {i : Nat} (d : String) (hw : Enc.WF .sym n e)
    (hi : i < n.toNat) (h2 : i < (Verify.symsOf n.toNat e).length)
    (hk : ∃ s : String, s.toUTF8.data.toList = (Verify.symsOf n.toNat e)[i]) :
    (((Enc.get .sym n e i).bind fun a => Carrier.of? (X := Empty) .sym (.atom a)).getD d).toUTF8.data.toList = (Verify.symsOf n.toNat e)[i] := by
  cases e with
  | syms b o =>
    rw [show Enc.get (X := Empty) .sym n (.syms b o) i = some (.sym ((String.fromUTF8? (Column.symKey b o i)).getD ""))
      by simp only [Enc.get, if_pos hi]; rfl]
    simp only [Option.bind_some, Carrier.of?, Option.getD_some, Verify.symsOf, List.getElem_map,
      List.getElem_range, Verify.symAt] at hk ⊢
    exact str_bytes hk
  | enum d o ids =>
    rw [show Enc.get (X := Empty) .sym n (.enum d o ids) i = some (.sym ((String.fromUTF8?
      (Column.symKey d o (Column.idAt ids (Column.idWidth o) i))).getD "")) by simp only [Enc.get, if_pos hi]; rfl]
    simp only [Option.bind_some, Carrier.of?, Option.getD_some, Verify.symsOf, List.getElem_map,
      List.getElem_range, Verify.symAt] at hk ⊢
    exact str_bytes hk
  | _ => all_goals first | exact (show False from hw).elim | exact absurd hw.1 (by decide)

/-- Under `wf`, a symbol column whose symbols are UTF-8 lists them: each element's bytes are `symsOf`'s
    symbol at its position, a blob's own or an interned column's dictionary entry. -/
theorem Arr.toList_sym {m : USize} (x : Arr .sym m)
    (hu : ∀ k ∈ Verify.symsOf m.toNat x.enc, ∃ s : String, s.toUTF8.data.toList = k) :
    x.toList.map (·.toUTF8.data.toList) = Verify.symsOf m.toNat x.enc := by
  have hw := x.wf
  have hl : (Verify.symsOf m.toNat x.enc).length = m.toNat := by
    revert hw; generalize x.enc = e; intro hw
    cases e <;> simp_all [Enc.WF, QAtomicType.width, Verify.symsOf] <;> omega
  refine List.ext_getElem (by rw [List.length_map, Arr.length_toList, hl]) fun i h1 h2 => ?_
  rw [List.length_map, Arr.length_toList] at h1
  rw [List.getElem_map, Arr.getElem_toList, Arr.get_ne x _ (by decide)]
  exact get_sym_bytes _ hw h1 h2 (hu _ (List.getElem_mem h2))

/-- A long payload as dense bytes: `bytes` as it is, `foR` decoded once (`Coc.decode`). -/
def longBytes (n : USize) (e : Enc) : Option ByteArray :=
  match e with
  | .bytes b => some b
  | .foR md pk => some (Kernel.Coc.decode 8 md pk n)
  | _ => none

/-- A side of a relation: an atomic type, a product of sides, or an array of a side. A tree, so
    `Vals (.atom t)` is `Arr t` itself and every one-column path is unchanged. A `arr b` element is an
    ARRAY of `b`: its order and multiplicity are part of the value. -/
inductive Obj
  | atom (t : QAtomicType)
  | prod (a b : Obj)
  | arr (b : Obj)
  | sum (a b : Obj)

instance : Coe QAtomicType Obj := ⟨.atom⟩

/-- The atoms the verbs name, so `.long` reads the same at `Obj` as at `QAtomicType`. -/
@[match_pattern, reducible] def Obj.long : Obj := .atom .i64
@[match_pattern, reducible] def Obj.general : Obj := .atom .general

/-- An element of a side: a tuple of its atoms' elements. -/
@[reducible] def Obj.El : Obj → Type
  | .atom t => Carrier t
  | .prod a b => a.El × b.El
  | .arr b => List b.El
  | .sum a b => Sum a.El b.El

/-- The element a row reads where its side holds no value at all (a side of `0` values), the one position no
    clamp can land in: what a gather past the side reads — an atom's `default` (q's null), an empty array, a
    sum's `inl` of its left side's own. -/
def Obj.dflt : (A : Obj) → A.El
  | .atom _ => default
  | .prod a b => (a.dflt, b.dflt)
  | .arr _ => []
  | .sum a _ => .inl a.dflt

/-- `n` values of `A`, one column per atom, side by side (struct of arrays): nothing boxed. A `arr b`
    column is one flat payload of `m` values of `b` and two long columns `lo`, `hi`: row `i` is the slice
    `[lo i, hi i)` of the payload, so picking rows gathers `lo` and `hi` and copies no flat value. A `sum a b`
    column is a tag and a position per row into one of two payloads, `l` values of `a` (tag `false`) and `r`
    of `b` (tag `true`): picking rows gathers the tag and the position and copies no value. -/
@[reducible] def Vals : Obj → USize → Type
  | .atom t, n => Arr t n
  | .prod a b, n => Vals a n × Vals b n
  | .arr b, n => (m : USize) × Arr .i64 n × Arr .i64 n × Vals b m
  | .sum a b, n => (l : USize) × (r : USize) × Arr .u1 n × Arr .i64 n × Vals a l × Vals b r

/-- The position `k` clamped into `[0, m)`: the nearest position of a side of `m > 0` values. -/
def clampFin (k : Int64) (m : Nat) (h : 0 < m) : Fin m :=
  ⟨min (max k.toInt 0).toNat (m - 1), Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

/-- The value at row `i`, read across the columns. An array row is its slice clamped to `[0, m)`, so every
    `lo`, `hi` reads as an array. A sum row is its side's value at its position clamped into the side, so
    every position reads as a value of its side; a side of no values reads that side's `Obj.dflt`, the null a
    gather past the side reads, so the row keeps its tag. -/
def Vals.row : {A : Obj} → {n : USize} → Vals A n → Fin n.toNat → A.El
  | .atom _, _, x, i => Arr.get x i
  | .prod _ _, _, x, i => (Vals.row x.1 i, Vals.row x.2 i)
  | .arr _, _, ⟨m, lo, hi, f⟩, i => (List.finRange m.toNat).filterMap fun (j : Fin m.toNat) =>
      if (lo.get i).toInt ≤ (j.1 : Int) ∧ (j.1 : Int) < (hi.get i).toInt then some (Vals.row f j) else none
  | .sum a b, _, ⟨l, r, tag, idx, x, y⟩, i =>
    if tag.get i then .inr (if h : 0 < r.toNat then Vals.row y (clampFin (idx.get i) r.toNat h) else b.dflt)
    else .inl (if h : 0 < l.toNat then Vals.row x (clampFin (idx.get i) l.toNat h) else a.dflt)

-- Kept with no caller: an atom side's row is the `Arr`'s element, the `List` reading of a side.
@[simp] theorem Vals.row_atom {t : QAtomicType} {n : USize} (x : Arr t n) (i : Fin n.toNat) :
    Vals.row (A := .atom t) x i = x.get i := rfl

/-- A relation from `k` to `v`: `n` positions, a key and a value at each — q's dict, two arrays at atoms,
    one column per atom of a product side, so `B×C` stored as two columns IS one side of pairs. -/
structure Tab (k v : Obj) where
  n : USize
  key : Vals k n
  val : Vals v n

namespace Tab

variable {k v : Obj}

/-- The relation `R` denotes: `R x y ↔ ∃ i, key.row i = x ∧ val.row i = y`. -/
def Holds (R : Tab k v) (x : k.El) (y : v.El) : Prop := ∃ i, R.key.row i = x ∧ R.val.row i = y

/-- The pairs, in position order, for proofs only. -/
def toList (R : Tab k v) : List (k.El × v.El) := List.ofFn fun i => (R.key.row i, R.val.row i)

-- Kept with no caller: what a `Rel` holds, read off its `List` of pairs.
theorem holds_iff_mem_toList (R : Tab k v) (x : k.El) (y : v.El) : R.Holds x y ↔ (x, y) ∈ R.toList := by
  simp [Holds, toList, List.mem_ofFn]

end Tab

/-! ## Payload helpers on qlean kernels -/

section Payload

open Rel.Kernel

/-- One long as an eight-byte payload: the atom operand of an `av`/`va` kernel call. -/
def one (v : UInt64) : ByteArray := Column.pushBits .empty v 8

theorem bitsAt_one (v : UInt64) : Column.bitsAt (one v) 0 8 = v := by
  simpa using Verify.bitsAt_pushBits8 ByteArray.empty v

/-- `Ew.cmp`'s `u1` `foR` read through `boolBits` (its `foR` branch, `bitsOfFoR`): the bitmap a bitmap consumer
    (`whereBits`, `Ew.notBits`) takes, one name for the read so no consumer restates it. -/
def Ew.cmpBits (op cls shape : UInt8) (a b : ByteArray) (n : USize) : ByteArray :=
  let c := Ew.cmp op cls shape a b n; bitsOfFoR c.1 c.2 n

/-- `Ew.bit`'s `u1` `foR` read through `boolBits`, as `Ew.cmpBits` reads `Ew.cmp`'s. -/
def Ew.bitBits (op shape : UInt8) (a b : ByteArray) (n : USize) : ByteArray :=
  let c := Ew.bit op shape a b n; bitsOfFoR c.1 c.2 n

/-- `Ew.cmpBits` is the bitmap `cmpBitmap`, whose bits `Verify.cmp_bitAt` states (`boolBits_bools`). -/
theorem Ew.cmpBits_eq (op cls shape : UInt8) (a b : ByteArray) (n : USize) :
    Ew.cmpBits op cls shape a b n = Ew.cmpBitmap op cls shape a b n :=
  Option.some.inj (boolBits_bools (n := n) fun i =>
    Ew.cmpStep op cls (Ew.elem cls a (Ew.shapeIdx shape i).1) (Ew.elem cls b (Ew.shapeIdx shape i).2))

/-- `Ew.bitBits` is the bitmap `bitBitmap`, whose bits `Verify.Ew.bit_bitAt` states (`boolBits_bools`). -/
theorem Ew.bitBits_eq (op shape : UInt8) (a b : ByteArray) (n : USize) :
    Ew.bitBits op shape a b n = Ew.bitBitmap op shape a b n :=
  Option.some.inj (boolBits_bools (n := n) fun i =>
    Ew.bitStep op (Column.bitAt a (Ew.shapeIdx shape i).1) (Column.bitAt b (Ew.shapeIdx shape i).2))

/-- `~` on `m` bits: `Ew.bit` xor a ones mask, the mask a one-bit atom in shape `av` (xor is `≠` on bits). -/
def Ew.notBits (m : USize) (b : ByteArray) : ByteArray := Ew.bitBits (Ew.bitCmp + Ew.ne) Ew.av ⟨#[1]⟩ b m

end Payload

/-! ## Sanity checks on small literal columns -/

section Checks

open Rel.Column

/-- `Enc.WF` of a literal payload at a literal `USize` count: `decide` cannot reduce `USize.toNat` of a
    numeral, so the count is read as a `Nat` numeral first. -/
macro "wf_lit" : tactic => `(tactic| (unfold Enc.WF; simp only [USize.reduceToNat, QAtomicType.width]; decide))
/-- A literal count below `2³²` fits a `USize` on every platform (`USize.le_size`). -/
macro "fits_lit" : tactic => `(tactic| (refine Nat.lt_of_lt_of_le ?_ USize.le_size; simp))

private def l3 : Arr .i64 3 := Arr.mk (.bytes <| packLongs [7, -1, 42]) (by wf_lit)
#guard l3.toList == [7, -1, 42]

private def bs : Arr .u1 3 := Arr.bools 3 (Column.bitAt ⟨#[0b101]⟩)
#guard bs.toList == [true, false, true]

-- one symbol column, as `syms` and as `enum` over the dictionary `a, bc`
private def blob : ByteArray := ByteArray.mk #[97, 0, 98, 99, 0]
private def ss : Arr .sym 3 := Arr.mk (.syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8]) (by wf_lit)
private def es : Arr .sym 3 :=
  Arr.mk (.enum blob #[0, 2, 5] (packIds (idWidth #[0, 2, 5]) 3 fun i => [1, 0, 1][i]!)) (by wf_lit)
#guard ss.toList == ["bc", "a", "bc"]
#guard es.toList == ss.toList

private def gs : Arr .general 2 := Arr.mk (.gen #[(.atom (.i64 1) : QValue), (.general #[] 0 : QValue)]) (by unfold Enc.WF; simp only [USize.reduceToNat]; rfl)
#guard match id (α := QValue) (gs.get ⟨0, by simp⟩), id (α := QValue) (gs.get ⟨1, by simp⟩) with | .atom (.i64 1), .general #[] _ _ => true | _, _ => false

#guard ss.toList.zipIdx == [("bc", 0), ("a", 1), ("bc", 2)]
example : ss.Holds 1 "a" := ⟨⟨1, by simp⟩, rfl, by simp only [Arr.get_ne _ _ (show QAtomicType.sym ≠ .general by decide), Enc.get, USize.reduceToNat]; decide⟩

end Checks

#print axioms Arr.get
#print axioms Tab.holds_iff_mem_toList

end Rel
