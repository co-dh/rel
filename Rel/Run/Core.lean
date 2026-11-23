/-
  The RelRep core: a relation is a key and a value column of one length `n` over the positions
  `0 … n-1`, `R x y ↔ ∃ i, key.get i = x ∧ val.get i = y` — a tabulation, `key° ≫ val = R`.
  Columns are qlean's `Column`s in whatever encoding carries them; an element is read through
  `Column.get` (qlean's one-element reader over `bitsAt`/`bitAt`/`foRBits`), never
  `Column.atoms`. Lists exist in proofs only (`toList`).
-/
import Rel.Kernel.Dep.Monadic
import Rel.KernelSpec.Alp
import Rel.KernelSpec.SymFind
import Rel.KernelSpec.Gather
import Rel.KernelSpec.Closure

open Rel.Ext

namespace Rel

open Rel Rel.Dep

/-- The row count from which `expandNote` warns. -/
def expandWarnRows : Nat := 1000000

/-- `expandNote`'s code: `k ()`, after a line on stderr where `rows` reaches `expandWarnRows`. -/
def expandNoteImpl {α : Type u} (what : String) (rows : Nat) (k : Unit → α) : α :=
  if expandWarnRows ≤ rows then dbgTrace s!"rel: warning: {what} expanded to {rows} rows" k else k ()

/-- The one place the run path turns a form that is not rows — a bit matrix (`Tab.ofBits`), a product of value sets
    (`Vals.cross`: `⊤`, a universe of a product), the groups of a composition (`expand`) — into `rows` rows. It is
    `k ()`; its code (`expandNoteImpl`) also warns past `expandWarnRows`, so an expansion cannot slow a program
    silently. Reducible, so a proof about a body that calls it reads `k ()` and never names it. -/
@[reducible, implemented_by expandNoteImpl]
def expandNote {α : Type u} (what : String) (rows : Nat) (k : Unit → α) : α := k ()

/-- An element of a column of type `t`: qlean's `Carrier`, a `QValue` in a general list. -/
abbrev El := Carrier

/-- A vector of `n` elements of type `t`: the encoded column itself, `Enc.WF` saying it holds `n` elements of `t`
    (`t` and `n` live in the type, never in a header beside the payload); a general list is `.gen xs`. Its payload
    holds no flagged block (`Kernel.hasNul`): an `Arr t n` is the atom object `t`, and only `t+1` holds the in-band
    null (design card "atom+1", decision K). -/
abbrev Arr (t : QAtomicType) (n : USize) := {e : Enc // Enc.WF t n e ∧ Kernel.hasNul e = false}

namespace Arr

variable {t : QAtomicType} {n : USize}

/-- The payload. -/
def enc (x : Arr t n) : Enc := x.1

/-- The payload agrees with the type. -/
theorem wf (x : Arr t n) : Enc.WF t n x.enc := x.2.1

/-- The payload holds no null: no block is flagged. -/
theorem plain (x : Arr t n) : Kernel.hasNul x.enc = false := x.2.2

/-- `e` as a column of `n` elements of `t`. -/
def mk (e : Enc) (h : Enc.WF t n e) (hN : Kernel.hasNul e = false) : Arr t n := ⟨e, h, hN⟩

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


-- Kept with no caller: the specification of `Arr` as a `List`, `Arr` the implementation, `List` for proofs.

/-- The list as a relation from its positions: `x i y ↔ x[j] = y` at the `j` with `Int64.ofNat j = i`. -/
def Holds (x : Arr t n) (i : Int64) (y : El t) : Prop := ∃ j : Fin n.toNat, Int64.ofNat j = i ∧ x.get j = y


/-- A payload as an `Arr`, the one way in: `Enc.WF` is decided, never assumed; `what` names the producer in the
    error. -/
def of (t : QAtomicType) (n : USize) (e : Enc) (what : String) : Except String (Arr t n) :=
  if h : Enc.WF t n e then
    if hN : Kernel.hasNul e = false then .ok ⟨e, h, hN⟩
    else .error s!"{what}: a column holding a null, and its type has none"
  else .error s!"{what}: a payload that is not {n} well-formed elements of {repr t}"

end Arr


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
  simp only [Kernel.Coc.encodeAt, Nat.one_shiftLeft]
  generalize width.toNat = w at hw ⊢
  generalize x.size / w = n
  refine (Verify.foRMeta_reads lg hlg _ n _ fun b h => ?_).2.1
  simp only [Array.size_map, Array.size_range] at h
  simp only [Array.getElem_map, Verify.getElem_range]
  exact Nat.lt_of_le_of_lt (Verify.planBlock_bounds lg w n _ x b (Verify.mul_lt_of_lt_cdiv hKp h)).2.1
    (by decide)

/-- `encode`'s metadata passes `Enc.WF`'s `lgOk`: it is `encodeAt` at `Column.lgEnc`. -/
theorem lgOk_encode (width : USize) (hw : width.toNat ≤ 8) (x : ByteArray) :
    Column.lgOk (Kernel.Coc.encode width x).1 = true := by
  rw [Kernel.Coc.encode, Column.lgOk, lgAt_encodeAt _ (by decide) _ hw (patch := true)]; rfl

/-- A dense payload `b` of `n` elements of a fixed-width type `t` other than `u1`, `w` bytes each, Frame-of-Reference
    encoded at `w` is well formed at `n`: every such column the runtime builds (`Arr.ofBytes`), which `decide` cannot
    evaluate through `Coc.encode`. -/
theorem foRBytes_wf {X : Type} (t : QAtomicType) (hu : t ≠ .u1 ∧ t.width.isSome) (b : ByteArray) {n : USize}
    (hn : b.size = t.width.getD 0 * n.toNat) : Enc.WF (X := X) t n
    (.foR (Kernel.Coc.encode (t.width.getD 0).toUSize b).1 (Kernel.Coc.encode (t.width.getD 0).toUSize b).2) := by
  have hw : 0 < t.width.getD 0 ∧ t.width.getD 0 ≤ 8 := by cases t <;> simp [QAtomicType.width] at hu ⊢
  have h := Verify.nblk_encode Column.lgEnc (by decide) _ hw.1 hw.2 b (patch := true) (nul := .empty)
  rw [hn, Nat.mul_div_cancel_left _ hw.1] at h
  have hk : n.toNat ≤ Column.blk (Kernel.Coc.encodeAt Column.lgEnc (t.width.getD 0).toUSize b).1 *
      Column.nblk (Kernel.Coc.encodeAt Column.lgEnc (t.width.getD 0).toUSize b).1 := by
    rw [h.1, h.2.1]; simp only [Column.lgEnc, Nat.reducePow]; omega
  have hl := lgOk_encode (t.width.getD 0).toUSize (by
    rw [USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw.2 (Nat.lt_of_lt_of_le (by decide) USize.le_size))]; exact hw.2) b
  have hN : ∀ c < Column.nblk (Kernel.Coc.encodeAt Column.lgEnc (t.width.getD 0).toUSize b).1,
      Column.nulAt (Kernel.Coc.encodeAt Column.lgEnc (t.width.getD 0).toUSize b).1 c = false :=
    Verify.nulAt_encodeAt_empty Column.lgEnc (by decide) _ hw.1 hw.2 b
  cases t <;> simp only [Enc.WF] <;> first
    | exact absurd rfl hu.1 | exact absurd hu.2 (by decide)
    | exact ⟨rfl, fun h => absurd h (by decide), hk, hl, fun c hc h => absurd ((hN c hc).symm.trans h) Bool.false_ne_true⟩

/-- A dense payload encoded at `w` bytes holds no null: the encoder flags no block without a null bitmap. Stated on
    `ofBytes` itself, so a caller at a literal width unifies it without evaluating the encoder. -/
theorem ofBytes_plain (w : Nat) (hw : 0 < w ∧ w ≤ 8) (b : ByteArray) : Kernel.hasNul (Ext.Enc.ofBytes w b) = false :=
  Verify.hasNul_of_nulAt (Verify.nulAt_encodeAt_empty Column.lgEnc (by decide) w hw.1 hw.2 b)

/-- `foRBits` with no hoisted table reads the start `blockStarts` holds (`blockStarts_get`), so
    `Column.get`'s `#[]` and the kernels' table are one decode. -/
theorem foRBits_starts (md pk : ByteArray) (i : Nat) :
    Column.foRBits md pk #[] i = Column.foRBits md pk (Column.blockStarts md) i := by
  have hs : (Column.blockStarts md).size = Column.nblk md + 1 := (Verify.blockStarts_fold md (Column.nblk md)).2.1
  unfold Column.foRBits
  by_cases h : i / Column.blk md ≤ Column.nblk md
  · simp [Verify.blockStarts_get md h, Verify.blockStarts_get md (Nat.le_refl _)]
  · simp [Verify.blockStarts_get md (Nat.le_refl _), Array.getElem?_eq_none (show (Column.blockStarts md).size ≤ i / Column.blk md by omega)]

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

/-- A long payload's `n` words in position order: a `foR` payload's `foRBits` decode, a `pos` payload's positions;
    `none` at the non-long constructors. -/
def longWords (n : USize) (e : Enc) : Option (List UInt64) :=
  match e with
  | .foR md pk => some ((List.range n.toNat).map (Column.foRBits md pk (Column.blockStarts md)))
  | .pos => some ((List.range n.toNat).map Nat.toUInt64)
  | _ => none

/-- A column of `n` rows of the fixed-width type `t` from the dense payload `b`, `w` bytes a row: `Coc.encode` at `w`,
    so the column is `foR` where it is produced (decision M), a float's stored bits included. Every type with a width
    but `u1`, whose bits `Arr.bools` lays out. A literal is packed and encoded here once; an old kernel's dense answer is
    encoded here at its exit, which goes with the old layer (W5). -/
def Arr.ofBytes (t : QAtomicType) {n : USize} (b : ByteArray) (h : b.size = t.width.getD 0 * n.toNat)
    (hu : t ≠ .u1 ∧ t.width.isSome := by decide) : Arr t n :=
  Arr.mk (Ext.Enc.ofBytes (t.width.getD 0) b) (foRBytes_wf t hu b h)
    (ofBytes_plain _ (by cases t <;> simp [QAtomicType.width] at hu ⊢) b)



/-- The column of `t` holding the stored words `f` at the positions `0 … n-1`, each cut to `t`'s width (a float is its
    bits, `-0.0` and a NaN's payload included), packed by Lean with no kernel: `Arr.ofBytes` of the packing. -/
def Arr.ofFn (t : QAtomicType) (n : USize) (f : Fin n.toNat → UInt64) (hu : t ≠ .u1 ∧ t.width.isSome := by decide) :
    Arr t n :=
  Arr.ofBytes t ((List.ofFn f).foldl (fun b x => Column.pushBits b x (t.width.getD 0)) .empty) (by
    have h := (Verify.foldl_pushBits (fun x : UInt64 => x) (t.width.getD 0)
      (by cases t <;> simp [QAtomicType.width] at hu ⊢) (List.ofFn f) .empty).1
    rw [h]; simp) hu


/-- Reading a word as a long loses nothing. -/
theorem toInt64_inj {x y : UInt64} (h : x.toInt64 = y.toInt64) : x = y := by
  simpa using congrArg Int64.toUInt64 h

/-- A boolean column's bitmap: `boolBits` reads one off the one form `Enc.WF .u1` admits, a `u1` `foR`. -/
def Alg.tagBits {n : USize} (x : Arr .u1 n) : ByteArray :=
  (Kernel.boolBits .u1 n x.enc).get (by
    have hw := x.wf; revert hw; cases x.enc <;> simp [Enc.WF, Kernel.boolBits])


/-- Under `Enc.WF`, a boolean payload's element `j` that is no null is bit `j` of the bitmap `boolBits` reads: such a
    `u1` `foR` element is `0` or `1`, so its low bit, which `bitsOfFoR` keeps, is whether it is nonzero. -/
theorem get_boolBits {n : USize} {e : Enc} (hw : Enc.WF .u1 n e) {b : ByteArray}
    (ht : Kernel.boolBits .u1 n e = some b) {j : Nat} (hj : j < n.toNat)
    (hnn : ∀ md pk, e = .foR md pk → Column.foRNul md pk (Column.blockStarts md) j = false) :
    Enc.get .u1 n e j = some (.u1 (Column.bitAt b j)) := by
  revert ht hw hnn
  cases e <;> simp only [Kernel.boolBits, Enc.WF, reduceCtorEq, false_implies, true_implies, implies_true, Option.some.injEq]
  · rename_i md pk
    rintro ⟨-, hl, hn, -⟩ rfl hnn
    have h2 := hl j hj (Column.foRBits md pk (Column.blockStarts md) j) (by simp [Column.foROpt, hnn md pk rfl])
    have hb : j < Column.blk md * Column.nblk md := Nat.lt_of_lt_of_le hj hn
    simp only [Enc.get, if_pos hj, QAtomicType.width, Kernel.bitsOfFoR, Verify.bitAt_packOf _ _ _ hj,
      foRBits_starts, decide_eq_true hb, Bool.true_and]
    generalize Column.foRBits md pk (Column.blockStarts md) j = v at h2
    rcases (show v.toNat = 0 ∨ v.toNat = 1 by omega) with h | h
    · obtain rfl : v = 0 := UInt64.toNat_inj.1 h; rfl
    · obtain rfl : v = 1 := UInt64.toNat_inj.1 h; rfl


/-- `Coc.bools` at a count `n` is a well formed boolean column of `n` rows: each element `0` or `1`
    (`foRBits_bools`), its blocks covering `n`, its `lg` the encoder's. -/
theorem wf_bools {X : Type} {n : USize} (p : Nat → Bool) :
    Ext.Enc.WF .u1 n (.foR (Kernel.Coc.bools n.toNat p).1 (Kernel.Coc.bools n.toNat p).2 : Ext.Enc X) := by
  have h1 : USize.ofNat32 1 (by decide) = (1 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp)
  obtain ⟨hs, -⟩ := Verify.packIds_bytes 1 n.toNat (fun i => (p i).toNat) (by decide) (by decide)
  simp only [Nat.mul_one] at hs
  obtain ⟨hn, hk, -⟩ := Verify.nblk_encode Column.lgEnc (by decide) 1 (by decide) (by decide)
    (Column.packIds 8 n.toNat fun i => (p i).toNat) (patch := false)
  refine ⟨rfl, fun _ i hi v hv => ?_, ?_, ?_, ?_⟩
  · rw [(foRBits_bools _ _ hi).1] at hv; obtain rfl := Option.some.inj hv; cases p i <;> decide
  · rw [show Kernel.Coc.bools n.toNat p = _ from congrArg (fun w => Kernel.Coc.encodeAt Column.lgEnc w _ false) h1, hn, hk, hs]
    simp only [Nat.div_one, Nat.one_mul, Column.lgEnc, Nat.reducePow]; omega
  · rw [Kernel.Coc.bools, Column.lgOk, lgAt_encodeAt Column.lgEnc (by decide) (USize.ofNat32 1 (by decide)) (by simp)]; rfl
  · rw [show Kernel.Coc.bools n.toNat p = _ from congrArg (fun w => Kernel.Coc.encodeAt Column.lgEnc w _ false) h1]
    exact fun b hb h => absurd ((Verify.nulAt_encodeAt_empty Column.lgEnc (by decide) 1 (by decide) (by decide) _ b
      hb).symm.trans h) Bool.false_ne_true

/-- `wf_bools`'s column holds no null: `Coc.bools` passes the encoder no null bitmap. -/
theorem bools_plain (n : USize) (p : Nat → Bool) :
    Kernel.hasNul (.foR (Kernel.Coc.bools n.toNat p).1 (Kernel.Coc.bools n.toNat p).2) = false := by
  have h1 : USize.ofNat32 1 (by decide) = (1 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp)
  rw [show Kernel.Coc.bools n.toNat p = _ from congrArg (fun w => Kernel.Coc.encodeAt Column.lgEnc w _ false) h1]
  exact Verify.hasNul_of_nulAt (Verify.nulAt_encodeAt_empty Column.lgEnc (by decide) 1 (by decide) (by decide) _)

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
  · simp only [hi, decide_true, Bool.true_and, (foRBits_bools _ _ hi).2, hf i hi, decide_eq_true (Nat.lt_of_lt_of_le hi hb)]
    cases f i <;> decide
  · simp [hi]

/-- **A boolean writer's column, bit by bit**: below `n`, the bitmap `boolBits` reads off `Coc.bools` of `n` rows is
    the predicate it encodes (`foRBits_bools`). Every writer's `*_bitAt` lemma states its predicate; this composes. -/
theorem bitAt_bools {N : Nat} {n : USize} (p : Nat → Bool) (hN : N = n.toNat) {i : Nat} (hi : i < n.toNat) :
    Column.bitAt (Kernel.bitsOfFoR (Kernel.Coc.bools N p).1 (Kernel.Coc.bools N p).2 n) i = p i := by
  subst hN
  have hb := Nat.lt_of_lt_of_le hi (wf_bools (X := Unit) (n := n) p).2.2.1
  simp only [Kernel.bitsOfFoR, Verify.bitAt_packOf _ _ _ hi, (foRBits_bools _ _ hi).2, hb, decide_true, Bool.true_and]
  cases p i <;> decide

/-- **A bitmap kernel's answer, read back**: element `j < n` of the column `Coc.boolsOf n g` writes is bit `j` of
    `g` (`get_boolBits`, `bitAt_bools`). -/
theorem get_boolsOf {n : USize} (g : ByteArray) {j : Nat} (hj : j < n.toNat) :
    Enc.get .u1 n (.foR (Kernel.Coc.boolsOf n g).1 (Kernel.Coc.boolsOf n g).2 : Enc) j =
      some (.u1 (Column.bitAt g j)) := by
  show Enc.get .u1 n
    (.foR (Kernel.Coc.bools n.toNat (Column.bitAt g)).1 (Kernel.Coc.bools n.toNat (Column.bitAt g)).2) j = _
  refine (get_boolBits (wf_bools (Column.bitAt g)) rfl hj fun md pk he => ?_).trans (by rw [bitAt_bools _ rfl hj])
  injection he with h1 h2; subst h1 h2
  have ho := (foRBits_bools _ (Column.bitAt g) hj).1
  unfold Column.foROpt at ho; split at ho; · cases ho
  rename_i hf; simpa using hf

/-- The boolean column of the `n` booleans `p`, as every boolean writer lays it out (`Coc.bools`). -/
def Arr.bools (n : USize) (p : Nat → Bool) : Arr .u1 n :=
  Arr.mk (.foR (Kernel.Coc.bools n.toNat p).1 (Kernel.Coc.bools n.toNat p).2) (wf_bools p) (bools_plain n p)

theorem Ext.Enc.blank_WF {X : Type} (t : QAtomicType) (n : USize) : Ext.Enc.WF t n (Ext.Enc.blank (X := X) t n) := by
  cases t
  case u1 => exact wf_bools fun _ => false
  case general => simp [Ext.Enc.blank, Ext.Enc.WF]
  -- every fixed-width type: `blank` is `ofBytes` of `n` zero elements
  all_goals exact foRBytes_wf _ (by decide) _ ((Array.size_replicate).trans (Nat.mul_comm _ _))

theorem Ext.Enc.blank_plain (t : QAtomicType) (n : USize) : Kernel.hasNul (Ext.Enc.blank t n) = false := by
  cases t
  case u1 => exact bools_plain n fun _ => false
  case general => rfl
  all_goals (simp only [Ext.Enc.blank, QAtomicType.width]; exact ofBytes_plain _ (by decide) _)

namespace Column
open Ext.Enc


end Column


/-- A side of a relation: an atomic type, a product of sides, or an array of a side. A tree, so
    `Vals (.atom t)` is `Arr t` itself and every one-column path is unchanged. A `arr b` element is an
    ARRAY of `b`: its order and multiplicity are part of the value. -/
inductive Obj
  | atom (t : QAtomicType)
  | prod (a b : Obj)
  | arr (b : Obj)
  | sum (a b : Obj)
  /-- The unit (terminal) object `1`: one value, so a side of it stores nothing. -/
  | one

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
  | .one => Unit

/-- The element a row reads where its side holds no value at all (a side of `0` values), the one position no
    clamp can land in: what a gather past the side reads — an atom's `default` (q's null), an empty array, a
    sum's `inl` of its left side's own. -/
def Obj.dflt : (A : Obj) → A.El
  | .atom _ => default
  | .prod a b => (a.dflt, b.dflt)
  | .arr _ => []
  | .sum a _ => .inl a.dflt
  | .one => ()

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
  | .one, _ => Unit

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
  | .one, _, _, _ => ()

-- Kept with no caller: an atom side's row is the `Arr`'s element, the `List` reading of a side.
@[simp] theorem Vals.row_atom {t : QAtomicType} {n : USize} (x : Arr t n) (i : Fin n.toNat) :
    Vals.row (A := .atom t) x i = x.get i := rfl

/-- Every row of `x` in position order, `Array.ofFn (Vals.row x)`, as `Tab.toList` runs it: each column read once
    front to back. `Vals.row` at an `arr` side scans all `m` payload values per row, reading `lo i` and `hi i` at
    each, which over all rows is `n * m` reads; here a row is the payload's slice `[lo i, hi i)`, the clamp
    `Vals.row` applies, and a sum row indexes its side's rows by the clamped position. -/
private def Arr.rowsImpl {t : QAtomicType} {n : USize} (x : Arr t n) : Array (El t) :=
  match t, x with
  | .general, x => Array.ofFn x.get
  -- `Arr.get`'s atom with the block starts hoisted (`Enc.get`'s `starts`): `x.get` per element sums every block
  -- before it, so a whole `.foR` column read that way is quadratic in its block count
  | t, x =>
    let s := match x.enc with | .foR m _ => Column.blockStarts m | _ => #[]
    Array.ofFn (n := n.toNat) fun i => ((Enc.get t n x.enc i s).bind fun a => Carrier.of? t (.atom a)).getD default

private def Vals.rowsImpl : {A : Obj} → {n : USize} → Vals A n → Array A.El
  | .atom _, _, x => Arr.rowsImpl x
  | .prod _ _, _, x => (Vals.rowsImpl x.1).zip (Vals.rowsImpl x.2)
  | .arr _, n, ⟨_, lo, hi, f⟩ =>
    let fs := Vals.rowsImpl f
    let los := Arr.rowsImpl lo; let his := Arr.rowsImpl hi
    Array.ofFn (n := n.toNat) fun i =>
      (fs.extract (los[i]?.getD 0).toInt.toNat (his[i]?.getD 0).toInt.toNat).toList
  | .sum a b, n, ⟨l, r, tag, idx, x, y⟩ =>
    let xs := Vals.rowsImpl x; let ys := Vals.rowsImpl y
    let tags := Arr.rowsImpl tag; let idxs := Arr.rowsImpl idx
    Array.ofFn (n := n.toNat) fun i =>
      if tags[i]?.getD false then .inr (ys[min (idxs[i]?.getD 0).toInt.toNat (r.toNat - 1)]?.getD b.dflt)
      else .inl (xs[min (idxs[i]?.getD 0).toInt.toNat (l.toNat - 1)]?.getD a.dflt)
  | .one, n, _ => Array.replicate n.toNat ()

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

/-- What `toList` runs as: `Vals.rowsImpl` of each side, zipped. -/
private def toListImpl (R : Tab k v) : List (k.El × v.El) := ((Vals.rowsImpl R.key).zip (Vals.rowsImpl R.val)).toList

/-- The pairs, in position order. The body is the specification; it runs as `toListImpl` (not proved equal: the
    `#guard`s under `Checks` compare the two on an `arr` and a `sum` side). -/
@[implemented_by toListImpl]
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


/-- `Ew.cmp`'s `u1` `foR` read through `boolBits` (its `foR` branch, `bitsOfFoR`): the bitmap a bitmap consumer
    (`Ew.notBits`) takes, one name for the read so no consumer restates it. -/
def Ew.cmpBits (op cls shape : UInt8) (a b : ByteArray) (n : USize) : ByteArray :=
  let c := Ew.cmp op cls shape a b n; bitsOfFoR c.1 c.2 n

/-- `Ew.bit`'s `u1` `foR` read through `boolBits`, as `Ew.cmpBits` reads `Ew.cmp`'s. -/
def Ew.bitBits (op shape : UInt8) (a b : ByteArray) (n : USize) : ByteArray :=
  let c := Ew.bit op shape a b n; bitsOfFoR c.1 c.2 n



/-- `~` on `m` bits: `Ew.bit` xor a ones mask, the mask a one-bit atom in shape `av` (xor is `≠` on bits). -/
def Ew.notBits (m : USize) (b : ByteArray) : ByteArray := Ew.bitBits (Ew.bitCmp + Ew.ne) Ew.av ⟨#[1]⟩ b m

end Payload

/-! ## Sanity checks on small literal columns -/

section Checks

open Rel.Column

/-- `Enc.WF` of a literal payload at a literal `USize` count: `decide` cannot reduce `USize.toNat` of a
    numeral, so the count is read as a `Nat` numeral first. -/
macro "wf_lit" : tactic => `(tactic| (unfold Enc.WF; simp only [USize.reduceToNat, QAtomicType.width]; decide))
/-- The size side of `Arr.ofBytes .i64 (packLongs xs)` at a literal count. -/
macro "longs_lit" : tactic => `(tactic| (rw [packLongs_size]; simp [QAtomicType.width]))
/-- A literal count below `2³²` fits a `USize` on every platform (`USize.le_size`). -/
macro "fits_lit" : tactic => `(tactic| (refine Nat.lt_of_lt_of_le ?_ USize.le_size; simp))

private def l3 : Arr .i64 3 := Arr.ofBytes .i64 (packLongs [7, -1, 42]) (by longs_lit)
#guard l3.toList == [7, -1, 42]

private def bs : Arr .u1 3 := Arr.bools 3 (Column.bitAt ⟨#[0b101]⟩)
#guard bs.toList == [true, false, true]


private def gs : Arr .general 2 := Arr.mk (.gen #[(.atom (.i64 1) : QValue), (.general #[] 0 : QValue)]) (by unfold Enc.WF; simp only [USize.reduceToNat]; rfl) rfl
#guard match id (α := QValue) (gs.get ⟨0, by simp⟩), id (α := QValue) (gs.get ⟨1, by simp⟩) with | .atom (.i64 1), .general #[] _ _ => true | _, _ => false

-- `Tab.toList` runs as `toListImpl`; the spec `List.ofFn` of the rows is computed beside it. An `arr` side whose
-- slices are in range, past the payload and negative, and a `sum` side whose positions clamp at both ends.
private def ta : Tab .long (.arr .long) := ⟨3, l3, ⟨4, Arr.ofBytes .i64 (packLongs [0, 2, -5]) (by longs_lit),
  Arr.ofBytes .i64 (packLongs [2, 9, 0]) (by longs_lit), Arr.ofBytes .i64 (packLongs [10, 20, 30, 40]) (by longs_lit)⟩⟩
private def tsum : Tab .long (.sum .long .long) :=
  ⟨3, l3, ⟨2, 1, bs, Arr.ofBytes .i64 (packLongs [0, 7, -3]) (by longs_lit),
  Arr.ofBytes .i64 (packLongs [5, 6]) (by longs_lit), Arr.ofBytes .i64 (packLongs [9]) (by longs_lit)⟩⟩
#guard (ta.toList : List (Int64 × List Int64)) == [(7, [10, 20]), (-1, [30, 40]), (42, [])]
#guard (ta.toList : List (Int64 × List Int64)) == List.ofFn fun i => (ta.key.row i, ta.val.row i)
#guard (tsum.toList : List (Int64 × Sum Int64 Int64)) == [(7, .inr 9), (-1, .inl 6), (42, .inr 9)]
#guard (tsum.toList : List (Int64 × Sum Int64 Int64)) == List.ofFn fun i => (tsum.key.row i, tsum.val.row i)
-- on a multi-block `foR` side (`Arr.ofFn` encodes), with an `arr` of it
private def big (d : Nat) : Arr .i64 1100 := Arr.ofFn .i64 1100 fun i => (i.1 * 7 % 1000 + d).toUInt64
private def tbig : Tab .long (.arr .long) := ⟨1100, big 0, ⟨1100, big 0, big 3, big 5⟩⟩
#guard (tbig.toList : List (Int64 × List Int64)) == List.ofFn fun i => (tbig.key.row i, tbig.val.row i)


end Checks

#print axioms Arr.get
#print axioms Tab.holds_iff_mem_toList

end Rel

namespace Rel.Alg
open Rel.Kernel

/-- A literal long column, `Coc.encode`d where it is built (`Arr.ofBytes`), its count `xs.length` proved by
    `packLongs_size`; it runs where the count fits a `USize`. -/
def col (xs : List Int64) : Arr .i64 xs.length.toUSize :=
  need (xs.length < USize.size) (fun _ => s!"col: {xs.length} longs do not fit a USize")
    (fun _ => Arr.mk (Enc.blank .i64 _) (Enc.blank_WF .i64 _) (Enc.blank_plain .i64 _)) fun h =>
  Arr.ofBytes .i64 (packLongs xs) (show _ = 8 * _ by rw [packLongs_size, USize.toNat_ofNat_of_lt' h])

/-- The null long. -/
def nul : Int64 := Int64.minValue

end Rel.Alg
