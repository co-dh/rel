import Rel.Kernel.Dep.Monadic
import Rel.Kernel.Scan
import Rel.Kernel.Structural
import Rel.KernelSpec.Alp
import Rel.KernelSpec.AlpConcat
import Rel.KernelSpec.BinWin
import Rel.KernelSpec.Chain
import Rel.KernelSpec.Elementwise
import Rel.KernelSpec.Encoding
import Rel.KernelSpec.EwEnc
import Rel.KernelSpec.Gather
import Rel.KernelSpec.Grade
import Rel.KernelSpec.Group
import Rel.KernelSpec.Ids
import Rel.KernelSpec.ScanOver
import Rel.KernelSpec.Search
import Rel.KernelSpec.Structural
import Rel.KernelSpec.SymFind
import Rel.ObjOrder
import Rel.Run.Core
import Rel.Rep

/-! Read lemmas of the run path's own definitions (`Enc.get`, `Enc.raw`, `Vals.row`, the foR block layout, the
    symbol id widths), kept from the deleted `Rel.KernelWF.*` modules whose other contents were about the old layer.
    Each section names the module it came from. -/

-- from Rel.KernelWF.AppendFoR
namespace Rel.KernelWF

open Tab Rel.Kernel Rel

/-- `foRBits` with no hoisted table: the block's start is summed. -/
theorem foRBits_nil (md pk : ByteArray) (i : Nat) : Column.foRBits md pk #[] i =
    match Column.foRExc md pk i with
    | some v => v
    | none => Column.baseAt md (i / Column.blk md) + Column.foRFrame md pk (i / Column.blk md) +
        Column.resAt pk (Column.blockStart md (i / Column.blk md)) (Column.widthAt md (i / Column.blk md)) (i % Column.blk md) := by
  unfold Column.foRBits; cases h : Column.foRExc md pk i <;> simp [h]

/-- A pack that ends by its last block's residuals has no patch list. -/
theorem foRExc_none {md pk : ByteArray} (h : pk.size ≤ Column.blockStart md (Column.nblk md)) (i : Nat) :
    Column.foRExc md pk i = none := by unfold Column.foRExc; simp [h]

/-- A pack that ends by its last block's residuals has no frames. -/
theorem foRFrame_zero {md pk : ByteArray} (h : pk.size ≤ Column.blockStart md (Column.nblk md)) (b : Nat) :
    Column.foRFrame md pk b = 0 := by unfold Column.foRFrame; simp [h]

/-- With no patch list, element `i` is its block's base plus its residual. -/
theorem foRBits_plain {md pk : ByteArray} (h : pk.size ≤ Column.blockStart md (Column.nblk md)) (i : Nat) :
    Column.foRBits md pk (Column.blockStarts md) i = Column.baseAt md (i / Column.blk md) +
      Column.resAt pk (Column.blockStart md (i / Column.blk md)) (Column.widthAt md (i / Column.blk md)) (i % Column.blk md) := by
  rw [← foRBits_starts, foRBits_nil, foRExc_none h, foRFrame_zero h]; simp

theorem blockStart_succ (md : ByteArray) (b : Nat) :
    Column.blockStart md (b + 1) = Column.blockStart md b + Column.blk md * Column.widthAt md b / 8 := by
  simp [Column.blockStart, Nat.fold_succ]

theorem blockStart_mono (md : ByteArray) {a b : Nat} (h : a ≤ b) : Column.blockStart md a ≤ Column.blockStart md b := by
  induction b with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [blockStart_succ]; exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · exact Nat.le_refl _

/-- Blocks `a, a+1, …` of `M` laid out as `m`'s, at `m`'s block size: their starts are `m`'s, shifted by `M`'s start of block `a`. -/
theorem blockStart_shift {M m : ByteArray} (a : Nat) (hB : Column.blk M = Column.blk m) : ∀ b, (∀ c < b, Column.widthAt M (a + c) = Column.widthAt m c) →
    Column.blockStart M (a + b) = Column.blockStart M a + Column.blockStart m b
  | 0, _ => by simp [Column.blockStart]
  | b + 1, h => by
    rw [← Nat.add_assoc, blockStart_succ, blockStart_succ, blockStart_shift a hB b (fun c hc => h c (by omega)),
      h b (by omega), hB, Nat.add_assoc]

/-- `resAt` reads only the bytes its field overlaps. -/
theorem resAt_congr {P Q : ByteArray} {s s' w j : Nat}
    (h : ∀ k < (j * w + w + 7) / 8, P[s + k]? = Q[s' + k]?) : Column.resAt P s w j = Column.resAt Q s' w j := by
  unfold Column.resAt
  have key : ∀ {f g : UInt64 → Nat → UInt64} (l : List Nat) (a : UInt64), (∀ k ∈ l, ∀ acc, f acc k = g acc k) →
      l.foldl f a = l.foldl g a := by
    intro f g l; induction l with
    | nil => intro a _; rfl
    | cons k l ih =>
      intro a hl; simp only [List.foldl_cons]; rw [hl k (by simp)]
      exact ih _ (fun k' hk' => hl k' (by simp [hk']))
  exact key _ _ fun k hk acc => by
    simp [List.mem_range'] at hk; simp only [h k (by omega)]

/-- A residual read at width `w` is under `2 ^ w`: each byte's share is cut to `w` bits. -/
theorem resAt_lt (P : ByteArray) (s w j : Nat) : (Column.resAt P s w j).toNat < 2 ^ w := by
  unfold Column.resAt
  have key : ∀ (l : List Nat) (a : UInt64), a.toNat < 2 ^ w → (l.foldl (fun acc k =>
      acc ||| (((P[s + k]?.getD 0).toNat * 2 ^ (8 * k) / 2 ^ (j * w) : Nat) % 2 ^ w).toUInt64) a).toNat < 2 ^ w := by
    intro l; induction l with
    | nil => intro a h; exact h
    | cons k l ih =>
      intro a ha; rw [List.foldl_cons]; apply ih
      rw [UInt64.toNat_or]
      refine Nat.or_lt_two_pow ha ?_
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  exact key _ 0 (by simp [Nat.two_pow_pos])

/-- The patch list reads only the pack's size and its bytes from the end of the last block on. -/
theorem foRExc_congr {md P Q : ByteArray} (hs : P.size = Q.size)
    (h : ∀ k, P[Column.blockStart md (Column.nblk md) + k]? = Q[Column.blockStart md (Column.nblk md) + k]?)
    (i : Nat) : Column.foRExc md P i = Column.foRExc md Q i := by
  have hb0 : ∀ w, Column.bitsAt P (Column.blockStart md (Column.nblk md)) w =
      Column.bitsAt Q (Column.blockStart md (Column.nblk md)) w := fun w =>
    Verify.bitsAt_shift P Q _ _ w fun k _ => h k
  have hb : ∀ x w, Column.bitsAt P (Column.blockStart md (Column.nblk md) + x) w =
      Column.bitsAt Q (Column.blockStart md (Column.nblk md) + x) w := fun x w =>
    Verify.bitsAt_shift P Q _ _ w fun k _ => by rw [Nat.add_assoc]; exact h _
  unfold Column.foRExc
  simp only [hs, Nat.add_assoc, hb, hb0]

/-- The frames read only the pack's size and its bytes from the end of the last block on. -/
theorem foRFrame_congr {md P Q : ByteArray} (hs : P.size = Q.size)
    (h : ∀ k, P[Column.blockStart md (Column.nblk md) + k]? = Q[Column.blockStart md (Column.nblk md) + k]?)
    (b : Nat) : Column.foRFrame md P b = Column.foRFrame md Q b := by
  have hb0 : ∀ w, Column.bitsAt P (Column.blockStart md (Column.nblk md)) w =
      Column.bitsAt Q (Column.blockStart md (Column.nblk md)) w := fun w =>
    Verify.bitsAt_shift P Q _ _ w fun k _ => h k
  have hb : ∀ x w, Column.bitsAt P (Column.blockStart md (Column.nblk md) + x) w =
      Column.bitsAt Q (Column.blockStart md (Column.nblk md) + x) w := fun x w =>
    Verify.bitsAt_shift P Q _ _ w fun k _ => by rw [Nat.add_assoc]; exact h _
  unfold Column.foRFrame
  simp only [hs, Nat.add_assoc, hb, hb0]

end Rel.KernelWF

-- from Rel.Run.KernelWF.Raze
-- the lane widths an id pack may have: one home for the disjunction every lane hypothesis states
notation "laneOK(" w ")" => (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)

namespace Rel.KernelWF

open Rel.Kernel Rel

/-- A `Nat.fold` that pushes a byte a step answers one byte per step. -/
private theorem fold_push_size (g : Nat → UInt8) :
    ∀ (k : Nat) (b : ByteArray), (Nat.fold k (fun i _ acc => acc.push (g i)) b).size = b.size + k
  | 0, b => by simp
  | k + 1, b => by
    rw [Nat.fold_succ, ← Nat.add_assoc, ← fold_push_size g k b]
    simp only [ByteArray.size, ByteArray.push, Array.size_push]

/-- **`packIds` at a lane is `⌈n·w/8⌉` bytes**, the size `Enc.WF` asks of an id pack. -/
theorem packIds_size {w : Nat} (hw : w = 0 ∨ laneOK(w))
    (n : Nat) (f : Nat → Nat) : (Column.packIds w n f).size = (n * w + 7) / 8 := by
  have hbytes : ∀ c, 1 ≤ c → c ≤ 8 → (Column.packIds (8 * c) n f).size = (n * (8 * c) + 7) / 8 :=
    fun c h1 h8 => by rw [(Verify.packIds_bytes c n f h1 h8).1, Nat.mul_comm n, Nat.mul_assoc]; omega
  have hsub : ∀ w, 1 ≤ w → w < 8 → (Column.packIds w n f).size = (n + 8 / w - 1) / (8 / w) := fun w h1 h8 => by
    unfold Column.packIds
    rw [if_neg (by omega), if_neg (by omega)]
    exact (fold_push_size _ _ _).trans (Nat.zero_add _)
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Column.packIds]
  · rw [hsub 1 (by decide) (by decide)]; omega
  · rw [hsub 2 (by decide) (by decide)]; omega
  · rw [hsub 4 (by decide) (by decide)]; omega
  · exact hbytes 1 (by decide) (by decide)
  · exact hbytes 2 (by decide) (by decide)
  · exact hbytes 4 (by decide) (by decide)
  · exact hbytes 8 (by decide) (by decide)

end Rel.KernelWF

-- from Rel.KernelWF.Driver
open Rel.Ext

namespace Rel.Kernel
open Column

/-- A fixed-width type's width is one to eight bytes, two or more where it is Frame-of-Reference encoded and four or
eight where it is ALP encoded. -/
theorem width_cases (t : QAtomicType) (w : Nat) (ht : t.width = some w) :
    1 ≤ w ∧ w ≤ 8 ∧ (encodes t = true → 1 < w) ∧ (alpEncodes t = true → w = 4 ∨ w = 8) := by
  cases t <;> simp_all [QAtomicType.width, encodes, alpEncodes] <;> subst ht <;> decide

/-- The raw elements of a boolean column, a `foR` of `u1`, are `0` or `1`. -/
theorem raw_boolean_le (n : USize) (e : Enc) : ∀ v ∈ e.raw .u1 n, v ≤ 1 := by
  intro v hv
  cases e <;> simp only [Enc.raw, Array.mem_map, Array.mem_range, Array.not_mem_empty] at hv
  all_goals obtain ⟨i, -, rfl⟩ := hv
  case foR m p =>
    have h2 := Nat.mod_lt ((foRBits m p (blockStarts m) i).toNat) (show 0 < 2 by decide)
    generalize (foRBits m p (blockStarts m) i).toNat % 2 = k at h2 ⊢
    rcases k with _ | _ | k
    · decide
    · decide
    · omega
  all_goals split <;> decide

/-- **The rule `Enc.raw` keeps**: an element of a `w`-byte type is below `2 ^ (8 * w)`, in every form. -/
theorem raw_lt (t : QAtomicType) (w : Nat) (ht : t.width = some w) (n : USize) (e : Enc) :
    ∀ v ∈ e.raw t n, v.toNat < 2 ^ (8 * w) := by
  obtain ⟨hw1, hw8, -, -⟩ := width_cases t w ht
  have hM : 2 ^ (8 * w) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hmod : ∀ x : UInt64, (UInt64.ofNat (x.toNat % 2 ^ (8 * w))).toNat < 2 ^ (8 * w) := fun x => by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hM)]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  intro v hv
  by_cases hb : t = .u1
  · subst hb
    exact Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.1 (raw_boolean_le n e v hv))
      (Nat.lt_of_lt_of_le (show (1 : UInt64).toNat < 2 ^ 8 by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  cases e with
  | foR M P => rw [Verify.raw_foR t w ht hb] at hv; obtain ⟨i, -, rfl⟩ := Array.mem_map.1 hv; exact hmod _
  -- `pos` is read at `i64` only, where every word is below `2 ^ 64`
  | pos =>
    by_cases hi : t = .i64
    · subst hi; obtain rfl : w = 8 := by simp [QAtomicType.width] at ht; omega
      exact v.toNat_lt
    · cases t <;> simp_all [Enc.raw, QAtomicType.width]
  | _ => cases t <;> simp_all [Enc.raw, QAtomicType.width]

end Rel.Kernel

-- from Rel.KernelWF.Lane
namespace Rel.Alg

open Tab Rel.Kernel Rel

/-- At a whole-byte lane `8c` a code is the `c` bytes from `c·i` (`resAt_lane`). -/
theorem idAt_lane (b : ByteArray) {c : Nat} (hc : c ≤ 8) (i : Nat) :
    Column.idAt b (8 * c) i = (Column.bitsAt b (i * c) c).toNat := by
  rw [Column.idAt, Verify.resAt_lane b c i hc, Nat.mul_comm]

end Rel.Alg

-- from Rel.KernelWF.RazeSpec
open Rel.Ext

namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Dep Rel Rel.Alg

/-- A byte read as `bitsAt` reads it, zero past the end. -/
theorem dite_byte (b : ByteArray) (j : Nat) : (if h : j < b.size then b[j] else 0) = (b.data[j]?).getD 0 := by
  split
  · rename_i h; rw [Array.getElem?_eq_getElem (by rw [ByteArray.size_data]; exact h)]; rfl
  · rename_i h; rw [Array.getElem?_eq_none (by rw [ByteArray.size_data]; omega)]; rfl

/-- `bitsAt` reads only its own `w` bytes. -/
theorem bitsAt_congr {b b' : ByteArray} {o o' : Nat} : ∀ {w : Nat}, (∀ j < w, b.data[o + j]? = b'.data[o' + j]?) →
    Column.bitsAt b o w = Column.bitsAt b' o' w
  | 0, _ => rfl
  | w + 1, h => by
    simp only [Column.bitsAt]
    rw [bitsAt_congr (fun j hj => h j (by omega)), dite_byte b, dite_byte b', h w (by omega)]

/-- A type with a width is at most eight bytes wide. -/
theorem width_le8 {t : QAtomicType} {w : Nat} (hw : t.width = some w) : w ≤ 8 := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    decide

/-- A Frame-of-Reference element is its `foRBits` atom. -/
theorem get_foR_eq {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .u1)
    {n : USize} (md pk : ByteArray) {i : Nat} (hi : i < n.toNat) :
    Enc.get (X := Empty) t n (.foR md pk) i =
      some (Column.atomOfBits t (Column.foRBits md pk #[] i) (QAtomicType.ne_general_of_width hw)) := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    first | exact absurd rfl hb |
      (simp only [Enc.get, hi, ↓reduceIte, QAtomicType.width] <;> rfl)

end Rel.KernelWF

-- from Rel.KernelWF.RazeSym
open Rel.Ext

namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Dep Rel Rel.Alg

end Rel.KernelWF

-- from Rel.KernelWF.RazeRowN
namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Dep Rel Rel.Alg Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- A function of a part and a row index, at equal parts. -/
theorem sig_congr {β : USize → Type} {T : Type} (f : ∀ n, β n → Fin n.toNat → T) :
    ∀ {x y : (n : USize) × β n}, x = y → ∀ i hx hy, f x.1 x.2 ⟨i, hx⟩ = f y.1 y.2 ⟨i, hy⟩
  | _, _, rfl, _, _, _ => rfl

theorem get_congr {t : QAtomicType} {x y : (n : USize) × Arr t n} (e : x = y) (i hx hy) :
    x.2.get ⟨i, hx⟩ = y.2.get ⟨i, hy⟩ := sig_congr (fun _ v k => Arr.get v k) e i hx hy

end Rel.KernelWF

-- from Rel.KernelWF.RazeRowRec
namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Dep Rel Rel.Alg Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- A sum row, read through the side's projections. -/
theorem row_sum_eq {a b : Obj} {n : USize} (X : Vals (.sum a b) n) (i : Fin n.toNat) :
    Vals.row X i = if X.2.2.1.get i then
        .inr (if h : 0 < X.2.1.toNat then Vals.row X.2.2.2.2.2 (clampFin (X.2.2.2.1.get i) X.2.1.toNat h) else b.dflt)
      else .inl (if h : 0 < X.1.toNat then Vals.row X.2.2.2.2.1 (clampFin (X.2.2.2.1.get i) X.1.toNat h) else a.dflt) := by
  obtain ⟨l, r, tag, idx, xa, xb⟩ := X; rfl

end Rel.KernelWF

-- from Rel.KernelWF.PickSpec
open Rel.Ext

namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Verify


/-- `pushBits` appends: the bytes it writes do not depend on the payload before them. -/
theorem pushBits_append (a : ByteArray) (v : UInt64) (w : Nat) :
    Column.pushBits a v w = a ++ Column.pushBits .empty v w := by
  induction w with
  | zero => apply ByteArray.ext; simp [Column.pushBits]
  | succ w ih => apply ByteArray.ext; simp [Column.pushBits, ih, ByteArray.data_append, ByteArray.data_push]

/-- `pushBits` writes `w` bytes. -/
theorem size_pushBits (a : ByteArray) (v : UInt64) (w : Nat) : (Column.pushBits a v w).size = a.size + w := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [Column.pushBits, ← ByteArray.size_data, ByteArray.data_push, Array.size_push] at ih ⊢; omega

/-- A dictionary's id width grows with its size. -/
theorem idWidthOf_mono {a b : Nat} (h : a ≤ b) : Column.idWidthOf a ≤ Column.idWidthOf b := by
  have hw : Column.widthFor (a - 1) ≤ Column.widthFor (b - 1) := by
    unfold Column.widthFor
    split
    · exact Nat.zero_le _
    · rw [if_neg (by omega)]
      have hb : b - 1 < 2 ^ ((b - 1).log2 + 1) := (Nat.log2_lt (by omega)).1 (Nat.lt_succ_self _)
      have := (Nat.log2_lt (by omega : a - 1 ≠ 0)).2 (Nat.lt_of_le_of_lt (by omega) hb)
      omega
  unfold Column.idWidthOf Column.laneWidth
  repeat' split
  all_goals omega

/-- A byte array cut where it starts is empty. -/
theorem extract_self (b : ByteArray) (x : Nat) : b.extract x x = ByteArray.empty := by
  apply ByteArray.ext; simp

end Rel.KernelWF

namespace Rel.Alg

open Tab Rel.Kernel Rel

/-- A general list's element `j` is its `gen` column's. -/
theorem get_general {n : USize} (x : Arr .general n) {xs : Array QValue} (hc : x.enc = .gen xs)
    (j : Fin n.toNat) : x.get j = xs[j.1]'(by rw [Arr.gen_size x hc]; exact j.2) := by
  simp only [Arr.get]; split
  · rename_i ys hc'; rw [hc] at hc'; cases hc'; rfl
  · rename_i hn; exact (hn xs hc).elim

/-- An `Arr` moved along a count equation keeps its elements. -/
theorem cast_get {t : QAtomicType} {a b : USize} (e : a = b) (x : Arr t a) (k : Fin b.toNat) :
    (e ▸ x : Arr t b).get k = x.get ⟨k, e ▸ k.2⟩ := by subst e; rfl

/-- An atom type's `default` is the element its null reads as. -/
theorem default_of_null {t : QAtomicType} (hg : t ≠ .general) :
    ((Dep.Carrier.of? t (.atom (Eval.nullAtom t hg))).getD default : Dep.Carrier t) = default := by
  have hd : (default : Dep.Carrier t) = Dep.Carrier.null t hg := by
    show (if h : t = .general then _ else _ : Inhabited (Dep.Carrier t)).default = _
    rw [dif_neg hg]; rfl
  rw [hd]; unfold Dep.Carrier.null
  have key : ∀ (o : Option (Dep.Carrier t)) (p : o.isSome), o.getD (o.get p) = o.get p := fun o p => by
    cases o with | none => cases p | some v => rfl
  exact key _ _

end Rel.Alg

-- from Rel.KernelWF.RowsSpec
namespace Rel.Alg

open Tab Rel.Kernel Rel.Verify Rel

/-- **The window `Vals.row` reads at an array row**: the positions `j < m` with `a ≤ j < b` are the run
    from `a` clamped into `[0, m]` to `b` clamped there, read in order; `d` answers no position of it. -/
theorem filterMap_window {β : Type} (d : β) : ∀ {m : Nat} (f : Fin m → β) (a b : Int),
    (List.finRange m).filterMap (fun j => if a ≤ (j.1 : Int) ∧ (j.1 : Int) < b then some (f j) else none) =
      (List.range' (min (max a 0).toNat m) (min (max b 0).toNat m - min (max a 0).toNat m)).map
        fun r => if h : r < m then f ⟨r, h⟩ else d
  | 0, f, a, b => by simp
  | m + 1, f, a, b => by
    rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map]
    have ih := filterMap_window d (fun j : Fin m => f j.castSucc) a b
    simp only [Function.comp_def, Fin.val_castSucc] at ih ⊢
    rw [ih]
    have hm : ∀ r ∈ List.range' (min (max a 0).toNat m) (min (max b 0).toNat m - min (max a 0).toNat m),
        (if h : r < m then f (Fin.castSucc ⟨r, h⟩) else d) = (if h : r < m + 1 then f ⟨r, h⟩ else d) := by
      intro r hr; rw [List.mem_range'_1] at hr
      rw [dif_pos (by omega), dif_pos (by omega)]; rfl
    rw [List.map_congr_left hm]
    simp only [List.filterMap_cons, List.filterMap_nil, Fin.val_last]
    by_cases hw : a ≤ (m : Int) ∧ (m : Int) < b
    · rw [if_pos hw]; dsimp only
      have e1 : min (max a 0).toNat (m + 1) = min (max a 0).toNat m := by omega
      have e2 : min (max b 0).toNat (m + 1) - min (max a 0).toNat m =
          (min (max b 0).toNat m - min (max a 0).toNat m) + 1 := by omega
      rw [e1, e2, List.range'_concat, List.map_append]
      simp only [List.map_cons, List.map_nil, Nat.one_mul]
      rw [dif_pos (by omega)]
      congr 3; ext; simp only [Fin.val_last]; omega
    · rw [if_neg hw, List.append_nil]
      have e : (min (max b 0).toNat m - min (max a 0).toNat m = 0 ∧
            min (max b 0).toNat (m + 1) - min (max a 0).toNat (m + 1) = 0) ∨
          (min (max a 0).toNat (m + 1) = min (max a 0).toNat m ∧
            min (max b 0).toNat (m + 1) - min (max a 0).toNat m =
              min (max b 0).toNat m - min (max a 0).toNat m) := by omega
      rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; simp
      · rw [e1, e2]

end Rel.Alg

-- from Rel.KernelWF.PickRow
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Kernel Rel.Verify Rel

/-- An array row, as a list: the payload from its clamped start, its clamped count long. -/
theorem arr_row {b : Obj} {m : USize} (x : Vals (.arr b) m) (q : Fin m.toNat) :
    Vals.row x q = (List.range (min (max (x.2.2.1.get q).toInt 0).toNat x.1.toNat -
        min (max (x.2.1.get q).toInt 0).toNat x.1.toNat)).map fun j =>
      if h : min (max (x.2.1.get q).toInt 0).toNat x.1.toNat + j < x.1.toNat then
        Vals.row x.2.2.2 ⟨_, h⟩ else b.dflt := by
  obtain ⟨p, lo, hi, f⟩ := x
  show List.filterMap _ _ = _
  rw [filterMap_window b.dflt, List.range'_eq_map_range, List.map_map]
  rfl

/-- The long null a picked long column reads at a miss is q's `0N`, `nul`. -/
theorem long_default : (@default (El .i64) Dep.instInhabitedCarrier) = nul := rfl

/-- A side of no values or of `k`, read at the position `I` clamped into it, is the side read at `I`
    clamped into `[0, k - 1]` where that is a row, else the side's `dflt`. -/
theorem clamp_row {c : Obj} {k : USize} (xc : Vals c k) (I : Int64) :
    (if h : 0 < k.toNat then Vals.row xc (clampFin I k.toNat h) else c.dflt) =
      if hin : min (max I.toInt 0).toNat (k.toNat - 1) < k.toNat then Vals.row xc ⟨_, hin⟩ else c.dflt := by
  by_cases h : 0 < k.toNat
  · rw [dif_pos h, dif_pos (by omega)]; rfl
  · rw [dif_neg h, dif_neg (by omega)]

end Rel.Alg

-- from Rel.KernelWF.CodesSpec
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel

/-- A small integral column is Frame-of-Reference encoded (`Enc.WF`). -/
theorem small_int_enc {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .c8 ∨ k = .i8 ∨ k = .i16 ∨ k = .i32) {n : USize} (x : Arr t n) :
    ∃ md pk, x.enc = .foR md pk := by
  have hwf := x.wf
  revert hwf
  cases x.enc with
  | foR md pk => exact fun _ => ⟨md, pk, rfl⟩
  | _ => intro hwf; exfalso; rcases hk with rfl | rfl | rfl | rfl | rfl <;> cases t <;> simp_all [Enc.WF,
    orderKind]

/-- A small integral payload's raw word `i`: its `foRBits` cut to `8 * w` bits. -/
theorem raw_small_int {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .c8 ∨ k = .i8 ∨ k = .i16 ∨ k = .i32) {n : USize} {i : Nat} (hi : i < n.toNat) :
    ∀ md pk, (Enc.raw (X := Empty) t n (.foR md pk)).toList.getD i 0 =
      UInt64.ofNat ((Column.foRBits md pk (Column.blockStarts md) i).toNat % 2 ^ (8 * k.width)) := by
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> cases t <;> simp [orderKind] at ht <;>
    exact fun md pk => by simp [Enc.raw, QAtomicType.width, Scan.Kind.width, List.getD_eq_getElem?_getD, hi]

/-- An eight-byte integral payload's raw word `i`: its `foRBits`. -/
theorem raw_long {t : QAtomicType} (ht : orderKind t = some .i64) {n : USize} {i : Nat} (hi : i < n.toNat) :
    ∀ md pk, (Enc.raw (X := Empty) t n (.foR md pk)).toList.getD i 0 = Column.foRBits md pk (Column.blockStarts md) i := by
  cases t <;> simp [orderKind] at ht <;>
    exact fun md pk => by simp [Enc.raw, QAtomicType.width, List.getD_eq_getElem?_getD, hi]


/-- A shift by `-base` of an element `x` with `base ≤ x < base + 2^63`: the integer difference, not the null. -/
theorem shift_toInt {x base : Int64} (hb : base ≠ nul) (h1 : base.toInt ≤ x.toInt) (h2 : x.toInt - base.toInt < 2 ^ 63) :
    (x + -base).toInt = x.toInt - base.toInt ∧ x + -base ≠ nul := by
  have hbl := Int64.le_toInt base; have hbu := Int64.toInt_lt base
  have hxl := Int64.le_toInt x; have hxu := Int64.toInt_lt x
  have hbn : base.toInt ≠ -2 ^ 63 := fun h => hb (Int64.toInt_inj.1 (by rw [h]; decide))
  have hs : (x + -base).toInt = x.toInt - base.toInt := by
    rw [Int64.toInt_add, Int64.toInt_neg]
    simp only [Int.bmod]; split <;> split <;> omega
  refine ⟨hs, fun h => ?_⟩
  have := congrArg Int64.toInt h; rw [hs] at this
  have : nul.toInt = -2 ^ 63 := by decide
  omega

/-- Negation keeps every long but the null off the null. -/
theorem neg_ne_nul {B : Int64} (hB : B ≠ nul) : -B ≠ nul := fun h => by
  have hbl := Int64.le_toInt B; have hbu := Int64.toInt_lt B
  have hbn : B.toInt ≠ -2 ^ 63 := fun e => hB (Int64.toInt_inj.1 (by rw [e]; decide))
  have := congrArg Int64.toInt h
  rw [Int64.toInt_neg, show nul.toInt = -2 ^ 63 by decide] at this
  simp only [Int.bmod] at this; split at this <;> omega

/-- Offsets from one `base`, the null at `card - 1` and every other value below `card - 1`, are equal
    exactly where the values are. -/
theorem offset_iff {base x y : Int64} {card : Nat}
    (hx : x ≠ nul → base.toInt ≤ x.toInt ∧ x.toInt - base.toInt + 2 ≤ card)
    (hy : y ≠ nul → base.toInt ≤ y.toInt ∧ y.toInt - base.toInt + 2 ≤ card) :
    (if x = nul then card - 1 else (x.toInt - base.toInt).toNat) =
        (if y = nul then card - 1 else (y.toInt - base.toInt).toNat) ↔ x = y := by
  by_cases h1 : x = nul <;> by_cases h2 : y = nul
  · rw [h1, h2]; simp
  · rw [if_pos h1, if_neg h2]; obtain ⟨a, b⟩ := hy h2
    exact ⟨fun _ => by omega, fun e => (h2 (by rw [← e]; exact h1)).elim⟩
  · rw [if_neg h1, if_pos h2]; obtain ⟨a, b⟩ := hx h1
    exact ⟨fun _ => by omega, fun e => (h1 (by rw [e]; exact h2)).elim⟩
  · rw [if_neg h1, if_neg h2]; obtain ⟨a, b⟩ := hx h1; obtain ⟨c, d⟩ := hy h2
    exact ⟨fun e => Int64.toInt_inj.1 (by omega), fun e => by rw [e]⟩

end Rel.Alg

-- from Rel.KernelWF.CodesSym
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel

/-- The largest id below `nd` fits a lane `idWidthOf nd` under a byte: a lane of no bits leaves room for the
    id `0` only. (At `64` bits it need not: `nd` is not bounded.) -/
theorem pred_lt_idWidthOf {nd : Nat} (h8 : Column.idWidthOf nd < 8) : nd - 1 < 2 ^ Column.idWidthOf nd := by
  have h := lt_widthFor (nd - 1)
  unfold Column.idWidthOf at h8 ⊢
  generalize Column.widthFor (nd - 1) = w at h h8 ⊢
  have hl : w ≤ Column.laneWidth w := by
    unfold Column.laneWidth at h8 ⊢
    repeat' split
    all_goals (repeat' split at h8)
    all_goals omega
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hl)

end Rel.Alg

-- from Rel.KernelWF.CodesProd
namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel

/-- **Past its `n` ids a sub-byte `packIds` payload reads `0`**: the last byte's tail fields are cleared,
    and a byte past the payload is missing, which `resAt` reads as `0`. -/
theorem idAt_packIds_past {w n i : Nat} {f : Nat → Nat} (hw : w = 1 ∨ w = 2 ∨ w = 4) (hi : n ≤ i) :
    Column.idAt (Column.packIds w n f) w i = 0 := by
  have hs := KernelWF.packIds_size (w := w) (by omega) n f
  obtain ⟨per, hper, hwp⟩ : ∃ per, 8 / w = per ∧ (w = 1 ∧ per = 8 ∨ w = 2 ∧ per = 4 ∨ w = 4 ∧ per = 2) := by
    rcases hw with rfl | rfl | rfl <;> exact ⟨_, rfl, by decide⟩
  have hp : 0 < per := by rcases hwp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < per ∧ i = q * per + r :=
    ⟨i / per, i % per, Nat.mod_lt _ hp, (Nat.div_add_mod' _ _).symm⟩
  by_cases hq : q < (n + per - 1) / per
  · simp only [Column.idAt, Column.packIds, if_neg (show ¬ 8 ≤ w by omega), if_neg (show w ≠ 0 by omega), ite_shift]
    rw [hper, resAt_sub _ _ w per q r hwp hr hq,
      byte_field w per hwp _ (fun j _ => by
        split <;> first | exact Nat.mod_lt _ (Nat.two_pow_pos _) | exact Nat.two_pow_pos _) hr,
      if_neg (by omega)]
  -- byte `q` lies past the payload
  generalize Column.packIds w n f = P at hs
  have h3 : (q * per + r) * w = 8 * q + r * w := by rcases hwp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hrw : r * w + w ≤ 8 := by rcases hwp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hPq : P.size ≤ q := by rw [hs]; rcases hwp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have h1 : (q * per + r) * w / 8 = q := Nat.div_eq_of_lt_le (by rw [h3]; omega) (by rw [h3]; omega)
  have h2 : ((q * per + r) * w + w + 7) / 8 = q + 1 := Nat.div_eq_of_lt_le (by rw [h3]; omega) (by rw [h3]; omega)
  unfold Column.idAt Column.resAt
  rw [h2, h1, Nat.add_sub_cancel_left, List.range'_one]
  simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, getElem?_neg P q (by omega), Option.getD_none]
  rw [show UInt8.toNat 0 = 0 from rfl, Nat.zero_mul, Nat.zero_div, Nat.zero_mod]; rfl

end Rel.Alg

-- from Rel.KernelWF.AscSpec
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel Rel.KernelWF

theorem width_num {t : QAtomicType} {k : Scan.Kind} (h : orderKind t = some k) (hk : k ≠ .bit) :
    t.width = some k.width := by
  cases t <;> simp only [orderKind, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | exact absurd rfl hk | rfl

theorem arr_not_lt_of_key {A : Obj} {x y : A.El} (e : A.key x = A.key y) : ¬ A.lt x y := fun h =>
  Obj.lt_irrefl A y (by unfold Obj.lt at h ⊢; rwa [e] at h)

/-- Arrays of one key have one length: an array's key is one `1` per element, each before a self-delimiting
    element key (`Obj.key_prefix`), then a `0`. -/
theorem arr_key_length {b : Obj} : ∀ xs ys : List b.El, (Obj.arr b).key xs = (Obj.arr b).key ys →
    xs.length = ys.length
  | [], [], _ => rfl
  | [], y :: ys, h => by
    have h' : [0] = 1 :: (b.key y ++ (Obj.arr b).key ys) := h
    simp at h'
  | x :: xs, [], h => by
    have h' : 1 :: (b.key x ++ (Obj.arr b).key xs) = [0] := h
    simp at h'
  | x :: xs, y :: ys, h => by
    have h' : 1 :: (b.key x ++ (Obj.arr b).key xs) = 1 :: (b.key y ++ (Obj.arr b).key ys) := h
    have e := (List.cons.inj h').2
    rw [Obj.key_prefix b x y _ _ e, List.append_cancel_left_eq] at e
    simp [arr_key_length xs ys e]

/-- Arrays ordered by their first `T` elements are ordered. -/
theorem arr_lt_take {b : Obj} : ∀ (T : Nat) (xs ys : List b.El),
    (Obj.arr b).lt (xs.take T) (ys.take T) → (Obj.arr b).lt xs ys
  | 0, _, _, h => by simp only [List.take_zero] at h; exact absurd h (Obj.lt_irrefl _ _)
  | _ + 1, [], [], h => by simp only [List.take_nil] at h; exact absurd h (Obj.lt_irrefl _ _)
  | _ + 1, [], _ :: _, _ => Obj.lt_nil_cons _ _ _
  | _ + 1, _ :: _, [], h => by simp only [List.take_succ_cons, List.take_nil] at h; exact absurd h (Obj.not_lt_nil _ _)
  | T + 1, x :: xs, y :: ys, h => by
    rw [List.take_succ_cons, List.take_succ_cons, Obj.lt_cons] at h
    rw [Obj.lt_cons]
    exact h.imp_right fun ⟨e, h⟩ => ⟨e, arr_lt_take T xs ys h⟩

/-- **`¬ Obj.lt` is antisymmetric where `Obj.key` is injective**: neither below the other means equal keys
    (`lt_trichotomy`), so equal elements. `Ordered` alone does not give it: every general atom keys as `[]`. -/
theorem _root_.Rel.Obj.eq_of_not_lt (A : Obj) (hA : ∀ x y : A.El, A.key x = A.key y → x = y) {x y : A.El}
    (h1 : ¬ A.lt x y) (h2 : ¬ A.lt y x) : x = y :=
  hA x y (((A.lt_trichotomy x y).resolve_left h1).resolve_right h2)

end Rel.Alg

-- from Rel.KernelWF.CrossSpec
namespace Rel.KernelWF

open Tab Rel.Kernel Rel Rel.Alg

/-- The position `j < m`, below `2^63`, read as a long and clamped into `[0, m)`, is `j`. -/
private theorem clampFin_ofNat {j m : Nat} (hj : j < m) (h63 : j < 2 ^ 63) (h : 0 < m) :
    clampFin (Int64.ofNat j) m h = ⟨j, hj⟩ :=
  Fin.ext (by simp only [clampFin, Int64.toInt_ofNat_of_lt h63]; omega)

end Rel.KernelWF

-- from Rel.KernelWF.JoinContent
namespace Rel.Alg

open Tab Rel.Kernel Rel.Verify Rel

/-- A class count's width is a lane: at most `64` bits. -/
theorem idWidthOf_le (n : Nat) : Column.idWidthOf n ≤ 64 := by
  rcases laneWidth_cases (Column.widthFor (n - 1)) with h | h | h | h | h | h | h | h <;>
    simp only [Column.idWidthOf, h] <;> omega

end Rel.Alg

-- from Rel.KernelWF.RunSpec
namespace Rel.Alg

open Tab Rel.Kernel Rel.Verify Rel Rel.KernelWF

/-- **Run starts group a column whose equal elements are contiguous.** `r 0 < … < r m = n` lists every
    run start of `key` below `n` and nothing else; then the run keys `key (r j)` are one-to-one and
    `key s = key (r j) ⟺ r j ≤ s < r (j+1)`. Encoding-free: each lane's kernel answers these hypotheses. -/
theorem runs_group {α : Type} {n m : Nat} (key : Nat → α) (r : Nat → Nat) (hlast : r m = n)
    (hasc : ∀ i j, i < j → j ≤ m → r i < r j) (h0 : 0 < n → r 0 = 0)
    (hstart : ∀ j, j < m → r j = 0 ∨ key (r j) ≠ key (r j - 1))
    (hall : ∀ s, s < n → (s = 0 ∨ key s ≠ key (s - 1)) → ∃ j, j < m ∧ r j = s)
    (hcont : ∀ s t u, s ≤ t → t ≤ u → u < n → key s = key u → key t = key s) :
    (∀ j j', j < m → j' < m → key (r j) = key (r j') → j = j') ∧
    (∀ s j, s < n → j < m → (key s = key (r j) ↔ r j ≤ s ∧ s < r (j + 1))) := by
  have hle : ∀ i j, i ≤ j → j ≤ m → r i ≤ r j := fun i j h hj => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact Nat.le_of_lt (hasc i j h hj)
    · exact Nat.le_refl _
  -- inside a run, every row holds its start's element
  have hin : ∀ j, j < m → ∀ s, r j ≤ s → s < r (j + 1) → key s = key (r j) := by
    intro j hj s
    induction s with
    | zero => intro h _; rw [Nat.le_zero.1 h]
    | succ s ih =>
      intro h1 h2
      rcases Nat.lt_or_eq_of_le h1 with h1 | h1
      · have hn : s + 1 < n := hlast ▸ Nat.lt_of_lt_of_le h2 (hle (j + 1) m hj (Nat.le_refl m))
        by_cases hk : key (s + 1) = key s
        · exact hk.trans (ih (Nat.le_of_lt_succ h1) (by omega))
        · exfalso
          obtain ⟨j', hj', e⟩ := hall (s + 1) hn (.inr hk)
          rcases Nat.lt_or_ge j' (j + 1) with h | h
          · have := hle j' j (by omega) (by omega); omega
          · have := hle (j + 1) j' h (by omega); omega
      · rw [← h1]
  have hcov : ∀ s, s < n → ∃ j, j < m ∧ r j ≤ s ∧ s < r (j + 1) := by
    intro s
    induction s with
    | zero =>
      intro hn
      have hm : 0 < m := Nat.pos_of_ne_zero fun e => by subst e; have := h0 hn; omega
      exact ⟨0, hm, Nat.le_of_eq (h0 hn), by have := hasc 0 (0 + 1) (by omega) hm; have := h0 hn; omega⟩
    | succ s ih =>
      intro hn
      obtain ⟨j, hj, h1, h2⟩ := ih (by omega)
      rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt h2) with h | h
      · exact ⟨j, hj, by omega, h⟩
      · have hj1 : j + 1 < m := by
          rcases Nat.lt_or_ge (j + 1) m with h' | h'
          · exact h'
          · have : j + 1 = m := by omega
            subst this; omega
        exact ⟨j + 1, hj1, by omega, by have := hasc (j + 1) (j + 1 + 1) (by omega) hj1; omega⟩
  have hinj : ∀ j j', j < j' → j' < m → key (r j) ≠ key (r j') := by
    intro j j' hjj hj' e
    have hlt := hasc j j' hjj (by omega)
    have hn : r j' < n := hlast ▸ hasc j' m hj' (Nat.le_refl _)
    rcases hstart j' hj' with h | h
    · omega
    · exact h ((hcont (r j) (r j' - 1) (r j') (by omega) (by omega) hn e).trans e).symm
  refine ⟨fun j j' hj hj' e => ?_, fun s j hs hj => ⟨fun e => ?_, fun ⟨h1, h2⟩ => hin j hj s h1 h2⟩⟩
  · rcases Nat.lt_trichotomy j j' with h | h | h
    · exact absurd e (hinj j j' h hj')
    · exact h
    · exact absurd e.symm (hinj j' j h hj)
  · obtain ⟨j', hj', h1, h2⟩ := hcov s hs
    have e' := (hin j' hj' s h1 h2).symm.trans e
    rcases Nat.lt_trichotomy j' j with h | h | h
    · exact absurd e' (hinj j' j h hj)
    · subst h; exact ⟨h1, h2⟩
    · exact absurd e'.symm (hinj j j' h hj')

/-- **The run-start fold cuts a column into its runs**, for any `f`: `B` holds `m` starts and then `n`, read
    back as naturals, ascending; where `key` agrees exactly where `f` does and its equal elements stand
    together, the run keys are one-to-one and `key s = key (r j) ⟺ r j ≤ s < r (j+1)` (`runs_group`). -/
theorem runs_fold {α β : Type} [BEq α] [LawfulBEq α] (f : Nat → α) (n : Nat) (t : UInt64) (ht : t.toNat = n)
    (key : Nat → β) (hk : ∀ i j, i < n → j < n → (key i = key j ↔ f i = f j))
    (hcont : ∀ s t u, s ≤ t → t ≤ u → u < n → key s = key u → key t = key s)
    (B : ByteArray) (hB : B = Column.pushBits ((List.range n).foldl (init := ByteArray.empty) fun acc i =>
      if i == 0 || f i != f (i - 1) then Column.pushBits acc i.toUInt64 8 else acc) t 8) :
    ∃ m, B.size = 8 * (m + 1) ∧ (Column.bitsAt B (m * 8) 8).toNat = n ∧
      (∀ i j, i < j → j ≤ m → (Column.bitsAt B (i * 8) 8).toNat < (Column.bitsAt B (j * 8) 8).toNat) ∧
      (∀ j j', j < m → j' < m →
        key (Column.bitsAt B (j * 8) 8).toNat = key (Column.bitsAt B (j' * 8) 8).toNat → j = j') ∧
      (∀ s j, s < n → j < m → (key s = key (Column.bitsAt B (j * 8) 8).toNat ↔
        (Column.bitsAt B (j * 8) 8).toNat ≤ s ∧ s < (Column.bitsAt B ((j + 1) * 8) 8).toNat)) ∧
      (∀ s, s < n → ∃ j, j < m ∧
        (Column.bitsAt B (j * 8) 8).toNat ≤ s ∧ s < (Column.bitsAt B ((j + 1) * 8) 8).toNat) := by
  have hn64 : n < 2 ^ 64 := ht ▸ UInt64.toNat_lt t
  let p : Nat → Bool := fun i => i == 0 || f i != f (i - 1)
  have hp : ∀ r, p r = true ↔ (r = 0 ∨ f r ≠ f (r - 1)) := fun r => by
    simp only [p, Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  have hf : ∀ (l : List Nat) (acc : ByteArray),
      l.foldl (fun acc i => if p i then Column.pushBits acc i.toUInt64 8 else acc) acc =
        (l.filter p).foldl (fun acc i => Column.pushBits acc i.toUInt64 8) acc := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro acc; simp only [List.foldl_cons, List.filter_cons]
      cases h : p a <;> simp only [ite_true, Bool.false_eq_true, ite_false, List.foldl_cons, ih]
  have htn : t = n.toUInt64 :=
    UInt64.toNat_inj.1 (by rw [ht, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn64])
  obtain ⟨F, hFd⟩ : ∃ F, F = (List.range n).filter p := ⟨_, rfl⟩
  have hout : B = (F ++ [n]).foldl (fun acc i => Column.pushBits acc i.toUInt64 8) ByteArray.empty := by
    rw [hB, htn, hFd, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hf]
  have hmem : ∀ x, x ∈ F ↔ x < n ∧ p x = true := fun x => by rw [hFd, List.mem_filter, List.mem_range]
  have hF : F.Pairwise (· < ·) := by
    rw [hFd]; exact (by simpa using (pairwise_map_range_iff (· < ·) id n).2 (fun i j h _ => h) :
      (List.range n).Pairwise (· < ·)).filter p
  have hL : (F ++ [n]).Pairwise (· < ·) := List.pairwise_append.2 ⟨hF, by simp,
    fun a ha b hb => by rw [List.mem_singleton] at hb; rw [hb]; exact ((hmem a).1 ha).1⟩
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun i : Nat => i.toUInt64) 8 (by decide) (F ++ [n]) ByteArray.empty
  rw [← hout, show ByteArray.empty.size = 0 from rfl] at hs hg
  have hlen : (F ++ [n]).length = F.length + 1 := by simp
  have hv : ∀ j (h : j < (F ++ [n]).length), (Column.bitsAt B (j * 8) 8).toNat = (F ++ [n])[j] := by
    intro j h
    have hle : (F ++ [n])[j] ≤ n := by
      have hm := List.getElem_mem h
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Nat.le_of_lt ((hmem _).1 hm).1
      · exact Nat.le_of_eq hm
    have h64 : (F ++ [n])[j] < 2 ^ 64 := by omega
    rw [show j * 8 = 0 + 8 * j by omega, hg j h, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt h64, show (2 : Nat) ^ (8 * 8) = 2 ^ 64 from rfl, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h64]
  have hleft : ∀ j (h : j < F.length), (F ++ [n])[j]'(by omega) = F[j] := fun j h => List.getElem_append_left h
  have hlast : (Column.bitsAt B (F.length * 8) 8).toNat = n := by
    rw [hv _ (by omega)]; simp
  have hasc : ∀ i j, i < j → j ≤ F.length →
      (Column.bitsAt B (i * 8) 8).toNat < (Column.bitsAt B (j * 8) 8).toNat := fun i j hij hj => by
    rw [hv i (by omega), hv j (by omega)]
    exact List.pairwise_iff_getElem.1 hL i j (by omega) (by omega) hij
  have hrj : ∀ j (h : j < F.length), (Column.bitsAt B (j * 8) 8).toNat = F[j] := fun j h => by
    rw [hv j (by omega), hleft j h]
  have h00 : 0 < n → 0 < F.length ∧ (Column.bitsAt B (0 * 8) 8).toNat = 0 := fun h0 => by
    have h0m : 0 ∈ F := (hmem 0).2 ⟨h0, rfl⟩
    have hpos := List.length_pos_of_mem h0m
    obtain ⟨k, hk', hk0⟩ := List.getElem_of_mem h0m
    refine ⟨hpos, ?_⟩
    rw [hrj 0 hpos]
    rcases Nat.eq_zero_or_pos k with rfl | hk''
    · exact hk0
    · have := List.pairwise_iff_getElem.1 hF 0 k hpos hk' hk''; omega
  -- every row below `n` lies in some run: the runs start at `0` and end at `n`
  have hcov : ∀ s, s < n → ∃ j, j < F.length ∧
      (Column.bitsAt B (j * 8) 8).toNat ≤ s ∧ s < (Column.bitsAt B ((j + 1) * 8) 8).toNat := by
    intro s
    induction s with
    | zero =>
      intro hn0
      obtain ⟨hm, e⟩ := h00 hn0
      exact ⟨0, hm, by omega, by have := hasc 0 (0 + 1) (by omega) hm; omega⟩
    | succ s ih =>
      intro hn'
      obtain ⟨j, hj, h1, h2⟩ := ih (by omega)
      rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt h2) with h | h
      · exact ⟨j, hj, by omega, h⟩
      · have hj1 : j + 1 < F.length := by
          rcases Nat.lt_or_ge (j + 1) F.length with h' | h'
          · exact h'
          · have : j + 1 = F.length := by omega
            rw [this] at h; omega
        exact ⟨j + 1, hj1, by omega, by have := hasc (j + 1) (j + 1 + 1) (by omega) hj1; omega⟩
  have G := runs_group key (fun j => (Column.bitsAt B (j * 8) 8).toNat) hlast hasc
    (fun h0 => (h00 h0).2)
    (fun j hj => by
      show (Column.bitsAt B (j * 8) 8).toNat = 0 ∨ key (Column.bitsAt B (j * 8) 8).toNat ≠
        key ((Column.bitsAt B (j * 8) 8).toNat - 1)
      rw [hrj j hj]
      have hm := (hmem _).1 (List.getElem_mem hj)
      exact ((hp _).1 hm.2).imp id fun h e => h ((hk _ _ hm.1 (by omega)).1 e))
    (fun s hs' h => by
      have hps : p s = true := (hp s).2 (h.imp id fun h e => h ((hk _ _ hs' (by omega)).2 e))
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem ((hmem s).2 ⟨hs', hps⟩)
      exact ⟨j, hj, by show (Column.bitsAt B (j * 8) 8).toNat = s; rw [hrj j hj, e]⟩)
    hcont
  exact ⟨F.length, by rw [hs, hlen]; omega, hlast, hasc, G.1, G.2, hcov⟩

end Rel.Alg
