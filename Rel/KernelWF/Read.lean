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


theorem blockStart_succ (md : ByteArray) (b : Nat) :
    Column.blockStart md (b + 1) = Column.blockStart md b + Column.blk md * Column.widthAt md b / 8 := by
  simp [Column.blockStart, Nat.fold_succ]







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


end Rel.Kernel

-- from Rel.KernelWF.Lane
namespace Rel.Alg

open Tab Rel.Kernel Rel


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


end Rel.KernelWF

-- from Rel.KernelWF.RazeRowRec
namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Dep Rel Rel.Alg Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc


end Rel.KernelWF

-- from Rel.KernelWF.PickSpec
open Rel.Ext

namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Verify




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


end Rel.KernelWF

namespace Rel.Alg

open Tab Rel.Kernel Rel




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
  | _ => intro hwf; exfalso; rcases hk with rfl | rfl | rfl | rfl | rfl <;> cases t <;> simp_all [Enc.WF, orderKind, QAtomicType.width]







end Rel.Alg

-- from Rel.KernelWF.CodesSym
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel


end Rel.Alg

-- from Rel.KernelWF.CodesProd
namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel


end Rel.Alg

-- from Rel.KernelWF.AscSpec
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel Rel.KernelWF



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


/-- **`¬ Obj.lt` is antisymmetric where `Obj.key` is injective**: neither below the other means equal keys
    (`lt_trichotomy`), so equal elements. `Ordered` alone does not give it: every general atom keys as `[]`. -/
theorem _root_.Rel.Obj.eq_of_not_lt (A : Obj) (hA : ∀ x y : A.El, A.key x = A.key y → x = y) {x y : A.El}
    (h1 : ¬ A.lt x y) (h2 : ¬ A.lt y x) : x = y :=
  hA x y (((A.lt_trichotomy x y).resolve_left h1).resolve_right h2)

end Rel.Alg

-- from Rel.KernelWF.CrossSpec
namespace Rel.KernelWF

open Tab Rel.Kernel Rel Rel.Alg


end Rel.KernelWF

-- from Rel.KernelWF.JoinContent
namespace Rel.Alg

open Tab Rel.Kernel Rel.Verify Rel


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


end Rel.Alg
