module

public import Rel.KernelSpec.Encoding
public import Rel.KernelSpec.Group
public import Rel.Kernel.Need
public import Rel.Kernel.Sort
public import Rel.Kernel.Coc
public import Rel.Kernel.Scan
public import Rel.Kernel.Value
public import Rel.Kernel.Search

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Verify.Codes` the Rel kernels reach; `Rel.Verify.Codes` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel
open Rel.Kernel.Scan (Kind)

/-- Two indices share a group exactly when they share a key. -/
theorem groupOf_iff {α : Type} [DecidableEq α] {g : Nat → α} {m i j : Nat} (hi : i < m) (hj : j < m) :
    groupOf g m i = groupOf g m j ↔ g i = g j :=
  ⟨fun e => ((groupOf_eq_iff hi (groupOf_lt hj)).1 e).trans (groupOf_get hj),
   fun e => (groupOf_eq_iff hi (groupOf_lt hj)).2 (e.trans (groupOf_get hj).symm)⟩

/-- Every id below `n` fits the width `idWidthOf n` packs it at, for any count a `USize` holds. -/
theorem lt_idWidthOf {x n : Nat} (hx : x < n) (hn : n ≤ 2 ^ 64) : x < 2 ^ Column.idWidthOf n := by
  unfold Column.idWidthOf Column.widthFor
  split
  · exact Nat.lt_of_lt_of_le (show x < 1 by omega) (Nat.one_le_two_pow)
  · rename_i h0
    have hl := widthFor_le (n - 1) (by omega)
    rw [Column.widthFor, if_neg h0] at hl
    have hlane : Nat.log2 (n - 1) + 1 ≤ Column.laneWidth (Nat.log2 (n - 1) + 1) := by
      unfold Column.laneWidth; repeat' split
      all_goals omega
    exact Nat.lt_of_le_of_lt (Nat.le_sub_one_of_lt hx)
      (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) hlane))

/-- The kernels' `firstsBy` (a `BEq` key) is the specification's `firstsOf` at a lawful one. -/
theorem firstsBy_eq {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (m : Nat) (key : Nat → α) :
    Order.firstsBy m key = firstsOf key m := by
  have hb : ∀ a b : α, (a != b) = !decide (a = b) := fun a b => by
    rw [bne, Bool.eq_iff_iff.2 (show (a == b) = true ↔ decide (a = b) = true by rw [beq_iff_eq, decide_eq_true_iff])]
  unfold Order.firstsBy firstsOf; simp only [hb]

/-- The kernels' group rule (`groupIn` over `firstsBy`, a `BEq` key) is the specification's `groupOf` at a lawful one. -/
theorem groupIn_firstsBy {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (m : Nat) (key : Nat → α) (i : Nat) :
    Order.groupIn (Order.firstsBy m key) key i = groupOf key m i := by
  have hb : ∀ a b : α, (a == b) = decide (a = b) := fun a b => Bool.eq_iff_iff.2 (by
    rw [beq_iff_eq, decide_eq_true_iff])
  simp only [Order.groupIn, groupOf, firstsBy_eq, hb]





end Rel.Verify
