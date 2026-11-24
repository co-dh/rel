module

public import Rel.Lang.PreludeRows
public import Rel.Lang.PreludeDfn
public import Rel.Lang.PreludeConcat
public import Rel.Programs.Prelude

@[expose] public section

/-! `merge(Q) ≜ ⟨⟨𝟙, nil⟩, cat⟩ loop(π₁ (l …)) π₂` (`Programs/Prelude.lean`) means the row `merge`'s `rowDens` term,
    `List.merge` by `Q`'s test (B10b, architecture §4 "merge(Q)"): the state is `((xs, ys), acc)`, the clock `cat(x, y)`
    gives `|x| + |y|` rounds, each moves the head of `xs` (when `a Q b` or `ys` is empty) or of `ys` onto `acc`.
    The loop's step is `mstep`; after `t` rounds `acc ++ merge xs ys = merge x y` and `|xs| + |ys| = |x| + |y| - t`
    (`mstep_inv`), so the final state has empty lists and `acc = merge x y` (`loopDen_merge`). -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open Classical

/-- One round of the merge loop on `((xs, ys), acc)`: the head of `xs` when it is `le`-before the head of `ys` or `ys`
    is empty, else the head of `ys`. -/
def mstep {α : Type} (le : α → α → Bool) : (List α × List α) × List α → (List α × List α) × List α
  | ((a :: xs, b :: ys), acc) => if le a b then ((xs, b :: ys), acc ++ [a]) else ((a :: xs, ys), acc ++ [b])
  | ((a :: xs, []), acc) => ((xs, []), acc ++ [a])
  | (([], b :: ys), acc) => (([], ys), acc ++ [b])
  | s => s

/-- A round keeps `acc ++ merge xs ys` and takes one element off the lists. -/
theorem mstep_inv {α : Type} (le : α → α → Bool) (s : (List α × List α) × List α) (h : s.1.1 ≠ [] ∨ s.1.2 ≠ []) :
    (mstep le s).2 ++ List.merge (mstep le s).1.1 (mstep le s).1.2 le = s.2 ++ List.merge s.1.1 s.1.2 le ∧
      (mstep le s).1.1.length + (mstep le s).1.2.length + 1 = s.1.1.length + s.1.2.length := by
  obtain ⟨⟨xs, ys⟩, acc⟩ := s
  rcases xs with _ | ⟨a, xs⟩ <;> rcases ys with _ | ⟨b, ys⟩
  · simp at h
  · simp [mstep]
  · simp [mstep]
  · by_cases hab : le a b <;> simp [mstep, hab] <;> omega

/-- `mstep` run `t` times. -/
def miter {α : Type} (le : α → α → Bool) : Nat → (List α × List α) × List α → (List α × List α) × List α
  | 0, s => s
  | t + 1, s => mstep le (miter le t s)

/-- After `t ≤ n` rounds from `((x, y), [])`, `n = |x| + |y|`: the invariant of `mstep_inv`. -/
theorem mstep_iter {α : Type} (le : α → α → Bool) (x y : List α) (t : Nat) (ht : t ≤ x.length + y.length) :
    (miter le t ((x, y), [])).2 ++ List.merge (miter le t ((x, y), [])).1.1 (miter le t ((x, y), [])).1.2 le =
        List.merge x y le ∧
      (miter le t ((x, y), [])).1.1.length + (miter le t ((x, y), [])).1.2.length = x.length + y.length - t := by
  induction t with
  | zero => simp [miter]
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hne : (miter le t ((x, y), [])).1.1 ≠ [] ∨ (miter le t ((x, y), [])).1.2 ≠ [] := by
      refine Classical.byContradiction fun hc => ?_
      simp only [not_or, ne_eq, not_not] at hc
      simp [hc.1, hc.2] at h2
      omega
    obtain ⟨h3, h4⟩ := mstep_inv le _ hne
    rw [miter]
    exact ⟨h3.trans h1, by omega⟩

/-- The loop with step `T = mstep` (on non-final states) from `((x, y), [])` clocked by `x ++ y` ends at `merge x y`. -/
theorem loopDen_merge {B : Obj} (le : B.El → B.El → Bool)
    (T : Core.Rel (Obj.El (.prod (.prod (.prod (.arr B) (.arr B)) (.arr B)) B))
      (Obj.El (.prod (.prod (.arr B) (.arr B)) (.arr B))))
    (hT : ∀ s e w, T (s, e) w ↔ (s.1.1 ≠ [] ∨ s.1.2 ≠ []) ∧ w = mstep le s) (x y : List B.El) (c) :
    loopDen T (((x, y), []), x ++ y) c ↔ c = (([], []), List.merge x y le) := by
  rw [loopDen_iff]
  have hlen : (x ++ y).length = x.length + y.length := List.length_append
  constructor
  · rintro ⟨g, hg0, hg, rfl⟩
    have hgi : ∀ t, t ≤ x.length + y.length → g t = miter le t ((x, y), []) := by
      intro t
      induction t with
      | zero => intro _; exact hg0
      | succ t ih =>
        intro ht
        have := (hT _ _ _).1 (hg t (by simp only [hlen]; omega))
        rw [this.2, ih (by omega)]; rfl
    simp only [hlen]
    obtain ⟨h1, h2⟩ := mstep_iter le x y _ (Nat.le_refl _)
    rw [← hgi _ (Nat.le_refl _)] at h1 h2
    have e1 : (g (x.length + y.length)).1.1 = [] := List.length_eq_zero_iff.1 (by omega)
    have e2 : (g (x.length + y.length)).1.2 = [] := List.length_eq_zero_iff.1 (by omega)
    rw [e1, e2] at h1
    simp only [List.nil_merge, List.append_nil] at h1
    exact Prod.ext (Prod.ext e1 e2) h1
  · rintro rfl
    refine ⟨fun t => miter le t ((x, y), []), rfl, fun t ht => ?_, ?_⟩
    · have ht' : t < x.length + y.length := by simpa [hlen] using ht
      obtain ⟨h1, h2⟩ := mstep_iter le x y t (Nat.le_of_lt ht')
      refine (hT _ _ _).2 ⟨?_, rfl⟩
      refine Classical.byContradiction fun hc => ?_
      simp only [not_or, ne_eq, not_not] at hc
      simp [hc.1, hc.2] at h2
      omega
    · simp only [hlen]
      obtain ⟨h1, h2⟩ := mstep_iter le x y _ (Nat.le_refl _)
      generalize miter le (x.length + y.length) ((x, y), []) = s at h1 h2 ⊢
      obtain ⟨⟨xs, ys⟩, acc⟩ := s
      simp only [Nat.sub_self, Nat.add_eq_zero_iff, List.length_eq_zero_iff] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp only [List.nil_merge, List.append_nil] at h1
      simp [h1]

theorem Prim.den_loop {X Y : Obj} (T : Core.Rel (Obj.El (.prod X Y)) (Obj.El X)) :
    Prim.den (rowOf "loop") (.prod X (.arr Y)) X [⟨.prod X Y, X, T⟩] = loopDen T := by
  have hs : (rowOf "loop").sig = ([((.prod (.var {} "X") (.var {} "Y"), .var {} "X"), some false)],
      .prod (.var {} "X") (.list (.var {} "Y")), .var {} "X") := rfl
  have ho : (rowOf "loop").objs (.prod X (.arr Y)) X [(.prod X Y, X)] = some [X, Y] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "loop").sym) = some ⟨RowCode.loop, fun σ =>
      Sem.one (X := .prod (σ₁ σ) (σ₂ σ)) (Y := σ₁ σ) loopDen⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

theorem Prim.den_merge {B : Obj} (T : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) :
    Prim.den (rowOf "merge") (.prod (.arr B) (.arr B)) (.arr B) [⟨.prod B B, .prod B B, T⟩] =
      fun p ys => ys = List.merge p.1 p.2 fun a b => decide (T (a, b) (a, b)) := by
  have hs : (rowOf "merge").sig = ([((.var {} "B", .var {} "B"), some true)],
      .prod (.list (.var {} "B")) (.list (.var {} "B")), .list (.var {} "B")) := rfl
  have ho : (rowOf "merge").objs (.prod (.arr B) (.arr B)) (.arr B) [(.prod B B, .prod B B)] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "merge").sym) = some ⟨RowCode.merge, fun σ =>
      Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) fun T =>
        graph fun p => List.merge p.1 p.2 fun a b => decide (T (a, b) (a, b))⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- The literal `0` the prelude elaborates for `at(0)`: the one-row table `{(0, 0)}` of `i64`. -/
def Tm.zeroLit : Tm (.atom .i64) (.atom .i64) :=
  .val (Gen.relV (.atom .i64) (.atom .i64) (USize.ofNat 1)
    (Gen.atom .i64 (USize.ofNat 1) "0000000000000000000000000000000000000000000000000000000000000000000000000000008001000000000000000a0000000000000000" "")
    (Gen.atom .i64 (USize.ofNat 1) "0000000000000000000000000000000000000000000000000000000000000000000000000000008001000000000000000a0000000000000000" "")).1

/-- `at(0)` as the prelude elaborates it (`Tm.at0` with the table literal for `0`). -/
def Tm.headAt {B : Obj} : Tm (.arr B) B := .comp (.pair .id (.top Tm.zeroLit)) (.prim indexRow)

/-- The prelude's `tail`, `cat° dom(π₁ (at(0)τ ∩ 𝟙))π₂`, as a call. -/
def Tm.mergeTail (B : Obj) : Tm (.arr B) (.arr B) :=
  .call [] `Rel.Programs.prelude.tail (some `Rel.Programs.prelude.tail.conv) [B]
    (.comp (.comp (.prim (rowOf "uncat")) (.dom (.comp .outl (.meet (.comp (Tm.headAt (B := B)) (.prim (rowOf "τ"))) .id)))) .outr)

theorem Tm.headAt_den (ρ : Val) {B : Obj} (xs : Obj.El (.arr B)) (b : Obj.El B) :
    (Tm.headAt (B := B)).den ρ xs b ↔ ∃ h : 0 < xs.length, b = xs[0]'h := by
  rw [← Tm.at0_den ρ xs b]
  have hz : Tm.zeroLit.den ρ = (Tm.uni (A := .atom .i64) (zeroCol .i64 rfl)).den ρ := by
    funext x y; apply propext
    rw [Tm.zeroLit, Tm.relV_den, Gen.atom_zero]
    simp only [Tm.den, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
    constructor
    · rintro ⟨i, h1, h2⟩; exact ⟨i, by rw [h1], by rw [h2]⟩
    · rintro ⟨i, h1, h2⟩; exact ⟨i, by rw [h1], by rw [h2]⟩
  simp only [Tm.headAt, Tm.at0, Tm.den, hz]

theorem Tm.mergeTail_den (ρ : Val) {B : Obj} (xs ys : Obj.El (.arr B)) :
    (Tm.mergeTail B).den ρ xs ys ↔ ∃ a, xs = a :: ys := by
  simp only [Tm.mergeTail, Tm.den, Val.args, Tm.dom_den, Prim.den_uncat, Prim.den_tau, Core.Rel.comp, Core.Rel.inter,
    Core.Rel.recip, Core.Rel.graph, Core.Rel.id, Tm.headAt_den, exists_eq_left]
  constructor
  · rintro ⟨b, ⟨b1, hx, rfl, b2, ⟨⟨b', -, hb2⟩, hfst⟩, -⟩, rfl⟩
    exact ⟨b', by rw [hx, hfst, hb2]; rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨([a], ys), ⟨([a], ys), rfl, rfl, [a], ⟨⟨a, ⟨by simp, rfl⟩, rfl⟩, rfl⟩, ⟨a, ⟨by simp, rfl⟩, rfl⟩, rfl⟩, rfl⟩

end Rel.Lang
