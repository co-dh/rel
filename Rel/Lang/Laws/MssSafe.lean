import Rel.Lang.Laws.MssFuse

/-! # The no-overflow premises of `prefix ⦇[e, +]⦈ = ⦇[e, ⊤e ∪ +]⦈ʳ` on a bounded `i64` universe

`+` cut to a universe `TU` of bounded words (`arithDen`) is exact integer addition between members of `TU`. A list
is `safe` when every segment has a sum; there every partial sum is a member, so the fold's step commutes and associates
(`foldDen_cons_assoc`'s `hc`, `ha`), and `safe` is closed under prefix and tail (`hGp`, `hGt`). -/

namespace Rel.Lang
open Rel.Kernel

/-- The left fold over `i64` words, `E` and `V` named so that a `List Int64` argument elaborates. -/
abbrev FI (Te : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64)))
    (TS : Core.Rel (Obj.El (.prod (.atom .i64) (.atom .i64))) (Obj.El (.atom .i64))) :
    Core.Rel (Obj.El (.arr (.atom .i64))) (Obj.El (.atom .i64)) := foldDen (E := .atom .i64) (V := .atom .i64) Te TS

/-- A word of `TU` stays clear of the `i64` edge, so a sum of two of them is exact. -/
def Bnd (a : Int64) : Prop := -2 ^ 62 < a.toInt ∧ a.toInt < 2 ^ 62

/-- `+` on the universe `TU`: both operands and the result members, and the result is the sum of the integers. -/
theorem arithAdd_iff {TU : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64))} (hU : ∀ a b, TU a b → a = b ∧ Bnd a) (a b w : Int64) :
    arithDen .i64 Ew.add TU (a, b) w ↔ TU a a ∧ TU b b ∧ TU w w ∧ w.toInt = a.toInt + b.toInt := by
  refine (arithDen_iff .i64 Ew.add TU (a, b) w).trans ?_
  have hne : ∀ x : Int64, Bnd x → x ≠ Alg.nul := fun x hx e => by
    subst e
    have : Alg.nul.toInt = -2 ^ 63 := by decide
    obtain ⟨h1, -⟩ := hx; omega
  constructor
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩, v, hv, hvw⟩
    obtain ⟨rfl, ⟨ha1, ha2⟩⟩ := hU _ _ hc
    obtain ⟨rfl, ⟨hb1, hb2⟩⟩ := hU _ _ hd
    obtain ⟨-, -, h1, h2, rfl⟩ := (stepDen_add_iff _ _ _).1 hv
    obtain ⟨rfl, -⟩ := hU _ _ hvw
    refine ⟨hc, hd, hvw, ?_⟩
    rw [Int64.toInt_add, Int.bmod_eq_of_le (by omega) (by omega)]
  · rintro ⟨ha, hb, hw, h⟩
    obtain ⟨-, ha1, ha2⟩ := hU _ _ ha
    obtain ⟨-, hb1, hb2⟩ := hU _ _ hb
    have hs : a + b = w := by
      rw [← Int64.toInt_inj, Int64.toInt_add, Int.bmod_eq_of_le (by omega) (by omega), h]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, a + b, (stepDen_add_iff _ _ _).2 ⟨hne _ ⟨ha1, ha2⟩, hne _ ⟨hb1, hb2⟩, by omega, by omega, rfl⟩,
      hs ▸ hw⟩

theorem arithAdd_comm {TU : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64))} (hU : ∀ a b, TU a b → a = b ∧ Bnd a) (a b w : Int64) :
    arithDen .i64 Ew.add TU (a, b) w ↔ arithDen .i64 Ew.add TU (b, a) w := by
  rw [arithAdd_iff hU, arithAdd_iff hU]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h2, h1, h3, by omega⟩

/-- The integer sum of a list of words. -/
def ysum (ys : List Int64) : Int := ys.foldr (fun a s => a.toInt + s) 0

theorem ysum_cons (y : Int64) (ys : List Int64) : ysum (y :: ys) = y.toInt + ysum ys := rfl

theorem ysum_snoc (ys : List Int64) (y : Int64) : ysum (ys ++ [y]) = ysum ys + y.toInt := by
  induction ys with
  | nil => simp [ysum]
  | cons a as ih => rw [List.cons_append, ysum_cons, ih, ysum_cons]; omega

/-- The fold of `+` from the one seed `z` over `ys` is `z` plus the sum of `ys`, and the elements and (past the seed) the
    value are members. -/
theorem foldAdd_facts {TU : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64))} (hU : ∀ a b, TU a b → a = b ∧ Bnd a) {Te : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64))}
    {z : Int64} (hz : ∀ u, (∃ a, Te a u) ↔ u = z) (ys : List Int64) :
    ∀ v, FI Te (arithDen .i64 Ew.add TU) ys v →
      v.toInt = z.toInt + ysum ys ∧ (∀ y ∈ ys, TU y y) ∧ (ys ≠ [] → TU v v) := by
  induction h : ys.length generalizing ys with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 h
    intro v h; obtain rfl := (hz v).1 ((foldDen_empty ..).1 h); simp [ysum]
  | succ n ih =>
    obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left (by rintro rfl; simp at h)
    rw [List.concat_eq_append]
    intro v h'
    obtain ⟨u, hu, hs⟩ := (foldDen_snoc ..).1 h'
    have ih := ih ys (by simpa using h)
    obtain ⟨h1, h2, -⟩ := ih u hu
    obtain ⟨-, hy, hv, h4⟩ := (arithAdd_iff hU _ _ _).1 hs
    refine ⟨by rw [ysum_snoc]; omega, ?_, fun _ => hv⟩
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h2 x hx
    · rw [List.mem_singleton.1 hx]; exact hy

/-- The segments of a list that all have a sum. -/
def SumGood {α β : Type} (Sm : List α → β → Prop) (xs : List α) : Prop := ∀ b, b <:+: xs → ∃ w, Sm b w

theorem SumGood.infix {α β : Type} {Sm : List α → β → Prop} {xs ys : List α} (h : SumGood Sm xs) (hy : ys <:+: xs) :
    SumGood Sm ys := fun b hb => h b (hb.trans hy)

theorem SumGood.prefix {α β : Type} {Sm : List α → β → Prop} (ys zs : List α) (h : SumGood Sm (ys ++ zs)) :
    SumGood Sm ys := h.infix (List.prefix_append ys zs).isInfix

theorem SumGood.tail {α β : Type} {Sm : List α → β → Prop} (x : α) (xs : List α) (h : SumGood Sm (x :: xs)) :
    SumGood Sm xs := h.infix (List.suffix_cons x xs).isInfix

/-- The seed commutes with `+`. -/
theorem foldAdd_hc {TU : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64))} (hU : ∀ a b, TU a b → a = b ∧ Bnd a) (Te : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64))) (x w : Int64) :
    (∃ u, (∃ a, Te a u) ∧ arithDen .i64 Ew.add TU (u, x) w) ↔ ∃ u, (∃ a, Te a u) ∧ arithDen .i64 Ew.add TU (x, u) w :=
  exists_congr fun u => and_congr_right fun _ => arithAdd_comm hU u x w

/-- `+` associates on the fold value `v` of `ys` when `x :: (ys ++ [y])` is safe. -/
theorem foldAdd_ha {TU : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64))} (hU : ∀ a b, TU a b → a = b ∧ Bnd a) {Te : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64))}
    {z : Int64} (hz : ∀ u, (∃ a, Te a u) ↔ u = z) (x y : Int64) (ys : List Int64)
    (hg : SumGood (FI Te (arithDen .i64 Ew.add TU)) (x :: (ys ++ [y]))) (v w : Int64)
    (hv : FI Te (arithDen .i64 Ew.add TU) ys v) :
    (∃ u, arithDen .i64 Ew.add TU (x, v) u ∧ arithDen .i64 Ew.add TU (u, y) w) ↔
      ∃ v', arithDen .i64 Ew.add TU (v, y) v' ∧ arithDen .i64 Ew.add TU (x, v') w := by
  obtain ⟨w0, h0⟩ := hg [x] ⟨[], ys ++ [y], by simp⟩
  obtain ⟨w1, h1⟩ := hg (ys ++ [y]) (List.suffix_cons x _).isInfix
  obtain ⟨w2, h2⟩ := hg (x :: ys) (show x :: ys <+: x :: (ys ++ [y]) from ⟨[y], by simp⟩).isInfix
  have hx := (foldAdd_facts hU hz _ _ h0).2.1 x (by simp)
  have hvv := foldAdd_facts hU hz ys v hv
  obtain ⟨u, hu, hs1⟩ := (foldDen_snoc ..).1 h1
  have hu' := foldAdd_facts hU hz ys u hu
  have huv : u = v := by rw [← Int64.toInt_inj]; omega
  subst huv
  obtain ⟨hu1, hy, hw1, hw1'⟩ := (arithAdd_iff hU _ _ _).1 hs1
  have h2f := foldAdd_facts hU hz _ _ h2
  have hw2 := h2f.2.2 (by simp)
  have hs2 : arithDen .i64 Ew.add TU (x, u) w2 := by
    rw [arithAdd_iff hU]; refine ⟨hx, hu1, hw2, ?_⟩; have := h2f.1; rw [ysum_cons] at this; omega
  have hxw2 : w2.toInt = x.toInt + u.toInt := by have := h2f.1; rw [ysum_cons] at this; omega
  constructor
  · rintro ⟨u', hs, hs'⟩
    obtain ⟨-, -, hu'1, hu'2⟩ := (arithAdd_iff hU _ _ _).1 hs
    obtain ⟨-, -, hw, hw'⟩ := (arithAdd_iff hU _ _ _).1 hs'
    exact ⟨w1, (arithAdd_iff hU _ _ _).2 ⟨hu1, hy, hw1, hw1'⟩,
      (arithAdd_iff hU _ _ _).2 ⟨hx, hw1, hw, by omega⟩⟩
  · rintro ⟨v', hs, hs'⟩
    obtain ⟨-, -, hv'1, hv'2⟩ := (arithAdd_iff hU _ _ _).1 hs
    obtain ⟨-, -, hw, hw'⟩ := (arithAdd_iff hU _ _ _).1 hs'
    exact ⟨w2, hs2, (arithAdd_iff hU _ _ _).2 ⟨hw2, hy, hw, by omega⟩⟩

end Rel.Lang

