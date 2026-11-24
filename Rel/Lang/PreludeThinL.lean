module

public import Rel.Lang.PreludeRows
public import Rel.Lang.DfnLaw
public import Rel.Programs.Prelude

@[expose] public section

/-! `thinL(Q : α ⟶ α) : [α] ⟶ [α] ≜ ⦇[nil, bump(Q)]⦈ʳ where h ≜ ⟨π₁, π₂ at(0)⟩` (`Programs/Prelude.lean`) means the row
    `thinL`'s `rowDens` term `thinLDen` (B10b): the definition's term is built here. The step is a relation, a union
    of the three ways `x` meets the head `b` of the accumulator, so the fold is read as its chain (`foldrDen_iff`). -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open Classical

/-- The step of `thinL(Q)` on `(x, ys)`, `h` the pair `(x, head ys)`, `c` the coreflexive `cor(Q)` on pairs and `tl`
    `tail`: `x :: tail ys` where `x Q b`, `ys` where `b Q x`, `x :: ys` where neither (or `ys = []`). -/
def Tm.thinLStep {B : Obj} (h : Tm (.prod B (.arr B)) (.prod B B)) (c : Tm (.prod B B) (.prod B B))
    (tl : Tm (.arr B) (.arr B)) : Tm (.prod B (.arr B)) (.arr B) :=
  let d₁ : Tm (.prod B (.arr B)) (.prod B (.arr B)) := .dom (.comp h c)
  let d₂ : Tm (.prod B (.arr B)) (.prod B (.arr B)) := .dom (.comp (.comp h (.pair .outr .outl)) c)
  .join (.join (.comp (.comp d₁ (.pair .outl (.comp .outr tl))) (.prim (rowOf "cons"))) (.comp d₂ .outr))
    (.comp (.diff (.diff .id d₁) d₂) (.prim (rowOf "cons")))

/-- `thinL(Q)` at `[B] ⟶ [B]`: the right fold from `nil` of `Tm.thinLStep`. -/
def Tm.thinLDef {B : Obj} (h : Tm (.prod B (.arr B)) (.prod B B)) (c : Tm (.prod B B) (.prod B B))
    (tl : Tm (.arr B) (.arr B)) : Tm (.arr B) (.arr B) := .foldr .nil (Tm.thinLStep h c tl)

theorem Prim.den_thinL {B : Obj} (T : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) :
    Prim.den (rowOf "thinL") (.arr B) (.arr B) [⟨.prod B B, .prod B B, T⟩] =
      Rel.Rep.thinLDen fun a b => decide (T (a, b) (a, b)) := by
  have hs : (rowOf "thinL").sig =
      ([((.var {} "B", .var {} "B"), some true)], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have ho : (rowOf "thinL").objs (.arr B) (.arr B) [(.prod B B, .prod B B)] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "thinL").sym) = some ⟨RowCode.thinL, fun σ =>
      Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) fun T =>
        Rel.Rep.thinLDen fun a b => decide (T (a, b) (a, b))⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- The step on `(x, u)`, wherever `h` reads `(x, head u)` of a non-empty `u`, `c` is `Q` on pairs read as the order
    `le`, and `tl` drops the head: the three ways `x` meets the head `b` of `u`, or `[x]` when `u = []`. -/
theorem Tm.thinLStep_den (ρ : Val) {B : Obj} (h : Tm (.prod B (.arr B)) (.prod B B)) (c : Tm (.prod B B) (.prod B B))
    (tl : Tm (.arr B) (.arr B)) (le : B.El → B.El → Bool)
    (hh : ∀ x ys p, h.den ρ (x, ys) p ↔ ∃ y t, ys = y :: t ∧ p = (x, y))
    (hc : ∀ a b p, c.den ρ (a, b) p ↔ p = (a, b) ∧ le a b = true)
    (htl : ∀ a as w, tl.den ρ (a :: as) w ↔ w = as) (x : B.El) (u v : List B.El) :
    (Tm.thinLStep h c tl).den ρ (x, u) v ↔ (u = [] ∧ v = [x]) ∨ ∃ b bs, u = b :: bs ∧
      ((le x b = true ∧ v = x :: bs) ∨ (le b x = true ∧ v = u) ∨ (le x b = false ∧ le b x = false ∧ v = x :: u)) := by
  have hd₁ : ∀ q, (Tm.dom (.comp h c)).den ρ (x, u) q ↔ q = (x, u) ∧ ∃ b bs, u = b :: bs ∧ le x b = true := by
    intro q
    simp only [Tm.dom_den, Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Tm.den, hh, hc]
    constructor
    · rintro ⟨rfl, p, ⟨_, ⟨y, t, rfl, rfl⟩, rfl, hl⟩, -⟩
      exact ⟨rfl, y, t, rfl, hl⟩
    · rintro ⟨rfl, y, t, rfl, hl⟩
      exact ⟨rfl, _, ⟨_, ⟨y, t, rfl, rfl⟩, rfl, hl⟩, _, ⟨y, t, rfl, rfl⟩, rfl, hl⟩
  have hd₂ : ∀ q, (Tm.dom (.comp (.comp h (.pair .outr .outl)) c)).den ρ (x, u) q ↔
      q = (x, u) ∧ ∃ b bs, u = b :: bs ∧ le b x = true := by
    intro q
    simp only [Tm.dom_den, Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Tm.den, hh, hc,
      Core.Rel.rpair, Core.Rel.graph]
    constructor
    · rintro ⟨rfl, _, ⟨⟨a₁, a₂⟩, ⟨_, ⟨y, t, rfl, rfl⟩, h₁, h₂⟩, -, hl⟩, -⟩
      obtain rfl : a₁ = y := h₁
      obtain rfl : a₂ = x := h₂
      exact ⟨rfl, a₁, t, rfl, hl⟩
    · rintro ⟨rfl, y, t, rfl, hl⟩
      exact ⟨rfl, (y, x), ⟨(y, x), ⟨(x, y), ⟨y, t, rfl, rfl⟩, rfl, rfl⟩, rfl, hl⟩, (y, x),
        ⟨(x, y), ⟨y, t, rfl, rfl⟩, rfl, rfl⟩, rfl, hl⟩
  simp only [Tm.thinLStep, Tm.den, Prim.den_cons, Core.Rel.union, Core.Rel.diff, Core.Rel.comp, Core.Rel.id,
    Core.Rel.graph, Core.Rel.rpair, hd₁, hd₂]
  rcases u with _ | ⟨b, bs⟩
  · simp
  · simp only [Prod.exists, exists_eq_left, Prod.mk.injEq, List.cons.injEq]
    simp only [exists_and_right, exists_eq_left, exists_eq_left', and_assoc, exists_and_left,
      true_and, reduceCtorEq, false_and, false_or, exists_eq', htl]
    cases hx : le x b <;> cases hb : le b x <;> simp

/-- **A fold of `thinL`'s step means the row**, whatever its seed `e` whose only value is `[]`: its chain
    `ys[n], …, ys[0]` is `thinLDen`'s (`foldrDen_iff`). -/
theorem Tm.thinLFold_row (ρ : Val) {B : Obj} (e : Tm (.arr B) (.arr B)) (h : Tm (.prod B (.arr B)) (.prod B B))
    (c : Tm (.prod B B) (.prod B B)) (tl : Tm (.arr B) (.arr B)) (le : B.El → B.El → Bool)
    (he : ∀ v, (∃ a, e.den ρ a v) ↔ v = [])
    (hh : ∀ x ys p, h.den ρ (x, ys) p ↔ ∃ y t, ys = y :: t ∧ p = (x, y))
    (hc : ∀ a b p, c.den ρ (a, b) p ↔ p = (a, b) ∧ le a b = true)
    (htl : ∀ a as w, tl.den ρ (a :: as) w ↔ w = as) (xs ys : Obj.El (.arr B)) :
    (Tm.foldr e (Tm.thinLStep h c tl)).den ρ xs ys ↔ Rel.Rep.thinLDen le xs ys := by
  simp only [Tm.den]
  rw [foldrDen_iff]
  refine exists_congr fun zs => exists_congr fun hz => and_congr (he _) (and_congr ?_ Iff.rfl)
  exact forall_congr' fun t => forall_congr' fun ht => Tm.thinLStep_den ρ h c tl le hh hc htl _ _ _

/-- **The definition of `thinL` means the row**: the chain of bumps of `xs` from `[]`, `le` the test `Q` on pairs. -/
theorem Tm.thinLDef_row (ρ : Val) {B : Obj} (h : Tm (.prod B (.arr B)) (.prod B B)) (c : Tm (.prod B B) (.prod B B))
    (tl : Tm (.arr B) (.arr B)) (T : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B)))
    (hh : ∀ x ys p, h.den ρ (x, ys) p ↔ ∃ y t, ys = y :: t ∧ p = (x, y))
    (hc : ∀ a b p, c.den ρ (a, b) p ↔ p = (a, b) ∧ T (a, b) (a, b))
    (htl : ∀ a as w, tl.den ρ (a :: as) w ↔ w = as) (xs ys : Obj.El (.arr B)) :
    (Tm.thinLDef h c tl).den ρ xs ys ↔ Prim.den (rowOf "thinL") (.arr B) (.arr B) [⟨.prod B B, .prod B B, T⟩] xs ys := by
  rw [Prim.den_thinL]
  refine Tm.thinLFold_row ρ _ h c tl _ (fun v => ?_) hh (fun a b p => by simp [hc]) htl xs ys
  simp only [Tm.nil, Tm.den, Prim.den_nilRow, nilDen]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨[], h⟩⟩

theorem Tm.thinLDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.atom .general).inst ph σ).arr ((Obj.atom .general).inst ph σ).arr}
    (ht : Rel.Programs.prelude.thinL.body.instObj ph σ = .ok t') (xs ys : Obj.El ((Obj.atom .general).inst ph σ).arr) :
    t'.den ρ xs ys ↔
      Prim.den (rowOf "thinL") ((Obj.atom .general).inst ph σ).arr ((Obj.atom .general).inst ph σ).arr
        [⟨_, _, (pairTest (Tm.var 1 : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ))).den ρ⟩] xs ys := by
  obtain rfl := Except.ok.inj ht
  rw [Prim.den_thinL]
  show Tm.den _ (Tm.foldr _ (Tm.thinLStep _ _ _)) xs ys ↔ _
  refine (Tm.thinLFold_row _ _ _ _ _ (fun a b => decide ((pairTest (Tm.var 1)).den ρ (a, b) (a, b))) ?he ?hh ?hc ?htl xs ys).trans ?_
  case he =>
    intro v
    simp only [Tm.den, Tm.argDen, cast_eq]
    erw [Prim.den_ranRow, Prim.den_nilRow]
    simp only [Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, nilDen]
    have i : Fin (USize.ofNat 1).toNat := ⟨0, by simp [USize.toNat_ofNat]⟩
    constructor
    · rintro ⟨a, rfl, b, ⟨b₁, -, -⟩, b₂, -, h⟩; exact h
    · rintro rfl; exact ⟨[], rfl, _, ⟨_, ⟨i, rfl, rfl⟩, rfl⟩, _, ⟨i, rfl, rfl⟩, rfl⟩
  case hh =>
    intro x ys p
    simp only [Tm.den, Val.args, Val.bind, cast_eq]
    simp only [if_true]
    rw [dif_pos ⟨rfl, rfl⟩]
    simp only [Gen.atom_zero]
    have hu : Rep.rep (Gen.relV (.atom .i64) (.atom .i64) (USize.ofNat 1) (zeroCol .i64 rfl, true)
        (zeroCol .i64 rfl, true)).fst = (Tm.uni (A := .atom .i64) (zeroCol .i64 rfl)).den ρ := by
      funext x y; apply propext
      refine (Tm.relV_den ρ (zeroCol .i64 rfl, true) (zeroCol .i64 rfl, true) x y).trans ?_
      simp only [Tm.den, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
      exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h1.symm, h2.symm⟩, fun ⟨i, h1, h2⟩ => ⟨i, h1.symm, h2.symm⟩⟩
    rw [hu]
    have h0 := fun b => Tm.at0_den ρ (B := (Obj.atom .general).inst ph σ) ys b
    simp only [Tm.at0, Tm.den, Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph] at h0
    simp only [Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph]
    constructor
    · rintro ⟨h1, q, rfl, hat⟩
      obtain ⟨hl, hb⟩ := (h0 _).1 hat
      cases q with
      | nil => exact absurd hl (by simp)
      | cons y t => exact ⟨y, t, rfl, Prod.ext h1 (by simpa using hb)⟩
    · rintro ⟨y, t, rfl, rfl⟩
      exact ⟨rfl, _, rfl, (h0 _).2 ⟨by simp, rfl⟩⟩
  case hc =>
    intro a b p
    simp only [Tm.den, Tm.argDen, Val.args, Val.bind, cast_eq]
    erw [Prim.den_domRow]
    simp [pairTest, Tm.dom_den, Tm.den, Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
    constructor
    · rintro ⟨rfl, h⟩; simp_all
    · rintro ⟨rfl, h⟩; simp_all
  case htl =>
    intro a as w
    simp only [Tm.den, Tm.argDen, Val.args, cast_eq]
    erw [Prim.den_uncat, Prim.den_domRow, Prim.den_tau]
    simp only [Gen.atom_zero]
    have hu : Rep.rep (Gen.relV (.atom .i64) (.atom .i64) (USize.ofNat 1) (zeroCol .i64 rfl, true)
        (zeroCol .i64 rfl, true)).fst = (Tm.uni (A := .atom .i64) (zeroCol .i64 rfl)).den ρ := by
      funext x y; apply propext
      refine (Tm.relV_den ρ (zeroCol .i64 rfl, true) (zeroCol .i64 rfl, true) x y).trans ?_
      simp only [Tm.den, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
      exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h1.symm, h2.symm⟩, fun ⟨i, h1, h2⟩ => ⟨i, h1.symm, h2.symm⟩⟩
    rw [hu]
    have h0 := fun xs b => Tm.at0_den ρ (B := (Obj.atom .general).inst ph σ) xs b
    simp only [Tm.at0, Tm.den, Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph, Core.Rel.id, Core.Rel.recip, indexRow] at h0
    simp only [Tm.den, Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph, Core.Rel.inter, Core.Rel.id, Core.Rel.recip]
    have hX := fun (a : (Obj.inst ph σ (Obj.atom .general)).El) => (h0 [a] a).2 ⟨by simp, rfl⟩
    constructor
    · rintro ⟨p, ⟨_, hcat, rfl, _, ⟨_, rfl, ⟨y, -, rfl⟩, hq⟩, -⟩, rfl⟩
      simp only [hq, List.singleton_append] at hcat
      exact (List.cons.inj hcat).2.symm
    · intro hw
      exact ⟨([a], as), ⟨([a], as), rfl, rfl, [a], ⟨[a], rfl, ⟨a, hX a, rfl⟩, rfl⟩, [a], rfl, ⟨a, hX a, rfl⟩, rfl⟩, hw⟩
  exact Iff.rfl

end Rel.Lang
