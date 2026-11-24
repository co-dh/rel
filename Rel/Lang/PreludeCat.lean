module

public import Rel.Lang.PreludeRows
public import Rel.Lang.PreludeConcat
public import Rel.Lang.PreludeLoop
public import Rel.Programs.Prelude

@[expose] public section

/-! `cat : [α]×[α] ⟶ [α] ≜ ⟨π₂, π₁ r⟩ loop(s) where s ≜ ⟨π₂,π₁⟩cons, r ≜ ⟨nil,𝟙⟩ loop(s)` (`Programs/Prelude.lean`) means
    the row `cat`'s `rowDens` term `xs ++ ys` (B10b): `s` is `cons` on (acc, x), so the left fold `loop(s)` of a list `l`
    from `a` is `l.reverse ++ a` (`loopDen_cons`); `r` reverses, and `cat (xs, ys)` folds the reversed `xs` from `ys`. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The left fold of `cons` on (acc, x), from `a` over `l`, is `l.reverse ++ a`. -/
theorem loopDen_cons {B : Obj} (T : Core.Rel (Obj.El (.prod (.arr B) B)) (Obj.El (.arr B)))
    (hT : ∀ acc y w, T (acc, y) w ↔ w = y :: acc) (a l : List B.El) (c : List B.El) :
    loopDen T (a, l) c ↔ c = l.reverse ++ a := by
  rw [loopDen_iff]
  have tk : ∀ t (h : t < l.length), l.take (t + 1) = l.take t ++ [l[t]] := fun t h => by
    rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl
  have key : ∀ g : Nat → List B.El, g 0 = a → (∀ t (ht : t < l.length), T (g t, l[t]'ht) (g (t + 1))) →
      ∀ t, t ≤ l.length → g t = (l.take t).reverse ++ a := by
    intro g h0 hg t
    induction t with
    | zero => intro _; simpa using h0
    | succ t ih =>
      intro ht
      have := (hT _ _ _).1 (hg t (by omega))
      rw [this, ih (by omega), tk t (by omega)]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  constructor
  · rintro ⟨g, h0, hg, rfl⟩
    rw [key g h0 hg _ (Nat.le_refl _)]; simp
  · rintro rfl
    refine ⟨fun t => (l.take t).reverse ++ a, by simp, fun t ht => (hT _ _ _).2 ?_, by simp⟩
    dsimp only
    rw [tk t ht]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]

/-- `cat` at `[B]×[B] ⟶ [B]`: the prelude body `prelude.cat.body` as the term the elaborator builds (`s` the variable 1,
    `r` the variable 8). -/
def Tm.catDef (B : Obj) : Tm (.prod (.arr B) (.arr B)) (.arr B) :=
  .arg (.call [1] `s none []
    (.arg (.arg (.call [8, 1] `r none []
        (.comp (.pair .outr (.comp .outl (.var 8 : Tm (.arr B) (.arr B))))
          (.arg (.prim (rowOf "loop") : Tm (.prod (.arr B) (.arr B)) (.arr B)) (.var 1 : Tm (.prod (.arr B) B) (.arr B)))
          : Tm (.prod (.arr B) (.arr B)) (.arr B)))
      (.comp (.pair (.nil : Tm (.arr B) (.arr B)) .id)
        (.arg (.prim (rowOf "loop") : Tm (.prod (.arr B) (.arr B)) (.arr B)) (.var 1 : Tm (.prod (.arr B) B) (.arr B)))
        : Tm (.arr B) (.arr B)))
      (.var 1 : Tm (.prod (.arr B) B) (.arr B))))
    (.comp (.pair .outr .outl) (.prim (rowOf "cons")) : Tm (.prod (.arr B) B) (.arr B))

/-- **The definition of `cat` means the row**: `zs` is `xs ++ ys`. -/
theorem Tm.catDef_row (ρ : Val) {B : Obj} (p : (Obj.prod (.arr B) (.arr B)).El) (zs : (Obj.arr B).El) :
    (Tm.catDef B).den ρ p zs ↔ Prim.den (rowOf "cat") (.prod (.arr B) (.arr B)) (.arr B) [] p zs := by
  rw [Prim.den_cat]
  obtain ⟨xs, ys⟩ := p
  simp only [Tm.catDef, Tm.den, Tm.argDen, Val.args, Val.bind, Val.empty, Nat.reduceEqDiff, reduceIte, and_self,
    Prim.den_loopRow, ↓reduceDIte, Tm.nil, Prim.den_nilRow, Prim.den_cons]
  have hL : ∀ (p : List B.El × List B.El) (c : List B.El), loopDen (X := .arr B) (Y := B)
      (Core.Rel.comp (Core.Rel.rpair (Core.Rel.graph Prod.snd) (Core.Rel.graph Prod.fst))
        (fun (p : B.El × List B.El) (ys : List B.El) => ys = p.1 :: p.2)) p c ↔ c = p.2.reverse ++ p.1 :=
    fun p c => loopDen_cons _ (fun acc y w => by
      simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
      exact ⟨fun ⟨b, ⟨h1, h2⟩, h⟩ => by rw [h, h1, h2], fun h => ⟨(y, acc), ⟨rfl, rfl⟩, h⟩⟩) p.1 p.2 c
  generalize loopDen (X := .arr B) (Y := B)
      (Core.Rel.comp (Core.Rel.rpair (Core.Rel.graph Prod.snd) (Core.Rel.graph Prod.fst))
        (fun (p : B.El × List B.El) (ys : List B.El) => ys = p.1 :: p.2)) = L at hL ⊢
  simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id, nilDen, Prod.exists, hL]
  simp only [exists_eq_left', exists_and_left, and_assoc, exists_eq_left]
  simp

/-- **`cat`'s text means the row** (Q3 = G): the body the prelude elaborates, `prelude.cat.body`, at any objects `σ`
    (`Tm.instObj`), means `cat` there. -/
theorem Tm.catDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm (Obj.prod (Obj.arr ((Obj.atom .general).inst ph σ)) (Obj.arr ((Obj.atom .general).inst ph σ)))
      (Obj.arr ((Obj.atom .general).inst ph σ))}
    (ht : Rel.Programs.prelude.cat.body.instObj ph σ = .ok t') (p zs) :
    t'.den ρ p zs ↔ Prim.den (rowOf "cat") (.prod (.arr ((Obj.atom .general).inst ph σ)) (.arr ((Obj.atom .general).inst ph σ)))
      (.arr ((Obj.atom .general).inst ph σ)) [] p zs := by
  obtain rfl : Tm.catDef _ = t' := Except.ok.inj ht
  exact Tm.catDef_row ρ p zs

end Rel.Lang
