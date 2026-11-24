import Rel.Lang.PreludeMerge
import Rel.Lang.PreludeLoop
import Rel.Lang.PreludeOrd

namespace Rel.Lang
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open Classical

set_option hygiene false in
/-- The merge loop's state `((xs, ys), acc)`. -/
local notation "𝕊" => Obj.prod (Obj.prod (Obj.arr B) (Obj.arr B)) (Obj.arr B)

/-- `merge(Q)` as the prelude elaborates it: the calls `a`, `b`, `l` of its `where` around the clocked `loop`, the
    state `S = ((xs, ys), acc)`; `.var 6 : S ⟶ S` is `l`, `.var 2`, `.var 3 : S ⟶ B` are `a`, `b`, `.var 1` is `Q`. -/
def Tm.mergeDef {B : Obj} (Q : Tm B B) : Tm (.prod (.arr B) (.arr B)) (.arr B) :=
  .arg (.arg (.call [2, 1] `a none [] (.arg (.arg (.arg (.call [3, 2, 1] `b none []
      (.arg (.arg (.arg (.arg (.call [6, 3, 2, 1] `l none []
        (.comp (.comp (.pair (.pair .id Tm.nil) (.prim (rowOf "cat")) : Tm (.prod (.arr B) (.arr B)) (.prod 𝕊 (.arr B))) (.arg (.prim (rowOf "loop") : Tm (.prod 𝕊 (.arr B)) 𝕊)
          (.comp (.outl : Tm (.prod 𝕊 B) 𝕊) (.join
            (.comp (.var 6 : Tm 𝕊 𝕊)
              (.pair (.pair (.comp (.comp .outl .outl) (Tm.mergeTail B)) (.comp .outl .outr))
                (.comp (.pair .outr (.var 2 : Tm 𝕊 B)) (.prim (rowOf "snoc") : Tm (.prod (.arr B) B) (.arr B)))))
            (.comp (.diff .id (.var 6))
              (.pair (.pair (.comp .outl .outl) (.comp (.comp .outl .outr) (Tm.mergeTail B)))
                (.comp (.pair .outr (.var 3 : Tm 𝕊 B)) (.prim (rowOf "snoc") : Tm (.prod (.arr B) B) (.arr B))))))))) .outr))
        (.join (.dom (.comp (.pair (.var 2 : Tm 𝕊 B) (.var 3))
            (.arg (.call [2] `Rel.Programs.prelude.cor (some `Rel.Programs.prelude.cor.conv) [B, B]
              (.dom (.meet (.comp .outl (.var 2 : Tm B B)) .outr))) (.var 1 : Tm B B))))
          (.diff (.dom (.var 2 : Tm 𝕊 B))
            (.dom (.var 3 : Tm 𝕊 B)))))
        (.var 3 : Tm 𝕊 B)) (.var 2 : Tm 𝕊 B))
        (.var 1 : Tm B B)))
      (.comp (.comp .outl .outr) Tm.headAt : Tm 𝕊 B))
      (.var 2 : Tm 𝕊 B)) (.var 1 : Tm B B)))
    (.comp (.comp .outl .outl) Tm.headAt : Tm 𝕊 B)) Q

example (ph : List QAtomicType) (σ : List Obj) {t' : Tm (Obj.prod (Obj.arr ((Obj.atom .general).inst ph σ))
    (Obj.arr ((Obj.atom .general).inst ph σ))) (Obj.arr ((Obj.atom .general).inst ph σ))}
    (ht : Rel.Programs.prelude.merge.body.instObj ph σ = .ok t') : True := by
  obtain rfl : Tm.mergeDef (.var 1) = t' := Except.ok.inj ht
  trivial

theorem Tm.mergeDef_row (ρ : Val) {B : Obj} (Q : Tm B B) (p : (Obj.prod (Obj.arr B) (Obj.arr B)).El)
    (ys : (Obj.arr B).El) :
    (Tm.mergeDef Q).den ρ p ys ↔ (Tm.arg (.prim (rowOf "merge")) (pairTest Q)).den ρ p ys := by
  have hτ : ∀ a b, (pairTest Q).den ρ (a, b) (a, b) ↔ Q.den ρ a b := fun a b => by
    simp [pairTest, Tm.dom_den, Tm.den, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.graph, Core.Rel.id]
  have hnil : ∀ x (l : (Obj.arr B).El), (nilDen : Core.Rel (Obj.El (.prod (.arr B) (.arr B))) _) x l ↔ l = [] :=
    fun x l => by
      simp [nilDen, Core.Rel.graph]
  -- the clocked loop from `((x, y), [])` over `x ++ y`, then `π₂`, is `merge x y` for any step that is `mstep`
  have outer : ∀ (T : Core.Rel (Obj.El (.prod 𝕊 B)) (Obj.El 𝕊)) (le : B.El → B.El → Bool),
      (∀ s e w, T (s, e) w ↔ (s.1.1 ≠ [] ∨ s.1.2 ≠ []) ∧ w = mstep le s) →
      ((((((𝟙 _).rpair nilDen).rpair fun (q : (Obj.prod (.arr B) (.arr B)).El) (zs : (Obj.arr B).El) => zs = q.1 ++ q.2) ≫ loopDen T) ≫ graph Prod.snd) p ys ↔
        ys = List.merge p.1 p.2 le) := by
    intro T le hT
    obtain ⟨x, y⟩ := p
    have hl := loopDen_merge le T hT x y
    generalize loopDen T = L at hl ⊢
    simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id, hnil, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨a, b, a1, b1, b2, b3, ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, h⟩
      exact (Prod.mk.inj ((hl _).1 h)).2
    · rintro rfl; exact ⟨[], [], x, y, [], x ++ y, ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, (hl _).2 rfl⟩
  simp only [Tm.mergeDef, Tm.den, Tm.argDen, Val.args, Val.bind, Val.empty, Nat.reduceEqDiff, reduceIte, and_self,
    Prim.den_loopRow, Prim.den_merge, ↓reduceDIte, Tm.nil, Prim.den_nilRow, Prim.den_cat, hτ]
  refine outer _ _ fun s e w => ?_
  obtain ⟨⟨xs, zs⟩, acc⟩ := s
  simp only [Core.Rel.comp, Core.Rel.union, Core.Rel.diff, Core.Rel.inter, Core.Rel.id, Core.Rel.graph,
    Core.Rel.rpair, Core.Rel.recip, Prim.den_domRow, Prim.den_snoc, Tm.headAt_den, Tm.mergeTail_den, Tm.dom_den, Tm.den,
    Tm.argDen, Val.args, Val.bind, Val.empty, Nat.reduceEqDiff, reduceIte, ↓reduceDIte]
  sorry

