import Rel.Lang.Laws.AopA4_4
import Rel.Lang.Laws.AopA5_7_ListBeads
import Rel.Lang.PreludeHead

/-! # Laws of freyd §7.5 `AOP/A7_5_Van.lean`, on the concrete core

`Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`; `Rel/Programs/Aop/A7_5_Van.lean`
states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `R;H ⊑ R` for `R;H ≜ R ∩ (R° ⇒ H)`. -/
theorem Tm.rh_le_r_den {A : Obj} {R H : Tm A A} {c : Lean.Name} {cv : Option Lean.Name} {os : List Obj} (ρ : Val) :
    (Tm.meet R (Tm.implC c cv os R.conv H)).den ρ ⊑ R.den ρ :=
  Core.Rel.le_iff.2 fun a b h => (show _ ∧ _ from h).1

/-- `R ∩ H ⊑ R;H`. -/
theorem Tm.inter_le_rh_den {A : Obj} {R H : Tm A A} {c : Lean.Name} {cv : Option Lean.Name} {os : List Obj} (ρ : Val) :
    (Tm.meet R H).den ρ ⊑ (Tm.meet R (Tm.implC c cv os R.conv H)).den ρ :=
  Core.Rel.le_iff.2 fun a b h => by
    obtain ⟨hr, hh⟩ := (show _ ∧ _ from h)
    exact ⟨hr, (Tm.implC_den c cv os R.conv H ρ a b).2 (Or.inr hh)⟩

/-- `(𝟙×R)(T×𝟙)K = (T×R)K`: the two products act on disjoint halves of the pair. -/
theorem Tm.new_eq_cons_den {X Y Z V W : Obj} {T : Tm X V} {R : Tm Y Z} {K : Tm (.prod V Z) W} (ρ : Val) :
    (Tm.comp (Tm.pair (Tm.comp Tm.outl Tm.id) (Tm.comp Tm.outr R))
      (Tm.comp (Tm.pair (Tm.comp Tm.outl T) (Tm.comp Tm.outr Tm.id)) K)).den ρ =
    (Tm.comp (Tm.pair (Tm.comp Tm.outl T) (Tm.comp Tm.outr R)) K).den ρ := by
  refine Core.Rel.ext fun xy w => ?_
  simp only [Tm.den, Core.Rel.comp]
  obtain ⟨x, y⟩ := xy
  simp only [Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph, Core.Rel.id]
  simp [Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨rfl, hR⟩, a1, b1, ⟨hT, rfl⟩, hk⟩
    exact ⟨a1, b, ⟨hT, hR⟩, hk⟩
  · rintro ⟨a, b, ⟨hT, hR⟩, hk⟩
    exact ⟨x, b, ⟨rfl, hR⟩, a, b, ⟨hT, rfl⟩, hk⟩

/-- `(𝟙×R)K ⊑ K R` for `R = ℓ O ℓ°` (B&dM p.186, `cons` monotonic on `R = length ≤ length°`), stated for any map `ℓ`
    (entire, simple) that `K` sends to the `u`-image of `ℓ` of its second component (`K ℓ = π₂ ℓ u`), `u` entire and
    `O`-monotone (`u° O u ⊑ O`); the book's case is `ℓ = length`, `u = succ`, `O = ≤`. -/
theorem Tm.cons_mono_r_den {L G V : Obj} {K : Tm (.prod V L) L} {l : Tm L G} {O u : Tm G G} (ρ : Val)
    (ha : (Tm.comp (Tm.comp Tm.outr l) u).den ρ ⊑ (Tm.comp K l).den ρ)
    (hb' : (Tm.comp K l).den ρ ⊑ (Tm.comp (Tm.comp Tm.outr l) u).den ρ)
    (hb : (Tm.comp (Tm.comp u.conv O) u).den ρ ⊑ O.den ρ)
    (hu : (Tm.dom u).den ρ = (Tm.id (A := G)).den ρ)
    (hl : (Tm.dom l).den ρ = (Tm.id (A := L)).den ρ)
    (hs : (Tm.comp l.conv l).den ρ ⊑ (Tm.id (A := G)).den ρ) :
    (Tm.comp (Tm.pair (Tm.comp Tm.outl Tm.id) (Tm.comp Tm.outr (Tm.comp (Tm.comp l O) l.conv))) K).den ρ ⊑
      (Tm.comp K (Tm.comp (Tm.comp l O) l.conv)).den ρ := by
  have eu := Tm.entire_of_dom hu
  have el := Tm.entire_of_dom hl
  have sl := fun_of_simple hs
  refine Core.Rel.le_iff.2 fun sx w h => ?_
  obtain ⟨s, x⟩ := sx
  simp [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id, Core.Rel.recip, Prod.exists] at h ha hb hb' ⊢
  obtain ⟨a, y, ⟨rfl, n0, ⟨m, hm, hO⟩, hy⟩, hK⟩ := h
  obtain ⟨m', hu1⟩ := eu m
  obtain ⟨v, hlw⟩ := el w
  obtain ⟨c, hKc, hlc⟩ := Core.Rel.le_iff.1 ha (s, x) m' ⟨m, ⟨x, rfl, hm⟩, hu1⟩
  obtain ⟨g, ⟨y', rfl, hyg⟩, hug⟩ := Core.Rel.le_iff.1 hb' (s, y) v ⟨w, hK, hlw⟩
  obtain rfl := sl _ g n0 hyg hy
  have hO' := Core.Rel.le_iff.1 hb m' v ⟨g, ⟨m, hu1, hO⟩, hug⟩
  exact ⟨c, hKc, v, ⟨m', hlc, hO'⟩, hlw⟩

/-- **(7.18)** `(𝟙×T) new ⊑ new H` for `H = head prefix° head° ∪ X`, any `T` and `X`: both sides open the segment `[a]`
    of their own, so the two first segments are equal and the first branch of `H` holds by `prefix` reflexive. -/
theorem Tm.van718_den {B : Obj} {T X : Tm (.arr (.arr B)) (.arr (.arr B))} {t1 : Tm (.arr (.arr B)) (.arr B)}
    {os1 os2 : List Obj}
    (ht1 : Rel.Programs.prelude.head.body.instObj [.general] [.arr B] = .ok t1 := by rfl) (ρ : Val) :
    (Tm.comp (Tm.pair (Tm.comp Tm.outl Tm.id) (Tm.comp Tm.outr T))
      (Tm.comp (Tm.pair (Tm.comp Tm.outl (Tm.prim (rowOf "τ") : Tm B (.arr B))) (Tm.comp Tm.outr Tm.id))
        (Tm.prim (rowOf "cons") : Tm (.prod (.arr B) (.arr (.arr B))) (.arr (.arr B))))).den ρ ⊑
    (Tm.comp (Tm.comp (Tm.pair (Tm.comp Tm.outl (Tm.prim (rowOf "τ") : Tm B (.arr B))) (Tm.comp Tm.outr Tm.id))
        (Tm.prim (rowOf "cons") : Tm (.prod (.arr B) (.arr (.arr B))) (.arr (.arr B))))
      (Tm.join (Tm.comp (Tm.comp (Tm.call [] `Rel.Programs.prelude.head (some `Rel.Programs.prelude.head.conv) os1 t1)
        (Tm.conv (Tm.comp Tm.id (Tm.prim (rowOf "prefix") : Tm (.arr B) (.arr B)))))
        (Tm.call [] `Rel.Programs.prelude.head.conv (some `Rel.Programs.prelude.head) os2 (Tm.headConvBody (B := .arr B)))) X)).den ρ := by
  refine Core.Rel.le_iff.2 fun p r h => ?_
  obtain ⟨a, x⟩ := p
  simp only [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id, Core.Rel.recip, Core.Rel.union, Prim.den_tau, Prim.den_cons, Prod.exists] at h ⊢
  obtain ⟨a1, y, ⟨⟨a2, h1, h2⟩, x2, h3, hT⟩, a3, b1, ⟨⟨a4, h4, h5⟩, x3, h6, h7⟩, h8⟩ := h
  obtain rfl := h1.symm
  obtain rfl := h2
  obtain rfl := h3.symm
  obtain rfl := h4.symm
  obtain rfl := h5
  obtain rfl := h6.symm
  obtain rfl := h7
  obtain rfl := h8
  exact ⟨[a] :: x, ⟨[a], x, ⟨⟨a, rfl, rfl⟩, x, rfl, rfl⟩, rfl⟩, Or.inl ⟨[a],
    ⟨[a], (Tm.headDef_den [.general] [.arr B] _ ht1 _ _).2 ⟨by simp, rfl⟩, [a], rfl,
      (Tm.prefixRow_iff ρ [a] [a]).2 (List.prefix_refl _)⟩,
    (Tm.headConvBody_den _ [a] ([a] :: y)).2 ⟨by simp, rfl⟩⟩⟩

end Rel.Lang
