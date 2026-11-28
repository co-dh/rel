import Rel.Lang.Laws.AopS2_10
import Rel.Lang.Laws.AopA5_5_TypeFunctor

/-! # Laws of AOP `A9_1.lean` (companion `09-dynamic.typ`), on the concrete core

`F` is the list relator `F(R) = mapDen R` (`Rel/Lang/Laws/AopA5_5_TypeFunctor.lean`); a freyd `Alg F A` is `[A] ⟶ A`.
`Rel/Programs/Aop/A9_1.lean` states each law as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Proposition 9.2 (B&dM p.222): a cost `cost` that is a map, an algebra `h` with `h cost = F(cost) k`, and `k`
    monotonic on `S`: `h` is monotonic on `cost S cost°`. Pointwise on the list: pick the costs `cs` of `xs`, the
    costs `ds` of `ys` from `h ys a ↦ e`, relate them by `S`, and take `k`'s answer back to `h` through `cost`. -/
theorem presOfCost_core {A C : Obj} {h : Core.Rel (List A.El) A.El} {cost : Core.Rel A.El C.El}
    {k : Core.Rel (List C.El) C.El} {S : Core.Rel C.El C.El}
    (he : ∀ a, ∃ c, cost a c) (hs : ∀ a c c', cost a c → cost a c' → c = c')
    (hch : h ≫ cost = mapDen cost ≫ k) (hk : mapDen S ≫ k ⊑ k ≫ S) :
    mapDen ((cost ≫ S) ≫ cost°) ≫ h ⊑ h ≫ ((cost ≫ S) ≫ cost°) := by
  classical
  refine Core.Rel.le_iff.2 fun xs a ⟨ys, hR, hya⟩ => ?_
  obtain ⟨hl, hR⟩ := (mapDen_iff _ _ _).1 hR
  obtain ⟨e, hae⟩ := he a
  have hye : (h ≫ cost) ys e := ⟨a, hya, hae⟩
  rw [hch] at hye
  obtain ⟨ds, hds, hkd⟩ := hye
  obtain ⟨hl2, hds'⟩ := (mapDen_iff _ _ _).1 hds
  let cs : List C.El := List.ofFn fun i : Fin xs.length => Classical.choose (he xs[i])
  have hcs : mapDen cost xs cs := (mapDen_iff _ _ _).2 ⟨by simp [cs], fun t h1 h2 => by
    simpa [cs] using Classical.choose_spec (he xs[t])⟩
  have hSd : mapDen S cs ds := (mapDen_iff _ _ _).2 ⟨by simp [cs]; omega, fun t h1 h2 => by
    obtain ⟨d, ⟨c, hc, hSc⟩, hd⟩ := hR t (by simpa [cs] using h1) (by omega)
    have e1 : cs[t] = c := hs _ _ _ (by simpa [cs] using Classical.choose_spec (he xs[t])) hc
    have e2 : ds[t] = d := hs _ _ _ (hds' t (by omega) h2) hd
    rw [e1, e2]; exact hSc⟩
  obtain ⟨e', hke, hSe⟩ := Core.Rel.le_iff.1 hk cs e ⟨ds, hSd, hkd⟩
  have hxe : (mapDen cost ≫ k) xs e' := ⟨cs, hcs, hke⟩
  rw [← hch] at hxe
  obtain ⟨a', hxa, hae'⟩ := hxe
  exact ⟨a', hxa, e, ⟨e', hae', hSe⟩, hae⟩

theorem Tm.presOfCost_den {A C : Obj} {h : Tm (.arr A) A} {cost : Tm A C} {k : Tm (.arr C) C} {S : Tm C C} (ρ : Val)
    (he : (Tm.dom cost).den ρ = (Tm.id (A := A)).den ρ)
    (hs : (Tm.comp cost.conv cost).den ρ ⊑ (Tm.id (A := C)).den ρ)
    (hch : (Tm.comp h cost).den ρ = (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr C)) cost) k).den ρ)
    (hk : (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr C) (.arr C)) S) k).den ρ ⊑ (Tm.comp k S).den ρ) :
    (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr A)) (Tm.comp (Tm.comp cost S) cost.conv)) h).den ρ ⊑
      (Tm.comp h (Tm.comp (Tm.comp cost S) cost.conv)).den ρ := by
  have sf := fun_of_simple hs
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow] at hch hk ⊢
  exact presOfCost_core (Tm.entire_of_dom he) sf hch hk

/-- Proposition 9.3 (B&dM p.223), monotonicity in context: `Hc = H°` is simple, `cost` bundled with it is `⟨cost,Hc⟩`,
    and `k` monotonic on `S×𝟙`. Related elements of `xs, ys` share one `Hc`-image `b`, so the bundles of `ys` are those
    of `xs` with the cost moved by `S`. -/
theorem presInContext_core {A B C : Obj} {h : Core.Rel (List A.El) A.El} {cost : Core.Rel A.El C.El}
    {Hc : Core.Rel A.El B.El} {k : Core.Rel (List (Obj.El (.prod C B))) C.El} {S : Core.Rel C.El C.El}
    (he : ∀ a, ∃ c, cost a c) (hs : ∀ a c c', cost a c → cost a c' → c = c')
    (hH : ∀ a b b', Hc a b → Hc a b' → b = b')
    (hch : h ≫ cost = mapDen (Core.Rel.rpair cost Hc) ≫ k)
    (hk : mapDen (Core.Rel.rpair (Core.Rel.graph Prod.fst ≫ S) (Core.Rel.graph Prod.snd) : Core.Rel (Obj.El (.prod C B)) (Obj.El (.prod C B))) ≫ k ⊑ k ≫ S) :
    mapDen (((cost ≫ S) ≫ cost°) ∩ (Hc ≫ Hc°)) ≫ h ⊑ h ≫ ((cost ≫ S) ≫ cost°) := by
  classical
  refine Core.Rel.le_iff.2 fun xs a ⟨ys, hR, hya⟩ => ?_
  obtain ⟨hl, hR⟩ := (mapDen_iff _ _ _).1 hR
  obtain ⟨e, hae⟩ := he a
  have hye : (h ≫ cost) ys e := ⟨a, hya, hae⟩
  rw [hch] at hye
  obtain ⟨ps, hps, hkp⟩ := hye
  obtain ⟨hl2, hps'⟩ := (mapDen_iff _ _ _).1 hps
  have hb : ∀ t (h1 : t < xs.length), ∃ b, Hc xs[t] b := fun t h1 => by
    obtain ⟨b, h1, _⟩ := (hR t h1 (by omega)).2
    exact ⟨b, h1⟩
  let cs : List (Obj.El (.prod C B)) :=
    List.ofFn fun i : Fin xs.length => (Classical.choose (he xs[i]), Classical.choose (hb i.1 i.2))
  have hcs : mapDen (Core.Rel.rpair cost Hc) xs cs := (mapDen_iff _ _ _).2 ⟨by simp [cs], fun t h1 h2 =>
    ⟨by simpa [cs] using Classical.choose_spec (he xs[t]), by simpa [cs] using Classical.choose_spec (hb t h1)⟩⟩
  have hSd : mapDen (Core.Rel.rpair (Core.Rel.graph Prod.fst ≫ S) (Core.Rel.graph Prod.snd) : Core.Rel (Obj.El (.prod C B)) (Obj.El (.prod C B))) cs ps :=
    (mapDen_iff _ _ _).2 ⟨by simp [cs]; omega, fun t h1 h2 => by
      obtain ⟨⟨d, ⟨c, hc, hSc⟩, hd⟩, b, hb1, hb2⟩ := hR t (by simpa [cs] using h1) (by omega)
      have e1 : cs[t].1 = c := hs _ _ _ (by simpa [cs] using Classical.choose_spec (he xs[t])) hc
      have e2 : ps[t].1 = d := hs _ _ _ (hps' t (by omega) h2).1 hd
      have e3 : cs[t].2 = b := hH _ _ _ (by simpa [cs] using Classical.choose_spec (hb t (by simpa [cs] using h1))) hb1
      have e4 : ps[t].2 = b := hH _ _ _ (hps' t (by omega) h2).2 hb2
      exact ⟨⟨cs[t].1, rfl, by rw [e1, e2]; exact hSc⟩, (by show ps[t].snd = cs[t].snd; rw [e3, e4])⟩⟩
  obtain ⟨e', hke, hSe⟩ := Core.Rel.le_iff.1 hk cs e ⟨ps, hSd, hkp⟩
  have hxe : (mapDen (Core.Rel.rpair cost Hc) ≫ k) xs e' := ⟨cs, hcs, hke⟩
  rw [← hch] at hxe
  obtain ⟨a', hxa, hae'⟩ := hxe
  exact ⟨a', hxa, e, ⟨e', hae', hSe⟩, hae⟩

theorem Tm.presInContext_den {A B C : Obj} {h : Tm (.arr A) A} {cost : Tm A C} {H : Tm B A} {k : Tm (.arr (.prod C B)) C}
    {S : Tm C C} (ρ : Val)
    (he : (Tm.dom cost).den ρ = (Tm.id (A := A)).den ρ)
    (hs : (Tm.comp cost.conv cost).den ρ ⊑ (Tm.id (A := C)).den ρ)
    (hH : (Tm.comp H H.conv).den ρ ⊑ (Tm.id (A := B)).den ρ)
    (hch : (Tm.comp h cost).den ρ =
      (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr (.prod C B))) (Tm.pair cost H.conv)) k).den ρ)
    (hk : (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr (.prod C B)) (.arr (.prod C B)))
        (Tm.pair (Tm.comp Tm.outl S) (Tm.outr : Tm (.prod C B) B))) k).den ρ ⊑ (Tm.comp k S).den ρ) :
    (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr A))
        (Tm.meet (Tm.comp (Tm.comp cost S) cost.conv) (Tm.comp H.conv H))) h).den ρ ⊑
      (Tm.comp h (Tm.comp (Tm.comp cost S) cost.conv)).den ρ := by
  have hHs := fun_of_simple (T := (H.den ρ)°) hH
  have hss := fun_of_simple hs
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow] at hch hk ⊢
  exact presInContext_core (Tm.entire_of_dom he) hss hHs hch hk

end Rel.Lang
