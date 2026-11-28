import Rel.Lang.Laws.Cylinder

/-! # B&dM §1.7 (1.7): `zip` is natural

`⟨F(R), F(S)⟩ zip = F(⟨R,S⟩)`: `F(R)` and `F(S)` keep the length, so the truncation of the row `zip` never acts, and
`zip` of the two images is the image of the pair. The row `zip` is `Prim.den_zip` (Laws/Cylinder). -/

namespace Rel.Lang
open Rel.Lang

/-- `⟨F(R), F(S)⟩ zip = F(⟨R,S⟩)` as the program elaborates it. -/
theorem Tm.zipNatural_den {X A B : Obj} (ρ : Val) :
    Tm.den ρ (((Tm.prim mapRow : Tm (.arr X) (.arr A)).arg (Tm.var 0 : Tm X A)).pair
        ((Tm.prim mapRow : Tm (.arr X) (.arr B)).arg (Tm.var 1 : Tm X B))
      |>.comp (Tm.prim (rowOf "zip") : Tm (.prod (.arr A) (.arr B)) (.arr (.prod A B)))) =
    Tm.den ρ ((Tm.prim mapRow : Tm (.arr X) (.arr (.prod A B))).arg
      ((Tm.var 0 : Tm X A).pair (Tm.var 1 : Tm X B))) := by
  funext xs zs; apply propext
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Prim.den_zip, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
  constructor
  · rintro ⟨⟨ys, ws⟩, ⟨h1, h2⟩, rfl⟩
    obtain ⟨l1, g1⟩ := (mapDen_iff _ _ _).1 h1
    obtain ⟨l2, g2⟩ := (mapDen_iff _ _ _).1 h2
    refine (mapDen_iff _ _ _).2 ⟨by simp [l1, l2], fun t ht ht' => ?_⟩
    simp only [List.getElem_zip]
    exact ⟨g1 t ht (by omega), g2 t ht (by omega)⟩
  · intro h
    obtain ⟨l, g⟩ := (mapDen_iff _ _ _).1 h
    refine ⟨⟨zs.map Prod.fst, zs.map Prod.snd⟩, ⟨(mapDen_iff _ _ _).2 ⟨by simp [l], fun t ht ht' => ?_⟩,
      (mapDen_iff _ _ _).2 ⟨by simp [l], fun t ht ht' => ?_⟩⟩, by simpa [List.unzip_eq_map] using (List.zip_unzip zs).symm⟩
    · simpa using (g t ht (by omega)).1
    · simpa using (g t ht (by omega)).2

end Rel.Lang
