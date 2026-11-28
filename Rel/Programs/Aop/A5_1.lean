/-! # Relators (`AOP/A5_1.lean`), in Rel: no row ported

A freyd `Relator 𝒜 ℬ` is a functor between allegories that preserves `⊑`, taken as a parameter of every row. Rel has no
relator parameter (the object universe is closed), so a row is stated at the list relator `F(R)` where it is true there.
The rows that are an instance already proved are cited:
- `F(R°) = F(R)°` is `fmapRecip` of `Rel/Programs/Aop/A5_5_TypeFunctor.lean`, which gives `map_recip`, `map_recip_map`
  and `preservesRecip_of_tabular` (the weaker form for a map `f` is the same law);
- `F(R) F(S) = F(R S)` and `F(𝟙) = 𝟙` are `fmapComp`, `fmapId` there. -/

-- not ported: map_recip (Freyd.Alg.Relator.map_recip, 05-datatypes.typ:29): at the list relator it is `fmapRecip` of Rel/Programs/Aop/A5_5_TypeFunctor.lean (Rel.Lang.Tm.fmap_recip_den); a general relator is not a parameter
-- not ported: map_recip_map (Freyd.Alg.Relator.map_recip_map, 05-datatypes.typ:19): the instance `F(f°) = F(f)°` of `fmapRecip` (A5_5_TypeFunctor), which holds for every `f`, a map or not
-- not ported: preservesRecip_of_tabular (Freyd.Alg.Relator.preservesRecip_of_tabular, 05-datatypes.typ:26): at the list relator it is `fmapRecip` (A5_5_TypeFunctor); the general statement quantifies over a relator `F` and a tabular allegory
-- not ported: map_is_map (Freyd.Alg.Relator.map_is_map, 05-datatypes.typ:19): `Map f → Map (F f)` for an arbitrary relator `F`; at the list relator it needs a list induction for the entire half (`dom(F(f)) = 𝟙`), not in rel yet
-- not ported: map_inter_le (Freyd.Alg.Relator.map_inter_le, 05-datatypes.typ:37): `F(R ∩ S) ⊑ F(R) ∩ F(S)` for an arbitrary relator `F`; at the list relator it is monotonicity of `F(-)` (mapDen_mono, Laws/AopA7_2), but no Tm law states it yet
-- not ported: map_inter_coreflexive (Freyd.Alg.Relator.map_inter_coreflexive, 05-datatypes.typ:34): arbitrary relator `F`; its list instance (equal lengths, elementwise) is not a Tm law yet
-- not ported: map_dom (Freyd.Alg.Relator.map_dom, 05-datatypes.typ:39): `F(dom R) = dom F(R)` for an arbitrary relator `F` over a tabular allegory; its list instance is not a Tm law yet
-- not ported: map_laxNatural (Freyd.Alg.Relator.map_laxNatural, 05-datatypes.typ:808): `laxNatural_*` over a relator (A5_7: not portable)
