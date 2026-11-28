/-! # `diag/S2_124.lean` in Rel: nothing new to port

`diag/S2_124.lean` proves §2.124 diagrammatically in a cartesian bicategory. The one row marked 可写, `dom_comp_le`, is
`◁(𝟙⊗(R S))(𝟙⊗⊸) ≤ ◁(𝟙⊗R)(𝟙⊗⊸)`, and `◁(𝟙⊗T)(𝟙⊗⊸)` is `dom(T)`, so it reads `dom(R S) ⊑ dom(R)`: the statement Rel
already has as `aopS2_10.domCompLe` (`Rel/Programs/Aop/S2_10.lean`, `Tm.dom_comp_le_den`). It is cited, not restated. -/

-- not ported: dom_comp_le (Freyd.Diag.dom_comp_le, 00-laws.typ:286): same statement as `domCompLe` in Rel/Programs/Aop/S2_10.lean (Rel.Lang.Tm.dom_comp_le_den): dom(R S) ⊑ dom(R)
