import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA7_5_Van

/-! # Laws of freyd §7.5 `AOP/A7_5_Van.lean`, in Rel (laws: `Rel/Lang/Laws/AopA7_5_Van.lean`)

A segment is a list `[α]` and a schedule a list of segments `[[α]]`. `new ≜ (τ×𝟙) cons` is B&dM p.185's `(wrap×𝟙) cons`.
The orders `R`, `H` of the book are parameters `R`, `H : α ⟶ α` where the proof reads nothing of them (stronger form,
`R = length ≤ length°` and `H = head prefix° head° ∪ nil° nil` are instances), and `R;H ≜ R ∩ (R° ⇒ H)` is written out. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA7_5_Van where
    new : α×[[α]] ⟶ [[α]] ≜ (τ×𝟙) cons
    -- Freyd.Alg.RelSet.Van.new_eq_cons, 07-optimisation.typ:1889
    theorem newEqCons(R : [[α]] ⟶ [[α]]) : (𝟙×R) new = (τ×R) cons by Rel.Lang.Tm.new_eq_cons_den
    -- Freyd.Alg.RelSet.Van.cons_mono_R, 07-optimisation.typ:1896. Stronger form: `R = ℓ O ℓ°` for a map `ℓ` and an entire
    -- `O`-monotone `u` with `cons ℓ = π₂ ℓ u`; the book's `R = length ≤ length°` is `ℓ = length`, `u = succ`, `O = ≤`
    -- (`length°` has no universe at `[[α]]`, so `R` itself cannot be written)
    theorem consMonoR(ℓ : [[α]] ⟶ γ, O : γ ⟶ γ, u : γ ⟶ γ) if π₂ ℓ u ⊑ cons ℓ, cons ℓ ⊑ π₂ ℓ u, (u° O) u ⊑ O, dom(u) = 𝟙, dom(ℓ) = 𝟙, ℓ° ℓ ⊑ 𝟙 : (𝟙×(ℓ O ℓ°)) cons ⊑ cons (ℓ O ℓ°) by Rel.Lang.Tm.cons_mono_r_den
    -- Freyd.Alg.RelSet.Van.RH_le_R, 07-optimisation.typ:1942 (R;H ≜ R ∩ (R° ⇒ H))
    theorem rhLeR(R : α ⟶ α, H : α ⟶ α) : (R ∩ (R° ⇒ H)) ⊑ R by Rel.Lang.Tm.rh_le_r_den
    -- Freyd.Alg.RelSet.Van.inter_le_RH, 07-optimisation.typ:1952
    theorem interLeRH(R : α ⟶ α, H : α ⟶ α) : (R ∩ H) ⊑ (R ∩ (R° ⇒ H)) by Rel.Lang.Tm.inter_le_rh_den

-- not ported: RH_eq (07-optimisation.typ:1745): `R;H` is written R ∩ (R° ⇒ H) here, so the equation is a syntactic identity
-- not ported: new_eq (07-optimisation.typ:1806): `new` is defined as `(τ×𝟙) cons`, so `new = (τ×𝟙) cons` is a syntactic identity
-- not ported: glue_eq (07-optimisation.typ:1811): `glue` would be defined as the book's `(𝟙×cons°) assocl (cons×𝟙) cons`, so the equation is a syntactic identity
-- not ported: RH_eq_strict (1749): `|R| ≜ R ∩ ¬R°` needs `R` a total preorder (`length ≤ length°`), which cannot be written at `[[α]]`
-- not ported: van_7_18 (1920): needs `head`, `prefix` and `nil° nil` at schedules with den lemmas for `at(0)` and `cat° π₁` on lists of lists
-- not ported: R_eq (1687): `graph` of a Lean function `clen`; `length°` has no universe at `[[α]]`
-- not ported: partition_cata (1721): `partition` is `cconcat° ∩ allNonempty`, a host function on `ConsList`, and the fold-uniqueness proof needs list-level `cat°` reasoning
-- not ported: old_eq (1816), prog_le_greedy (2043), secure_bmax (1767), secure_prefix (1761), van_7_14 (1876), van_7_19 (1961), van_7_20 (1962), van_7_21 (1963), van_mono (1956), van_mono_new (1915), van_strict_old (2015): class parameters `[Amount A] [Van]` (a host `Int` amount and capacity); the prelude has no minus, max or signed object, so `ceiling`, `floor`, `secure` cannot be defined
-- not ported: run_glue (2057), run_new (2061), run_offers (2053), run_van (2050): `#eval`-style checks of the program on host `List`/`Nat` data, no relation statement
-- not ported: van_fusion_cond (1826), van_laws (2034), van_spec (1732): element quantifier over the transactions plus `secure`, which cannot be defined (see above)

end Rel.Programs
