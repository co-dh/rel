/-
  `(μX : φX)` and `(νX : φX)` on a hom-set of relations (B&dM Theorem 6.1), defined for every `φ`: a fixed point
  when `φ` is monotonic. The one copy of the fixed points Rel proper uses; `Gen.mu`, `Gen.nu` compute them.
-/
module

public import Rel.Core.Rel

-- exposed: `mu`/`nu` are unfolded by `Gen.mu`, `Gen.nu` and the denotation proofs that import them
@[expose] public section

namespace Rel.Core.Rel

open Rel.Core

variable {α β : Type} {φ ψ : Rel α β → Rel α β} {Y : Rel α β}

/-- A monotonic map on a hom-set ("not necessarily a functor", Theorem 6.1). -/
def Monotonic (φ : Rel α β → Rel α β) : Prop := ∀ X Y : Rel α β, X ⊑ Y → φ X ⊑ φ Y

/-- `(μX : φX)`: the pairs in every prefixed point. -/
def mu (φ : Rel α β → Rel α β) : Rel α β := fun a b => ∀ Y : Rel α β, φ Y ⊑ Y → Y a b

/-- `(νX : φX)`: the pairs in some postfixed point. -/
def nu (φ : Rel α β → Rel α β) : Rel α β := fun a b => ∃ Y : Rel α β, Y ⊑ φ Y ∧ Y a b

theorem mu_le (h : φ Y ⊑ Y) : mu φ ⊑ Y := le_iff.2 fun _ _ hx => hx Y h

theorem le_nu (h : Y ⊑ φ Y) : Y ⊑ nu φ := le_iff.2 fun _ _ hy => ⟨Y, h, hy⟩

theorem mu_prefixed (hφ : Monotonic φ) : φ (mu φ) ⊑ mu φ :=
  le_iff.2 fun a b hx _ hY => le_iff.1 hY a b (le_iff.1 (hφ _ _ (mu_le hY)) a b hx)

theorem mu_fix (hφ : Monotonic φ) : φ (mu φ) = mu φ :=
  le_antisymm (mu_prefixed hφ) (mu_le (hφ _ _ (mu_prefixed hφ)))

theorem nu_fix (hφ : Monotonic φ) : φ (nu φ) = nu φ := by
  have h1 : nu φ ⊑ φ (nu φ) :=
    le_iff.2 fun a b ⟨Y, hY, hy⟩ => le_iff.1 (hφ _ _ (le_nu hY)) a b (le_iff.1 hY a b hy)
  exact le_antisymm (le_nu (hφ _ _ h1)) h1

/-- `mu` is monotone in its body, pointwise: no monotonicity of either body is needed. -/
theorem mu_mono (h : ∀ X, φ X ⊑ ψ X) : mu φ ⊑ mu ψ :=
  le_iff.2 fun _ _ hx Y hY => hx Y (le_trans (h Y) hY)

theorem nu_mono (h : ∀ X, φ X ⊑ ψ X) : nu φ ⊑ nu ψ :=
  le_iff.2 fun _ _ ⟨Y, hY, hy⟩ => ⟨Y, le_trans hY (h Y), hy⟩

/-- `starLinear` (the prelude's `star(R) ≜ μX : 𝟙 ∪ R X`): `μX : S ∪ R X = star(R) S`, so a linear recursion runs
    as the row `star` (`Tab.star`, semi-naive) on `S`. -/
theorem starLinear (R : Rel α α) (S : Rel α β) :
    mu (fun X => S ∪ R ≫ X) = mu (fun X => 𝟙 α ∪ R ≫ X) ≫ S := by
  apply le_antisymm
  · -- `star(R) S` is a prefixed point of `S ∪ R X`
    refine mu_le (le_iff.2 fun a c h => ?_)
    rcases h with h | ⟨b, hR, d, hs, hS⟩
    · exact ⟨a, fun Y hY => le_iff.1 hY a a (Or.inl rfl), h⟩
    · exact ⟨d, fun Y hY => le_iff.1 hY a d (Or.inr ⟨b, hR, hs Y hY⟩), hS⟩
  · -- `star(R)` is below the pairs `(a,b)` with `S b c ⟹ M a c`, `M` the left side: a prefixed point of `𝟙 ∪ R X`
    refine le_iff.2 fun a c h => ?_
    obtain ⟨b, hs, hS⟩ := h
    refine hs (fun a b => ∀ c, S b c → mu (fun X => S ∪ R ≫ X) a c) (le_iff.2 fun a b h c hc Z hZ => ?_) c hS
    rcases h with rfl | ⟨d, hR, hd⟩
    · exact le_iff.1 hZ a c (Or.inl hc)
    · exact le_iff.1 hZ a c (Or.inr ⟨d, hR, hd c hc Z hZ⟩)

/-! ### Keying (§e): a family `F : ι → Rel α β` run once as one relation on (key, source) -/

/-- The family `F` keyed, `⟨π₁,Fᴵ⟩ : ι×α ⟶ ι×β` with `Fᴵ (i,a) b = F i a b`: each key kept, its fibre run on the
    source. A row given families runs once on them keyed exactly where its meaning commutes with `keyOf`. -/
def keyOf {ι : Type} (F : ι → Rel α β) : Rel (ι × α) (ι × β) := rpair (graph Prod.fst) fun x b => F x.1 x.2 b

theorem keyOf_mono {ι : Type} {F G : ι → Rel α β} (h : ∀ i, F i ⊑ G i) : keyOf F ⊑ keyOf G :=
  le_iff.2 fun x _ ⟨e, f⟩ => ⟨e, le_iff.1 (h x.1) _ _ f⟩

theorem keyOf_zero {ι : Type} : keyOf (fun _ : ι => (𝟘 : Rel α β)) = 𝟘 :=
  le_antisymm (le_iff.2 fun _ _ h => h.2.elim) (zero_le _)

theorem id_keyOf {ι : Type} : 𝟙 (ι × α) = keyOf fun _ => 𝟙 α :=
  ext fun _ _ => ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => Prod.ext h1.symm h2⟩

theorem union_keyOf {ι : Type} (F G : ι → Rel α β) : keyOf F ∪ keyOf G = keyOf fun i => F i ∪ G i :=
  ext fun _ _ => ⟨fun h => h.elim (fun ⟨e, f⟩ => ⟨e, Or.inl f⟩) fun ⟨e, g⟩ => ⟨e, Or.inr g⟩,
    fun ⟨e, h⟩ => h.elim (fun f => Or.inl ⟨e, f⟩) fun g => Or.inr ⟨e, g⟩⟩

theorem comp_keyOf {γ ι : Type} (F : ι → Rel α β) (G : ι → Rel β γ) :
    keyOf F ≫ keyOf G = keyOf fun i => F i ≫ G i :=
  ext fun x _ => ⟨fun ⟨y, ⟨e1, f⟩, e2, g⟩ => ⟨e2.trans e1, y.2, f, e1 ▸ g⟩,
    fun ⟨e, b, f, g⟩ => ⟨(x.1, b), ⟨rfl, f⟩, e, g⟩⟩

/-- `μ` commutes with keying: where `Φ` at keyed families is `Ψ i` at each key, `μΦ` is `μ(Ψ i)` keyed. The fibres
    `Y(i,−)(i,−)` of a prefixed point `Y` of `Φ` are prefixed points of `Ψ i`, as `keyOf` of them is below `Y`. -/
theorem mu_keyOf {ι : Type} {Φ : Rel (ι × α) (ι × β) → Rel (ι × α) (ι × β)} {Ψ : ι → Rel α β → Rel α β}
    (hΦ : Monotonic Φ) (hΨ : ∀ i, Monotonic (Ψ i)) (h : ∀ G, Φ (keyOf G) = keyOf fun i => Ψ i (G i)) :
    mu Φ = keyOf fun i => mu (Ψ i) := by
  apply le_antisymm
  · refine mu_le ?_
    rw [h]
    exact keyOf_mono fun i => mu_prefixed (hΨ i)
  · refine le_iff.2 fun x y ⟨hy, hx⟩ Y hY => ?_
    have hk : keyOf (fun i a b => Y (i, a) (i, b)) ⊑ Y := le_iff.2 fun x y ⟨e, f⟩ => by
      obtain ⟨i, a⟩ := x; obtain ⟨j, b⟩ := y; cases e; exact f
    have hfib : ∀ i, Ψ i (fun a b => Y (i, a) (i, b)) ⊑ fun a b => Y (i, a) (i, b) := fun i =>
      le_iff.2 fun a b hab => le_iff.1 (le_trans (hΦ _ _ hk) hY) (i, a) (i, b) (by rw [h]; exact ⟨rfl, hab⟩)
    obtain ⟨i, a⟩ := x; obtain ⟨j, b⟩ := y; cases hy
    exact hx _ (hfib i)

/-- `star` commutes with keying: `star(⟨π₁,Fᴵ⟩) = ⟨π₁,(fun i => star(F i))ᴵ⟩`, since `𝟙`, `∪` and `≫` do
    (`id_keyOf`, `union_keyOf`, `comp_keyOf`) and so `μ` of their composition does (`mu_keyOf`). -/
theorem star_keyOf {ι : Type} (F : ι → Rel α α) :
    mu (fun X => 𝟙 _ ∪ keyOf F ≫ X) = keyOf fun i => mu fun X => 𝟙 α ∪ F i ≫ X := by
  have hm : ∀ {γ : Type} (R : Rel γ γ), Monotonic fun X => 𝟙 γ ∪ R ≫ X := fun R X Y hXY =>
    le_iff.2 fun a b hab => by
      rcases hab with h | ⟨c, hR, hX⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, hR, le_iff.1 hXY _ _ hX⟩
  exact mu_keyOf (hm _) (fun i => hm _) fun G => by rw [comp_keyOf, id_keyOf, union_keyOf]

end Rel.Core.Rel

end
