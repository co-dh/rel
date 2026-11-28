import Rel.Lang.Laws.AopA6_2

/-! # Laws of freyd `AOP/A6_6b_SortConcrete.lean` (B&dM §6.6, selection sort), at the list fold on snoc

freyd folds over `cons`, the prelude over `snoc`: `ok cons` becomes `K snoc`, with `K` any `[α]×α ⟶ [α]×α` (the book's
`ok`, the coreflexive "the element is below all of the array"), and `perm` is any `P` with the two facts the proof uses
(`K` commutes with `P×𝟙`, and `snoc P = (P×𝟙) snoc P`): the stronger form, with `P = perm`, `K = ok` an instance. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude row `snoc`, with its object fixed. -/
abbrev Tm.snocRow (B : Obj) : Tm (.prod (.arr B) B) (.arr B) := .prim (rowOf "snoc")

theorem lcompLe {α β γ : Type} {R : Core.Rel α β} {S T : Core.Rel β γ} (h : S ⊑ T) : R ≫ S ⊑ R ≫ T :=
  Core.Rel.le_iff.2 fun a c ⟨b, hr, hs⟩ => ⟨b, hr, Core.Rel.le_iff.1 h b c hs⟩

/-- p.153 `select_proviso`: `(P×𝟙) select° ⊑ K snoc P` from `select° ⊑ K snoc P`, `K (P×𝟙) = (P×𝟙) K` (Ex 6.22) and the
    snoc branch of `P`. -/
theorem selectProviso_core {X Y : Type} {A K : Core.Rel X X} {sn : Core.Rel X Y} {P : Core.Rel Y Y} {S' : Core.Rel X Y}
    (hK : K ≫ A = A ≫ K) (hs : sn ≫ P = (A ≫ sn) ≫ P) (hsel : S' ⊑ (K ≫ sn) ≫ P) : A ≫ S' ⊑ (K ≫ sn) ≫ P := by
  have heq : A ≫ ((K ≫ sn) ≫ P) = (K ≫ sn) ≫ P :=
    calc A ≫ ((K ≫ sn) ≫ P) = A ≫ (K ≫ (sn ≫ P)) := by rw [Core.Rel.comp_assoc K sn P]
      _ = (A ≫ K) ≫ (sn ≫ P) := (Core.Rel.comp_assoc A K _).symm
      _ = (K ≫ A) ≫ (sn ≫ P) := by rw [hK]
      _ = K ≫ (A ≫ (sn ≫ P)) := Core.Rel.comp_assoc K A _
      _ = K ≫ (sn ≫ P) := by rw [← Core.Rel.comp_assoc A sn P, ← hs]
      _ = (K ≫ sn) ≫ P := (Core.Rel.comp_assoc K sn P).symm
  have h1 : A ≫ S' ⊑ A ≫ ((K ≫ sn) ≫ P) := lcompLe hsel
  rwa [heq] at h1

theorem Tm.selectProviso_den {B : Obj} {P : Tm (.arr B) (.arr B)} {K : Tm (.prod (.arr B) B) (.prod (.arr B) B)}
    {S : Tm (.arr B) (.prod (.arr B) B)} (ρ : Val)
    (hK : (Tm.comp K (Tm.pair (.comp .outl P) (.comp .outr .id))).den ρ
      = (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) K).den ρ)
    (hs : (Tm.comp (Tm.snocRow B) P).den ρ
      = (Tm.comp (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) (Tm.snocRow B)) P).den ρ)
    (hsel : S.conv.den ρ ⊑ (Tm.comp (Tm.comp K (Tm.snocRow B)) P).den ρ) :
    (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) S.conv).den ρ
      ⊑ (Tm.comp (Tm.comp K (Tm.snocRow B)) P).den ρ :=
  selectProviso_core hK hs hsel

/-- p.152 `selection_sort` at the list fold: `⦇[e, select°]⦈° ⊑ P O` for `O = ⦇[e, K snoc]⦈` a coreflexive, `P° = P`
    and `e ⊑ e P` (freyd gets it from `perm` reflexive): (6.4) fusion under the proviso, then the converse. -/
theorem Tm.selectionSort_den {B : Obj} {P O : Tm (.arr B) (.arr B)} {K : Tm (.prod (.arr B) B) (.prod (.arr B) B)}
    {S : Tm (.arr B) (.prod (.arr B) B)} {e : Tm .one (.arr B)} (ρ : Val)
    (hP : P.conv.den ρ = P.den ρ) (hOid : O.den ρ ⊑ (Tm.id (A := .arr B)).den ρ)
    (hO : O.den ρ = (Tm.fold (Tm.ran e) (Tm.comp K (Tm.snocRow B))).den ρ)
    (hK : (Tm.comp K (Tm.pair (.comp .outl P) (.comp .outr .id))).den ρ
      = (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) K).den ρ)
    (hs : (Tm.comp (Tm.snocRow B) P).den ρ
      = (Tm.comp (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) (Tm.snocRow B)) P).den ρ)
    (he : e.den ρ ⊑ (Tm.comp e P).den ρ)
    (hsel : S.conv.den ρ ⊑ (Tm.comp (Tm.comp K (Tm.snocRow B)) P).den ρ) :
    (Tm.comp Tm.id (Tm.fold (Tm.ran e) S.conv)).conv.den ρ ⊑ (Tm.comp P O).den ρ := by
  have hf := Tm.relCata_le_comp_den (e := e) (f := Tm.comp K (Tm.snocRow B)) (e' := e) (g := S.conv) (S := P) ρ he
    (Tm.selectProviso_den ρ hK hs hsel)
  refine Core.Rel.le_iff.2 fun w xs h => ?_
  have h' : (𝟙 _ ≫ (Tm.fold (Tm.ran e) S.conv).den ρ) xs w := h
  rw [Core.Rel.id_comp] at h'
  obtain ⟨u, hu, hPu⟩ := Core.Rel.le_iff.1 hf xs w h'
  rw [← hO] at hu
  obtain rfl : xs = u := Core.Rel.le_iff.1 hOid xs u hu
  exact ⟨xs, (congrFun (congrFun hP w) xs).mp hPu, hu⟩

/-- p.153: the converse of the fold unfolds one `select` at a time, `X° = e°nil ∪ select (X°×𝟙) snoc`. -/
theorem Tm.sortRec_den {B : Obj} {S : Tm (.arr B) (.prod (.arr B) B)} {e : Tm .one (.arr B)} (ρ : Val) :
    (Tm.comp Tm.id (Tm.fold (Tm.ran e) S.conv)).conv.den ρ
      = (Tm.join (Tm.comp e.conv (Tm.nil : Tm .one (.arr B)))
          (Tm.comp (Tm.comp S (Tm.pair (Tm.comp .outl (Tm.comp Tm.id (Tm.fold (Tm.ran e) S.conv)).conv) (Tm.comp .outr .id)))
            (Tm.snocRow B))).den ρ := by
  apply Core.Rel.ext
  intro w xs
  induction xs using snocInd generalizing w with
  | nil =>
    simp only [↓pairComp_den, Tm.nil, Prim.den_nilRow, Tm.den, Prim.den_snoc, nilDen, Core.Rel.union, Core.Rel.comp,
      Core.Rel.rprodMap, Core.Rel.recip, Core.Rel.graph, Core.Rel.id, exists_eq_left, exists_eq_left']
    rw [foldDen_empty]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨m, hm⟩ := (ranSeed_iff ρ e w).1 ⟨a, ha⟩
      exact Or.inl ⟨m, hm, by simp⟩
    · rintro (⟨m, hm, -⟩ | ⟨b, -, h⟩)
      · exact (ranSeed_iff ρ e w).2 ⟨m, hm⟩
      · exact absurd h (by simp)
  | snoc L x ih =>
    simp only [↓pairComp_den, Tm.nil, Prim.den_nilRow, Tm.den, Prim.den_snoc, nilDen, Core.Rel.union, Core.Rel.comp,
      Core.Rel.rprodMap, Core.Rel.recip, Core.Rel.graph, Core.Rel.id, exists_eq_left, exists_eq_left']
    rw [foldDen_snoc]
    constructor
    · rintro ⟨u, hu, hS⟩
      exact Or.inr ⟨(L, x), ⟨(u, x), hS, hu, rfl⟩, rfl⟩
    · rintro (⟨m, -, h⟩ | ⟨⟨L', x'⟩, ⟨⟨u, y⟩, hS, hf, hs⟩, h⟩)
      · exact absurd h (by simp)
      · dsimp only at h hs hf
        obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
        obtain rfl := (List.cons.inj h2).1
        subst hs
        exact ⟨u, hf, hS⟩

end Rel.Lang
