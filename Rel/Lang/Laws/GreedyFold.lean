module

public import Rel.Lang.Laws.Eunion
public import Rel.Lang.Laws.Absorb

@[expose] public section

/-! B&dM's greedy theorem for a right fold: `(𝟙÷∋)E(⦇[e, S]⦈ʳ)est(R) = ⦇[(𝟙÷∋)E(e)est(R), (𝟙÷∋)E(S)est(R)]⦈ʳ`.
The `R`-extreme of all fold results is the fold of the `R`-extreme at each step.

Path: `R = ≥`, `S(x, u) = {0, x+u}`, `u* = 5` the largest value of the fold over `xs`, `u = 3` another. `S(x, 3) = {0, x+3}`
is dominated by `S(x, 5) = {0, x+5}` (`S` monotone: `u* ≥ u` gives `x+5 ≥ x+3`), so the largest of all results of
`x :: xs` is the largest of `S(x, u*)`, which is `S'(x, u*)` for `u*` the one value `⦇S'⦈` holds over `xs`.
General: `R` a total order, `S` monotone in its second argument on `R`, every image `Λ(S)` and `Λ(⦇S⦈ʳ)` an array. -/

namespace Rel.Lang
open scoped Rel.Core.Rel Classical
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {E V : Obj}

/-- `w` is the `R`-extreme of the set `T`: in it, and `R`-above every other member (`estDen`'s test). -/
def Extr (R : Core.Rel (Obj.El V) (Obj.El V)) (T : Obj.El V → Prop) (w : Obj.El V) : Prop :=
  T w ∧ ∀ c, T c → c ≠ w → R w c

/-- `est(R)` on the array of `Λ(X)` picks the `R`-extreme of the image of `X`. -/
theorem estDen_lam {A : Obj} (TQ : Core.Rel (Obj.El (.prod V V)) (Obj.El (.prod V V)))
    {X : Core.Rel (Obj.El A) (Obj.El V)} {a : Obj.El A} {ys : Obj.El (.arr V)} (h : lamDen X a ys) (w : Obj.El V) :
    estDen TQ ys w ↔ Extr (qtDen TQ) (X a) w := by
  obtain ⟨-, hm⟩ := (lamDen_iff _ _ _).1 h
  rw [estDen_iff]
  refine ⟨fun ⟨hw, hn⟩ => ⟨(hm w).1 hw, fun c hc hne => ?_⟩, fun ⟨hw, hn⟩ => ⟨(hm w).2 hw, ?_⟩⟩
  · exact (qtDen_iff TQ w c).2 (Classical.byContradiction fun hq => hn ⟨c, (hm c).2 hc, hne, hq⟩)
  · rintro ⟨c, hc, hne, hq⟩
    exact hq ((qtDen_iff TQ w c).1 (hn c ((hm c).1 hc) hne))

/-- A non-empty list has an `R`-extreme member under a total preorder. -/
theorem exists_ext {R : Core.Rel (Obj.El V) (Obj.El V)} (ht : ∀ b c, R b c ∨ R c b)
    (htr : ∀ b c d, R b c → R c d → R b d) :
    ∀ L : List V.El, L ≠ [] → ∃ u ∈ L, ∀ c ∈ L, c ≠ u → R u c
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun c hc hne => absurd (List.mem_singleton.1 hc) hne⟩
  | a :: b :: L, _ => by
    obtain ⟨u, hu, hmax⟩ := exists_ext ht htr (b :: L) (by simp)
    rcases ht a u with h | h
    · refine ⟨a, by simp, fun c hc hne => ?_⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact absurd rfl hne
      · by_cases e : c = u
        · exact e ▸ h
        · exact htr _ _ _ h (hmax c hc e)
    · refine ⟨u, List.mem_cons_of_mem _ hu, fun c hc hne => ?_⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h
      · exact hmax c hc hne

/-- The one step: the extreme of the results of `x :: xs` is the extreme of the step from an extreme result of `xs`. -/
theorem ext_cons {R : Core.Rel (Obj.El V) (Obj.El V)} (ht : ∀ b c, R b c ∨ R c b)
    (htr : ∀ b c d, R b c → R c d → R b d) (has : ∀ b c, R b c → R c b → b = c)
    (TS : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (hmono : ∀ x u u' c, R u u' → TS (x, u') c → ∃ c', TS (x, u) c' ∧ R c' c)
    (F : Obj.El V → Prop) (hFL : ∃ L : List V.El, L.Pairwise V.lt ∧ ∀ c, c ∈ L ↔ F c) (x : E.El) (w : V.El) :
    Extr R (fun c => ∃ u, F u ∧ TS (x, u) c) w ↔ ∃ u, Extr R F u ∧ Extr R (TS (x, u)) w := by
  constructor
  · rintro ⟨⟨u0, hu0, hw0⟩, hn⟩
    obtain ⟨L, -, hL⟩ := hFL
    obtain ⟨u, huL, hmax⟩ := exists_ext ht htr L (List.ne_nil_of_mem ((hL u0).2 hu0))
    have hu : F u := (hL u).1 huL
    have hRu : R u u0 := by
      by_cases e : u0 = u
      · subst e; exact (ht u0 u0).elim id id
      · exact hmax u0 ((hL u0).2 hu0) e
    obtain ⟨c', hc', hRc⟩ := hmono x u u0 w hRu hw0
    have hcw : c' = w := by
      by_cases e : c' = w
      · exact e
      · exact has _ _ (hn c' ⟨u, hu, hc'⟩ e) hRc |>.symm
    subst hcw
    exact ⟨u, ⟨hu, fun c hc hne => hmax c ((hL c).2 hc) hne⟩,
      hc', fun c hc hne => hn c ⟨u, hu, hc⟩ hne⟩
  · rintro ⟨u, ⟨hu, hmax⟩, hw, hn⟩
    refine ⟨⟨u, hu, hw⟩, fun c ⟨u', hu', hc⟩ hne => ?_⟩
    by_cases e : u' = u
    · subst e; exact hn c hc hne
    · obtain ⟨c', hc', hRc⟩ := hmono x u u' c (hmax u' hu' e) hc
      by_cases e' : c' = w
      · rw [← e']; exact hRc
      · exact htr _ _ _ (hn c' hc' e') hRc

/-- **Greedy fold** at `Tm.den`'s relations: `Λ(⦇Te, TS⦈ʳ) est(R) = ⦇Te', Λ(TS) est(R)⦈ʳ` where `R = qtDen TQ` is a total
    order (`ht`, `htr`, `has`), `TS` is monotone in its second argument on `R` (`hmono`), the images of `TS` and of the fold
    are arrays (`hS`, `hF`), and the new seed `Te'` is the `R`-extreme of the old one (`hZ`). -/
theorem greedyFold_den (Te Te' : Core.Rel (Obj.El V) (Obj.El V)) (TS : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (TQ : Core.Rel (Obj.El (.prod V V)) (Obj.El (.prod V V))) (ht : ∀ b c, qtDen TQ b c ∨ qtDen TQ c b)
    (htr : ∀ b c d, qtDen TQ b c → qtDen TQ c d → qtDen TQ b d) (has : ∀ b c, qtDen TQ b c → qtDen TQ c b → b = c)
    (hmono : ∀ x u u' c, qtDen TQ u u' → TS (x, u') c → ∃ c', TS (x, u) c' ∧ qtDen TQ c' c)
    (hS : ∀ p, ∃ ys, lamDen TS p ys) (hF : ∀ xs, ∃ ys, lamDen (foldrDen Te TS) xs ys)
    (hZ : ∀ w, (∃ a, Te' a w) ↔ Extr (qtDen TQ) (fun v => ∃ a, Te a v) w) :
    lamDen (foldrDen Te TS) ≫ estDen TQ = foldrDen Te' (lamDen TS ≫ estDen TQ) := by
  have key : ∀ xs w, (lamDen (foldrDen Te TS) ≫ estDen TQ) xs w ↔ Extr (qtDen TQ) (foldrDen Te TS xs) w := fun xs w =>
    ⟨fun ⟨ys, h1, h2⟩ => (estDen_lam TQ h1 w).1 h2, fun h =>
      let ⟨ys, hy⟩ := hF xs; ⟨ys, hy, (estDen_lam TQ hy w).2 h⟩⟩
  have keyS : ∀ p c, (lamDen TS ≫ estDen TQ) p c ↔ Extr (qtDen TQ) (TS p) c := fun p c =>
    ⟨fun ⟨ys, h1, h2⟩ => (estDen_lam TQ h1 c).1 h2, fun h =>
      let ⟨ys, hy⟩ := hS p; ⟨ys, hy, (estDen_lam TQ hy c).2 h⟩⟩
  funext xs w
  refine propext ?_
  rw [key]
  induction xs generalizing w with
  | nil =>
    rw [foldrDen_empty, hZ]
    simp only [Extr, foldrDen_empty Te TS]
  | cons x xs ih =>
    have hset : foldrDen Te TS (x :: xs) = fun c => ∃ u, foldrDen Te TS xs u ∧ TS (x, u) c :=
      funext fun c => propext (foldrDen_cons _ _ _ _ _)
    rw [foldrDen_cons, hset, ext_cons ht htr has TS hmono _ (by
      obtain ⟨L, hL⟩ := hF xs
      exact ⟨L, (lamDen_iff _ _ _).1 hL |>.1, fun c => ((lamDen_iff _ _ _).1 hL).2 c⟩) x w]
    exact exists_congr fun u => and_congr (ih u) (keyS _ _).symm

/-- The pair test the prelude builds from `R` reads back as `R`: `qtDen (dom(π₂ ∩ π₁R)) = R`. -/
theorem qtDen_estQ (ρ : Val) {V : Obj} (R : Tm V V) :
    qtDen ((Tm.dom (.meet .outr (.comp .outl R))).den ρ) = R.den ρ := by
  funext b c
  refine propext ((qtDen_iff _ b c).trans ?_)
  simp only [Tm.dom_den, Tm.den, Core.Rel.inter_apply, Core.Rel.comp_apply, Core.Rel.id, Core.Rel.recip, Core.Rel.graph]
  constructor
  · rintro ⟨-, d, ⟨hd, hr⟩, e, he⟩
    obtain ⟨b1, rfl, h⟩ := hr; subst hd; exact h
  · intro h
    exact ⟨trivial, c, ⟨rfl, b, rfl, h⟩, rfl, b, rfl, h⟩

/-- **Greedy fold** as the prelude states it: `(𝟙÷∋)E(⦇[e, S]⦈ʳ)est(R) = ⦇[(𝟙÷∋)E(e)est(R), (𝟙÷∋)E(S)est(R)]⦈ʳ`, in the
    shape the elaborator builds (`Λ(X) est(R)`, `Pre.compFuse`). `R` is a total order (`ht`, `htr`, `has`), `S` monotone in
    its second argument on `R` (`hmono`), and `Λ(S)`, `Λ(⦇[e, S]⦈ʳ)`, `Λ(e)` are arrays at every point (`hS`, `hF`, `he`). -/
theorem Tm.greedyFold_den {E V : Obj} {e : Tm .one V} {S : Tm (.prod E V) V} {R : Tm V V} (ρ : Val)
    (ht : ∀ b c, R.den ρ b c ∨ R.den ρ c b) (htr : ∀ b c d, R.den ρ b c → R.den ρ c d → R.den ρ b d)
    (has : ∀ b c, R.den ρ b c → R.den ρ c b → b = c)
    (hmono : ∀ x u u' c, R.den ρ u u' → S.den ρ (x, u') c → ∃ c', S.den ρ (x, u) c' ∧ R.den ρ c' c)
    (hS : (Tm.dom (.lam S)).den ρ = (Tm.id (A := .prod E V)).den ρ)
    (hF : (Tm.dom (.lam (.foldr (.ran e) S))).den ρ = (Tm.id (A := .arr E)).den ρ)
    (he : (Tm.dom (.lam e)).den ρ = (Tm.id (A := .one)).den ρ) :
    (Tm.comp (.lam (.foldr (.ran e) S)) (.est (.dom (.meet .outr (.comp .outl R))))).den ρ =
      (Tm.foldr (.ran (.comp (.lam e) (.est (.dom (.meet .outr (.comp .outl R)))))) (.comp (.lam S)
        (.est (.dom (.meet .outr (.comp .outl R)))))).den ρ := by
  have hq := qtDen_estQ ρ R
  simp only [Tm.den, Tm.est_den, Tm.ran_den]
  generalize (Tm.dom (.meet .outr (.comp .outl R))).den ρ = TQ at hq ⊢
  rw [← hq] at ht htr has hmono
  have heA := Tm.entire_of_dom he
  have hE : ∀ x w, (lamDen (e.den ρ) ≫ estDen TQ) x w ↔ Extr (qtDen TQ) (e.den ρ x) w := fun x w =>
    ⟨fun ⟨ys, h1, h2⟩ => (estDen_lam TQ h1 w).1 h2, fun h =>
      let ⟨ys, hy⟩ := heA x; ⟨ys, hy, (estDen_lam TQ hy w).2 h⟩⟩
  have hF' := Tm.entire_of_dom hF
  simp only [Tm.den, Tm.ran_den] at hF'
  have hZe : ∀ b : Obj.one.El, (fun v => ∃ a, a = v ∧ ∃ b', den ρ e b' a ∧ den ρ e b' v) = den ρ e b := fun b =>
    funext fun v => propext ⟨fun ⟨_, rfl, b', h, _⟩ => (show b' = b from rfl) ▸ h,
      fun h => ⟨v, rfl, b, h, h⟩⟩
  refine Rel.Lang.greedyFold_den _ _ _ TQ ht htr has hmono (Tm.entire_of_dom hS) hF' fun w => ?_
  generalize (lamDen (e.den ρ) ≫ estDen TQ) = M at hE ⊢
  simp only [Core.Rel.inter_apply, Core.Rel.comp_apply, Core.Rel.id, Core.Rel.recip, hE]
  constructor
  · rintro ⟨a, rfl, b, hb, -⟩
    rwa [hZe b]
  · intro h
    rw [hZe ()] at h
    exact ⟨w, rfl, (), h, h⟩

end Rel.Lang
