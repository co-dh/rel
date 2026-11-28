import Rel.Lang.Laws.GreedyFold
import Rel.Lang.Laws.MssGreedy
import Rel.Lang.Laws.AopA5_5_TypeFunctor

/-! # Laws of AOP `A7_2` (the greedy theorem) on the concrete core, read off `Tm.den`

`Tm.greedy_den` is freyd's `greedy` at the list relator, `⦇[e, S]⦈ʳ` for `⦇S⦈`: the prelude's `est(Q)` is freyd's
`est(Q ∪ 𝟙)`, so freyd's `R` is `Q ∪ 𝟙`, transitive and monotone for `S`, and only `⊑` holds (no totality of `Q`). -/

namespace Rel.Lang
open scoped Rel.Core.Rel Classical
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {E V : Obj}

/-- The greedy step on relations: the fold of the `R`-extreme at each step is below the `R`-extreme of the fold, for
    `R' = R ∪ 𝟙` transitive (`htr`) and `TS(x, ·)` monotone on `R'` (`hmono`); no totality of `R`. -/
theorem greedyLe_den (Te Te' : Core.Rel (Obj.El V) (Obj.El V)) (TS : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (TQ : Core.Rel (Obj.El (.prod V V)) (Obj.El (.prod V V)))
    (htr : ∀ b c d, (b = c ∨ qtDen TQ b c) → (c = d ∨ qtDen TQ c d) → (b = d ∨ qtDen TQ b d))
    (hmono : ∀ x u u' c, (u = u' ∨ qtDen TQ u u') → TS (x, u') c →
      ∃ c', TS (x, u) c' ∧ (c' = c ∨ qtDen TQ c' c))
    (hF : ∀ xs, ∃ ys, lamDen (foldrDen Te TS) xs ys)
    (hZ : ∀ w, (∃ a, Te' a w) → Extr (qtDen TQ) (fun v => ∃ a, Te a v) w) :
    foldrDen Te' (lamDen TS ≫ estDen TQ) ⊑ lamDen (foldrDen Te TS) ≫ estDen TQ := by
  have keyS : ∀ p c, (lamDen TS ≫ estDen TQ) p c → Extr (qtDen TQ) (TS p) c := fun p c ⟨ys, h1, h2⟩ =>
    (estDen_lam TQ h1 c).1 h2
  have main : ∀ xs w, foldrDen Te' (lamDen TS ≫ estDen TQ) xs w → Extr (qtDen TQ) (foldrDen Te TS xs) w := by
    intro xs
    induction xs with
    | nil => intro w h; simpa only [Extr, foldrDen_empty Te TS] using hZ w ((foldrDen_empty ..).1 h)
    | cons x xs ih =>
      intro w h
      obtain ⟨u, hu, hw⟩ := (foldrDen_cons ..).1 h
      have hIH := ih u hu
      have hSw := keyS _ _ hw
      refine ⟨(foldrDen_cons ..).2 ⟨u, hIH.1, hSw.1⟩, fun c hc hne => ?_⟩
      obtain ⟨u', hu', hc'⟩ := (foldrDen_cons ..).1 hc
      have hRu : u = u' ∨ qtDen TQ u u' := by
        by_cases e : u' = u
        · exact Or.inl e.symm
        · exact Or.inr (hIH.2 u' hu' e)
      obtain ⟨c', hc'S, hc'c⟩ := hmono x u u' c hRu hc'
      have hwc' : w = c' ∨ qtDen TQ w c' := by
        by_cases e : c' = w
        · exact Or.inl e.symm
        · exact Or.inr (hSw.2 c' hc'S e)
      exact (htr _ _ _ hwc' (hc'c)).resolve_left fun e => hne e.symm
  refine Core.Rel.le_iff.2 fun xs w h => ?_
  obtain ⟨ys, hy⟩ := hF xs
  exact ⟨ys, hy, (estDen_lam TQ hy w).2 (main xs w h)⟩

/-- **`greedy`** as the prelude states it, at the list relator: `⦇[Λ(e) est(Q), Λ(S) est(Q)]⦈ʳ ⊑ Λ(⦇[e, S]⦈ʳ) est(Q)`
    when `Q ∪ 𝟙` is transitive and `⟨π₁, π₂(Q ∪ 𝟙)⟩ S ⊑ S (Q ∪ 𝟙)` (`S` monotone on `Q ∪ 𝟙`, freyd's `Pres S R`);
    `Λ(⦇[e, S]⦈ʳ)` is total (`Λ(e)` and `Λ(S)` need not be: `est` of an array is read off the array). The seed `uni(1)` in front of `Λ(e) est(Q)` changes nothing on `1`. -/
theorem Tm.greedy_den {e : Tm .one V} {S : Tm (.prod E V) V} {Q : Tm V V} (ρ : Val)
    (htr : (Tm.comp (Tm.join Q Tm.id) (Tm.join Q Tm.id)).den ρ ⊑ (Tm.join Q Tm.id).den ρ)
    (hmono : (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr (Tm.join Q Tm.id))) S).den ρ ⊑
      (Tm.comp S (Tm.join Q Tm.id)).den ρ)
    (hF : (Tm.dom (.lam (.foldr (.ran e) S))).den ρ = (Tm.id (A := .arr E)).den ρ) :
    (Tm.foldr (.ran (.comp (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)
        (.comp (.lam e) (.est (.dom (.meet .outr (.comp .outl Q))))))) (.comp (.lam S)
        (.est (.dom (.meet .outr (.comp .outl Q)))))).den ρ ⊑
      (Tm.comp (.lam (.foldr (.ran e) S)) (.est (.dom (.meet .outr (.comp .outl Q))))).den ρ := by
  have hq := qtDen_estQ ρ Q
  have hseed : (Tm.ran (Tm.comp (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)
        (Tm.comp (.lam e) (.est (.dom (.meet .outr (.comp .outl Q))))))).den ρ =
      (Tm.ran (Tm.comp (.lam e) (.est (.dom (.meet .outr (.comp .outl Q)))))).den ρ := by
    rw [Tm.ran_den, Tm.ran_den, Tm.uni_one_comp]
  have hFe := Tm.entire_of_dom hF
  simp only [Tm.den, Core.Rel.le_iff, Core.Rel.comp_apply, Core.Rel.union_apply, Core.Rel.id, Core.Rel.rpair] at htr hmono
  simp only [Tm.den, Tm.est_den, Tm.ran_den] at hseed ⊢
  rw [hseed]
  simp only [Tm.den, Tm.ran_den] at hFe
  generalize (Tm.dom (.meet .outr (.comp .outl Q))).den ρ = TQ at hq ⊢
  rw [← hq] at htr hmono
  refine greedyLe_den _ _ _ TQ (fun b c d h1 h2 => ?_) (fun x u u' c h1 h2 => ?_) (fun xs => hFe xs)
    fun w => ?_
  · exact (htr b d ⟨c, h1.symm, h2.symm⟩).symm
  · obtain ⟨c', h3, h4⟩ := hmono (x, u) c ⟨(x, u'), ⟨rfl, u, rfl, h1.symm⟩, h2⟩
    exact ⟨c', h3, h4.symm⟩
  · have hE : ∀ x w, (lamDen (e.den ρ) ≫ estDen TQ) x w → Extr (qtDen TQ) (e.den ρ x) w := fun x w ⟨ys, h1, h2⟩ =>
      (estDen_lam TQ h1 w).1 h2
    have hZe : ∀ b : Obj.one.El, (fun v => ∃ a, a = v ∧ ∃ b', den ρ e b' a ∧ den ρ e b' v) = den ρ e b := fun b =>
      funext fun v => propext ⟨fun ⟨_, rfl, b', h, _⟩ => (show b' = b from rfl) ▸ h,
        fun h => ⟨v, rfl, b, h, h⟩⟩
    generalize (lamDen (e.den ρ) ≫ estDen TQ) = M at hE ⊢
    simp only [Core.Rel.inter_apply, Core.Rel.comp_apply, Core.Rel.id, Core.Rel.recip]
    rintro ⟨a, rfl, b, hb, -⟩
    rw [hZe b]
    exact hE b a hb

theorem Tm.den_lam_eq {A B : Obj} (ρ : Val) (X : Tm A B) : (Tm.lam X).den ρ = lamDen (X.den ρ) := by
  simp only [Tm.den]

theorem Tm.mem_den {A : Obj} (ρ : Val) : (Tm.mem : Tm (.arr A) A).den ρ = memDen := by
  simp only [Tm.den]

theorem Tm.den_comp_eq {A B C : Obj} (ρ : Val) (X : Tm A B) (Y : Tm B C) : (Tm.comp X Y).den ρ = X.den ρ ≫ Y.den ρ := by
  simp only [Tm.den]

theorem mapDen_mono {A B : Obj} {T U : Core.Rel (Obj.El A) (Obj.El B)} (h : T ⊑ U) : mapDen T ⊑ mapDen U :=
  Core.Rel.le_iff.2 fun xs ys hm => by
    obtain ⟨hl, ht⟩ := (mapDen_iff _ _ _).1 hm
    exact (mapDen_iff _ _ _).2 ⟨hl, fun t h1 h2 => Core.Rel.le_iff.1 h _ _ (ht t h1 h2)⟩

/-- `est(Q) ⊑ ∋` (an extreme element is a member), carried through the list relator and postcomposed with `f`:
    `F(est(Q)) f ⊑ F(∋) f`. -/
theorem Tm.fmapEstCompLeFmapEpsComp_den {B C : Obj} {f : Tm (.arr B) C} {Q : Tm B B} (ρ : Val) :
    (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr (.arr B)) (.arr B)) (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl Q)))))
      f).den ρ ⊑ (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr (.arr B)) (.arr B)) (Tm.mem : Tm (.arr B) B)) f).den ρ := by
  rw [Tm.den_comp_eq, Tm.den_comp_eq, Tm.fmap_den, Tm.fmap_den]
  have hm := Core.Rel.le_iff.1 (mapDen_mono (T := (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl Q)))).den ρ)
    (U := (Tm.mem : Tm (.arr B) B).den ρ) (Core.Rel.le_iff.2 fun xs b h => by
      rw [Tm.est_den] at h; exact ((estDen_iff _ _ _).1 h).1))
  exact Core.Rel.le_iff.2 fun a c ⟨b, h1, h2⟩ => ⟨b, hm _ _ h1, h2⟩

/-- `distributes_of_pres` on relations at the list relator, `F(est Q) f ⊑ Λ(F(∋) f) est Q` when `f` is simple and
    monotone, `F(R°) f ⊑ f R°` for `R = Q ∪ 𝟙` (`J' b c ↔ Q c b ∨ b = c`). Path: `ys` picks the `Q`-extreme `ys[t]` of
    each `zs[t]`; another pick `ys'` has `ys'[t] = ys[t]` or `Q(ys[t], ys'[t])`, so `ys' F(J') ys`, `f` carries it to
    `f ys' c` with `J' c w`, that is `c = w` or `Q(w, c)`: `w = f ys` is the extreme of the images of all picks. -/
theorem distributesOfPres_core {B : Obj} (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B)))
    (f : Core.Rel (Obj.El (.arr B)) (Obj.El B)) (J : Core.Rel (Obj.El B) (Obj.El B))
    (hJ : ∀ b c, J b c ↔ qtDen TQ c b ∨ b = c)
    (hsim : ∀ ys c c', f ys c → f ys c' → c = c')
    (hpres : ∀ ys ys' c, mapDen J ys' ys → f ys c → ∃ c', f ys' c' ∧ J c' c)
    (hF : ∀ zs, ∃ L, lamDen (mapDen memDen ≫ f) zs L) :
    mapDen (estDen TQ) ≫ f ⊑ lamDen (mapDen memDen ≫ f) ≫ estDen TQ := by
  refine Core.Rel.le_iff.2 fun zs w ⟨ys, hm, hf⟩ => ?_
  obtain ⟨L, hL⟩ := hF zs
  refine ⟨L, hL, (estDen_lam TQ hL w).2 ?_⟩
  obtain ⟨hl, hy⟩ := (mapDen_iff _ _ _).1 hm
  refine ⟨⟨ys, (mapDen_iff _ _ _).2 ⟨hl, fun t h1 h2 => ((estDen_iff _ _ _).1 (hy t h1 h2)).1⟩, hf⟩,
    fun c ⟨ys', hm', hf'⟩ hne => ?_⟩
  obtain ⟨hl', hy'⟩ := (mapDen_iff _ _ _).1 hm'
  have hJ' : mapDen J ys' ys := (mapDen_iff _ _ _).2 ⟨hl.trans hl'.symm, fun t h1 h2 => (hJ _ _).2 (by
    by_cases e : ys'[t] = ys[t]
    · exact Or.inr e
    · obtain ⟨-, hn⟩ := (estDen_iff _ _ _).1 (hy t (by omega) h2)
      exact Or.inl (Classical.byContradiction fun hq => hn ⟨_, hy' t (by omega) h1, e, fun h => hq ((qtDen_iff TQ _ _).2 h)⟩))⟩
  obtain ⟨c', hc', hq⟩ := hpres ys ys' w hJ' hf
  obtain rfl := hsim ys' c c' hf' hc'
  exact ((hJ _ _).1 hq).resolve_right hne

/-- **`distributes_of_pres`** as the prelude states it, at the list relator, `R = Q ∪ 𝟙` (`(Q ∪ 𝟙)° = Q° ∪ 𝟙`). -/
theorem Tm.distributesOfPres_den {B : Obj} {f : Tm (.arr B) B} {Q : Tm B B} (ρ : Val)
    (hsim : (Tm.comp (Tm.conv f) f).den ρ ⊑ (Tm.id (A := B)).den ρ)
    (hpres : (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr B) (.arr B)) (Tm.join (Tm.conv Q) Tm.id)) f).den ρ ⊑
      (Tm.comp f (Tm.join (Tm.conv Q) Tm.id)).den ρ)
    (hF : (Tm.dom (Tm.lam (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr (.arr B)) (.arr B)) (Tm.mem : Tm (.arr B) B)) f))).den ρ =
      (Tm.id (A := .arr (.arr B))).den ρ) :
    (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr (.arr B)) (.arr B)) (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl Q)))))
      f).den ρ ⊑
    (Tm.comp (Tm.lam (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr (.arr B)) (.arr B)) (Tm.mem : Tm (.arr B) B)) f))
      (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl Q))))).den ρ := by
  have hq := qtDen_estQ ρ Q
  have hFe := Tm.entire_of_dom hF
  rw [Tm.den_comp_eq, Tm.den_comp_eq, Tm.fmap_den] at hpres
  rw [Tm.den_comp_eq, Tm.den_comp_eq, Tm.den_lam_eq, Tm.den_comp_eq, Tm.fmap_den, Tm.fmap_den, Tm.est_den, Tm.mem_den]
  rw [Tm.den_lam_eq, Tm.den_comp_eq, Tm.fmap_den, Tm.mem_den] at hFe
  simp only [Tm.den, Core.Rel.le_iff, Core.Rel.comp_apply, Core.Rel.recip, Core.Rel.id] at hsim
  generalize (Tm.dom (.meet .outr (.comp .outl Q))).den ρ = TQ at hq ⊢
  refine distributesOfPres_core TQ (f.den ρ) ((Q.den ρ)° ∪ 𝟙 _) (fun b c => ?_) (fun ys c c' h1 h2 => hsim c c' ⟨ys, h1, h2⟩)
    (fun ys ys' c hm hf => ?_) hFe
  · rw [hq]; simp only [Core.Rel.union_apply, Core.Rel.recip, Core.Rel.id]
  · simp only [Tm.den] at hpres
    exact Core.Rel.le_iff.1 hpres ys' c ⟨ys, hm, hf⟩

end Rel.Lang
