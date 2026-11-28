import Rel.Lang.Laws.AopA7_2

/-! # Laws of AOP `A10_1.lean` (companion `10-greedy.typ`), on the concrete core

`F` is the list relator `F(R) = mapDen R`, so freyd's `Alg F A` is `T : [A] ⟶ A` and the base functor's `F.map` is `F(R)`.
The hylomorphism `H = ⦇h⦈ ⦇T⦈°` is a parameter `H : A ⟶ B` that is a fixed point of `H = T° F(H) h` (`hylo_fixed`), one
inequation for each theorem: a stronger form, with `⦇h⦈ ⦇T⦈°` as an instance. The prelude's `est(Q)` is freyd's
`est(Q ∪ 𝟙)`, so freyd's `≤` and `Q` are `R ∪ 𝟙` and `Q ∪ 𝟙`, with no reflexivity premise. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel Classical
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `est(Q)` reads: `c` of `xs`, and every `a` of `xs` is `c` or `Q`-after `c`. -/
theorem estP_iff {B : Obj} (Q : Tm B B) (ρ : Val) (xs : List B.El) (c : B.El) :
    (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl Q)))).den ρ xs c ↔ c ∈ xs ∧ ∀ a ∈ xs, c = a ∨ Q.den ρ c a := by
  rw [Tm.est_den, estDen_iff]
  refine and_congr_right fun _ => ?_
  simp only [← qtDen_iff, qtDen_estQ]
  refine ⟨fun h a ha => ?_, fun h ⟨a, ha, hne, hq⟩ => ?_⟩
  · by_cases hq : Q.den ρ c a
    · exact .inr hq
    · by_cases he : a = c
      · exact .inl he.symm
      · exact absurd ⟨a, ha, he, hq⟩ h
  · rcases h a ha with h | h
    · exact hne h.symm
    · exact hq h

/-- Theorem 10.1 (i), B&dM p.245: the greedy body at `M = Λ(H) est(R)` returns only what `H` returns. `est(Q) ⊑ ∋` and
    `est(R) ⊑ ∋` pick members, `Λ(T°) ∋ ⊑ T°` and `Λ(H) ∋ ⊑ H`, and `T° F(H) h ⊑ H`. -/
theorem greedyDpLower_core {A B : Obj} (T : Core.Rel (Obj.El (.arr A)) (Obj.El A)) (h : Core.Rel (Obj.El (.arr B)) (Obj.El B))
    (H : Core.Rel (Obj.El A) (Obj.El B)) (E : Core.Rel (Obj.El (.arr (.arr A))) (Obj.El (.arr A))) (ER : Core.Rel (Obj.El (.arr B)) (Obj.El B))
    (hE : ∀ xs c, E xs c → c ∈ xs) (hER : ∀ xs c, ER xs c → c ∈ xs)
    (hH : ((T° ≫ mapDen H) ≫ h) ⊑ H) :
    ((((lamDen T°) ≫ E) ≫ mapDen (lamDen H ≫ ER)) ≫ h) ⊑ H := by
  refine Core.Rel.le_iff.2 fun a y ⟨ms, ⟨l, ⟨S, hS, hEl⟩, hF⟩, hy⟩ => ?_
  have hT : T l a := ((lamDen_iff _ _ _).1 hS).2 l |>.1 (hE _ _ hEl)
  obtain ⟨hlen, hm⟩ := (mapDen_iff _ _ _).1 hF
  refine Core.Rel.le_iff.1 hH a y ⟨ms, ⟨l, hT, (mapDen_iff _ _ _).2 ⟨hlen, fun t h1 h2 => ?_⟩⟩, hy⟩
  obtain ⟨S', hS', hr⟩ := hm t h1 h2
  exact ((lamDen_iff _ _ _).1 hS').2 _ |>.1 (hER _ _ hr)

/-- Theorem 10.1 (ii), B&dM p.245, with `Rb = R ∪ 𝟙` and `Qb = Q ∪ 𝟙`: from `H a b'` unfold `H` to `l` with `T l a`, so
    `l` is a candidate of `Λ(T°)`, and the extreme `l0` is `Qb`-before it. `Qb F(H) h ⊑ F(H) h Rb` moves `l0` to `ls0`
    with `h ls0 b''`, `Rb b'' b'`; `M = Λ(H) est(R)` gives `Rb m_i ls0_i` pointwise, so `F(Rb) ms ls0`, `h` monotone on
    `Rb` and simple gives `h ms y` with `Rb y b''`, and `Rb` transitive finishes. -/
theorem greedyDpUpper_core {A B : Obj} (T : Core.Rel (Obj.El (.arr A)) (Obj.El A)) (h : Core.Rel (Obj.El (.arr B)) (Obj.El B))
    (H : Core.Rel (Obj.El A) (Obj.El B)) (Q : Core.Rel (Obj.El (.arr A)) (Obj.El (.arr A))) (R : Core.Rel (Obj.El B) (Obj.El B))
    (E : Core.Rel (Obj.El (.arr (.arr A))) (Obj.El (.arr A))) (ER : Core.Rel (Obj.El (.arr B)) (Obj.El B))
    (hE : ∀ xs c, E xs c → c ∈ xs ∧ ∀ a ∈ xs, c = a ∨ Q c a)
    (hER : ∀ xs c, ER xs c → c ∈ xs ∧ ∀ a ∈ xs, c = a ∨ R c a)
    (hfix : H ⊑ ((T° ≫ mapDen H) ≫ h))
    (hs : ∀ ms y y', h ms y → h ms y' → y = y')
    (hp : ∀ ms ls z, mapDen (fun x y => R x y ∨ x = y) ms ls → h ls z → ∃ y, h ms y ∧ (R y z ∨ y = z))
    (htr : ∀ x y z, (R x y ∨ x = y) → (R y z ∨ y = z) → (R x z ∨ x = z))
    (hQ : ∀ l0 l z, (Q l0 l ∨ l0 = l) → (mapDen H ≫ h) l z →
      ∃ ls0 b, mapDen H l0 ls0 ∧ h ls0 b ∧ (R b z ∨ b = z)) :
    ((((H° ≫ lamDen T°) ≫ E) ≫ mapDen (lamDen H ≫ ER)) ≫ h) ⊑ (fun b' y => R y b' ∨ b' = y) := by
  refine Core.Rel.le_iff.2 fun b' y ⟨ms, ⟨l0, ⟨S, ⟨a, hHa, hS⟩, hEl⟩, hF⟩, hy⟩ => ?_
  have hHa : H a b' := hHa
  obtain ⟨ls, ⟨l, hTl, hFH⟩, hh⟩ := Core.Rel.le_iff.1 hfix a b' hHa
  have hl : l ∈ S := (((lamDen_iff _ _ _).1 hS).2 l).2 hTl
  obtain ⟨hl0, hmin⟩ := hE _ _ hEl
  obtain ⟨ls0, b'', hFH0, hh0, hRb⟩ := hQ l0 l b' ((hmin l hl).symm) ⟨ls, hFH, hh⟩
  obtain ⟨hlen, hm⟩ := (mapDen_iff _ _ _).1 hF
  obtain ⟨hlen0, hm0⟩ := (mapDen_iff _ _ _).1 hFH0
  have hmap : mapDen (fun x y => R x y ∨ x = y) ms ls0 := (mapDen_iff _ _ _).2 ⟨by omega, fun t h1 h2 => by
    obtain ⟨S', hS', hr⟩ := hm t (by omega) h1
    have hmem : ls0[t] ∈ S' := (((lamDen_iff _ _ _).1 hS').2 _).2 (hm0 t (by omega) h2)
    rcases (hER _ _ hr).2 _ hmem with h | h
    · exact .inr h
    · exact .inl h⟩
  obtain ⟨y', hy', hRy⟩ := hp ms ls0 b'' hmap hh0
  obtain rfl := hs ms y y' hy hy'
  exact (htr y b'' b' hRy hRb).imp_right Eq.symm

/-- **Theorem 10.1 (i)** (freyd `greedy_dp_lower`) at the list relator, for any `H` with `T° F(H) h ⊑ H` (`H = ⦇h⦈⦇T⦈°`
    is one). -/
theorem Tm.greedyDpLower_den {A B : Obj} {T : Tm (.arr A) A} {h : Tm (.arr B) B} {H : Tm A B} {Q : Tm (.arr A) (.arr A)}
    {R : Tm B B} (ρ : Val)
    (hH : (Tm.comp (Tm.comp T.conv (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) H)) h).den ρ ⊑ H.den ρ) :
    (Tm.comp (Tm.comp (Tm.comp (Tm.lam T.conv) (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl Q)))))
      (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B))
        (Tm.comp (Tm.lam H) (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl R))))))) h).den ρ ⊑ H.den ρ := by
  simp only [Tm.den_comp_eq, Tm.den_lam_eq, Tm.fmap_den] at hH ⊢
  refine greedyDpLower_core (T.den ρ) (h.den ρ) (H.den ρ) _ _ (fun xs c hc => ((estP_iff Q ρ xs c).1 hc).1)
    (fun xs c hc => ((estP_iff R ρ xs c).1 hc).1) ?_
  simpa only [Tm.den] using hH

theorem Tm.join_id_den {C : Obj} (X : Tm C C) (ρ : Val) :
    (Tm.join X Tm.id).den ρ = fun x y => X.den ρ x y ∨ x = y := by
  funext x y
  exact propext (by simp only [Tm.den, Core.Rel.union, Core.Rel.id])

/-- **Theorem 10.1 (ii)** (freyd `greedy_dp_upper`) at the list relator, for any `H ⊑ T° F(H) h`, `h` simple,
    monotone on the transitive `R ∪ 𝟙` (freyd's `≤`), and `(Q ∪ 𝟙) F(H) h ⊑ F(H) h (R ∪ 𝟙)` (freyd's `ThinCondition`). -/
theorem Tm.greedyDpUpper_den {A B : Obj} {T : Tm (.arr A) A} {h : Tm (.arr B) B} {H : Tm A B} {Q : Tm (.arr A) (.arr A)}
    {R : Tm B B} (ρ : Val)
    (hfix : H.den ρ ⊑ (Tm.comp (Tm.comp T.conv (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) H)) h).den ρ)
    (hs : (Tm.comp h.conv h).den ρ ⊑ (Tm.id (A := B)).den ρ)
    (hp : (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr B) (.arr B)) (Tm.join R Tm.id)) h).den ρ ⊑
      (Tm.comp h (Tm.join R Tm.id)).den ρ)
    (htr : (Tm.comp (Tm.join R Tm.id) (Tm.join R Tm.id)).den ρ ⊑ (Tm.join R Tm.id).den ρ)
    (hQ : (Tm.comp (Tm.comp (Tm.join Q Tm.id) (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) H)) h).den ρ ⊑
      (Tm.comp (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) H) h) (Tm.join R Tm.id)).den ρ) :
    (Tm.comp (Tm.comp (Tm.comp (Tm.comp H.conv (Tm.lam T.conv))
      (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl Q)))))
      (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B))
        (Tm.comp (Tm.lam H) (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl R))))))) h).den ρ ⊑
      (Tm.join R.conv Tm.id).den ρ := by
  simp only [Tm.den_comp_eq, Tm.den_lam_eq, Tm.fmap_den, Tm.join_id_den] at hfix hp htr hQ ⊢
  simp only [Tm.den, Core.Rel.le_iff, Core.Rel.comp_apply, Core.Rel.recip, Core.Rel.id] at hs
  change _ ⊑ (fun b' y => R.den ρ y b' ∨ b' = y)
  refine greedyDpUpper_core (T.den ρ) (h.den ρ) (H.den ρ) (Q.den ρ) (R.den ρ) _ _
    (fun xs c hc => (estP_iff Q ρ xs c).1 hc) (fun xs c hc => (estP_iff R ρ xs c).1 hc) ?_
    (fun ms y y' h1 h2 => hs y y' ⟨ms, h1, h2⟩) (fun ms ls z hm hh => ?_)
    (fun x y z h1 h2 => ?_) (fun l0 l z hq hh => ?_)
  · simpa only [Tm.den] using hfix
  · obtain ⟨y, hy, hr⟩ := Core.Rel.le_iff.1 hp ms z ⟨ls, hm, hh⟩
    exact ⟨y, hy, hr⟩
  · exact Core.Rel.le_iff.1 htr x z ⟨y, h1, h2⟩
  · obtain ⟨ls, hFH, hh'⟩ := hh
    obtain ⟨b, ⟨ls0, hH, hh1⟩, hr⟩ := Core.Rel.le_iff.1 hQ l0 z ⟨ls, ⟨l, hq, hFH⟩, hh'⟩
    exact ⟨ls0, b, hH, hh1, hr⟩

/-! ### Proposition 10.1: disjoint ranges -/

theorem map_inl_sorted {A B : Obj} (S1 : List A.El) :
    (S1.map (Sum.inl : A.El → Obj.El (.sum A B))).Pairwise (Obj.sum A B).lt ↔ S1.Pairwise A.lt := by
  rw [List.pairwise_map]; simp only [Obj.lt_inl]

theorem map_inr_sorted {A B : Obj} (S1 : List B.El) :
    (S1.map (Sum.inr : B.El → Obj.El (.sum A B))).Pairwise (Obj.sum A B).lt ↔ S1.Pairwise B.lt := by
  rw [List.pairwise_map]; simp only [Obj.lt_inr]

theorem exists_map_inl {X Y : Type} (S : List (X ⊕ Y)) (h : ∀ s ∈ S, ∃ x, s = Sum.inl x) :
    ∃ S1 : List X, S = S1.map Sum.inl := by
  induction S with
  | nil => exact ⟨[], rfl⟩
  | cons s S ih =>
    obtain ⟨x, rfl⟩ := h s (by simp)
    obtain ⟨S1, rfl⟩ := ih fun s hs => h s (by simp [hs])
    exact ⟨x :: S1, rfl⟩

theorem exists_map_inr {X Y : Type} (S : List (X ⊕ Y)) (h : ∀ s ∈ S, ∃ y, s = Sum.inr y) :
    ∃ S1 : List Y, S = S1.map Sum.inr := by
  induction S with
  | nil => exact ⟨[], rfl⟩
  | cons s S ih =>
    obtain ⟨y, rfl⟩ := h s (by simp)
    obtain ⟨S1, rfl⟩ := ih fun s hs => h s (by simp [hs])
    exact ⟨y :: S1, rfl⟩

/-- **Proposition 10.1** (B&dM p.245) on relations: with `V₁`, `V₂` of disjoint ranges the sorted list of `Λ([V₁,V₂]°)`
    at `a` holds only left summands (or only right ones), so the extreme under `Q₁ + Q₂` is the extreme of `Λ(V₁°)` (or
    `Λ(V₂°)`) under `Q₁`, and `ran(V₁)` (`ran(V₂)`) tells which side `a` is on. -/
theorem greedyDisjoint_core {A B C D : Obj}
    (V1 : Core.Rel (Obj.El A) (Obj.El C)) (V2 : Core.Rel (Obj.El B) (Obj.El C))
    (U1 : Core.Rel (Obj.El A) (Obj.El D)) (U2 : Core.Rel (Obj.El B) (Obj.El D))
    (Q1 : Core.Rel (Obj.El A) (Obj.El A)) (Q2 : Core.Rel (Obj.El B) (Obj.El B))
    (JV : Core.Rel (Obj.El C) (Obj.El (.sum A B))) (JU : Core.Rel (Obj.El (.sum A B)) (Obj.El D))
    (Qs : Core.Rel (Obj.El (.sum A B)) (Obj.El (.sum A B)))
    (E : Core.Rel (Obj.El (.arr (.sum A B))) (Obj.El (.sum A B)))
    (E1 : Core.Rel (Obj.El (.arr A)) (Obj.El A)) (E2 : Core.Rel (Obj.El (.arr B)) (Obj.El B))
    (R1 : Core.Rel (Obj.El C) (Obj.El C)) (R2 : Core.Rel (Obj.El C) (Obj.El C))
    (hJV : ∀ a t, JV a t ↔ (∃ x, V1 x a ∧ t = Sum.inl x) ∨ (∃ y, V2 y a ∧ t = Sum.inr y))
    (hJU : ∀ t z, JU t z ↔ (∃ x, t = Sum.inl x ∧ U1 x z) ∨ (∃ y, t = Sum.inr y ∧ U2 y z))
    (hQs : ∀ s t, Qs s t ↔ (∃ x y, s = Sum.inl x ∧ t = Sum.inl y ∧ Q1 x y) ∨ (∃ x y, s = Sum.inr x ∧ t = Sum.inr y ∧ Q2 x y))
    (hE : ∀ S t, E S t ↔ t ∈ S ∧ ∀ s ∈ S, t = s ∨ Qs t s)
    (hE1 : ∀ S t, E1 S t ↔ t ∈ S ∧ ∀ s ∈ S, t = s ∨ Q1 t s)
    (hE2 : ∀ S t, E2 S t ↔ t ∈ S ∧ ∀ s ∈ S, t = s ∨ Q2 t s)
    (hR1 : ∀ a w, R1 a w ↔ a = w ∧ ∃ m, V1 m a) (hR2 : ∀ a w, R2 a w ↔ a = w ∧ ∃ m, V2 m a)
    (hd : ∀ a x y, V1 x a → V2 y a → False) :
    ((lamDen JV ≫ E) ≫ JU) =
      ((((R1 ≫ lamDen V1°) ≫ E1) ≫ U1) ∪ (((R2 ≫ lamDen V2°) ≫ E2) ≫ U2)) := by
  refine Core.Rel.ext fun a z => ?_
  constructor
  · rintro ⟨t, ⟨S, hS, hEt⟩, hU⟩
    obtain ⟨hsort, hmem⟩ := (lamDen_iff _ _ _).1 hS
    obtain ⟨ht, hmin⟩ := (hE _ _).1 hEt
    rcases t with x | y
    · have hx : V1 x a := by
        rcases (hJV _ _).1 ((hmem _).1 ht) with ⟨x', h', e⟩ | ⟨y, _, e⟩
        · cases e; exact h'
        · cases e
      have hall : ∀ s ∈ S, ∃ x, s = Sum.inl x := fun s hs => by
        rcases (hJV _ _).1 ((hmem s).1 hs) with ⟨x', _, e⟩ | ⟨y, hy, e⟩
        · exact ⟨x', e⟩
        · exact (hd a x y hx hy).elim
      obtain ⟨S1, rfl⟩ := exists_map_inl S hall
      have hin : ∀ b, (Sum.inl b : Obj.El (.sum A B)) ∈ S1.map Sum.inl ↔ b ∈ S1 := fun b => by simp
      refine Or.inl ⟨x, ⟨S1, ⟨a, (hR1 _ _).2 ⟨rfl, x, hx⟩, (lamDen_iff _ _ _).2 ⟨(map_inl_sorted S1).1 hsort, fun b => ?_⟩⟩,
        (hE1 _ _).2 ⟨(hin x).1 ht, fun s hs => ?_⟩⟩, ?_⟩
      · refine ⟨fun hb => ?_, fun hb => (hin b).1 ((hmem _).2 ((hJV _ _).2 (.inl ⟨b, hb, rfl⟩)))⟩
        rcases (hJV _ _).1 ((hmem _).1 ((hin b).2 hb)) with ⟨x', h', e⟩ | ⟨y, _, e⟩
        · cases e; exact h'
        · cases e
      · rcases hmin (Sum.inl s) ((hin s).2 hs) with e | h
        · exact .inl (Sum.inl.inj e)
        · rcases (hQs _ _).1 h with ⟨x1, y1, e1, e2, hq⟩ | ⟨x1, y1, e1, _⟩
          · cases e1; cases e2; exact .inr hq
          · cases e1
      · rcases (hJU _ _).1 hU with ⟨x', e, h⟩ | ⟨y, e, _⟩
        · cases e; exact h
        · cases e
    · have hy : V2 y a := by
        rcases (hJV _ _).1 ((hmem _).1 ht) with ⟨x', _, e⟩ | ⟨y', h', e⟩
        · cases e
        · cases e; exact h'
      have hall : ∀ s ∈ S, ∃ y, s = Sum.inr y := fun s hs => by
        rcases (hJV _ _).1 ((hmem s).1 hs) with ⟨x', hx', e⟩ | ⟨y', _, e⟩
        · exact (hd a x' y hx' hy).elim
        · exact ⟨y', e⟩
      obtain ⟨S1, rfl⟩ := exists_map_inr S hall
      have hin : ∀ b, (Sum.inr b : Obj.El (.sum A B)) ∈ S1.map Sum.inr ↔ b ∈ S1 := fun b => by simp
      refine Or.inr ⟨y, ⟨S1, ⟨a, (hR2 _ _).2 ⟨rfl, y, hy⟩, (lamDen_iff _ _ _).2 ⟨(map_inr_sorted S1).1 hsort, fun b => ?_⟩⟩,
        (hE2 _ _).2 ⟨(hin y).1 ht, fun s hs => ?_⟩⟩, ?_⟩
      · refine ⟨fun hb => ?_, fun hb => (hin b).1 ((hmem _).2 ((hJV _ _).2 (.inr ⟨b, hb, rfl⟩)))⟩
        rcases (hJV _ _).1 ((hmem _).1 ((hin b).2 hb)) with ⟨x', _, e⟩ | ⟨y', h', e⟩
        · cases e
        · cases e; exact h'
      · rcases hmin (Sum.inr s) ((hin s).2 hs) with e | h
        · exact .inl (Sum.inr.inj e)
        · rcases (hQs _ _).1 h with ⟨x1, y1, e1, _⟩ | ⟨x1, y1, e1, e2, hq⟩
          · cases e1
          · cases e1; cases e2; exact .inr hq
      · rcases (hJU _ _).1 hU with ⟨x', e, _⟩ | ⟨y', e, h⟩
        · cases e
        · cases e; exact h
  · rintro (⟨x, ⟨S1, ⟨a', hR, hS1⟩, hEx⟩, hU⟩ | ⟨y, ⟨S1, ⟨a', hR, hS1⟩, hEx⟩, hU⟩)
    · obtain ⟨rfl, m, hm⟩ := (hR1 _ _).1 hR
      obtain ⟨hs1, hmem1⟩ := (lamDen_iff _ _ _).1 hS1
      obtain ⟨hx, hmin⟩ := (hE1 _ _).1 hEx
      refine ⟨Sum.inl x, ⟨S1.map Sum.inl, (lamDen_iff _ _ _).2 ⟨(map_inl_sorted S1).2 hs1, fun s => ?_⟩,
        (hE _ _).2 ⟨List.mem_map.2 ⟨x, hx, rfl⟩, fun s hs => ?_⟩⟩, (hJU _ _).2 (.inl ⟨x, rfl, hU⟩)⟩
      · refine ⟨fun hs => ?_, fun hs => ?_⟩
        · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hs
          exact (hJV _ _).2 (.inl ⟨x', (hmem1 x').1 hx', rfl⟩)
        · rcases (hJV _ _).1 hs with ⟨x', h', rfl⟩ | ⟨y, hy, rfl⟩
          · exact List.mem_map.2 ⟨x', (hmem1 x').2 h', rfl⟩
          · exact (hd _ m y hm hy).elim
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
        rcases hmin s' hs' with e | h
        · exact .inl (by rw [e])
        · exact .inr ((hQs _ _).2 (.inl ⟨x, s', rfl, rfl, h⟩))
    · obtain ⟨rfl, m, hm⟩ := (hR2 _ _).1 hR
      obtain ⟨hs1, hmem1⟩ := (lamDen_iff _ _ _).1 hS1
      obtain ⟨hy, hmin⟩ := (hE2 _ _).1 hEx
      refine ⟨Sum.inr y, ⟨S1.map Sum.inr, (lamDen_iff _ _ _).2 ⟨(map_inr_sorted S1).2 hs1, fun s => ?_⟩,
        (hE _ _).2 ⟨List.mem_map.2 ⟨y, hy, rfl⟩, fun s hs => ?_⟩⟩, (hJU _ _).2 (.inr ⟨y, rfl, hU⟩)⟩
      · refine ⟨fun hs => ?_, fun hs => ?_⟩
        · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hs
          exact (hJV _ _).2 (.inr ⟨y', (hmem1 y').1 hy', rfl⟩)
        · rcases (hJV _ _).1 hs with ⟨x', hx', rfl⟩ | ⟨y', h', rfl⟩
          · exact (hd _ x' m hx' hm).elim
          · exact List.mem_map.2 ⟨y', (hmem1 y').2 h', rfl⟩
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
        rcases hmin s' hs' with e | h
        · exact .inl (by rw [e])
        · exact .inr ((hQs _ _).2 (.inr ⟨y, s', rfl, rfl, h⟩))

/-- **Proposition 10.1** (freyd `greedy_disjoint_ranges`), `Q₁ + Q₂ = [Q₁ inl, Q₂ inr]`, `V₂ V₁° = 𝟘` read as `V₁`, `V₂`
    having no common image. -/
theorem Tm.greedyDisjointRanges_den {A B C D : Obj} {V₁ : Tm A C} {V₂ : Tm B C} {U₁ : Tm A D} {U₂ : Tm B D}
    {Q₁ : Tm A A} {Q₂ : Tm B B} (ρ : Val) (hd : (Tm.comp V₂ V₁.conv).den ρ = Tm.zero.den ρ) :
    (Tm.comp (Tm.comp (Tm.lam (Tm.join (Tm.comp V₁.conv Tm.inl) (Tm.comp V₂.conv Tm.inr)))
      (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl
        (Tm.join (Tm.comp Tm.inl.conv (Tm.comp Q₁ Tm.inl)) (Tm.comp Tm.inr.conv (Tm.comp Q₂ Tm.inr))))))))
      (Tm.join (Tm.comp Tm.inl.conv U₁) (Tm.comp Tm.inr.conv U₂))).den ρ =
    (Tm.join (Tm.comp (Tm.comp (Tm.comp (Tm.ran V₁) (Tm.lam V₁.conv))
        (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl Q₁))))) U₁)
      (Tm.comp (Tm.comp (Tm.comp (Tm.ran V₂) (Tm.lam V₂.conv))
        (Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl Q₂))))) U₂)).den ρ := by
  have hd' : ∀ a x y, V₁.den ρ x a → V₂.den ρ y a → False := fun a x y h1 h2 => by
    have h3 : (Tm.comp V₂ V₁.conv).den ρ y x := ⟨a, h2, h1⟩
    rw [hd] at h3
    exact h3
  simp only [Tm.den_comp_eq, Tm.den_lam_eq]
  refine greedyDisjoint_core (V₁.den ρ) (V₂.den ρ) (U₁.den ρ) (U₂.den ρ) (Q₁.den ρ) (Q₂.den ρ) _ _
    ((Tm.join (Tm.comp Tm.inl.conv (Tm.comp Q₁ Tm.inl)) (Tm.comp Tm.inr.conv (Tm.comp Q₂ Tm.inr))).den ρ) _ _ _ _ _
    ?_ ?_ ?_ (fun S t => estP_iff _ ρ S t) (fun S t => estP_iff Q₁ ρ S t) (fun S t => estP_iff Q₂ ρ S t)
    (fun a w => Tm.ran_den' ρ V₁ a w) (fun a w => Tm.ran_den' ρ V₂ a w) hd'
  · intro a t
    simp only [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]
  · intro t z
    simp only [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]
  · intro s t
    simp only [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]
    constructor
    · rintro (⟨x, hs, y, hq, ht⟩ | ⟨x, hs, y, hq, ht⟩)
      · exact .inl ⟨x, y, hs, ht, hq⟩
      · exact .inr ⟨x, y, hs, ht, hq⟩
    · rintro (⟨x, y, hs, ht, hq⟩ | ⟨x, y, hs, ht, hq⟩)
      · exact .inl ⟨x, hs, y, hq, ht⟩
      · exact .inr ⟨x, hs, y, hq, ht⟩

end Rel.Lang
