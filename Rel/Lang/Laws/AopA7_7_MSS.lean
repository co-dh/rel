import Rel.Lang.Laws.Map
import Rel.Lang.Laws.MssFuse
import Rel.Lang.Laws.AopA10_4_Tex
import Rel.Lang.Laws.EstMap

/-! # Laws of freyd `AOP/A7_7_MSS.lean` (Ex 7.40, the maximum segment sum), on the concrete core

`Rel.Lang.Tm.<name>_den` is the law of the row `<name>` read off `Tm.den`; `Rel/Programs/Aop/A7_7_MSS.lean` states it. The
rows are stated at an arbitrary seed `e`, step `P` and order `R` (the stronger form: `zero`, `plus`, `≥` are instances). -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `mss_mono` at any seed `e`, step `P`, order `R`: `F(R)[e, ⊤e ∪ P] ⊑ [e, ⊤e ∪ P] R` when `e ⊑ e R` (the `zero` arm; `R`
    reflexive on `e`'s values) and `⟨π₁,π₂R⟩P ⊑ P R` (`plus` monotone). The `⊤e` arm discards its argument, so it is the
    seed arm again (`Tm.topSeed_den`). -/
theorem Tm.mssMono_den {D B : Obj} {e : Tm .one B} {P : Tm (.prod D B) B} {R : Tm B B} (ρ : Val)
    (he : e.den ρ ⊑ (Tm.comp e R).den ρ)
    (hP : (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr R)) P).den ρ ⊑ (Tm.comp P R).den ρ) :
    (Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr R))
        (Tm.join (Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e) P)))).den ρ ⊑
      (Tm.comp (Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv
        (Tm.join (Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e) P))) R).den ρ := by
  refine Tm.tex_fusion_condition_den ρ he ?_
  refine Core.Rel.le_iff.2 fun m b h => ?_
  obtain ⟨q, hq, hs⟩ := h
  rcases m with ⟨x, w⟩
  have hT := Tm.topSeed_rel (A := D.prod B) ρ e
  simp only [Tm.den] at hT hq hs ⊢
  rw [hT] at hs ⊢
  obtain ⟨q1, q2⟩ := q
  simp only [Core.Rel.rpair, Core.Rel.graph, Core.Rel.comp] at hq
  obtain ⟨rfl, y, rfl, hR⟩ := hq
  rcases hs with ⟨t, ht⟩ | hs
  · obtain ⟨c, hc, hRc⟩ := Core.Rel.le_iff.1 he t b ht
    exact ⟨c, Or.inl ⟨t, hc⟩, hRc⟩
  · obtain ⟨c, hc, hRc⟩ := Core.Rel.le_iff.1 hP (q1, y) b ⟨(q1, q2), by simpa [Tm.den, Core.Rel.rpair, Core.Rel.graph, Core.Rel.comp] using hR, hs⟩
    exact ⟨c, Or.inr hc, hRc⟩

/-- `mss_step` at any seed `e` (simple), step `S`, order `R`: `Λ([e,S]) est(R) = [e, Λ(S) est(R)]`. The `inl` arm is
    `estMap` (the extreme of the singleton `Λ(e)`), the `inr` arm is `Λ(S)` itself. -/
theorem Tm.mssStep_den {D B : Obj} {e : Tm .one B} {S : Tm (.prod D B) B} {R : Tm B B} (ρ : Val)
    (hs : (Tm.comp e.conv e).den ρ ⊑ (Tm.id (A := B)).den ρ) :
    (Tm.comp (Tm.lam (Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv S)))
      (.est (.dom (.meet .outr (.comp .outl R))))).den ρ =
    (Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv (Tm.comp (Tm.lam S)
      (.est (.dom (.meet .outr (.comp .outl R))))))).den ρ := by
  have hE := Tm.estMap_den ρ (f := e) (R := R) hs
  refine Core.Rel.ext fun a b => ?_
  rcases a with u | p
  · obtain rfl : u = () := rfl
    have hJ : ∀ b, (Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv S) : Tm (.sum .one (.prod D B)) B).den ρ
        (Sum.inl ()) b ↔ e.den ρ () b := fun b => by
      simp [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]
      first | exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩ | exact ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩
    have hl : ∀ ys, lamDen ((Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv S) : Tm (.sum .one (.prod D B)) B).den ρ)
        (Sum.inl ()) ys ↔ lamDen (e.den ρ) () ys := fun ys => by
      rw [lamDen_iff, lamDen_iff]; simp only [hJ]
    have hE' : (∃ ys, lamDen (e.den ρ) () ys ∧ (Tm.est (.dom (.meet .outr (.comp .outl R))) : Tm B.arr B).den ρ ys b) ↔
        e.den ρ () b := Iff.of_eq (congrFun (congrFun hE ()) b)
    refine Iff.trans (b := ∃ ys, lamDen (e.den ρ) () ys ∧ (Tm.est (.dom (.meet .outr (.comp .outl R))) : Tm B.arr B).den ρ ys b)
      (exists_congr fun ys => and_congr_left' (hl ys)) (hE'.trans ?_)
    simp [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]
    first | exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩ | exact ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩
  · have hJ : ∀ b, (Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv S) : Tm (.sum .one (.prod D B)) B).den ρ
        (Sum.inr p) b ↔ S.den ρ p b := fun b => by
      simp [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]
    have hr : ∀ ys, lamDen ((Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv S) : Tm (.sum .one (.prod D B)) B).den ρ)
        (Sum.inr p) ys ↔ lamDen (S.den ρ) p ys := fun ys => by
      rw [lamDen_iff, lamDen_iff]; simp only [hJ]
    refine Iff.trans (b := ∃ ys, lamDen (S.den ρ) p ys ∧ (Tm.est (.dom (.meet .outr (.comp .outl R))) : Tm B.arr B).den ρ ys b)
      (exists_congr fun ys => and_congr_left' (hr ys)) ?_
    simp [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]

/-- `prefAlg_comp_sum` for any `X` entire with `nil X = e` and `cons X = ⟨π₁,π₂X⟩P` (`sum`'s equations): the algebra
    `[nil, ⊤nil ∪ cons]` of `prefix` composed with `X` is `F(X)[e, ⊤e ∪ P]`. The `⊤` arm is the seed arm because `X` is entire. -/
theorem Tm.prefAlgCompSum_den {B L V : Obj} {N : Tm .one L} {C : Tm (.prod B L) L} {X : Tm L V} {e : Tm .one V}
    {P : Tm (.prod B V) V} (ρ : Val)
    (hN : (Tm.comp (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst) (Tm.comp N X)).den ρ = e.den ρ)
    (hC : (Tm.comp C X).den ρ = (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr X)) P).den ρ)
    (hX : (Tm.dom X).den ρ = (Tm.id (A := L)).den ρ) :
    (Tm.comp (Tm.join (Tm.comp Tm.inl.conv N) (Tm.comp Tm.inr.conv
        (Tm.join (Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) N) C))) X).den ρ =
      (Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr X))
        (Tm.join (Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e) P)))).den ρ := by
  have hT1 := Tm.topSeed_rel (A := .prod B L) ρ N
  have hT2 := Tm.topSeed_rel (A := .prod B V) ρ e
  have hU : ∀ a b : Obj.one.El, (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst : Tm .one .one).den ρ a b := fun a b => by
    simp only [Tm.den]
    exact ⟨⟨0, by simp⟩, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hNX : ∀ v, (∃ l, N.den ρ () l ∧ X.den ρ l v) ↔ e.den ρ () v := fun v => by
    have := congrFun (congrFun hN ()) v
    simp only [Tm.den, Core.Rel.comp] at this
    rw [← this]
    exact ⟨fun ⟨l, h1, h2⟩ => ⟨(), hU _ _, l, h1, h2⟩, fun ⟨_, _, l, h1, h2⟩ => ⟨l, h1, h2⟩⟩
  have hXe : ∀ l, ∃ y, X.den ρ l y := fun l => by
    have h : (Tm.dom X).den ρ l l := by rw [hX]; rfl
    rw [Tm.dom_den] at h
    obtain ⟨-, y, hy, -⟩ := h
    exact ⟨y, hy⟩
  have hCp : ∀ p v, (∃ l, C.den ρ p l ∧ X.den ρ l v) ↔ ∃ y, X.den ρ p.2 y ∧ P.den ρ (p.1, y) v := fun ⟨a, xs⟩ v => by
    have := congrFun (congrFun hC (a, xs)) v
    simp only [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph] at this
    dsimp only
    rw [this]
    constructor
    · rintro ⟨⟨a', y⟩, ⟨rfl, _, rfl, hy⟩, hP⟩
      exact ⟨y, hy, hP⟩
    · rintro ⟨y, hy, hP⟩
      exact ⟨(a, y), ⟨rfl, xs, rfl, hy⟩, hP⟩
  refine Core.Rel.ext fun a v => ?_
  rcases a with u | p
  · obtain rfl : u = () := rfl
    simp [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph, Core.Rel.top]
    constructor
    · rintro ⟨l, ⟨t, ht⟩, hx⟩
      obtain rfl : t = () := rfl
      exact ⟨(), (hNX v).1 ⟨l, ht, hx⟩⟩
    · rintro ⟨t, he⟩
      obtain rfl : t = () := rfl
      obtain ⟨l, h1, h2⟩ := (hNX v).2 he
      exact ⟨l, ⟨(), h1⟩, h2⟩
  · simp [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph, Core.Rel.top,
      Core.Rel.rpair]
    constructor
    · rintro ⟨l, (⟨E, t, ht⟩ | hc), hx⟩
      · obtain rfl : t = () := rfl
        obtain ⟨y, hy⟩ := hXe p.2
        exact ⟨p.1, y, ⟨rfl, hy⟩, Or.inl ⟨E, (), (hNX v).1 ⟨l, ht, hx⟩⟩⟩
      · obtain ⟨y, hy, hP⟩ := (hCp p v).1 ⟨l, hc, hx⟩
        exact ⟨p.1, y, ⟨rfl, hy⟩, Or.inr hP⟩
    · rintro ⟨a, y, ⟨rfl, hy⟩, (⟨E, t, he⟩ | hP)⟩
      · obtain rfl : t = () := rfl
        obtain ⟨l, h1, h2⟩ := (hNX v).2 he
        exact ⟨l, Or.inl ⟨E, (), h1⟩, h2⟩
      · obtain ⟨l, hc, hx⟩ := (hCp p v).2 ⟨y, hy, hP⟩
        exact ⟨l, Or.inr hc, hx⟩

/-- `cons_comp_sum` at the right fold `X = ⦇[e,P]⦈ʳ` (any seed `E`, step `P`): `cons X = ⟨π₁,π₂X⟩P`, the fold's equation on a
    `cons`. For the prelude's left-fold `sum` the two sides differ on overflow of the bounded sums. -/
theorem Tm.consCompSum_den {B V : Obj} {E : Tm V V} {P : Tm (.prod B V) V} (ρ : Val) :
    (Tm.comp (Tm.prim (rowOf "cons")) (Tm.foldr E P) : Tm (.prod B (.arr B)) V).den ρ =
      (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr (Tm.foldr E P))) P).den ρ := by
  refine Core.Rel.ext fun ⟨a, xs⟩ w => ?_
  simp only [Tm.den, Prim.den_cons, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
  constructor
  · rintro ⟨l, rfl, h⟩
    obtain ⟨u, hu, hs⟩ := (foldrDen_cons _ _ a xs w).1 h
    exact ⟨(a, u), ⟨rfl, xs, rfl, hu⟩, hs⟩
  · rintro ⟨⟨a', u⟩, ⟨rfl, xs', rfl, hu⟩, hs⟩
    exact ⟨a' :: xs', rfl, (foldrDen_cons _ _ a' xs' w).2 ⟨u, hu, hs⟩⟩

end Rel.Lang
