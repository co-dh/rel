import Rel.Lang.Laws.AopS2_10
import Rel.Lang.Laws.LamTotal
import Rel.Lang.Laws.AopA4_6
import Rel.Lang.Laws.AopA5_3
import Rel.Lang.Laws.AopA7_7_Filter
import Rel.Programs.Prelude
import Rel.Lang.PreludeLoop

/-! # List-combinator laws of freyd `AOP/A5_6_ListCombinators.lean`, on the concrete core

`Rel/Programs/Aop/A5_6_ListCombinators.lean` states each as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `Λ(R S) = Λ(R) E(S)`, `E(S) = Λ(∋ S)`: the image of the set `Λ(R)` under `S`, when `Λ(R)` has a set at every point
    (`dom(Λ(R)) = 𝟙`). `Tm.Ecomp_den` is the case `R = ∋ R'`. -/
theorem Tm.lamE_den {A B C : Obj} {R : Tm A B} {S : Tm B C} (ρ : Val)
    (h : (Tm.dom (.lam R)).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.lam (.comp R S)).den ρ = (Tm.comp (.lam R) (.lam (.comp .mem S))).den ρ :=
  (lamDen_absorb (R.den ρ) (S.den ρ) (Tm.entire_of_dom h)).symm

/-- `Λ(nil) = nil Λ(𝟙)`: `nil` is a map at every source, so `Tm.singleton_natural_den` needs no premise. -/
theorem Tm.lamNilSingleton_den {A B : Obj} (ρ : Val) :
    (Tm.comp (Tm.nil (A := A) (B := B)) (Tm.lam Tm.id)).den ρ = (Tm.lam (Tm.nil (A := A) (B := B))).den ρ :=
  Tm.singleton_natural_den ρ
    (Core.Rel.ext fun a b => by
      rw [Tm.dom_den]
      simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.id]
      exact ⟨fun h => h.1, fun h => by subst h; exact ⟨rfl, [], rfl, rfl⟩⟩)
    (Core.Rel.le_iff.2 fun a b h => by
      simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.graph, Core.Rel.id, Core.Rel.comp, Core.Rel.recip] at h ⊢
      obtain ⟨_, rfl, rfl⟩ := h; rfl)

/-- The same after any prefix `P` (the elaborator puts the closed source `uni(1)` in front of a closed `nil`). -/
theorem Tm.lamNilSingletonPre_den {D A B : Obj} {P : Tm D A} (ρ : Val) :
    (Tm.comp P (Tm.comp (Tm.nil (A := A) (B := B)) (Tm.lam Tm.id))).den ρ
      = (Tm.comp P (Tm.lam (Tm.nil (A := A) (B := B)))).den ρ := by
  have := Tm.lamNilSingleton_den (A := A) (B := B) ρ
  simp only [Tm.den] at this ⊢
  rw [this]

/-- Composition distributes over `∪` on the right. -/
theorem Tm.compJoin_den {A B C : Obj} {P : Tm A B} {S T : Tm B C} (ρ : Val) :
    (Tm.comp P (Tm.join S T)).den ρ = (Tm.join (Tm.comp P S) (Tm.comp P T)).den ρ := by
  simp only [Tm.den]
  exact Core.Rel.ext fun a c => ⟨fun ⟨b, hb, h⟩ => h.elim (fun h => Or.inl ⟨b, hb, h⟩) (fun h => Or.inr ⟨b, hb, h⟩),
    fun h => h.elim (fun ⟨b, hb, h⟩ => ⟨b, hb, Or.inl h⟩) (fun ⟨b, hb, h⟩ => ⟨b, hb, Or.inr h⟩)⟩

/-- `⟨π₁,S⟩ π₂ = S`: the first component is total. -/
theorem Tm.pairOutr_den {B C D : Obj} {S : Tm (.prod B C) D} (ρ : Val) :
    (Tm.comp (Tm.pair Tm.outl S) Tm.outr).den ρ = S.den ρ := by
  simp only [Tm.den]
  exact Core.Rel.ext fun a d => ⟨fun ⟨y, ⟨_, hy⟩, hd⟩ => by subst hd; exact hy, fun h => ⟨(a.1, d), ⟨rfl, h⟩, rfl⟩⟩

/-- `⟨π₁,S⟩ (U ∪ π₂) ∪`-slide: replacing the second operand `⟨π₁,S⟩ π₂` of a union by `S`. -/
theorem Tm.joinSlideOutr_den {B C D : Obj} {S : Tm (.prod B C) D} {U : Tm (.prod B C) D} (ρ : Val) :
    (Tm.join U (Tm.comp (Tm.pair Tm.outl S) Tm.outr)).den ρ = (Tm.join U S).den ρ := by
  have := Tm.pairOutr_den (S := S) ρ
  simp only [Tm.den] at this ⊢
  rw [this]

/-- `Λ(π₂ R) = π₂ Λ(R)`: the second projection is a map, so `Tm.lam_fusion_den` needs no premise. -/
theorem Tm.lamOutr_den {B C D : Obj} {R : Tm C D} (ρ : Val) :
    (Tm.lam (Tm.comp (Tm.outr (A := B) (B := C)) R)).den ρ = (Tm.comp Tm.outr (Tm.lam R)).den ρ :=
  Tm.lam_fusion_den ρ
    (Core.Rel.ext fun a b => by
      simp only [Tm.dom_den, Tm.den]
      exact ⟨fun h => h.1, fun h => by subst h; exact ⟨rfl, a.2, rfl, rfl⟩⟩)
    (Core.Rel.le_iff.2 fun a b h => by
      simp only [Tm.den, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, Core.Rel.id] at h ⊢
      obtain ⟨_, rfl, rfl⟩ := h; rfl)

/-- `Λ(⟨π₁,π₂ R⟩ π₂) = π₂ Λ(R)`: `⟨π₁,S⟩ π₂ = S`, then `Tm.lamOutr_den`. -/
theorem Tm.lamPairOutr_den {B C D : Obj} {R : Tm C D} (ρ : Val) :
    (Tm.lam (Tm.comp (Tm.pair (Tm.outl (A := B) (B := C)) (Tm.comp Tm.outr R)) Tm.outr)).den ρ
      = (Tm.comp Tm.outr (Tm.lam R)).den ρ := by
  have h := Tm.pairOutr_den (S := Tm.comp (Tm.outr (A := B) (B := C)) R) ρ
  have := Tm.lamOutr_den (B := B) (R := R) ρ
  simp only [Tm.den] at h this ⊢
  rw [h]; exact this

/-- `[R inl, S inr] [P, Q] = [R P, S Q]`: a sum map before a junction is the junction of the branches. -/
theorem Tm.sumMapJunc_den {A A' B B' C : Obj} {R : Tm A B} {S : Tm A' B'} {P : Tm B C} {Q : Tm B' C} (ρ : Val) :
    (Tm.comp (Tm.junc (Tm.comp R Tm.inl) (Tm.comp S Tm.inr)) (Tm.junc P Q)).den ρ
      = (Tm.junc (Tm.comp R P) (Tm.comp S Q)).den ρ := by
  rw [Tm.junc_comp_den]
  have h1 := Tm.u1_junc_den (R := P) (S := Q) ρ
  have h2 := Tm.u2_junc_den (R := P) (S := Q) ρ
  simp only [Tm.den, Core.Rel.comp_assoc] at h1 h2 ⊢
  rw [h1, h2]

/-- `Λ([𝟙 inl, X inr] [nil, S]) = [nil Λ(𝟙), Λ(X S)]`: `sumMapJunc`, `Λ` of a junction (`Tm.Λ_junc_den`) and
    `Λ(nil) = nil Λ(𝟙)` (`Tm.lamNilSingleton_den`). -/
theorem Tm.subseqAlgLam_den {C D E : Obj} {X : Tm C D} {S : Tm D (.arr E)} (ρ : Val) :
    (Tm.lam (Tm.comp (Tm.junc (Tm.comp Tm.id Tm.inl) (Tm.comp X Tm.inr))
        (Tm.junc (Tm.nil (A := .one) (B := E)) S))).den ρ
      = (Tm.junc (Tm.comp (Tm.nil (A := .one) (B := E)) (Tm.lam Tm.id)) (Tm.lam (Tm.comp X S))).den ρ := by
  have e := Tm.sumMapJunc_den (R := (Tm.id (A := .one))) (S := X) (P := (Tm.nil (A := .one) (B := E))) (Q := S) ρ
  have l := Tm.Λ_junc_den (R := Tm.comp (Tm.id (A := .one)) (Tm.nil (A := .one) (B := E))) (S := Tm.comp X S) ρ
  have hn : (Tm.lam (Tm.comp (Tm.id (A := .one)) (Tm.nil (A := .one) (B := E)))).den ρ
      = (Tm.comp (Tm.nil (A := .one) (B := E)) (Tm.lam Tm.id)).den ρ := by
    rw [Tm.lamNilSingleton_den]; simp only [Tm.den, Core.Rel.id_comp]
  change lamDen _ = _
  rw [e]
  change (Tm.lam (Tm.junc (Tm.comp (Tm.id (A := .one)) (Tm.nil (A := .one) (B := E))) (Tm.comp X S))).den ρ = _
  rw [l]
  change Core.Rel.junc _ _ = Core.Rel.junc _ _
  rw [hn]

/-- `[Λ(nil), U] = [nil Λ(𝟙), U]`: `Tm.lamNilSingleton_den` in the first arm of a junction. -/
theorem Tm.lamNilJunc_den {D E : Obj} {U : Tm D (.arr (.arr E))} (ρ : Val) :
    (Tm.junc (Tm.lam (Tm.nil (A := .one) (B := E))) U).den ρ
      = (Tm.junc (Tm.comp (Tm.nil (A := .one) (B := E)) (Tm.lam Tm.id)) U).den ρ := by
  have h := Tm.lamNilSingleton_den (A := .one) (B := E) ρ
  change Core.Rel.junc (Tm.den ρ (Tm.lam Tm.nil)) _ = Core.Rel.junc (Tm.den ρ (Tm.comp Tm.nil (Tm.lam Tm.id))) _
  rw [h]

/-- The right fold with step `x :: u ∨ u` from `[]` relates `xs` to its sublists: keep or drop each head. -/
theorem foldrDen_sublist {E : Obj} {Te : Core.Rel (Obj.El (.arr E)) (Obj.El (.arr E))}
    {TS : Core.Rel (Obj.El (.prod E (.arr E))) (Obj.El (.arr E))} (hTe : ∀ v, (∃ a, Te a v) ↔ v = [])
    (hS : ∀ x u v, TS (x, u) v ↔ v = x :: u ∨ v = u) (xs w : List E.El) : foldrDen Te TS xs w ↔ w.Sublist xs := by
  induction xs generalizing w with
  | nil => rw [foldrDen_empty, hTe]; exact List.sublist_nil.symm
  | cons x xs ih =>
    rw [foldrDen_cons]
    constructor
    · rintro ⟨u, hu, h⟩
      rcases (hS x u w).1 h with rfl | rfl
      · exact ((ih u).1 hu).cons₂ x
      · exact ((ih w).1 hu).cons x
    · intro hw
      rcases List.sublist_cons_iff.1 hw with h1 | ⟨r, hr, h2⟩
      · exact ⟨w, (ih w).2 h1, (hS x w w).2 (Or.inr rfl)⟩
      · subst hr
        exact ⟨r, (ih r).2 h2, (hS x r _).2 (Or.inl rfl)⟩

/-- The left fold with step `u ++ [x] ∨ u` from `[]` relates `xs` to its sublists. -/
theorem foldDen_sublist {E : Obj} {Te : Core.Rel (Obj.El (.arr E)) (Obj.El (.arr E))}
    {TS : Core.Rel (Obj.El (.prod (.arr E) E)) (Obj.El (.arr E))} (hTe : ∀ v, (∃ a, Te a v) ↔ v = [])
    (hS : ∀ u x v, TS (u, x) v ↔ v = u ++ [x] ∨ v = u) (xs w : List E.El) : foldDen Te TS xs w ↔ w.Sublist xs := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n := ⟨_, rfl⟩
  induction n generalizing xs w with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 hn
    rw [foldDen_empty, hTe]; exact List.sublist_nil.symm
  | succ n ih =>
    obtain ⟨L, x, rfl⟩ := (List.eq_nil_or_concat xs).resolve_left (by rintro rfl; simp at hn)
    rw [List.concat_eq_append] at *
    have hL : L.length = n := by simpa using hn
    rw [foldDen_snoc, List.sublist_append_iff]
    constructor
    · rintro ⟨u, hu, h⟩
      rcases (hS u x w).1 h with rfl | rfl
      · exact ⟨u, [x], rfl, (ih L u hL).1 hu, List.Sublist.refl _⟩
      · exact ⟨_, [], by simp, (ih L _ hL).1 hu, List.nil_sublist _⟩
    · rintro ⟨l₁, l₂, rfl, h₁, h₂⟩
      rcases List.sublist_cons_iff.1 h₂ with h3 | ⟨r, hr, h4⟩
      · obtain rfl := List.sublist_nil.1 h3
        exact ⟨l₁, (ih L l₁ hL).2 h₁, (hS l₁ x _).2 (Or.inr (by simp))⟩
      · obtain rfl := List.sublist_nil.1 h4
        subst hr
        exact ⟨l₁, (ih L l₁ hL).2 h₁, (hS l₁ x _).2 (Or.inl rfl)⟩

/-- The prelude's `subseq ≜ ⦇[nil, snoc ∪ π₁]⦈` as `Tm.den` reads it. -/
abbrev Tm.subseqSnoc (B : Obj) : Tm (.arr B) (.arr B) :=
  Tm.fold (Tm.ran (Tm.closedNil B)) (Tm.join (Tm.prim (rowOf "snoc")) Tm.outl)

theorem Tm.subseqSnoc_iff {B : Obj} (ρ : Val) (xs ys : List B.El) : (Tm.subseqSnoc B).den ρ xs ys ↔ ys.Sublist xs :=
  foldDen_sublist (filtRanNil ρ _ (Tm.closedNil_iff ρ))
    (fun u x v => by simp only [Tm.den, Prim.den_snoc, Core.Rel.union_apply, Core.Rel.graph]) xs ys

/-- **`subseq`'s text relates an array to its sublists** (`ys` is a sublist of `xs`): the body the prelude elaborates,
    `prelude.subseq.body`, at any objects `σ` (`Tm.instObj`). A law about a call of `subseq` takes
    `(ht : prelude.subseq.body.instObj [.general] [B] = .ok t' := by rfl)` and states the node `Tm.call ks c cv os t'`. -/
theorem Tm.subseqDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.atom .general).arr.inst ph σ) ((Obj.atom .general).arr.inst ph σ)}
    (ht : Rel.Programs.prelude.subseq.body.instObj ph σ = .ok t') (xs ys : Obj.El ((Obj.atom .general).inst ph σ).arr) :
    t'.den ρ xs ys ↔ ys.Sublist xs := by
  obtain rfl := Except.ok.inj ht
  exact Tm.subseqSnoc_iff ρ xs ys

/-- A left fold `loop(T)` whose step is a function `f` of the state and the element is `List.foldl f`. -/
theorem loopDen_foldl {X Y : Obj} {T : Core.Rel (Obj.El (.prod X Y)) (Obj.El X)} {f : X.El → Y.El → X.El}
    (hT : ∀ s y w, T (s, y) w ↔ w = f s y) (s : X.El) (l : List Y.El) (c : X.El) :
    loopDen T (s, l) c ↔ c = l.foldl f s := by
  rw [loopDen_iff]
  have tk : ∀ t (h : t < l.length), l.take (t + 1) = l.take t ++ [l[t]] := fun t h => by
    rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl
  have key : ∀ g : Nat → X.El, g 0 = s → (∀ t (ht : t < l.length), T (g t, l[t]'ht) (g (t + 1))) →
      ∀ t, t ≤ l.length → g t = (l.take t).foldl f s := by
    intro g h0 hg t
    induction t with
    | zero => intro _; simpa using h0
    | succ t ih =>
      intro ht
      rw [(hT _ _ _).1 (hg t (by omega)), ih (by omega), tk t (by omega), List.foldl_append]
      rfl
  constructor
  · rintro ⟨g, h0, hg, rfl⟩
    simpa using key g h0 hg _ (Nat.le_refl _)
  · rintro rfl
    refine ⟨fun t => (l.take t).foldl f s, by simp, fun t ht => (hT _ _ _).2 ?_, by simp⟩
    show List.foldl f s (l.take (t + 1)) = f (List.foldl f s (l.take t)) l[t]
    rw [tk t ht, List.foldl_append]
    rfl

/-- The step of `cpr`: `⟨π₁π₁, ⟨π₁π₂, ⟨π₁π₁, π₂⟩⟩snoc⟩` on `((a, acc), b)`. -/
def Tm.cprStep (A B : Obj) : Tm (.prod (.prod A (.arr (.prod A B))) B) (.prod A (.arr (.prod A B))) :=
  Tm.pair (Tm.comp Tm.outl Tm.outl)
    (Tm.comp (Tm.pair (Tm.comp Tm.outl Tm.outr) (Tm.pair (Tm.comp Tm.outl Tm.outl) Tm.outr)) (Tm.prim (rowOf "snoc")))

/-- `cpr ≜ ⟨⟨π₁, nil⟩, π₂⟩ loop(step) π₂` as the program elaborates it. -/
def Tm.cprTm (A B : Obj) : Tm (.prod A (.arr B)) (.arr (.prod A B)) :=
  (((Tm.pair Tm.outl (Tm.nil : Tm (.prod A (.arr B)) (.arr (.prod A B))) :
      Tm (.prod A (.arr B)) (.prod A (.arr (.prod A B)))).pair Tm.outr).comp
    ((Tm.prim (rowOf "loop") : Tm (.prod (.prod A (.arr (.prod A B))) (.arr B)) (.prod A (.arr (.prod A B)))).arg
      (Tm.cprStep A B))).comp Tm.outr

theorem Tm.cprTm_iff {A B : Obj} (ρ : Val) (a : A.El) (ys : List B.El) (l : List (Obj.prod A B).El) :
    (Tm.cprTm A B).den ρ (a, ys) l ↔ l = ys.map fun b => (a, b) := by
  have hT : ∀ s y w, (Tm.cprStep A B).den ρ (s, y) w ↔ w = (s.1, s.2 ++ [(s.1, y)]) := by
    rintro ⟨a, acc⟩ y w
    simp only [Tm.cprStep, Tm.den, Prim.den_snoc, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
    obtain ⟨w1, w2⟩ := w
    simp [Prod.ext_iff, eq_comm]
    intro h
    subst h
    constructor
    · rintro ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h⟩
      exact h
    · intro h
      exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h⟩
  have hl := fun s l c => loopDen_foldl (T := (Tm.cprStep A B).den ρ) (f := fun s y => (s.1, s.2 ++ [(s.1, y)])) hT s l c
  simp only [Tm.cprTm, Tm.cprStep, Tm.den, Tm.argDen, Prim.den_loopRow, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.comp,
    Core.Rel.rpair, Core.Rel.graph] at hl ⊢
  have hf : ∀ (acc : List (A.prod B).El) (zs : List B.El),
      zs.foldl (fun s y => (s.1, s.2 ++ [(s.1, y)])) (a, acc) = (a, acc ++ zs.map fun b => (a, b)) := by
    intro acc zs
    induction zs generalizing acc with
    | nil => simp
    | cons z zs ih => simp [List.foldl, ih]
  constructor
  · rintro ⟨b, ⟨⟨⟨u, v⟩, z⟩, ⟨⟨h1, h2⟩, h3⟩, b2, hX, rfl⟩, rfl⟩
    simp only at h1 h2 h3
    subst u v z
    have := (hl (a, []) ys b2.snd).1 ⟨b2, hX, rfl⟩
    rw [hf] at this
    rw [this]
    simp
  · rintro rfl
    obtain ⟨b2, hX, hb⟩ := (hl (a, []) ys (a, [] ++ ys.map fun b => (a, b))).2 (by rw [hf])
    exact ⟨(a, [] ++ ys.map fun b => (a, b)), ⟨((a, []), ys), ⟨⟨rfl, rfl⟩, rfl⟩, b2, hX, hb⟩, by simp⟩

/-- **`cpr setify = (𝟙×setify) 𝟙×∋%∋`** at `Λ(∋)`. -/
theorem Tm.setifyCpr_den {A B : Obj} (ρ : Val) :
    (Tm.comp (Tm.cprTm A B) (Tm.lam Tm.mem)).den ρ =
      (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr (Tm.lam Tm.mem)))
        (Tm.lam (Tm.pair Tm.outl (Tm.comp Tm.outr Tm.mem)))).den ρ := by
  refine Core.Rel.ext fun ⟨a, ys⟩ s => ?_
  change (∃ l, (Tm.cprTm A B).den ρ (a, ys) l ∧ (Tm.lam (Tm.mem : Tm (.arr (.prod A B)) (.prod A B))).den ρ l s) ↔
    ∃ p, (Tm.pair Tm.outl (Tm.comp Tm.outr (Tm.lam (Tm.mem : Tm (.arr B) B))) : Tm (.prod A (.arr B)) (.prod A (.arr B))).den ρ (a, ys) p ∧
      (Tm.lam (Tm.pair Tm.outl (Tm.comp Tm.outr Tm.mem) : Tm (.prod A (.arr B)) (.prod A B))).den ρ p s
  refine (exists_congr fun l => and_congr_left' (Tm.cprTm_iff ρ a ys l)).trans ?_
  simp only [exists_eq_left]
  simp only [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, lamDen_iff]
  have hm : ∀ {C : Obj} (l : List C.El) (b : C.El), memDen l b ↔ b ∈ l := fun _ _ => Iff.rfl
  simp only [hm, List.mem_map]
  constructor
  · rintro ⟨hp, hs⟩
    have h1 : ∀ q ∈ s, q.1 = a := fun q hq => by
      obtain ⟨b, -, rfl⟩ := (hs q).1 hq
      rfl
    refine ⟨(a, s.map Prod.snd), ⟨rfl, ys, rfl, ?_, ?_⟩, hp, fun ⟨q1, q2⟩ => ?_⟩
    · refine List.pairwise_map.2 (hp.imp_of_mem fun {x y} hx hy hxy => ?_)
      obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      have e1 : x1 = a := h1 _ hx
      have e2 : y1 = a := h1 _ hy
      subst e1 e2
      rcases (Obj.lt_prod A B _ _ _ _).1 hxy with h | ⟨-, h⟩
      · exact absurd h (Obj.lt_irrefl _ _)
      · exact h
    · intro b
      simp only [List.mem_map]
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨b', hb', rfl⟩ := (hs q).1 hq
        exact hb'
      · intro hb
        exact ⟨(a, b), (hs _).2 ⟨b, hb, rfl⟩, rfl⟩
    · refine (hs (q1, q2)).trans ?_
      constructor
      · rintro ⟨b, hb, h⟩
        have e := Prod.mk.inj h
        refine ⟨e.1.symm, _, rfl, ?_⟩
        show q2 ∈ s.map Prod.snd
        exact List.mem_map.2 ⟨(a, b), (hs _).2 ⟨b, hb, rfl⟩, e.2⟩
      · rintro ⟨h1', _, rfl, hq⟩
        obtain ⟨r, hr, hr2⟩ := List.mem_map.1 (show q2 ∈ s.map Prod.snd from hq)
        obtain ⟨b, hb, hbr⟩ := (hs r).1 hr
        refine ⟨q2, ?_, Prod.ext h1'.symm rfl⟩
        rw [← hr2, ← hbr]
        exact hb
  · rintro ⟨p, ⟨hp1, t, rfl, hpw, hmem⟩, hs1, hs2⟩
    refine ⟨hs1, fun q => (hs2 q).trans ?_⟩
    obtain ⟨q1, q2⟩ := q
    constructor
    · rintro ⟨h1', _, rfl, hq⟩
      exact ⟨q2, (hmem _).1 hq, Prod.ext (h1'.trans hp1).symm rfl⟩
    · rintro ⟨b, hb, h⟩
      have e := Prod.mk.inj h
      exact ⟨e.1.symm.trans hp1.symm, _, rfl, e.2 ▸ (hmem _).2 hb⟩

/-- The step of `cpl`: `⟨π₁π₁, ⟨π₁π₂, ⟨π₂, π₁π₁⟩⟩snoc⟩` on `((b, acc), a)`. -/
def Tm.cplStep (A B : Obj) : Tm (.prod (.prod B (.arr (.prod A B))) A) (.prod B (.arr (.prod A B))) :=
  Tm.pair (Tm.comp Tm.outl Tm.outl)
    (Tm.comp (Tm.pair (Tm.comp Tm.outl Tm.outr) (Tm.pair Tm.outr (Tm.comp Tm.outl Tm.outl))) (Tm.prim (rowOf "snoc")))

/-- `cpl ≜ ⟨⟨π₂, nil⟩, π₁⟩ loop(step) π₂` as the program elaborates it. -/
def Tm.cplTm (A B : Obj) : Tm (.prod (.arr A) B) (.arr (.prod A B)) :=
  (((Tm.pair Tm.outr (Tm.nil : Tm (.prod (.arr A) B) (.arr (.prod A B))) :
      Tm (.prod (.arr A) B) (.prod B (.arr (.prod A B)))).pair Tm.outl).comp
    ((Tm.prim (rowOf "loop") : Tm (.prod (.prod B (.arr (.prod A B))) (.arr A)) (.prod B (.arr (.prod A B)))).arg
      (Tm.cplStep A B))).comp Tm.outr

theorem Tm.cplTm_iff {A B : Obj} (ρ : Val) (xs : List A.El) (b : B.El) (l : List (Obj.prod A B).El) :
    (Tm.cplTm A B).den ρ (xs, b) l ↔ l = xs.map fun a => (a, b) := by
  have hT : ∀ s y w, (Tm.cplStep A B).den ρ (s, y) w ↔ w = (s.1, s.2 ++ [(y, s.1)]) := by
    rintro ⟨b, acc⟩ y w
    simp only [Tm.cplStep, Tm.den, Prim.den_snoc, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
    obtain ⟨w1, w2⟩ := w
    simp [Prod.ext_iff, eq_comm]
    intro h
    subst h
    constructor
    · rintro ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h⟩
      exact h
    · intro h
      exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h⟩
  have hl := fun s l c => loopDen_foldl (T := (Tm.cplStep A B).den ρ) (f := fun s y => (s.1, s.2 ++ [(y, s.1)])) hT s l c
  simp only [Tm.cplTm, Tm.cplStep, Tm.den, Tm.argDen, Prim.den_loopRow, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.comp,
    Core.Rel.rpair, Core.Rel.graph] at hl ⊢
  have hf : ∀ (acc : List (A.prod B).El) (zs : List A.El),
      zs.foldl (fun s y => (s.1, s.2 ++ [(y, s.1)])) (b, acc) = (b, acc ++ zs.map fun a => (a, b)) := by
    intro acc zs
    induction zs generalizing acc with
    | nil => simp
    | cons z zs ih => simp [List.foldl, ih]
  constructor
  · rintro ⟨b', ⟨⟨⟨u, v⟩, z⟩, ⟨⟨h1, h2⟩, h3⟩, b2, hX, rfl⟩, rfl⟩
    simp only at h1 h2 h3
    subst u v z
    have := (hl (b, []) xs b2.snd).1 ⟨b2, hX, rfl⟩
    rw [hf] at this
    rw [this]
    simp
  · rintro rfl
    obtain ⟨b2, hX, hb⟩ := (hl (b, []) xs (b, [] ++ xs.map fun a => (a, b))).2 (by rw [hf])
    exact ⟨(b, [] ++ xs.map fun a => (a, b)), ⟨((b, []), xs), ⟨⟨rfl, rfl⟩, rfl⟩, b2, hX, hb⟩, by simp⟩

/-- **`cpl setify = (setify×𝟙) ∋×𝟙%∋`** at `Λ(∋)`. -/
theorem Tm.setifyCpl_den {A B : Obj} (ρ : Val) :
    (Tm.comp (Tm.cplTm A B) (Tm.lam Tm.mem)).den ρ =
      (Tm.comp (Tm.pair (Tm.comp Tm.outl (Tm.lam Tm.mem)) Tm.outr)
        (Tm.lam (Tm.pair (Tm.comp Tm.outl Tm.mem) Tm.outr))).den ρ := by
  refine Core.Rel.ext fun ⟨xs, b⟩ s => ?_
  change (∃ l, (Tm.cplTm A B).den ρ (xs, b) l ∧ (Tm.lam (Tm.mem : Tm (.arr (.prod A B)) (.prod A B))).den ρ l s) ↔
    ∃ p, (Tm.pair (Tm.comp Tm.outl (Tm.lam (Tm.mem : Tm (.arr A) A))) Tm.outr : Tm (.prod (.arr A) B) (.prod (.arr A) B)).den ρ (xs, b) p ∧
      (Tm.lam (Tm.pair (Tm.comp Tm.outl Tm.mem) Tm.outr : Tm (.prod (.arr A) B) (.prod A B))).den ρ p s
  refine (exists_congr fun l => and_congr_left' (Tm.cplTm_iff ρ xs b l)).trans ?_
  simp only [exists_eq_left]
  simp only [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, lamDen_iff]
  have hm : ∀ {C : Obj} (l : List C.El) (b : C.El), memDen l b ↔ b ∈ l := fun _ _ => Iff.rfl
  simp only [hm, List.mem_map]
  constructor
  · rintro ⟨hp, hs⟩
    have h1 : ∀ q ∈ s, q.2 = b := fun q hq => by
      obtain ⟨a', -, rfl⟩ := (hs q).1 hq
      rfl
    refine ⟨(s.map Prod.fst, b), ⟨⟨xs, rfl, ?_, ?_⟩, rfl⟩, hp, fun ⟨q1, q2⟩ => ?_⟩
    · refine List.pairwise_map.2 (hp.imp_of_mem fun {x y} hx hy hxy => ?_)
      obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      have e1 : x2 = b := h1 _ hx
      have e2 : y2 = b := h1 _ hy
      subst e1 e2
      rcases (Obj.lt_prod A B _ _ _ _).1 hxy with h | ⟨-, h⟩
      · exact h
      · exact absurd h (Obj.lt_irrefl _ _)
    · intro a'
      simp only [List.mem_map]
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨a'', ha, rfl⟩ := (hs q).1 hq
        exact ha
      · intro ha
        exact ⟨(a', b), (hs _).2 ⟨a', ha, rfl⟩, rfl⟩
    · refine (hs (q1, q2)).trans ?_
      constructor
      · rintro ⟨a', ha, h⟩
        have e := Prod.mk.inj h
        refine ⟨⟨_, rfl, ?_⟩, e.2.symm⟩
        show q1 ∈ s.map Prod.fst
        exact List.mem_map.2 ⟨(a', b), (hs _).2 ⟨a', ha, rfl⟩, e.1⟩
      · rintro ⟨⟨_, rfl, hq⟩, h2⟩
        obtain ⟨r, hr, hr2⟩ := List.mem_map.1 (show q1 ∈ s.map Prod.fst from hq)
        obtain ⟨a', ha, hbr⟩ := (hs r).1 hr
        refine ⟨q1, ?_, Prod.ext rfl h2.symm⟩
        rw [← hr2, ← hbr]
        exact ha
  · rintro ⟨p, ⟨⟨_, rfl, hpw, hmem⟩, hp2⟩, hs1, hs2⟩
    refine ⟨hs1, fun q => (hs2 q).trans ?_⟩
    obtain ⟨q1, q2⟩ := q
    constructor
    · rintro ⟨⟨_, rfl, hq⟩, h2⟩
      exact ⟨q1, (hmem _).1 hq, Prod.ext rfl (h2.trans hp2).symm⟩
    · rintro ⟨a', ha, h⟩
      have e := Prod.mk.inj h
      exact ⟨⟨_, rfl, e.1 ▸ (hmem _).2 ha⟩, e.2.symm.trans hp2.symm⟩

/-- The step of `cpp`: `⟨π₁π₁, ⟨π₁π₂, ⟨π₂, π₁π₁⟩cpr⟩cat⟩` on `((y, acc), a)`. -/
def Tm.cppStep (A B : Obj) : Tm (.prod (.prod (.arr B) (.arr (.prod A B))) A) (.prod (.arr B) (.arr (.prod A B))) :=
  Tm.pair (Tm.comp Tm.outl Tm.outl)
    (Tm.comp (Tm.pair (Tm.comp Tm.outl Tm.outr) (Tm.comp (Tm.pair Tm.outr (Tm.comp Tm.outl Tm.outl)) (Tm.cprTm A B)))
      (Tm.prim (rowOf "cat")))

/-- `cpp ≜ ⟨⟨π₂, nil⟩, π₁⟩ loop(step) π₂` as the program elaborates it. -/
def Tm.cppTm (A B : Obj) : Tm (.prod (.arr A) (.arr B)) (.arr (.prod A B)) :=
  (((Tm.pair Tm.outr (Tm.nil : Tm (.prod (.arr A) (.arr B)) (.arr (.prod A B))) :
      Tm (.prod (.arr A) (.arr B)) (.prod (.arr B) (.arr (.prod A B)))).pair Tm.outl).comp
    ((Tm.prim (rowOf "loop") : Tm (.prod (.prod (.arr B) (.arr (.prod A B))) (.arr A))
        (.prod (.arr B) (.arr (.prod A B)))).arg (Tm.cppStep A B))).comp Tm.outr

theorem Tm.cppTm_iff {A B : Obj} (ρ : Val) (xs : List A.El) (ys : List B.El) (l : List (Obj.prod A B).El) :
    (Tm.cppTm A B).den ρ (xs, ys) l ↔ l = xs.flatMap fun a => ys.map fun b => (a, b) := by
  have hT : ∀ s y w, (Tm.cppStep A B).den ρ (s, y) w ↔ w = (s.1, s.2 ++ s.1.map fun b => (y, b)) := by
    rintro ⟨ys', acc⟩ a w
    simp only [Tm.cppStep, Tm.den, Prim.den_cat, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
    obtain ⟨w1, w2⟩ := w
    simp [Prod.ext_iff, eq_comm]
    intro h
    subst h
    constructor
    · rintro ⟨_, b, ⟨rfl, _, _, ⟨rfl, rfl⟩, hb⟩, rfl⟩
      rw [(Tm.cprTm_iff ρ _ _ _).1 hb]
    · rintro rfl
      exact ⟨_, _, ⟨rfl, _, _, ⟨rfl, rfl⟩, (Tm.cprTm_iff ρ _ _ _).2 rfl⟩, rfl⟩
  have hl := fun s l c => loopDen_foldl (T := (Tm.cppStep A B).den ρ)
    (f := fun s y => (s.1, s.2 ++ s.1.map fun b => (y, b))) hT s l c
  simp only [Tm.cppTm, Tm.cppStep, Tm.den, Tm.argDen, Prim.den_loopRow, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.comp,
    Core.Rel.rpair, Core.Rel.graph] at hl ⊢
  have hf : ∀ (acc : List (A.prod B).El) (zs : List A.El),
      zs.foldl (fun s y => (s.1, s.2 ++ s.1.map fun b => (y, b))) (ys, acc) =
        (ys, acc ++ zs.flatMap fun a => ys.map fun b => (a, b)) := by
    intro acc zs
    induction zs generalizing acc with
    | nil => simp
    | cons z zs ih => simp [List.foldl, ih, List.append_assoc]
  constructor
  · rintro ⟨b', ⟨⟨⟨u, v⟩, z⟩, ⟨⟨h1, h2⟩, h3⟩, b2, hX, rfl⟩, rfl⟩
    simp only at h1 h2 h3
    subst u v z
    have := (hl (ys, []) xs b2.snd).1 ⟨b2, hX, rfl⟩
    rw [hf] at this
    rw [this]
    simp
  · rintro rfl
    obtain ⟨b2, hX, hb⟩ := (hl (ys, []) xs (ys, [] ++ xs.flatMap fun a => ys.map fun b => (a, b))).2 (by rw [hf])
    exact ⟨(ys, [] ++ xs.flatMap fun a => ys.map fun b => (a, b)), ⟨((ys, []), xs), ⟨⟨rfl, rfl⟩, rfl⟩, b2, hX, hb⟩,
      by simp⟩

/-- **`cpp setify = (setify×setify) ∋×∋%∋`** at `Λ(∋)`, `U`, `V` the two `Λ(∋)` with a set at every point
    (`Λ(∋)` has none where two elements of a general atom type tie in `Obj.lt`, so the empty list on one side
    does not give a set for the other). -/
theorem Tm.setifyCpp_den {A B : Obj} {U : Tm (.arr A) (.arr A)} {V : Tm (.arr B) (.arr B)} (ρ : Val)
    (hU : U.den ρ = (Tm.lam Tm.mem).den ρ) (hV : V.den ρ = (Tm.lam Tm.mem).den ρ)
    (hdU : (Tm.dom U).den ρ = (Tm.id (A := .arr A)).den ρ) (hdV : (Tm.dom V).den ρ = (Tm.id (A := .arr B)).den ρ) :
    (Tm.comp (Tm.cppTm A B) (Tm.lam Tm.mem)).den ρ =
      (Tm.comp (Tm.pair (Tm.comp Tm.outl U) (Tm.comp Tm.outr V))
        (Tm.lam (Tm.pair (Tm.comp Tm.outl Tm.mem) (Tm.comp Tm.outr Tm.mem)))).den ρ := by
  have tU := Tm.entire_of_dom hdU
  have tV := Tm.entire_of_dom hdV
  refine Core.Rel.ext fun ⟨xs, ys⟩ s => ?_
  change (∃ l, (Tm.cppTm A B).den ρ (xs, ys) l ∧ (Tm.lam (Tm.mem : Tm (.arr (.prod A B)) (.prod A B))).den ρ l s) ↔
    ∃ p, (Tm.pair (Tm.comp Tm.outl U) (Tm.comp Tm.outr V) : Tm (.prod (.arr A) (.arr B)) (.prod (.arr A) (.arr B))).den ρ
        (xs, ys) p ∧
      (Tm.lam (Tm.pair (Tm.comp Tm.outl Tm.mem) (Tm.comp Tm.outr Tm.mem) :
        Tm (.prod (.arr A) (.arr B)) (.prod A B))).den ρ p s
  refine (exists_congr fun l => and_congr_left' (Tm.cppTm_iff ρ xs ys l)).trans ?_
  simp only [exists_eq_left]
  simp only [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, lamDen_iff, hU, hV]
  have hm : ∀ {C : Obj} (l : List C.El) (b : C.El), memDen l b ↔ b ∈ l := fun _ _ => Iff.rfl
  simp only [hm, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨hp, hs⟩
    obtain ⟨t, ht⟩ := tU xs
    obtain ⟨u, hu⟩ := tV ys
    rw [hU] at ht
    rw [hV] at hu
    simp only [Tm.den, lamDen_iff, hm] at ht hu
    refine ⟨(t, u), ⟨⟨xs, rfl, ht⟩, ys, rfl, hu⟩, hp, fun q => (hs q).trans ?_⟩
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨⟨_, rfl, (ht.2 _).2 ha⟩, _, rfl, (hu.2 _).2 hb⟩
    · rintro ⟨⟨_, rfl, h1⟩, _, rfl, h2⟩
      exact ⟨q.1, (ht.2 _).1 h1, q.2, (hu.2 _).1 h2, rfl⟩
  · rintro ⟨⟨t, u⟩, ⟨⟨_, rfl, htp, ht⟩, _, rfl, hup, hu⟩, hs1, hs2⟩
    refine ⟨hs1, fun q => (hs2 q).trans ?_⟩
    constructor
    · rintro ⟨⟨_, rfl, h1⟩, _, rfl, h2⟩
      exact ⟨q.1, (ht _).1 h1, q.2, (hu _).1 h2, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨⟨_, rfl, (ht _).2 ha⟩, _, rfl, (hu _).2 hb⟩

/-- **`subseq = ⦇[nil, cons ∪ π₂]⦈ʳ`** (`subseq_cata`): the prelude's snoc fold and the cons fold both relate an array
    to its sublists. -/
theorem Tm.subseqCata_den {B : Obj} {t' : Tm (.arr B) (.arr B)}
    (ht : Rel.Programs.prelude.subseq.body.instObj [.general] [B] = .ok t' := by rfl) (ρ : Val) :
    Tm.den ρ (Tm.call [] `Rel.Programs.prelude.subseq (some `Rel.Programs.prelude.subseq.conv) [B] t') =
      Tm.den ρ (Tm.subseqC B) := by
  apply Core.Rel.ext
  intro xs ys
  refine (Tm.subseqDef_den [.general] [B] _ ht xs ys).trans ?_
  exact (foldrDen_sublist (filtRanNil ρ _ (Tm.closedNil_iff ρ)) (fun x u v => Tm.subseqStep_iff ρ x u v) xs ys).symm

end Rel.Lang
