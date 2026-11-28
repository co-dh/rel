import Rel.Lang.Laws.Cylinder

/-! # B&dM §1.7 (1.7): `zip` is natural

`⟨F(R), F(S)⟩ zip = F(⟨R,S⟩)`: `F(R)` and `F(S)` keep the length, so the truncation of the row `zip` never acts, and
`zip` of the two images is the image of the pair. The row `zip` is `Prim.den_zip` (Laws/Cylinder). -/

namespace Rel.Lang
open Rel.Lang

/-- `⟨F(R), F(S)⟩ zip = F(⟨R,S⟩)` as the program elaborates it. -/
theorem Tm.zipNatural_den {X A B : Obj} (ρ : Val) :
    Tm.den ρ (((Tm.prim mapRow : Tm (.arr X) (.arr A)).arg (Tm.var 0 : Tm X A)).pair
        ((Tm.prim mapRow : Tm (.arr X) (.arr B)).arg (Tm.var 1 : Tm X B))
      |>.comp (Tm.prim (rowOf "zip") : Tm (.prod (.arr A) (.arr B)) (.arr (.prod A B)))) =
    Tm.den ρ ((Tm.prim mapRow : Tm (.arr X) (.arr (.prod A B))).arg
      ((Tm.var 0 : Tm X A).pair (Tm.var 1 : Tm X B))) := by
  funext xs zs; apply propext
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Prim.den_zip, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
  constructor
  · rintro ⟨⟨ys, ws⟩, ⟨h1, h2⟩, rfl⟩
    obtain ⟨l1, g1⟩ := (mapDen_iff _ _ _).1 h1
    obtain ⟨l2, g2⟩ := (mapDen_iff _ _ _).1 h2
    refine (mapDen_iff _ _ _).2 ⟨by simp [l1, l2], fun t ht ht' => ?_⟩
    simp only [List.getElem_zip]
    exact ⟨g1 t ht (by omega), g2 t ht (by omega)⟩
  · intro h
    obtain ⟨l, g⟩ := (mapDen_iff _ _ _).1 h
    refine ⟨⟨zs.map Prod.fst, zs.map Prod.snd⟩, ⟨(mapDen_iff _ _ _).2 ⟨by simp [l], fun t ht ht' => ?_⟩,
      (mapDen_iff _ _ _).2 ⟨by simp [l], fun t ht ht' => ?_⟩⟩, by simpa [List.unzip_eq_map] using (List.zip_unzip zs).symm⟩
    · simpa using (g t ht (by omega)).1
    · simpa using (g t ht (by omega)).2

open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- freyd's conditional filter `F((K, D → τ, nil)) concat` on lists: at each element `x`, keep it where `K x`, drop it
    where `D x`; both where both hold (a relational test), neither where neither holds (no image). -/
def cfiltL {α : Type} (K D : α → Prop) : List α → List α → Prop
  | [], ys => ys = []
  | x :: xs, ys => (K x ∧ ∃ ys', ys = x :: ys' ∧ cfiltL K D xs ys') ∨ (D x ∧ cfiltL K D xs ys)

/-- The step `dom(π₁K)cons ∪ (dom(π₁D)π₂)` of `cfilter(K, D)`, its parameters the variables `k`, `d`. -/
abbrev Tm.cfilterStep (E C : Obj) (k d : Nat) : Tm (.prod E (.arr E)) (.arr E) :=
  ((Tm.dom (Tm.outl.comp (Tm.var k : Tm E C))).comp (Tm.prim (rowOf "cons"))).join
    ((Tm.dom (Tm.outl.comp (Tm.var d : Tm E C))).comp Tm.outr)

/-- `cfilter(K, D) ≜ ⦇[nil, dom(π₁K)cons ∪ (dom(π₁D)π₂)]⦈ʳ` as the program elaborates its body. -/
abbrev Tm.cfilterBody (E C : Obj) (k d : Nat) : Tm (.arr E) (.arr E) :=
  Tm.foldr (Tm.ran (Tm.closedNil E)) (Tm.cfilterStep E C k d)

theorem Tm.cfilterStep_iff {E C : Obj} (ρ : Val) (k d : Nat) (x : E.El) (u w : List E.El) :
    (Tm.cfilterStep E C k d).den ρ (x, u) w ↔ ((∃ c, ρ k E C x c) ∧ w = x :: u) ∨ ((∃ c, ρ d E C x c) ∧ w = u) := by
  simp only [Tm.den, Tm.dom_den, Prim.den_cons, Core.Rel.union_apply, Core.Rel.comp_apply,
    Core.Rel.inter_apply, Core.Rel.id, Core.Rel.recip, Core.Rel.graph, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro (⟨a, b, ⟨⟨rfl, rfl⟩, c, ⟨_, rfl, h⟩, -⟩, rfl⟩ | ⟨a, b, ⟨⟨rfl, rfl⟩, c, ⟨_, rfl, h⟩, -⟩, rfl⟩)
    · exact Or.inl ⟨⟨c, h⟩, rfl⟩
    · exact Or.inr ⟨⟨c, h⟩, rfl⟩
  · rintro (⟨⟨c, h⟩, rfl⟩ | ⟨⟨c, h⟩, rfl⟩)
    · exact Or.inl ⟨x, u, ⟨⟨rfl, rfl⟩, c, ⟨x, rfl, h⟩, x, rfl, h⟩, rfl⟩
    · exact Or.inr ⟨x, _, ⟨⟨rfl, rfl⟩, c, ⟨x, rfl, h⟩, x, rfl, h⟩, rfl⟩

/-- `cfilter(K, D)`'s body is `cfiltL` at `dom(K)`, `dom(D)`, read under `ρ`. -/
theorem Tm.cfilterBody_iff {E C : Obj} (ρ : Val) (k d : Nat) :
    ∀ xs ys : List E.El, (Tm.cfilterBody E C k d).den ρ xs ys ↔
      cfiltL (fun x => ∃ c, ρ k E C x c) (fun x => ∃ c, ρ d E C x c) xs ys
  | [], ys => by
    show foldrDen (E := E) (V := .arr E) _ _ [] ys ↔ _
    rw [foldrDen_empty]
    simp [cfiltL, Tm.ran_den, Tm.closedNil_den, nilDen, Core.Rel.inter_apply, Core.Rel.id, Core.Rel.comp_apply,
      Core.Rel.recip, Core.Rel.graph]
  | x :: xs, ys => by
    show foldrDen (E := E) (V := .arr E) _ _ (x :: xs) ys ↔ _
    rw [foldrDen_cons]
    simp only [cfiltL]
    constructor
    · rintro ⟨u, hu, hS⟩
      rcases (Tm.cfilterStep_iff ρ k d x u ys).1 hS with ⟨hk, rfl⟩ | ⟨hd, rfl⟩
      · exact Or.inl ⟨hk, u, rfl, (Tm.cfilterBody_iff ρ k d xs u).1 hu⟩
      · exact Or.inr ⟨hd, (Tm.cfilterBody_iff ρ k d xs ys).1 hu⟩
    · rintro (⟨hk, u, rfl, hu⟩ | ⟨hd, hu⟩)
      · exact ⟨u, (Tm.cfilterBody_iff ρ k d xs u).2 hu, (Tm.cfilterStep_iff ρ k d x u _).2 (Or.inl ⟨hk, rfl⟩)⟩
      · exact ⟨ys, (Tm.cfilterBody_iff ρ k d xs ys).2 hu, (Tm.cfilterStep_iff ρ k d x ys ys).2 (Or.inr ⟨hd, rfl⟩)⟩

/-- A call of the program's `cfilter` given `X`, `Y`: `cfiltL` at `dom(X)`, `dom(Y)`. -/
theorem Tm.cfilterCall_iff {E C : Obj} {k d : Nat} {c : Lean.Name} {cv : Option Lean.Name} {os : List Obj}
    (hkd : k ≠ d) (ρ : Val) (X Y : Tm E C) (xs ys : List E.El) :
    (((Tm.call [k, d] c cv os (Tm.cfilterBody E C k d)).arg X).arg Y).den ρ xs ys ↔
      cfiltL (fun x => ∃ c, X.den ρ x c) (fun x => ∃ c, Y.den ρ x c) xs ys := by
  have hk : Val.args [k, d] [⟨_, _, X.den ρ⟩, ⟨_, _, Y.den ρ⟩] k E C = X.den ρ := Val.bind_apply _ _ _ rfl rfl
  have hd : Val.args [k, d] [⟨_, _, X.den ρ⟩, ⟨_, _, Y.den ρ⟩] d E C = Y.den ρ := by
    show ((Val.args [d] [⟨_, _, Y.den ρ⟩]).bind k (X.den ρ)) d E C = _
    rw [Val.bind_ne hkd.symm]; exact Val.bind_apply _ _ _ rfl rfl
  show (Tm.cfilterBody E C k d).den (Val.args [k, d] [⟨_, _, X.den ρ⟩, ⟨_, _, Y.den ρ⟩]) xs ys ↔ _
  rw [Tm.cfilterBody_iff]; simp only [hk, hd]

/-- The list core of `filter_pointfree`: pairing each element with a `P`-image, filtering the pairs by their image,
    and dropping the images is filtering by "some `P`-image passes": each element's one image answers both sides. -/
theorem cfiltL_zip {α β : Type} (P : α → β → Prop) (K D : β → Prop) :
    ∀ xs ys : List α, (∃ ps qs, All2 P xs ps ∧ cfiltL (fun q => K q.2) (fun q => D q.2) (xs.zip ps) qs ∧
      All2 (fun q a => a = q.1) qs ys) ↔ cfiltL (fun a => ∃ b, P a b ∧ K b) (fun a => ∃ b, P a b ∧ D b) xs ys
  | [], ys => by
    simp only [cfiltL]
    constructor
    · rintro ⟨ps, qs, hp, hq, hm⟩
      cases hp
      obtain rfl : qs = [] := hq
      cases hm; rfl
    · rintro rfl; exact ⟨[], [], .nil, rfl, .nil⟩
  | x :: xs, ys => by
    simp only [cfiltL]
    constructor
    · rintro ⟨ps, qs, hp, hq, hm⟩
      cases hp with
      | cons hb hp' =>
        simp only [List.zip_cons_cons, cfiltL] at hq
        rcases hq with ⟨hK, qs', rfl, hq'⟩ | ⟨hD, hq'⟩
        · cases hm with
          | cons ha hm' =>
            subst ha
            exact Or.inl ⟨⟨_, hb, hK⟩, _, rfl, (cfiltL_zip P K D xs _).1 ⟨_, qs', hp', hq', hm'⟩⟩
        · exact Or.inr ⟨⟨_, hb, hD⟩, (cfiltL_zip P K D xs ys).1 ⟨_, qs, hp', hq', hm⟩⟩
    · rintro (⟨⟨b, hb, hK⟩, ys', rfl, h⟩ | ⟨⟨b, hb, hD⟩, h⟩)
      · obtain ⟨ps', qs', hp', hq', hm'⟩ := (cfiltL_zip P K D xs ys').2 h
        exact ⟨b :: ps', (x, b) :: qs', .cons hb hp', Or.inl ⟨hK, qs', rfl, hq'⟩, .cons rfl hm'⟩
      · obtain ⟨ps', qs, hp', hq', hm⟩ := (cfiltL_zip P K D xs ys).2 h
        exact ⟨b :: ps', qs, .cons hb hp', Or.inr ⟨hD, hq'⟩, hm⟩

/-- **`filter_pointfree`** (B&dM §1.7) as the program elaborates `⟨𝟙, F(p)⟩ zip cfilter(π₂K, π₂D) F(π₁) =
    cfilter(p K, p D)`: `p` the variable 0, the tests `K`, `D` the variables 1, 2; `cfilter` the program's call node. -/
theorem Tm.filterPointfree_den {A B C : Obj} {k d k' d' : Nat} {c c' : Lean.Name} {cv cv' : Option Lean.Name}
    {os os' : List Obj} (hkd : k ≠ d := by decide) (hkd' : k' ≠ d' := by decide) (ρ : Val) :
    Tm.den ρ ((((Tm.id.pair ((Tm.prim mapRow : Tm (.arr A) (.arr B)).arg (Tm.var 0 : Tm A B))).comp
          (Tm.prim (rowOf "zip") : Tm (.prod (.arr A) (.arr B)) (.arr (.prod A B)))).comp
        (((Tm.call [k, d] c cv os (Tm.cfilterBody (.prod A B) C k d)).arg ((Tm.outr : Tm (.prod A B) B).comp (Tm.var 1 : Tm B C))).arg
          ((Tm.outr : Tm (.prod A B) B).comp (Tm.var 2 : Tm B C)))).comp
      ((Tm.prim mapRow : Tm (.arr (.prod A B)) (.arr A)).arg (Tm.outl : Tm (.prod A B) A))) =
    Tm.den ρ (((Tm.call [k', d'] c' cv' os' (Tm.cfilterBody A C k' d')).arg ((Tm.var 0 : Tm A B).comp (Tm.var 1 : Tm B C))).arg
      ((Tm.var 0 : Tm A B).comp (Tm.var 2 : Tm B C))) := by
  have hL : Tm.den ρ ((((Tm.call [k, d] c cv os (Tm.cfilterBody (.prod A B) C k d)).arg
      ((Tm.outr : Tm (.prod A B) B).comp (Tm.var 1 : Tm B C))).arg ((Tm.outr : Tm (.prod A B) B).comp (Tm.var 2 : Tm B C)))) =
      cfiltL (fun q => ∃ c, ρ 1 B C q.2 c) (fun q => ∃ c, ρ 2 B C q.2 c) := by
    funext u v; apply propext; rw [Tm.cfilterCall_iff hkd]
    simp only [Tm.den, Core.Rel.comp_apply, Core.Rel.graph, exists_eq_left]
  have hR : Tm.den ρ (((Tm.call [k', d'] c' cv' os' (Tm.cfilterBody A C k' d')).arg ((Tm.var 0 : Tm A B).comp
      (Tm.var 1 : Tm B C))).arg ((Tm.var 0 : Tm A B).comp (Tm.var 2 : Tm B C))) =
      cfiltL (fun a => ∃ b, ρ 0 A B a b ∧ ∃ c, ρ 1 B C b c) (fun a => ∃ b, ρ 0 A B a b ∧ ∃ c, ρ 2 B C b c) := by
    funext u v; apply propext; rw [Tm.cfilterCall_iff hkd']; apply Iff.of_eq
    congr 1 <;> funext a <;> apply propext <;> simp only [Tm.den, Core.Rel.comp_apply] <;>
      exact ⟨fun ⟨c, b, h1, h2⟩ => ⟨b, h1, c, h2⟩, fun ⟨b, h1, c, h2⟩ => ⟨c, b, h1, h2⟩⟩
  rw [hR]
  funext xs ys; apply propext
  rw [← cfiltL_zip]
  simp only [↓hL, Tm.den, Tm.argDen, Prim.den_mapRow, Prim.den_zip, Core.Rel.comp_apply, Core.Rel.rpair,
    Core.Rel.graph, Core.Rel.id]
  constructor
  · rintro ⟨qs, ⟨_, ⟨⟨x', ps⟩, ⟨hx, hp⟩, rfl⟩, hq⟩, hm⟩
    subst hx
    exact ⟨ps, qs, (mapDen_all2 _ _ _).1 hp, hq, (mapDen_all2 _ _ _).1 hm⟩
  · rintro ⟨ps, qs, hp, hq, hm⟩
    exact ⟨qs, ⟨_, ⟨(xs, ps), ⟨rfl, (mapDen_all2 _ _ _).2 hp⟩, rfl⟩, hq⟩, (mapDen_all2 _ _ _).2 hm⟩

/-- `cond(K, D, R, S) ≜ dom(K) R ∪ (dom(D) S)` as the program elaborates its body, its parameters the variables
    `k`, `d`, `r`, `s`. -/
abbrev Tm.condBody (E B C : Obj) (k d r s : Nat) : Tm E B :=
  ((Tm.dom (Tm.var k : Tm E C)).comp (Tm.var r : Tm E B)).join ((Tm.dom (Tm.var d : Tm E C)).comp (Tm.var s : Tm E B))

theorem Tm.condBody_iff {E B C : Obj} (ρ : Val) (k d r s : Nat) (x : E.El) (y : B.El) :
    (Tm.condBody E B C k d r s).den ρ x y ↔
      ((∃ c, ρ k E C x c) ∧ ρ r E B x y) ∨ ((∃ c, ρ d E C x c) ∧ ρ s E B x y) := by
  simp only [Tm.den, Tm.dom_den, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.inter_apply, Core.Rel.id,
    Core.Rel.recip]
  constructor
  · rintro (⟨w, ⟨rfl, c, h, -⟩, h2⟩ | ⟨w, ⟨rfl, c, h, -⟩, h2⟩)
    · exact Or.inl ⟨⟨c, h⟩, h2⟩
    · exact Or.inr ⟨⟨c, h⟩, h2⟩
  · rintro (⟨⟨c, h⟩, h2⟩ | ⟨⟨c, h⟩, h2⟩)
    · exact Or.inl ⟨x, ⟨rfl, c, h, h⟩, h2⟩
    · exact Or.inr ⟨x, ⟨rfl, c, h, h⟩, h2⟩

/-- A call of the program's `cond` given `X`, `Y`, `Z`, `W`: `dom(X) Z ∪ (dom(Y) W)`. -/
theorem Tm.condCall_iff {E B C : Obj} {k d r s : Nat} {c : Lean.Name} {cv : Option Lean.Name} {os : List Obj}
    (hkd : k ≠ d) (hkr : k ≠ r) (hks : k ≠ s) (hdr : d ≠ r) (hds : d ≠ s) (hrs : r ≠ s)
    (ρ : Val) (X Y : Tm E C) (Z W : Tm E B) (x : E.El) (y : B.El) :
    (((((Tm.call [k, d, r, s] c cv os (Tm.condBody E B C k d r s)).arg X).arg Y).arg Z).arg W).den ρ x y ↔
      ((∃ c, X.den ρ x c) ∧ Z.den ρ x y) ∨ ((∃ c, Y.den ρ x c) ∧ W.den ρ x y) := by
  have hs' : Val.args [s] [⟨_, _, W.den ρ⟩] s E B = W.den ρ := Val.bind_apply _ _ _ rfl rfl
  have hr' : Val.args [r, s] [⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩] r E B = Z.den ρ := Val.bind_apply _ _ _ rfl rfl
  have hs'' : Val.args [r, s] [⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩] s E B = W.den ρ := by
    show ((Val.args [s] [⟨_, _, W.den ρ⟩]).bind r (Z.den ρ)) s E B = _
    rw [Val.bind_ne hrs.symm]; exact hs'
  have hd' : Val.args [d, r, s] [⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩] d E C = Y.den ρ :=
    Val.bind_apply _ _ _ rfl rfl
  have hr'' : Val.args [d, r, s] [⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩] r E B = Z.den ρ := by
    show ((Val.args [r, s] [⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩]).bind d (Y.den ρ)) r E B = _
    rw [Val.bind_ne hdr.symm]; exact hr'
  have hs3 : Val.args [d, r, s] [⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩] s E B = W.den ρ := by
    show ((Val.args [r, s] [⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩]).bind d (Y.den ρ)) s E B = _
    rw [Val.bind_ne hds.symm]; exact hs''
  have hk : Val.args [k, d, r, s] [⟨_, _, X.den ρ⟩, ⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩] k E C = X.den ρ :=
    Val.bind_apply _ _ _ rfl rfl
  have hd : Val.args [k, d, r, s] [⟨_, _, X.den ρ⟩, ⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩] d E C = Y.den ρ := by
    show ((Val.args [d, r, s] [⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩]).bind k (X.den ρ)) d E C = _
    rw [Val.bind_ne hkd.symm]; exact hd'
  have hr : Val.args [k, d, r, s] [⟨_, _, X.den ρ⟩, ⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩] r E B = Z.den ρ := by
    show ((Val.args [d, r, s] [⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩]).bind k (X.den ρ)) r E B = _
    rw [Val.bind_ne hkr.symm]; exact hr''
  have hs : Val.args [k, d, r, s] [⟨_, _, X.den ρ⟩, ⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩] s E B = W.den ρ := by
    show ((Val.args [d, r, s] [⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩]).bind k (X.den ρ)) s E B = _
    rw [Val.bind_ne hks.symm]; exact hs3
  show (Tm.condBody E B C k d r s).den
    (Val.args [k, d, r, s] [⟨_, _, X.den ρ⟩, ⟨_, _, Y.den ρ⟩, ⟨_, _, Z.den ρ⟩, ⟨_, _, W.den ρ⟩]) x y ↔ _
  rw [Tm.condBody_iff]; simp only [hk, hd, hr, hs]

/-- (1.11) `cond(K, D, R, S) T = cond(K, D, R T, S T)` as the program elaborates it. -/
theorem Tm.conditionalComp_den {A B C D : Obj} {c : Lean.Name} {cv : Option Lean.Name} {os : List Obj} (ρ : Val) :
    Tm.den ρ ((Tm.condBody A B C 0 1 2 3).comp (Tm.var 4 : Tm B D)) =
    Tm.den ρ (((((Tm.call [0, 1, 5, 6] c cv os (Tm.condBody A D C 0 1 5 6)).arg (Tm.var 0 : Tm A C)).arg
      (Tm.var 1 : Tm A C)).arg ((Tm.var 2 : Tm A B).comp (Tm.var 4 : Tm B D))).arg
      ((Tm.var 3 : Tm A B).comp (Tm.var 4 : Tm B D))) := by
  funext x z; apply propext
  rw [Tm.condCall_iff (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  show (∃ y, (Tm.condBody A B C 0 1 2 3).den ρ x y ∧ (Tm.var 4 : Tm B D).den ρ y z) ↔ _
  simp only [Tm.condBody_iff]
  simp only [Tm.den, Core.Rel.comp_apply]
  constructor
  · rintro ⟨y, (⟨hk, hr⟩ | ⟨hd, hs⟩), ht⟩
    · exact Or.inl ⟨hk, y, hr, ht⟩
    · exact Or.inr ⟨hd, y, hs, ht⟩
  · rintro (⟨hk, y, hr, ht⟩ | ⟨hd, y, hs, ht⟩)
    · exact ⟨y, Or.inl ⟨hk, hr⟩, ht⟩
    · exact ⟨y, Or.inr ⟨hd, hs⟩, ht⟩

/-- (1.10) `⟨𝟙, P⟩ cond(π₂K, π₂D, π₁R, π₁S) = cond(P K, P D, R, S)` as the program elaborates it: the test reads
    `P`, the branches read the element. -/
theorem Tm.pairConditional_den {A B C D : Obj} {c c' : Lean.Name} {cv cv' : Option Lean.Name} {os os' : List Obj}
    (ρ : Val) :
    Tm.den ρ ((Tm.id.pair (Tm.var 0 : Tm A B)).comp
      (((((Tm.call [5, 6, 7, 8] c cv os (Tm.condBody (.prod A B) D C 5 6 7 8)).arg
        ((Tm.outr : Tm (.prod A B) B).comp (Tm.var 1 : Tm B C))).arg
        ((Tm.outr : Tm (.prod A B) B).comp (Tm.var 2 : Tm B C))).arg
        ((Tm.outl : Tm (.prod A B) A).comp (Tm.var 3 : Tm A D))).arg
        ((Tm.outl : Tm (.prod A B) A).comp (Tm.var 4 : Tm A D)))) =
    Tm.den ρ (((((Tm.call [9, 10, 3, 4] c' cv' os' (Tm.condBody A D C 9 10 3 4)).arg
      ((Tm.var 0 : Tm A B).comp (Tm.var 1 : Tm B C))).arg ((Tm.var 0 : Tm A B).comp (Tm.var 2 : Tm B C))).arg
      (Tm.var 3 : Tm A D)).arg (Tm.var 4 : Tm A D)) := by
  funext x z; apply propext
  rw [Tm.condCall_iff (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  show (∃ q, (Tm.id.pair (Tm.var 0 : Tm A B)).den ρ x q ∧ _) ↔ _
  simp only [Tm.condCall_iff (by decide : (5 : Nat) ≠ 6) (by decide : (5 : Nat) ≠ 7) (by decide : (5 : Nat) ≠ 8)
    (by decide : (6 : Nat) ≠ 7) (by decide : (6 : Nat) ≠ 8) (by decide : (7 : Nat) ≠ 8)]
  simp only [Tm.den, Core.Rel.comp_apply, Core.Rel.rpair, Core.Rel.id, Core.Rel.graph]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨rfl, hp⟩, (⟨⟨c, hk⟩, hr⟩ | ⟨⟨c, hd⟩, hs⟩)⟩
    · obtain ⟨_, rfl, hk⟩ := hk
      obtain ⟨_, rfl, hr⟩ := hr
      exact Or.inl ⟨⟨c, _, hp, hk⟩, hr⟩
    · obtain ⟨_, rfl, hd⟩ := hd
      obtain ⟨_, rfl, hs⟩ := hs
      exact Or.inr ⟨⟨c, _, hp, hd⟩, hs⟩
  · rintro (⟨⟨c, b, hp, hk⟩, hr⟩ | ⟨⟨c, b, hp, hd⟩, hs⟩)
    · exact ⟨(x, b), ⟨rfl, hp⟩, Or.inl ⟨⟨c, b, rfl, hk⟩, x, rfl, hr⟩⟩
    · exact ⟨(x, b), ⟨rfl, hp⟩, Or.inr ⟨⟨c, b, rfl, hd⟩, x, rfl, hs⟩⟩

end Rel.Lang
