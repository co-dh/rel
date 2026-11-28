import Rel.Lang.Laws.PermConv
import Rel.Programs.Prelude

/-! # Laws of freyd §6.6 `AOP/A6_6e_Quicksort.lean`, on the concrete core

List cores of `join_perm` (`join perm = F(perm) join perm`): `perm` is `List.Perm` (`permDen_iff`). -/

namespace Rel.Lang

/-- `x a y` joins to a permutation of `z` iff some permuted parts join to it: `⊇` by `refl` parts, `⊆` by `Perm.append`. -/
theorem joinPerm_core {α : Type} (x y z : List α) (a : α) :
    (x ++ a :: y).Perm z ↔ ∃ x' y', x.Perm x' ∧ y.Perm y' ∧ (x' ++ a :: y').Perm z :=
  ⟨fun h => ⟨x, y, List.Perm.refl _, List.Perm.refl _, h⟩,
    fun ⟨_, _, hx, hy, h⟩ => (List.Perm.append hx (List.Perm.cons a hy)).trans h⟩

open Rel.Kernel Tab Rel.Rep

/-- **`perm`'s text relates an array to its permutations**: the body the prelude elaborates, `prelude.perm.body`, at
    any objects `σ` (`Tm.instObj`). A law about a call of `perm` takes
    `(ht : prelude.perm.body.instObj [.general] [B] = .ok t' := by rfl)` and states the node `Tm.call ks c cv os t'`. -/
theorem Tm.permDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.atom .general).arr.inst ph σ) ((Obj.atom .general).arr.inst ph σ)}
    (ht : Rel.Programs.prelude.perm.body.instObj ph σ = .ok t') (xs ys : Obj.El ((Obj.atom .general).inst ph σ).arr) :
    t'.den ρ xs ys ↔ xs.Perm ys := by
  obtain rfl := Except.ok.inj ht
  exact (Iff.of_eq (congrFun (congrFun (Tm.permCall_den (k := 31) (c := `add) (os := []) ρ) xs) ys)).trans
    (permDen_iff xs ys)

/-- `join(x,a,y) = x ⧺ [a] ⧺ y` on the left-nested triple, `(snoc×𝟙)cat` as the program elaborates it. -/
abbrev Tm.joinT (B : Obj) : Tm (.prod (.prod (.arr B) B) (.arr B)) (.arr B) :=
  ((Tm.outl.comp (Tm.prim (rowOf "snoc") : Tm (.prod (.arr B) B) (.arr B))).pair (Tm.outr.comp Tm.id : Tm (.prod (.prod (.arr B) B) (.arr B)) (.arr B))).comp
    (Tm.prim (rowOf "cat"))

/-- `join perm = (perm×𝟙)×perm join perm`: `perm` calls of the prelude at the one object `B`. -/
theorem Tm.joinPerm_den {B : Obj} {t' : Tm (.arr B) (.arr B)}
    (ht : Rel.Programs.prelude.perm.body.instObj [.general] [B] = .ok t' := by rfl) (ρ : Val) :
    Tm.den ρ ((Tm.joinT B).comp (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [B] t')) =
    Tm.den ρ ((((Tm.outl.comp ((Tm.outl.comp (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [B] t')).pair
        (Tm.outr.comp Tm.id))).pair (Tm.outr.comp (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [B] t'))).comp
      (Tm.joinT B)).comp (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [B] t')) := by
  have hP : ∀ xs ys, t'.den (Val.args [] []) xs ys ↔ xs.Perm ys := fun xs ys =>
    Tm.permDef_den [.general] [B] _ ht xs ys
  apply Core.Rel.ext
  rintro ⟨⟨x, a⟩, y⟩ z
  simp only [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, hP, Prim.den_snoc, Prim.den_cat, Core.Rel.id]
  simp only [Prod.exists, exists_eq_left, exists_eq_right, exists_and_left, exists_and_right, and_assoc,
    exists_eq_left', exists_eq_right', Prod.mk.injEq]
  rw [show x ++ [a] ++ y = x ++ a :: y by simp, joinPerm_core]
  constructor
  · rintro ⟨x', y', hx, hy, h⟩
    exact ⟨x' ++ a :: y', ⟨x', hx, y', hy, by simp⟩, h⟩
  · rintro ⟨b, ⟨x', hx, y', hy, rfl⟩, h⟩
    exact ⟨x', y', hx, hy, by simpa using h⟩

/-- `cor(S) ≜ dom(π₁S ∩ π₂)` (Prelude) at objects `A`, `B`, its parameter `S` the variable 2. -/
abbrev Tm.corDef (A B : Obj) : Tm (.prod A B) (.prod A B) :=
  Tm.dom ((Tm.outl.comp (Tm.var 2 : Tm A B)).meet Tm.outr)

/-- **`cor`'s text is the coreflexive of the pairs of `S`**: the body the prelude elaborates, `prelude.cor.body`, at
    any objects `σ` (placeholders `α = general`, `β = u1`), its parameter bound to `S`. -/
theorem Tm.corDef_den (ph : List QAtomicType) (σ : List Obj)
    {t' : Tm (((Obj.atom .general).prod (Obj.atom .u1)).inst ph σ) (((Obj.atom .general).prod (Obj.atom .u1)).inst ph σ)}
    (ht : Rel.Programs.prelude.cor.body.instObj ph σ = .ok t')
    (S : Core.Rel (Obj.El ((Obj.atom .general).inst ph σ)) (Obj.El ((Obj.atom .u1).inst ph σ))) (p q) :
    t'.den (Val.args [2] [⟨_, _, S⟩]) p q ↔ p = q ∧ S p.1 p.2 := by
  obtain rfl : Tm.corDef _ _ = t' := Except.ok.inj ht
  have hv : (Val.args [2] [⟨_, _, S⟩]) 2 ((Obj.atom .general).inst ph σ) ((Obj.atom .u1).inst ph σ) = S :=
    Val.bind_apply _ _ _ rfl rfl
  simp only [Tm.corDef, Tm.dom_den, Tm.den, hv, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph,
    Core.Rel.id]
  constructor
  · rintro ⟨rfl, b, ⟨⟨a, rfl, h⟩, rfl⟩, -⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, p.2, ⟨⟨p.1, rfl, h⟩, rfl⟩, ⟨p.1, rfl, h⟩, rfl⟩

/-- A call of `cor` given `X`, at the objects `[A, B]`: the pairs of `X`, as a coreflexive. -/
theorem Tm.corCall_den {A B : Obj} {cv : Option Lean.Name} {os : List Obj} {t' : Tm (.prod A B) (.prod A B)}
    (ht : Rel.Programs.prelude.cor.body.instObj [.general, .u1] [A, B] = .ok t') (ρ : Val) (X : Tm A B) (p q) :
    (Tm.arg (Tm.call [2] `Rel.Programs.prelude.cor cv os t') X).den ρ p q ↔ p = q ∧ X.den ρ p.1 p.2 :=
  Tm.corDef_den [.general, .u1] [A, B] ht (X.den ρ) p q

/-- `R/S` with the universes `𝟙` (an object variable's), `S` the converse of a membership `𝟙 ∋`: every element
    of the array is `R`-related to the left side; the universes' disjunct always holds. -/
theorem rdivDen_mem_iff {A C : Obj} (T : Core.Rel (Obj.El A) (Obj.El C)) (a : Obj.El A) (xs : Obj.El (.arr C)) :
    rdivDen T (Core.Rel.comp (Core.Rel.id _) memDen) (Core.Rel.id _) (Core.Rel.id _) a xs ↔ ∀ c ∈ xs, T a c := by
  rw [rdivDen_iff]
  simp only [Core.Rel.comp, Core.Rel.id, memDen]
  exact ⟨fun ⟨h, _⟩ c hc => h c ⟨xs, rfl, hc⟩, fun h => ⟨fun c ⟨_, e, hc⟩ => h c (e ▸ hc), Or.inr ⟨⟨a, rfl⟩, xs, rfl⟩⟩⟩

/-- B&dM p.155 `check'(R)` as the program elaborates it: `dom(π₁⟨π₂,π₁⟩cor(R°/∋)) ∩ dom(⟨π₁π₂,π₂⟩cor(R/∋))`, `R` the
    variable 0, `cor` the prelude call node `t'`. -/
abbrev Tm.checkT {A : Obj} (cv : Option Lean.Name) (os : List Obj) (t' : Tm (.prod A (.arr A)) (.prod A (.arr A))) :
    Tm (.prod (.prod (.arr A) A) (.arr A)) (.prod (.prod (.arr A) A) (.arr A)) :=
  (Tm.dom (((Tm.outl : Tm (.prod (.prod (.arr A) A) (.arr A)) (.prod (.arr A) A)).comp (Tm.outr.pair Tm.outl)).comp
      (Tm.arg (Tm.call [2] `Rel.Programs.prelude.cor cv os t')
        ((Tm.var 0 : Tm A A).conv.rdiv (Tm.id.comp Tm.mem) Tm.id Tm.id)))).meet
   (Tm.dom ((((Tm.outl : Tm (.prod (.prod (.arr A) A) (.arr A)) (.prod (.arr A) A)).comp Tm.outr).pair Tm.outr).comp
      (Tm.arg (Tm.call [2] `Rel.Programs.prelude.cor cv os t') ((Tm.var 0 : Tm A A).rdiv (Tm.id.comp Tm.mem) Tm.id Tm.id))))

/-- `check'(R)` keeps `(x, a, y)` when every element of `x` is `R`-below `a` and `a` is `R`-below every element of `y`. -/
theorem Tm.checkT_den {A : Obj} {cv : Option Lean.Name} {os : List Obj} {t' : Tm (.prod A (.arr A)) (.prod A (.arr A))}
    (ht : Rel.Programs.prelude.cor.body.instObj [.general, .u1] [A, .arr A] = .ok t') (ρ : Val) (p q) :
    (Tm.checkT cv os t').den ρ p q ↔ p = q ∧ (∀ c ∈ p.1.1, ρ 0 A A c p.1.2) ∧ (∀ c ∈ p.2, ρ 0 A A p.1.2 c) := by
  have h1 : ∀ p q, (Tm.arg (Tm.call [2] `Rel.Programs.prelude.cor cv os t')
      ((Tm.var 0 : Tm A A).conv.rdiv (Tm.id.comp Tm.mem) Tm.id Tm.id)).den ρ p q ↔ p = q ∧ ∀ c ∈ p.2, ρ 0 A A c p.1 :=
    fun p q => (Tm.corCall_den ht ρ _ p q).trans (and_congr Iff.rfl (rdivDen_mem_iff _ _ _))
  have h2 : ∀ p q, (Tm.arg (Tm.call [2] `Rel.Programs.prelude.cor cv os t')
      ((Tm.var 0 : Tm A A).rdiv (Tm.id.comp Tm.mem) Tm.id Tm.id)).den ρ p q ↔ p = q ∧ ∀ c ∈ p.2, ρ 0 A A p.1 c :=
    fun p q => (Tm.corCall_den ht ρ _ p q).trans (and_congr Iff.rfl (rdivDen_mem_iff _ _ _))
  obtain ⟨⟨x, a⟩, y⟩ := p
  show Core.Rel.inter (Tm.den ρ (Tm.dom _)) (Tm.den ρ (Tm.dom _)) _ _ ↔ _
  rw [Tm.dom_den, Tm.dom_den]
  simp only [Tm.den, Core.Rel.inter, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.graph, Core.Rel.rpair,
    Core.Rel.id] at h1 h2 ⊢
  simp only [h1, h2]
  constructor
  · rintro ⟨⟨rfl, _, ⟨⟨u, v⟩, ⟨_, rfl, h11, h12⟩, rfl, h1⟩, -⟩, -, _, ⟨⟨u', v'⟩, ⟨⟨_, rfl, h21⟩, h22⟩, rfl, h2⟩, -⟩
    dsimp only at h11 h12 h21 h22
    subst h11 h12 h21 h22
    exact ⟨rfl, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨⟨rfl, (a, x), ⟨(a, x), ⟨(x, a), rfl, rfl, rfl⟩, rfl, h1⟩, (a, x), ⟨(x, a), rfl, rfl, rfl⟩, rfl, h1⟩,
      rfl, (a, y), ⟨(a, y), ⟨⟨(x, a), rfl, rfl⟩, rfl⟩, rfl, h2⟩, (a, y), ⟨⟨(x, a), rfl, rfl⟩, rfl⟩, rfl, h2⟩

/-- `(P×𝟙)×P` on the left-nested triple, as the program elaborates it, `P` a node `t'`. -/
abbrev Tm.triple {A : Obj} (P : Tm (.arr A) (.arr A)) : Tm (.prod (.prod (.arr A) A) (.arr A)) (.prod (.prod (.arr A) A) (.arr A)) :=
  (Tm.outl.comp ((Tm.outl.comp P).pair (Tm.outr.comp Tm.id))).pair (Tm.outr.comp P)

theorem Tm.triple_den {A : Obj} (P : Tm (.arr A) (.arr A)) (ρ : Val) (p q) :
    (Tm.triple P).den ρ p q ↔ P.den ρ p.1.1 q.1.1 ∧ p.1.2 = q.1.2 ∧ P.den ρ p.2 q.2 := by
  obtain ⟨⟨x, a⟩, y⟩ := p
  obtain ⟨⟨x', a'⟩, y'⟩ := q
  simp only [Tm.den, Core.Rel.comp_apply, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id]
  constructor
  · rintro ⟨⟨_, rfl, ⟨_, rfl, h1⟩, _, rfl, h2⟩, _, rfl, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, rfl, h3⟩; exact ⟨⟨_, rfl, ⟨_, rfl, h1⟩, _, rfl, rfl⟩, _, rfl, h3⟩

/-- B&dM p.155 **`check'_perm`**: `check'(R) ((perm×𝟙)×perm) = ((perm×𝟙)×perm) check'(R)`, permuting the parts keeps
    the pivot between them; `cor`, `perm` calls of the prelude at the one object `A`. -/
theorem Tm.checkPerm_den {A : Obj} {cv : Option Lean.Name} {os : List Obj}
    {tc : Tm (.prod A (.arr A)) (.prod A (.arr A))} {tp : Tm (.arr A) (.arr A)}
    (hc : Rel.Programs.prelude.cor.body.instObj [.general, .u1] [A, .arr A] = .ok tc := by rfl)
    (hp : Rel.Programs.prelude.perm.body.instObj [.general] [A] = .ok tp := by rfl) (ρ : Val) :
    Tm.den ρ ((Tm.checkT cv os tc).comp
      (Tm.triple (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [A] tp))) =
    Tm.den ρ ((Tm.triple (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [A] tp)).comp
      (Tm.checkT cv os tc)) := by
  have hP : ∀ xs ys, (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [A] tp).den ρ xs ys ↔
      xs.Perm ys := fun xs ys => Tm.permDef_den [.general] [A] _ hp xs ys
  apply Core.Rel.ext
  intro p q
  show Core.Rel.comp _ _ p q ↔ Core.Rel.comp _ _ p q
  simp only [Core.Rel.comp_apply, Tm.checkT_den hc, Tm.triple_den, hP]
  constructor
  · rintro ⟨_, ⟨rfl, h1, h2⟩, hx, ha, hy⟩
    exact ⟨q, ⟨hx, ha, hy⟩, rfl, fun c hc => ha ▸ h1 c (hx.mem_iff.2 hc), fun c hc => ha ▸ h2 c (hy.mem_iff.2 hc)⟩
  · rintro ⟨_, ⟨hx, ha, hy⟩, rfl, h1, h2⟩
    exact ⟨p, ⟨rfl, fun c hc => ha ▸ h1 c (hx.mem_iff.1 hc), fun c hc => ha ▸ h2 c (hy.mem_iff.1 hc)⟩, hx, ha, hy⟩

/-- `join° = cat° ⟨π₁ snoc°, π₂⟩` on the left-nested triple, as the program elaborates the converse of `join`. -/
abbrev Tm.joinConvT (A : Obj) : Tm (.arr A) (.prod (.prod (.arr A) A) (.arr A)) :=
  (Tm.prim (rowOf "uncat") : Tm (.arr A) (.prod (.arr A) (.arr A))).comp
    ((Tm.outl.comp ((Tm.prim (rowOf "unsnoc") : Tm (.arr A) (.prod (.arr A) A)).comp Tm.id)).pair
      (Tm.outr.comp (Tm.id.comp Tm.id)))

/-- B&dM p.155 **`split_base`**: `base ⊑ τ perm join° check'(R)` with `base(a) = ([], a, [])`: the empty parts hold the
    `check'` conditions vacuously. -/
theorem Tm.splitBase_den {A : Obj} {cv : Option Lean.Name} {os : List Obj}
    {tc : Tm (.prod A (.arr A)) (.prod A (.arr A))} {tp : Tm (.arr A) (.arr A)}
    (hc : Rel.Programs.prelude.cor.body.instObj [.general, .u1] [A, .arr A] = .ok tc := by rfl)
    (hp : Rel.Programs.prelude.perm.body.instObj [.general] [A] = .ok tp := by rfl) (ρ : Val) :
    Core.Rel.le (Tm.den ρ (((Tm.nil : Tm A (.arr A)).pair Tm.id).pair Tm.nil))
      (Tm.den ρ ((((Tm.prim (rowOf "τ") : Tm A (.arr A)).comp
        (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [A] tp)).comp (Tm.joinConvT A)).comp
        (Tm.checkT cv os tc))) := by
  have hP := Tm.permDef_den [.general] [A] (Val.args [] []) hp
  refine Core.Rel.le_iff.mpr fun a q h => ?_
  obtain rfl : q = (([], a), []) := by
    simpa [Tm.den, Tm.nil, Prim.den_nilRow, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id, Prod.ext_iff, eq_comm] using h
  refine ⟨(([], a), []), ⟨[a], ⟨[a], ?_, (hP _ _).2 (List.Perm.refl _)⟩, ?_⟩, (Tm.checkT_den hc ρ _ _).2 ⟨rfl, ?_, ?_⟩⟩
  · simp [Tm.den, Prim.den_tau]
  · simp only [Tm.den, Prim.den_uncat, Prim.den_unsnoc, Core.Rel.comp_apply, Core.Rel.rpair, Core.Rel.graph,
      Core.Rel.recip, Core.Rel.id]
    exact ⟨([a], []), rfl, ⟨[a], rfl, ([], a), rfl, rfl⟩, [], rfl, [], rfl, rfl⟩
  · simp
  · simp

end Rel.Lang
