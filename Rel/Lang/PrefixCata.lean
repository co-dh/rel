import Rel.Lang.PreludePrefix
import Rel.Programs.Prefix

/-! B&dM's `prefix = ⦇[nil, nil ∪ cons]⦈` (p.126; `Programs/Prefix.lean`, the right fold) and the prelude's
    `prefix ≜ cat° π₁` (`Tm.prefixDef`) are one relation, `ys <+: xs`, at every object. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- **The fold of `nil ∪ cons` means the prefixes**, whatever its seed `e` whose values are `[]` alone. -/
theorem Tm.prefixFold_iff (ρ : Val) {B : Obj} (e : Tm (.arr B) (.arr B)) (he : ∀ v, (∃ a, e.den ρ a v) ↔ v = [])
    (xs ys : List B.El) :
    (Tm.foldr e (.join .nil (.prim (rowOf "cons")))).den ρ xs ys ↔ ys <+: xs := by
  simp only [Tm.den, Tm.nil, Prim.den_nilRow, Prim.den_cons]
  induction xs generalizing ys with
  | nil => rw [foldrDen_empty]; simp [he]
  | cons x xs ih =>
    rw [foldrDen_cons]
    simp only [ih, Core.Rel.union, nilDen, Core.Rel.graph]
    constructor
    · rintro ⟨u, hu, h | h⟩
      · subst h; exact List.nil_prefix
      · subst h; exact List.cons_prefix_cons.2 ⟨rfl, hu⟩
    · intro h
      rcases ys with _ | ⟨y, ys⟩
      · exact ⟨[], List.nil_prefix, .inl rfl⟩
      · obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.1 h
        exact ⟨ys, h', .inr rfl⟩

/-- **`⦇[nil, nil ∪ cons]⦈ʳ` and `cat° π₁` are one relation** at every object `B`, under any variables (neither
    term reads one), whatever the fold's seed `e` whose values are `[]` alone. -/
theorem Tm.prefixFold_prefixDef (ρ ρ' : Val) {B : Obj} (e : Tm (.arr B) (.arr B))
    (he : ∀ v, (∃ a, e.den ρ a v) ↔ v = []) :
    (Tm.foldr e (.join .nil (.prim (rowOf "cons")))).den ρ = (Tm.prefixDef B).den ρ' := by
  funext xs ys; apply propext
  rw [Tm.prefixFold_iff ρ e he]
  simp only [Tm.prefixDef, Tm.den, Prim.den_uncat, Core.Rel.comp, Core.Rel.graph]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨(ys, t), ht.symm, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp.symm⟩

/-- **The fold and the prelude's text of `prefix` are one relation**: the body the prelude elaborates,
    `prelude.prefix.body`, at any objects `σ` (`Tm.instObj`). -/
theorem Tm.prefixFold_den (ph : List QAtomicType) (σ : List Obj) (ρ ρ' : Val)
    {t' : Tm ((Obj.atom .general).arr.inst ph σ) ((Obj.atom .general).arr.inst ph σ)}
    (ht : Rel.Programs.prelude.prefix.body.instObj ph σ = .ok t')
    (e : Tm (.arr ((Obj.atom .general).inst ph σ)) (.arr ((Obj.atom .general).inst ph σ)))
    (he : ∀ v, (∃ a, e.den ρ a v) ↔ v = []) :
    (Tm.foldr e (.join .nil (.prim (rowOf "cons")))).den ρ = t'.den ρ' := by
  obtain rfl : Tm.prefixDef ((Obj.atom .general).inst ph σ) = t' := Except.ok.inj ht
  exact Tm.prefixFold_prefixDef ρ ρ' e he

/-! ### The program `prefixCata`

`rel_program` writes a definition with an object variable (`prefixC : [α] ⟶ [α]`) as a term only where it is used, at
the use's objects: `x prefixC` is the slot `prefixCata.c.t4`, `x` then the fold at `[N]`, its seed the slot `t3`. -/

/-- The seed `prefixCata` elaborates for the fold, `ran(U nil)` at the one-point universe `U`: `[]` alone. -/
theorem prefixCata_seed (ρ : Val) (v : Obj.El (.arr (.atom .i64))) :
    (∃ a, (Tm.call [] (.num `_slot 3) none [] Programs.prefixCata.c.t3).den ρ a v) ↔ v = [] := by
  simp only [Programs.prefixCata.c.t3, Programs.prefixCata.c.t2, Programs.prefixCata.c.t1, Tm.den, Tm.argDen]
  erw [Prim.den_ranRow, Prim.den_nilRow]
  simp only [Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, nilDen]
  have i : Fin (USize.ofNat 1).toNat := ⟨0, by simp [USize.toNat_ofNat]⟩
  constructor
  · rintro ⟨_, rfl, -, -, _, -, rfl⟩; rfl
  · rintro rfl
    exact ⟨_, rfl, (), ⟨(), ⟨i, by trivial, by trivial⟩, rfl⟩, (), ⟨i, by trivial, by trivial⟩, rfl⟩

/-- **The fold `prefixCata` elaborates `prefixC` to means the prelude's `prefix`**, `cat° π₁` at `[N]`. -/
theorem prefixCata_prefixDef (ρ ρ' : Val) :
    (Tm.foldr (.call [] (.num `_slot 3) none [] Programs.prefixCata.c.t3) (.join .nil (.prim (rowOf "cons")))).den ρ =
      (Tm.prefixDef (.atom .i64)).den ρ' :=
  Tm.prefixFold_prefixDef ρ ρ' _ (prefixCata_seed ρ)

/-- **The program's check `x prefixC = x prefix`, proved**: its two sides, the slots `t4` and `t7` as `rel_program`
    wrote them (the `show` is checked against the two constants), mean one relation. -/
theorem prefixCata_check (ρ : Val) : Programs.prefixCata.c.t4.den ρ = Programs.prefixCata.c.t7.den ρ := by
  show ((Tm.call [] (.num `_slot 0) none [] Programs.prefixCata.c.t0).comp (Tm.foldr
      (.call [] (.num `_slot 3) none [] Programs.prefixCata.c.t3) (.join .nil (.prim (rowOf "cons"))))).den ρ =
    ((Tm.call [] (.num `_slot 0) none [] Programs.prefixCata.c.t0).comp
      (.prim (rowOf "prefix") : Tm (.arr (.atom .i64)) (.arr (.atom .i64)))).den ρ
  have hc : ∀ {A B C : Obj} (R : Tm A B) (S : Tm B C), (R.comp S).den ρ = R.den ρ ≫ S.den ρ := fun R S => by
    simp only [Tm.den]
  rw [hc, hc, prefixCata_prefixDef ρ ρ]
  congr 1

end Rel.Lang

