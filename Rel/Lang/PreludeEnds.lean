module

public import Rel.Lang.PreludeMerge

@[expose] public section

/-! The prelude's `head`, `tail`, `last`, `init` as calls (`Programs/Prelude.lean`), over any instantiation `os` of the
    call's objects, so every program that inlines them can cite `Tm.headCall_den`, `Tm.tailCall_den`, `Tm.lastCall_den`,
    `Tm.initCall_den`; and `moves` of the cylinder program, built from them. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `head`, `at(0)`, as a call. -/
def Tm.headCall (B : Obj) (os : List Obj := [B]) : Tm (.arr B) B :=
  .call [] `Rel.Programs.prelude.head (some `Rel.Programs.prelude.head.conv) os (Tm.headAt (B := B))

/-- `(at(0)τ ∩ 𝟙)` keeps the one-element lists. -/
def Tm.single (B : Obj) : Tm (.arr B) (.arr B) := .meet (.comp (Tm.headAt (B := B)) (.prim (rowOf "τ"))) .id

/-- The prelude's `init`, `cat° dom(π₂ (at(0)τ ∩ 𝟙))π₁`, as a call. -/
def Tm.initCall (B : Obj) (os : List Obj := [B]) : Tm (.arr B) (.arr B) :=
  .call [] `Rel.Programs.prelude.init (some `Rel.Programs.prelude.init.conv) os
    (.comp (.comp (.prim (rowOf "uncat")) (.dom (.comp .outr (Tm.single B)))) .outl)

/-- The prelude's `last`, `cat° π₂ (at(0)τ ∩ 𝟙)at(0)`, as a call. -/
def Tm.lastCall (B : Obj) (os : List Obj := [B]) : Tm (.arr B) B :=
  .call [] `Rel.Programs.prelude.last (some `Rel.Programs.prelude.last.conv) os
    (.comp (B := .arr B) (.comp (B := .arr B) (.comp (B := .prod (.arr B) (.arr B)) (.prim (rowOf "uncat")) .outr) (Tm.single B)) (Tm.headAt (B := B)))

theorem Tm.headCall_den (ρ : Val) {B : Obj} {os : List Obj} (xs : Obj.El (.arr B)) (b : Obj.El B) :
    (Tm.headCall B os).den ρ xs b ↔ ∃ h : 0 < xs.length, b = xs[0]'h := by
  simp only [Tm.headCall, Tm.den]; exact Tm.headAt_den ρ xs b

theorem Tm.single_den (ρ : Val) {B : Obj} (l l' : Obj.El (.arr B)) :
    (Tm.single B).den ρ l l' ↔ (∃ a, l = [a]) ∧ l' = l := by
  simp only [Tm.single, Tm.den, Prim.den_tau, Core.Rel.comp, Core.Rel.inter, Core.Rel.id, Tm.headAt_den]
  constructor
  · rintro ⟨⟨b, ⟨h, hb⟩, hl⟩, hl'⟩
    subst hb; subst hl'
    exact ⟨⟨l[0], by simpa using hl⟩, rfl⟩
  · rintro ⟨⟨a, rfl⟩, rfl⟩
    exact ⟨⟨a, ⟨by simp, rfl⟩, rfl⟩, rfl⟩

theorem Tm.initCall_den (ρ : Val) {B : Obj} {os : List Obj} (xs ys : Obj.El (.arr B)) :
    (Tm.initCall B os).den ρ xs ys ↔ ∃ a, xs = ys ++ [a] := by
  simp only [Tm.initCall, Tm.den, Val.args, Tm.dom_den, Prim.den_uncat, Core.Rel.comp, Core.Rel.inter,
    Core.Rel.recip, Core.Rel.graph, Core.Rel.id, Tm.single_den]
  constructor
  · rintro ⟨p, ⟨p1, hx, hp, b2, ⟨b, hb, ⟨a, ha⟩, hb2⟩, b3, hb3, ⟨a', ha'⟩, hb23⟩, rfl⟩
    subst hp
    exact ⟨a, by simp_all⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(ys, [a]), ⟨(ys, [a]), rfl, rfl, [a], ⟨[a], rfl, ⟨a, rfl⟩, rfl⟩, [a], rfl, ⟨a, rfl⟩, rfl⟩, rfl⟩

theorem Tm.lastCall_den (ρ : Val) {B : Obj} {os : List Obj} (xs : Obj.El (.arr B)) (a : Obj.El B) :
    (Tm.lastCall B os).den ρ xs a ↔ ∃ ys, xs = ys ++ [a] := by
  simp only [Tm.lastCall, Tm.den, Val.args, Prim.den_uncat, Core.Rel.comp, Core.Rel.graph, Tm.single_den,
    Tm.headAt_den]
  constructor
  · rintro ⟨b, ⟨b1, ⟨p, hx, hb1⟩, ⟨a', ha'⟩, hb⟩, h, ha⟩
    subst hb; subst ha'
    have hs : p.2 = [a'] := hb1.symm
    refine ⟨p.1, ?_⟩
    rw [hx, hs]; simp at ha; rw [ha]
  · rintro ⟨ys, rfl⟩
    exact ⟨[a], ⟨[a], ⟨(ys, [a]), rfl, rfl⟩, ⟨a, rfl⟩, rfl⟩, by simp, rfl⟩

end Rel.Lang
