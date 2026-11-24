module

public import Rel.Lang.PreludeRows
public import Rel.Lang.PreludeDfn
public import Rel.Lang.GenSound
public import Rel.RepSymRank
public import Rel.Programs.Prelude

@[expose] public section

/-! `positions(p : α ⟶ α) : [α] ⟶ [ν] ≜ (𝟙 − dom(s (𝟙 − dom(len)))) Λ(s len) where s ≜ cat° dom(π₂ at(0) p) π₁,
    len ≜ length` (`Programs/Prelude.lean`) means the row `positions` cut to the universe of `ν` (B10b): `s` relates
    `xs` to its prefixes ending just before a passing element, `len` counts them, `Λ` lists the counts ascending, and
    the guard keeps `xs` only where every count is in the universe, so at an initial segment the text is the row
    cut by `F(u)` (`Prim.cut`) and at every number the row. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open Classical

/-- `s ≜ cat° dom(π₂ at(0) p) π₁`: `xs` to its prefixes `ys` with `xs = ys ⧺ zs` and the head of `zs` in `dom p`. -/
def Tm.positionsS {B : Obj} (p : Tm B B) : Tm (.arr B) (.arr B) :=
  .comp (B := .prod (.arr B) (.arr B)) (.prim (rowOf "uncat"))
    (.comp (.dom (.comp (A := .prod (.arr B) (.arr B)) .outr (.comp Tm.at0 p))) .outl)

/-- `(𝟙 − dom(s (𝟙 − dom(L)))) Λ(s L)`: the lists whose every `s`-image has a count `L`, to the list of the counts. -/
def Tm.positionsBody {B : Obj} (s : Tm (.arr B) (.arr B)) (L : Tm (.arr B) .long) : Tm (.arr B) (.arr .long) :=
  .comp (.diff .id (.dom (.comp s (.diff .id (.dom L))))) (.lam (.comp s L))

/-- The prelude's `positions`, its count `length` cut to the universes `u₀`, `u` (`Tm.lengthDef`). -/
def Tm.positionsDef {B : Obj} (p : Tm B B) (u₀ u : Tm .long .long) : Tm (.arr B) (.arr .long) :=
  Tm.positionsBody (Tm.positionsS p) (Tm.lengthDef u₀ u)

theorem Tm.positionsBody_den (ρ : Val) {B : Obj} (s : Tm (.arr B) (.arr B)) (L : Tm (.arr B) .long) (xs : List B.El)
    (w : List Int64) :
    (Tm.positionsBody s L).den ρ xs w ↔
      (∀ pre, s.den ρ xs pre → ∃ n, L.den ρ pre n) ∧ lamDen (s.den ρ ≫ L.den ρ) xs w := by
  simp only [Tm.positionsBody, Tm.den, Tm.dom_den, Core.Rel.diff, Core.Rel.comp, Core.Rel.inter, Core.Rel.id,
    Core.Rel.recip]
  constructor
  · rintro ⟨b, ⟨rfl, hn⟩, hl⟩
    refine ⟨fun pre hs => Classical.byContradiction fun hc => hn ⟨rfl, pre, ⟨pre, hs, rfl, ?_⟩, pre, hs, rfl, ?_⟩, hl⟩
    all_goals exact fun ⟨_, n, h1, _⟩ => hc ⟨n, h1⟩
  · rintro ⟨hg, hl⟩
    refine ⟨xs, ⟨rfl, ?_⟩, hl⟩
    rintro ⟨-, b₁, ⟨b', hs, rfl, hn⟩, b₂, -, rfl, -⟩
    obtain ⟨n, hn'⟩ := hg _ hs
    exact hn ⟨rfl, n, hn', hn'⟩

theorem Tm.positionsS_den (ρ : Val) {B : Obj} (p : Tm B B) (xs pre : List B.El) :
    (Tm.positionsS p).den ρ xs pre ↔ ∃ k, ∃ h : k < xs.length, pre = xs.take k ∧ ∃ c, p.den ρ xs[k] c := by
  simp only [Tm.positionsS, Tm.den, Tm.dom_den, Prim.den_uncat, Core.Rel.comp, Core.Rel.graph, Core.Rel.inter,
    Core.Rel.id, Core.Rel.recip, Tm.at0_den]
  constructor
  · rintro ⟨b, hxs, b₁, ⟨rfl, d, ⟨_, rfl, y, ⟨h, rfl⟩, hy⟩, -⟩, rfl⟩
    obtain ⟨a, c⟩ := b
    simp only at hxs h hy ⊢
    subst hxs
    have hl : (a ++ c)[a.length]'(by simp; omega) = c[0]'h := by simp [List.getElem_append_right]
    exact ⟨a.length, by simp; omega, by simp, d, by rw [hl]; exact hy⟩
  · rintro ⟨k, hk, rfl, c, hc⟩
    have hl : (xs.drop k)[0]'(by simp; omega) = xs[k] := by simp
    exact ⟨(xs.take k, xs.drop k), (List.take_append_drop k xs).symm, _, ⟨rfl, c, ⟨_, rfl, _, ⟨by simp; omega, hl.symm⟩, hc⟩,
      _, rfl, _, ⟨by simp; omega, rfl⟩, hl ▸ hc⟩, rfl⟩

theorem mem_positionsL {α : Type} (p : α → Bool) (xs : List α) (b : Int64) :
    b ∈ positionsL p xs ↔ ∃ k, ∃ h : k < xs.length, p xs[k] = true ∧ b = Int64.ofNat k := by
  simp only [positionsL, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨k, ⟨hk, hp⟩, rfl⟩
    rw [List.getElem?_eq_getElem hk] at hp
    exact ⟨k, hk, hp, rfl⟩
  · rintro ⟨k, hk, hp, rfl⟩
    exact ⟨k, ⟨hk, by rw [List.getElem?_eq_getElem hk]; exact hp⟩, rfl⟩

theorem positionsL_sorted {α : Type} (p : α → Bool) (xs : List α) (hx : xs.length < 2 ^ 63) :
    (positionsL p xs).Pairwise (Obj.lt .long) := by
  unfold positionsL
  rw [List.pairwise_map]
  refine (List.Pairwise.filter _ List.pairwise_lt_range).imp_of_mem ?_
  intro a b ha hb hab
  have ha' := List.mem_range.1 (List.mem_filter.1 ha).1
  have hb' := List.mem_range.1 (List.mem_filter.1 hb).1
  rw [Table.Obj.lt_long, Int64.lt_iff_toInt_lt, Int64.toInt_ofNat_of_lt (by omega), Int64.toInt_ofNat_of_lt (by omega)]
  omega

theorem Prim.den_positions {B : Obj} (T : Core.Rel (Obj.El B) (Obj.El B)) :
    Prim.den (rowOf "positions") (.arr B) (.arr .long) [⟨B, B, T⟩] =
      fun xs ys => ys = positionsL (fun x => decide (∃ y, T x y)) xs := by
  have hs : (rowOf "positions").sig = ([((.var {} "B", .var {} "B"), some false)], .list (.var {} "B"),
      .list (.var {} "ℕ")) := rfl
  have ho : (rowOf "positions").objs (.arr B) (.arr .long) [(B, B)] = some [B, .long] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "positions").sym) = some ⟨RowCode.positions, fun σ =>
      Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => graph (positionsL fun x => decide (inDom T x))⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; rw [dif_pos ⟨rfl, rfl⟩]
  rfl

end Rel.Lang
