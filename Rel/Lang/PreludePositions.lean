module

public import Rel.Lang.PreludeRows
public import Rel.Lang.PreludeDfn
public import Rel.Lang.PreludeOrd
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

/-- **The body, given its two parts**: `s` the prefixes before a passing element (`hS`) and `L` their count in `P`
    (`hL`), means the passing positions of `x` (`positionsL`, ascending) when all lie in `P`, and no list else. -/
theorem Tm.positionsBody_key (ρ : Val) {B : Obj} (p : Tm B B) (s : Tm (.arr B) (.arr B)) (L : Tm (.arr B) .long)
    {P : Obj.long.El → Prop}
    (hS : ∀ xs pre, s.den ρ xs pre ↔ ∃ k, ∃ h : k < xs.length, pre = xs.take k ∧ ∃ c, p.den ρ xs[k] c)
    (x : List B.El) (hx : x.length < 2 ^ 63)
    (hL : ∀ zs : List B.El, ∀ n, zs.length < 2 ^ 63 → (L.den ρ zs n ↔ n = Int64.ofNat zs.length ∧ P n))
    (w : List Int64) :
    (Tm.positionsBody s L).den ρ x w ↔
      ∃ b, b = positionsL (fun a => decide (∃ y, p.den ρ a y)) x ∧ w = b ∧ ∀ e ∈ b, P e := by
  simp only [Tm.positionsBody_den, lamDen_iff, Core.Rel.comp, hS]
  have hfa : ∀ a, decide (∃ y, p.den ρ a y) = true ↔ ∃ y, p.den ρ a y := fun a => decide_eq_true_iff
  have hlen : ∀ k, k < x.length → (x.take k).length = k := fun k hk => by simp; omega
  have hb63 : ∀ k, (x.take k).length < 2 ^ 63 := fun k => Nat.lt_of_le_of_lt (List.length_take_le' _ _) hx
  have hmem : ∀ b, (∃ pre, (∃ k h, pre = x.take k ∧ ∃ c, p.den ρ x[k] c) ∧ L.den ρ pre b) ↔
      b ∈ positionsL (fun a => decide (∃ y, p.den ρ a y)) x ∧ P b := by
    intro b; rw [mem_positionsL]
    constructor
    · rintro ⟨pre, ⟨k, hk, rfl, c, hc⟩, hb⟩
      have h := (hL _ _ (hb63 k)).1 hb
      rw [hlen k hk] at h
      exact ⟨⟨k, hk, (hfa _).2 ⟨c, hc⟩, h.1⟩, h.2⟩
    · rintro ⟨⟨k, hk, hf, rfl⟩, hPb⟩
      obtain ⟨c, hc⟩ := (hfa _).1 hf
      exact ⟨x.take k, ⟨k, hk, rfl, c, hc⟩, (hL _ _ (hb63 k)).2 ⟨by rw [hlen k hk], hPb⟩⟩
  constructor
  · rintro ⟨hg, hs, hm⟩
    have hP' : ∀ e ∈ positionsL (fun a => decide (∃ y, p.den ρ a y)) x, P e := fun e he => by
      obtain ⟨k, hk, hf, rfl⟩ := (mem_positionsL _ _ _).1 he
      obtain ⟨c, hc⟩ := (hfa _).1 hf
      obtain ⟨n, hn⟩ := hg (x.take k) ⟨k, hk, rfl, c, hc⟩
      have h := (hL _ _ (hb63 k)).1 hn
      rw [hlen k hk] at h
      exact h.1 ▸ h.2
    exact ⟨_, rfl, lt_sorted_unique hs (positionsL_sorted _ _ hx)
      fun b => (hm b).trans ((hmem b).trans ⟨fun h => h.1, fun h => ⟨h, hP' b h⟩⟩), hP'⟩
  · rintro ⟨b, rfl, rfl, hP'⟩
    refine ⟨fun pre ⟨k, hk, hpre, c, hc⟩ => ?_, positionsL_sorted _ _ hx, fun b => ?_⟩
    · subst hpre
      exact ⟨Int64.ofNat k, (hL _ _ (hb63 k)).2 ⟨by rw [hlen k hk], hP' _
        ((mem_positionsL _ _ _).2 ⟨k, hk, (hfa _).2 ⟨c, hc⟩, rfl⟩)⟩⟩
    · exact ⟨fun h => (hmem b).2 ⟨h, hP' b h⟩, fun h => ((hmem b).1 h).1⟩

/-- At the universes `u₀`, `u` of `length` (`P` every number, or an initial segment), `positions(p)`'s definition means
    the row cut to `P` (`F(u)` after it): the passing positions, ascending, all in `P`; at every number, the row. -/
theorem Tm.positionsDef_row (ρ : Val) {B : Obj} (p : Tm B B) (u₀ u : Tm .long .long) {P : Obj.long.El → Prop}
    (hP : (∀ x, P x) ∨ Seg .long P) (hU₀ : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) (hU : ∀ x y, u.den ρ x y ↔ x = y ∧ P x)
    (x : (Obj.arr B).El) (hx : Short _ x) (w : (Obj.arr .long).El) :
    ((Tm.positionsDef p u₀ u).den ρ x w ↔
      (Tm.comp (Tm.arg (.prim (rowOf "positions") : Tm (.arr B) (.arr .long)) p)
        (Tm.arg (.prim mapRow : Tm (.arr .long) (.arr .long)) u)).den ρ x w) ∧
      ((∀ x, P x) → ((Tm.positionsDef p u₀ u).den ρ x w ↔
        (Tm.arg (.prim (rowOf "positions") : Tm (.arr B) (.arr .long)) p).den ρ x w)) := by
  have hL : ∀ zs : List B.El, ∀ n, zs.length < 2 ^ 63 →
      ((Tm.lengthDef u₀ u).den ρ zs n ↔ n = Int64.ofNat zs.length ∧ P n) := fun zs n hs => by
    rw [(Tm.lengthDef_row ρ u₀ u hP hU₀ hU zs hs n).1]
    simp only [Tm.den, Prim.den_lengthRow, Core.Rel.comp, hU]
    constructor
    · rintro ⟨b, rfl, rfl, hb⟩; exact ⟨rfl, hb⟩
    · rintro ⟨rfl, hb⟩; exact ⟨_, rfl, rfl, hb⟩
  have key := Tm.positionsBody_key ρ p _ _ (Tm.positionsS_den ρ p) x hx hL w
  have e : Tm.positionsDef p u₀ u = Tm.positionsBody (Tm.positionsS p) (Tm.lengthDef u₀ u) := rfl
  refine ⟨?_, fun hall => ?_⟩
  · rw [e, key]
    simp only [Tm.den, Tm.argDen, Core.Rel.comp, Prim.den_positions, Prim.den_mapRow_corefl hU]
  · rw [e, key]
    simp only [Tm.den, Tm.argDen, Prim.den_positions]
    exact ⟨fun ⟨b, hb, h, _⟩ => h.trans hb, fun h => ⟨_, rfl, h, fun e _ => hall e⟩⟩

/-- **`positions`'s text means the row cut to the universe** (Q3 = H), as `Tm.ascDef_den`: `prelude.positions.body` at
    any objects `σ` is `Tm.positionsBody` of its items `s` (`Tm.positionsS` of the variable 2, its `at(0)` literal
    `Tm.zeroLit_den`) and `len` (`Tm.lengthDef_den` with the universe variable 1: `P`, every number or an initial
    segment, `P 0` as for `length`'s seed), so `Tm.positionsBody_key` gives the row cut to `P`, as `Tm.positionsDef_row`. -/
theorem Tm.positionsDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {P : Obj.long.El → Prop}
    (hP : (∀ x, P x) ∨ Seg .long P) (hU : ∀ x y, ρ 1 .long .long x y ↔ x = y ∧ P x) (h0 : P 0)
    {t' : Tm ((Obj.atom .general).arr.inst ph σ) ((Obj.atom .i64).arr.inst ph σ)}
    (ht : Rel.Programs.prelude.positions.body.instObj ph σ = .ok t') (x) (hx : Short _ x) (w) :
    (t'.den ρ x w ↔ (Tm.comp (Tm.arg (.prim (rowOf "positions") : Tm ((Obj.atom .general).arr.inst ph σ) (Obj.arr .long))
      (.var 2 : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ)))
      (Tm.arg (.prim mapRow : Tm (Obj.arr .long) (Obj.arr .long)) (.var 1 : Tm .long .long))).den ρ x w) ∧
      ((∀ x, P x) → (t'.den ρ x w ↔ (Tm.arg (.prim (rowOf "positions") : Tm ((Obj.atom .general).arr.inst ph σ)
        (Obj.arr .long)) (.var 2 : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ))).den ρ x w)) := by
  -- `i64` is no placeholder: `σ` keeps it
  have hU' : ∀ x y, ρ 1 ((Obj.atom .i64).inst ph σ) ((Obj.atom .i64).inst ph σ) x y ↔ x = y ∧ P x := hU
  -- the right side names `ρ 2`, not `(var 2).den ρ`, so `rw [Tm.den]` below can only unfold `t'`
  have key : t'.den ρ x w ↔ ∃ b, b = positionsL (fun a => decide (∃ y,
      ρ 2 ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ) a y)) x ∧ w = b ∧ ∀ e ∈ b, P e := by
    obtain rfl := Except.ok.inj ht
    have hz := Tm.zeroLit_den ρ
    simp only [Tm.den] at hz
    rw [Tm.den, Tm.argDen, Tm.argDen, Tm.argDen]
    -- `Tm.den.eq_25` is the `.arg` clause: a bare `Tm.den` would unfold a `.var` of the argument list first
    rw [Tm.den.eq_25, Tm.argDen, Tm.argDen, Tm.argDen]
    refine (Tm.positionsBody_key _ (P := P) (.var 2) _ _ ?_ x hx ?_ w).trans ?_
    -- the variables bound by the two calls: `Tm.den.eq_23` (the `.var` clause) unfolds them and nothing else
    · intro xs pre
      simp (config := { decide := true }) only [Tm.den.eq_23, Val.args, Val.bind, ↓reduceIte,
        and_self, dite_true]
      -- `[β].inst ph σ = [β.inst ph σ]` holds by `rfl`, so the binder's cast is the identity
      rw [dif_pos (show (Obj.atom .general).arr.inst ph σ = ((Obj.atom .general).inst ph σ).arr from rfl)]
      refine Iff.trans ?_ (Tm.positionsS_den ρ (.var 2) xs pre)
      simp only [Tm.positionsS, Tm.at0, Tm.dom, Tm.den, Tm.argDen, Gen.atom_zero, cast_eq, hz, Core.Rel.comp_assoc]
      exact Iff.rfl
    · intro zs n hs
      simp (config := { decide := true }) only [Tm.den.eq_23, Val.args, Val.bind, ↓reduceIte,
        and_self, dite_true]
      rw [Tm.den.eq_25, Tm.argDen, dif_pos ⟨rfl, rfl⟩]
      refine ((Tm.lengthDef_den [.general] [(Obj.atom .general).inst ph σ] _ hP ?_ h0 rfl zs hs n).1).trans ?_
      · intro x y
        simp (config := { decide := true }) only [Tm.den.eq_23, Val.args, Val.bind, ↓reduceIte,
          and_self, dite_true]
        exact hU' x y
      -- `length` is called at `[β]`: its row at `(Obj.arr α).inst [α] [β]`, which is `[β]`
      have hl : ∀ b, Prim.den lengthRow ((Obj.arr (.atom .general)).inst [.general] [(Obj.atom .general).inst ph σ])
          .long [] zs b ↔ b = Int64.ofNat zs.length :=
        fun b => iff_of_eq (congrFun (congrFun (Prim.den_lengthRow (E := (Obj.atom .general).inst ph σ)) zs) b)
      simp only [Tm.den, Core.Rel.comp, Val.args, Val.bind, if_true, and_self]
      constructor
      · rintro ⟨b, hb, h⟩; obtain rfl := (hl b).1 hb; obtain ⟨rfl, hb⟩ := (hU' _ _).1 h; exact ⟨rfl, hb⟩
      · rintro ⟨rfl, hb⟩; exact ⟨_, (hl _).2 rfl, (hU' _ _).2 ⟨rfl, hb⟩⟩
    · simp (config := { decide := true }) only [Tm.den.eq_23, Val.args, Val.bind, ↓reduceIte,
        and_self, dite_true]
  -- the row at `[β].inst ph σ`, which is `[β.inst ph σ]`
  have hp := Prim.den_positions (B := (Obj.atom .general).inst ph σ) (ρ 2 _ _)
  change Prim.den (rowOf "positions") ((Obj.atom .general).arr.inst ph σ) (Obj.arr .long) _ = _ at hp
  refine ⟨?_, fun hall => ?_⟩
  · rw [key]
    simp only [Tm.den, Tm.argDen, Core.Rel.comp, hp, Prim.den_mapRow_corefl hU]
  · rw [key]
    simp only [Tm.den, Tm.argDen, hp]
    exact ⟨fun ⟨b, hb, h, _⟩ => h.trans hb, fun h => ⟨_, rfl, h, fun e _ => hall e⟩⟩

end Rel.Lang
