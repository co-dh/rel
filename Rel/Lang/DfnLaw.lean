import Rel.Lang.GenKFold
import Rel.RepTabArith
import Rel.KernelSpec.Elementwise
import Rel.Run.Lang.Elab

/-! A row of `dfns` is its definition's fused form (§4). `build` runs, in place of the definition, the fused row at an
    unbounded object and the fused row followed by `𝟙` of the target at an initial segment `0…k`; `Tm.dfnCut_den`
    proves each means the definition, from one fact (`chain_in`): a fold from `0` whose step never decreases the
    value leaves `0…k` only at its result. At any other universe the definition runs: there a partial sum or count
    may leave the object while the result is in it. `Prim.dfn_read` ties `dfns` to the rows of `DfnCut`. -/

namespace Rel.Lang

open Rel.Kernel
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `P` an initial segment `0…k` of ℕ: no number in it is negative, and with a number every smaller one down to `0`
    is in it. -/
def InitSeg (P : Int64 → Prop) : Prop :=
  (∀ x, P x → 0 ≤ x.toInt) ∧ ∀ x y, P x → 0 ≤ y.toInt → y.toInt ≤ x.toInt → P y

/-- A source every run holds: a list of fewer than `2^63` elements (a list cell is two `Int64` offsets). -/
def Short : (A : Obj) → A.El → Prop
  | .arr _, xs => xs.length < 2 ^ 63
  | _, _ => True

/-- **A chain from `0` that never decreases stays in `P` iff its end does**, `P` every number or an initial
    segment: every value lies between `0` and the end. -/
theorem chain_in {P : Int64 → Prop} (hP : (∀ x, P x) ∨ InitSeg P) (g : Nat → Int64) (n : Nat)
    (hg : InitSeg P → 0 ≤ (g 0).toInt ∧ ∀ t < n, (g t).toInt ≤ (g (t + 1)).toInt) :
    (∀ t ≤ n, P (g t)) ↔ P (g n) := by
  refine ⟨fun h => h n (Nat.le_refl _), fun hn t ht => ?_⟩
  rcases hP with hP | hP
  · exact hP _
  obtain ⟨h0, hm⟩ := hg hP
  have up : ∀ s, s ≤ n → ∀ t ≤ s, (g t).toInt ≤ (g s).toInt := by
    intro s
    induction s with
    | zero => intro _ t ht; rw [Nat.le_zero.1 ht]; exact Int.le_refl _
    | succ s ih =>
      intro hs t ht
      rcases Nat.lt_or_eq_of_le ht with ht | rfl
      · exact Int.le_trans (ih (by omega) t (by omega)) (hm s (by omega))
      · exact Int.le_refl _
  exact hP.2 _ _ hn (Int.le_trans h0 (up t ht 0 (Nat.zero_le _))) (up n (Nat.le_refl _) t ht)

/-- The base `0` (`zeroTm`): its values are `0`, where `0` is in its universe. -/
theorem zeroTm_den (u₀ : Tm .long .long) (ρ : Val) {P : Int64 → Prop} (hU : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x)
    (v : Int64) : (∃ a, (zeroTm u₀).den ρ a v) ↔ v = 0 ∧ P 0 := by
  -- `⟨𝟙,𝟙⟩ minus ∩ 𝟙` keeps `0` alone, where `0` is in the universe
  have hz : ∀ y w, (Tm.meet (.comp (.pair .id .id) (.arith .i64 Rel.Kernel.Ew.sub u₀)) .id : Tm .long .long).den ρ y w ↔
      y = w ∧ w = 0 ∧ P 0 := fun y w => by
    simp only [Tm.den, Core.Rel.inter, Core.Rel.comp, Core.Rel.rpair, Core.Rel.id]
    constructor
    · rintro ⟨⟨⟨a1, a2⟩, ⟨h1, h2⟩, hA⟩, rfl⟩
      dsimp only at h1 h2
      subst h1 h2
      obtain ⟨-, -, v', ⟨hv, hn, -⟩, hv'⟩ := (arithDen_iff _ _ _ _ _).1 hA
      obtain ⟨rfl, hPa⟩ := (hU _ _).1 hv'
      rw [Rel.Verify.Ew.intStep_sub] at hv
      split at hv
      · exact absurd hv hn
      rw [Int64.sub_self] at hv
      subst hv
      exact ⟨rfl, rfl, hPa⟩
    · rintro ⟨rfl, rfl, h0⟩
      have hu : u₀.den ρ 0 0 := (hU _ _).2 ⟨rfl, h0⟩
      exact ⟨⟨(0, 0), ⟨rfl, rfl⟩, (arithDen_iff _ _ _ _ _).2 ⟨⟨0, hu⟩, ⟨0, hu⟩, 0, (by decide : stepDen Ew.sub ((0 : Int64), (0 : Int64)) 0), hu⟩⟩, rfl⟩
  simp only [zeroTm]
  generalize (Tm.meet (.comp (.pair .id .id) (.arith .i64 Rel.Kernel.Ew.sub u₀)) .id : Tm .long .long) = z at hz ⊢
  simp only [Tm.den, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.id, hz, hU]
  constructor
  · rintro ⟨a, rfl, b, -, b₁, -, -, h0, hP⟩
    exact ⟨h0, hP⟩
  · rintro ⟨rfl, h0⟩
    exact ⟨0, rfl, 0, ⟨0, ⟨rfl, h0⟩, rfl, rfl, h0⟩, 0, ⟨rfl, h0⟩, rfl, rfl, h0⟩

/-- `Int64`'s `+` with no null and no wrap: the integer sum. -/
theorem stepDen_add_iff (x v w : Int64) : stepDen Ew.add (x, v) w ↔
    x ≠ Alg.nul ∧ v ≠ Alg.nul ∧ -2 ^ 63 < x.toInt + v.toInt ∧ x.toInt + v.toInt < 2 ^ 63 ∧ w = x + v := by
  have hx1 := Int64.le_toInt x; have hx2 := Int64.toInt_lt x
  have hv1 := Int64.le_toInt v; have hv2 := Int64.toInt_lt v
  have hnul : Alg.nul.toInt = -2 ^ 63 := by decide
  have hs := Int64.toInt_add x v
  have hne : ∀ y : Int64, y ≠ Alg.nul ↔ y.toInt ≠ -2 ^ 63 := fun y =>
    ⟨fun h e => h (Int64.toInt_inj.1 (by rw [e, hnul])), fun h e => h (by rw [e, hnul])⟩
  simp only [stepDen, Rel.Verify.Ew.intStep_add, show (Ew.add == Ew.add) = true from rfl, if_true]
  constructor
  · rintro ⟨hw, hn, ho⟩
    by_cases hxn : x = Alg.nul ∨ v = Alg.nul
    · rw [if_pos hxn] at hw; exact absurd hw hn
    rw [if_neg hxn] at hw; subst hw
    obtain ⟨hxn, hvn⟩ := not_or.1 hxn
    rw [Int64.le_iff_toInt_le, Int64.le_iff_toInt_le] at ho
    have h0 : (0 : Int64).toInt = 0 := rfl
    rw [h0] at ho
    have hwn := (hne _).1 hn
    have hxi := (hne _).1 hxn
    have hvi := (hne _).1 hvn
    rw [hs] at ho hwn
    refine ⟨hxn, hvn, ?_, ?_, rfl⟩ <;> by_cases hv0 : 0 ≤ v.toInt
    all_goals
      first
        | (have := ho.1 hv0; simp only [Int.bmod] at this hwn; split at this <;> omega)
        | (have := mt ho.2 hv0; simp only [Int.bmod] at this hwn; split at this <;> omega)
  · rintro ⟨hxn, hvn, hl, hu, rfl⟩
    have h0 : (0 : Int64).toInt = 0 := rfl
    rw [if_neg (not_or.2 ⟨hxn, hvn⟩)]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hne, hs]; simp only [Int.bmod]; split <;> omega
    · rw [Int64.le_iff_toInt_le, Int64.le_iff_toInt_le, hs, h0]; simp only [Int.bmod]
      split <;> exact ⟨fun _ => by omega, fun _ => by omega⟩

/-- The definition `⦇[0, π₁ succ]⦈` of `length` on `TU`, its base `Te` the value `0`: the counts `0…n` all in `TU`,
    the result `n`. -/
theorem count_iff {E : Obj} {Te TU : Den .long .long} {P : Int64 → Prop}
    (he : ∀ v, (∃ a, Te a v) ↔ v = 0 ∧ P 0) (hU : ∀ x y, TU x y ↔ x = y ∧ P x)
    (xs : List E.El) (hn : xs.length < 2 ^ 63) (w : Int64) :
    foldDen (E := E) (V := .long) Te (graph Prod.fst ≫ succDen TU) xs w ↔
      (∀ t ≤ xs.length, P (Int64.ofNat t)) ∧ w = Int64.ofNat xs.length := by
  have hd : ∀ x, (∃ v, TU x v) ↔ P x := fun x =>
    ⟨fun ⟨_, h⟩ => ((hU _ _).1 h).2, fun h => ⟨x, (hU _ _).2 ⟨rfl, h⟩⟩⟩
  have step : ∀ t, t + 1 < 2 ^ 63 →
      Ew.intStep Ew.add Alg.nul (Int64.ofNat t) 1 = Int64.ofNat (t + 1) := fun t ht => by
    have hnt : Int64.ofNat t ≠ Alg.nul := fun e => by
      have := congrArg Int64.toInt e
      rw [Int64.toInt_ofNat_of_lt (by omega), show Alg.nul.toInt = -2 ^ 63 by decide] at this
      omega
    rw [Rel.Verify.Ew.intStep_add, if_neg (not_or.2 ⟨hnt, by decide⟩), Int64.ofNat_add]; rfl
  have hS : ∀ a x b, (graph Prod.fst ≫ succDen TU : Den (.prod .long E) .long) (a, x) b ↔
      P a ∧ b = Ew.intStep Ew.add Alg.nul a 1 ∧ P b := fun a x b => by
    simp only [Core.Rel.comp, Core.Rel.graph, succDen, hd]
    exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨a, rfl, h⟩⟩
  rw [foldDen_start]
  constructor
  · rintro ⟨v, hv, hf⟩
    obtain ⟨rfl, h0⟩ := (he v).1 hv
    obtain ⟨g, hg0, hs, rfl⟩ := (foldDen_iter (X := .long) _ xs 0 w).1 hf
    have hs := fun t ht => (hS _ _ _).1 (hs t ht)
    have hg : ∀ t ≤ xs.length, g t = Int64.ofNat t := by
      intro t
      induction t with
      | zero => intro _; exact hg0
      | succ t ih => intro ht; rw [(hs t (by omega)).2.1, ih (by omega), step t (by omega)]
    refine ⟨fun t ht => ?_, hg _ (Nat.le_refl _)⟩
    rw [← hg t ht]
    cases t with
    | zero => rw [hg0]; exact h0
    | succ t => exact (hs t (by omega)).2.2
  · rintro ⟨hP, rfl⟩
    exact ⟨0, (he 0).2 ⟨rfl, hP 0 (Nat.zero_le _)⟩, (foldDen_iter (X := .long) _ xs 0 _).2 ⟨Int64.ofNat, rfl,
      fun t ht => (hS _ _ _).2 ⟨hP t (by omega), (step t (by omega)).symm, hP (t + 1) (by omega)⟩, rfl⟩⟩

/-- **The definition `⦇[0, plus]⦈` of `sum` on `TU` from the value `0` is `sum`'s fold kept in `TU`**, `P` every
    number or an initial segment `0…k`: its elements and result in `P` and `stepDen add` folded from `0`, since from
    `0` the prefix sums of elements of `0…k` rise to the result (`chain_in`), so all are in `P` iff it is. -/
theorem plus_iff {TU : Den .long .long} {P : Int64 → Prop} (hP : (∀ x, P x) ∨ InitSeg P)
    (hU : ∀ x y, TU x y ↔ x = y ∧ P x) (xs : List Int64) (w : Int64) :
    (∃ v, (v = 0 ∧ P 0) ∧ foldDen (E := .long) (V := .long) (fun _ b => b = v) (arithDen .i64 Ew.add TU) xs w) ↔
      (∀ x ∈ xs, P x) ∧ P w ∧ foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add) xs w := by
  have hd : ∀ x, (∃ v, TU x v) ↔ P x := fun x =>
    ⟨fun ⟨_, h⟩ => ((hU _ _).1 h).2, fun h => ⟨x, (hU _ _).2 ⟨rfl, h⟩⟩⟩
  have hA : ∀ a x b, arithDen .i64 Ew.add TU (a, x) b ↔ P a ∧ P x ∧ stepDen Ew.add (a, x) b ∧ P b := fun a x b => by
    rw [arithDen_iff]
    constructor
    · rintro ⟨h1, h2, v', hs, hv⟩; obtain ⟨rfl, hw⟩ := (hU _ _).1 hv; exact ⟨(hd _).1 h1, (hd _).1 h2, hs, hw⟩
    · rintro ⟨h1, h2, hs, hw⟩; exact ⟨(hd _).2 h1, (hd _).2 h2, b, hs, (hU _ _).2 ⟨rfl, hw⟩⟩
  constructor
  · rintro ⟨_, ⟨rfl, h0⟩, hf⟩
    obtain ⟨g, hg0, hs, rfl⟩ := (foldDen_iter (X := .long) (Y := .long) _ xs 0 w).1 hf
    have hs := fun t ht => (hA _ _ _).1 (hs t ht)
    refine ⟨fun x hx => ?_, ?_, (foldDen_iter (X := .long) (Y := .long) _ xs 0 _).2 ⟨g, hg0, fun t ht => (hs t ht).2.2.1, rfl⟩⟩
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx; exact (hs t ht).2.1
    · rcases Nat.eq_zero_or_pos xs.length with e | e
      · rw [e, hg0]; exact h0
      · have := (hs (xs.length - 1) (by omega)).2.2.2; rwa [show xs.length - 1 + 1 = xs.length by omega] at this
  · rintro ⟨hE, hw, hf⟩
    obtain ⟨g, hg0, hs, rfl⟩ := (foldDen_iter (X := .long) (Y := .long) _ xs 0 w).1 hf
    have hP' := (chain_in hP g xs.length fun hI => ⟨by rw [hg0]; decide, fun t ht => by
      obtain ⟨-, -, h1, h2, e⟩ := (stepDen_add_iff _ _ _).1 (hs t ht)
      have := hI.1 _ (hE _ (List.getElem_mem ht))
      rw [e, Int64.toInt_add]; simp only [Int.bmod]; split <;> omega⟩).2 hw
    refine ⟨0, ⟨rfl, hg0 ▸ hP' 0 (Nat.zero_le _)⟩, (foldDen_iter (X := .long) (Y := .long) _ xs 0 _).2 ⟨g, hg0, fun t ht =>
      (hA _ _ _).2 ⟨hP' t (by omega), hE _ (List.getElem_mem ht), hs t ht, hP' (t + 1) (by omega)⟩, rfl⟩⟩

/-- `lengthRow` at `[E] ⟶ ℕ` is the count of its list. -/
theorem Prim.den_lengthRow {E : Obj} :
    Prim.den lengthRow (.arr E) .long [] = fun (xs : List E.El) w => w = Int64.ofNat xs.length := by
  have ho : lengthRow.objs (.arr E) .long = some [E, .long] := by
    simp [Prim.objs, lengthRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == lengthRow.sym) =
      some ⟨RowCode.length, fun _ _ xs w => w = Int64.ofNat xs.length⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `sumRow` at `[ℕ] ⟶ ℕ` is `sumAt`'s fold of `stepDen add` from `0`. -/
theorem Prim.den_sumRow : Prim.den sumRow (.arr .long) .long [] =
    foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add) := by
  have ho : sumRow.objs (.arr .long) .long = some [.long] := by
    simp [Prim.objs, sumRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == sumRow.sym) = some ⟨RowCode.sum, fun σ _ => sumAt (σ₁ σ)⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `flatRow` at `I×A ⟶ B` given `R : I ⟶ A×B` is `flatDen`. -/
theorem Prim.den_flatRow {I A B : Obj} (T : Den I (.prod A B)) :
    Prim.den flatRow (.prod I A) B [⟨I, .prod A B, T⟩] = flatDen T := by
  have ho : flatRow.objs (.prod I A) B = some [I, A, B] := by
    simp [Prim.objs, flatRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == flatRow.sym) = some ⟨RowCode.flat, fun σ =>
      Sem.one (X := σ₁ σ) (Y := .prod (σ₂ σ) (σ.getD 2 .long)) flatDen⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- `F(U)` at `[ℕ] ⟶ [ℕ]`, `U` the coreflexive on `P`: the lists whose elements are all in `P`. -/
theorem Prim.den_mapRow_corefl {TU : Den .long .long} {P : Int64 → Prop} (hU : ∀ x y, TU x y ↔ x = y ∧ P x)
    (xs ys : List Int64) :
    Prim.den mapRow (.arr .long) (.arr .long) [⟨.long, .long, TU⟩] xs ys ↔ ys = xs ∧ ∀ x ∈ xs, P x := by
  have ho : mapRow.objs (.arr .long) (.arr .long) = some [.long, .long] := by
    simp [Prim.objs, mapRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == mapRow.sym) = some ⟨RowCode.map, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ)
      fun T (xs : List (σ₁ σ).El) (ys : List (σ₂ σ).El) => ys.length = xs.length ∧
        ∀ t (ht : t < xs.length) (ht' : t < ys.length), T (xs[t]'ht) (ys[t]'ht')⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one, σ₁, σ₂, List.headD, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, dite_true, and_self]
  simp only [hU]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨List.ext_getElem hl fun t h1 h2 => (h t h2 h1).1.symm, fun x hx => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    exact (h t ht (by omega)).2
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, fun t ht _ => ⟨rfl, h _ (List.getElem_mem ht)⟩⟩

/-- **The definition built is its read-back cut**: where `c` reads `d` back (`Tm.dfnCut?`), and the universes
    `c.u₀`, `c.u` are the coreflexive on `P` — every number (an unbounded object's `𝟙`) or an initial segment
    `0…k` — `d` means `c.cut`, the fused row cut to the universe; at `𝟙` it means `c.fused`, the fused row. On every
    source a run holds (`Short`): the count of a list of `2^63` elements or more wraps in the fused row, not in
    the definition. -/
theorem Tm.dfnCut_den {A B : Obj} {d : Tm A B} (c : DfnCut d) (ρ : Val)
    {P : Int64 → Prop} (hP : (∀ x, P x) ∨ InitSeg P)
    (hUs : ∀ u₀ u, c.uni = some (u₀, u) → (∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) ∧ ∀ x y, u.den ρ x y ↔ x = y ∧ P x)
    (x : A.El) (hx : Short A x) (w : B.El) :
    (d.den ρ x w ↔ c.cut.den ρ x w) ∧ ((∀ x, P x) → (d.den ρ x w ↔ c.fused.den ρ x w)) := by
  cases c with
  | flat R =>
    -- `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂` is `flatDen` (`Tm.flat_den`), the row's meaning at every object
    have hd := congrFun (congrFun (Tm.flat_den ρ R) x) w
    simp only [DfnCut.cut, DfnCut.fused, Tm.den, Tm.argDen, Prim.den_flatRow] at hd ⊢
    exact ⟨hd.to_iff, fun _ => hd.to_iff⟩
  | length u₀ u =>
    -- `⦇[0, π₁ succ]⦈`: the counts `0…n` rise from `0`, so all are in `P` iff `n` is
    obtain ⟨hU₀, hU⟩ := hUs u₀ u rfl
    have hd := count_iff (zeroTm_den u₀ ρ hU₀) hU x hx w
    simp only [Tm.den, DfnCut.cut, DfnCut.fused, Prim.den_lengthRow]
    rw [hd]
    have hx : x.length < 2 ^ 63 := hx
    have hc : (∀ t ≤ x.length, P (Int64.ofNat t)) ↔ P (Int64.ofNat x.length) :=
      chain_in hP Int64.ofNat x.length fun _ => ⟨by decide, fun t ht => by
        rw [Int64.toInt_ofNat_of_lt (by omega), Int64.toInt_ofNat_of_lt (by omega)]; omega⟩
    refine ⟨⟨fun ⟨hp, hw⟩ => Exists.intro _ ⟨rfl, (hU _ _).2 ⟨hw.symm, hc.1 hp⟩⟩, ?_⟩,
      fun hall => ⟨fun h => h.2, fun h => ⟨fun _ _ => hall _, h⟩⟩⟩
    rintro ⟨b, rfl, hbw⟩
    obtain ⟨hw, hp⟩ := (hU _ _).1 hbw
    exact ⟨hc.2 hp, hw.symm⟩
  | sum u₀ u =>
    -- `⦇[0, plus]⦈`: `plus_iff` reads the fold kept in the universe as the row cut to it
    obtain ⟨hU₀, hU⟩ := hUs u₀ u rfl
    simp only [Tm.den, Tm.argDen, DfnCut.cut, DfnCut.fused, Prim.den_sumRow]
    rw [foldDen_start]
    simp only [zeroTm_den u₀ ρ hU₀]
    rw [plus_iff hP hU]
    refine ⟨⟨fun ⟨hE, hw, hf⟩ => ⟨w, ⟨x, (Prim.den_mapRow_corefl hU x x).2 ⟨rfl, hE⟩, hf⟩, (hU _ _).2 ⟨rfl, hw⟩⟩,
      fun ⟨w', ⟨y, hy, hf⟩, hw⟩ => ?_⟩, fun hall => ⟨fun h => h.2.2, fun h => ⟨fun _ _ => hall _, hall _, h⟩⟩⟩
    obtain ⟨rfl, hE⟩ := (Prim.den_mapRow_corefl hU x y).1 hy
    obtain ⟨rfl, hPw⟩ := (hU _ _).1 hw
    exact ⟨hE, hPw, hf⟩

/-- **The rows of `dfns` are those of `DfnCut`** (`lengthRow`, `sumRow`, `flatRow`), whose replacement
    `Tm.dfnCut_den` proves: a row given a definition that is not one of them fails here. -/
theorem Prim.dfn_read : dfns.map (·.1) = [lengthRow.sym, sumRow.sym, flatRow.sym] := rfl

end Rel.Lang
