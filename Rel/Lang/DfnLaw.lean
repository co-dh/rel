import Rel.Lang.GenKFold
import Rel.RepTabArith
import Rel.KernelSpec.Elementwise
import Rel.Run.Lang.Elab

/-! A row with a definition (`Prim.dfn`) is its definition's fused form (§4). `build` replaces the definition it
    built by the form `Tm.dfnCut?` reads it back to: the fused row at an unbounded object, the fused row cut to the
    universe at an initial segment `0…k`. `Tm.dfnCut_den` proves each replacement means the definition, from one
    fact (`chain_in`): a fold from `0` whose step never decreases the value leaves `0…k` only at its result.
    `Prim.dfn_read` enumerates the rows of `prims` with a definition and fails on one `Tm.dfnCut?` does not read. -/

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

/-- The right fold peeled at its head: a chain on `x :: xs` is one on `xs` to `v`, then one step `TS (x, v)`. -/
theorem foldrDen_cons {E V : Obj} (Te : Den V V) (TS : Den (.prod E V) V) (x : E.El) (xs : List E.El)
    (w : V.El) : foldrDen Te TS (x :: xs) w ↔ ∃ v, foldrDen Te TS xs v ∧ TS (x, v) w := by
  constructor
  · rintro ⟨_ | ⟨w', ys⟩, hy, ⟨a, ha⟩, hS, rfl⟩
    · simp at hy
    · simp only [List.length_cons, Nat.add_right_cancel_iff] at hy
      exact ⟨ys[0]'(by omega), ⟨ys, hy, ⟨a, by simpa using ha⟩,
        fun t ht => by simpa using hS (t + 1) (by simp; omega), rfl⟩, by simpa using hS 0 (by simp)⟩
  · rintro ⟨v, ⟨ys, hy, ⟨a, ha⟩, hS, rfl⟩, h⟩
    refine ⟨w :: ys, by simp [hy], ⟨a, by simpa using ha⟩, fun t ht => ?_, rfl⟩
    cases t with
    | zero => simpa using h
    | succ t => simpa using hS t (by simpa using ht)

/-- The base `0` (`zeroTm`): its values are `0`, where `0` is in its universe. -/
theorem zeroTm_den (u₀ : Tm .long .long) (ρ : Val) {P : Int64 → Prop} (hU : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x)
    (v : Int64) : (∃ a, (zeroTm u₀).den ρ a v) ↔ v = 0 ∧ P 0 := by
  simp only [zeroTm, Tm.den, Core.Rel.inter, Core.Rel.comp, Core.Rel.rpair, Core.Rel.id]
  constructor
  · rintro ⟨a, ⟨⟨a1, a2⟩, ⟨h1, h2⟩, hA⟩, rfl⟩
    dsimp only at h1 h2
    subst h1 h2
    obtain ⟨-, -, v', ⟨hv, hn, -⟩, hv'⟩ := (arithDen_iff _ _ _ _).1 hA
    obtain ⟨rfl, hPa⟩ := (hU _ _).1 hv'
    rw [Rel.Verify.Ew.intStep_sub] at hv
    split at hv
    · exact absurd hv hn
    rw [Int64.sub_self] at hv
    subst hv
    exact ⟨rfl, hPa⟩
  · rintro ⟨rfl, h0⟩
    have hu : u₀.den ρ 0 0 := (hU _ _).2 ⟨rfl, h0⟩
    exact ⟨0, ⟨(0, 0), ⟨rfl, rfl⟩, (arithDen_iff _ _ _ _).2 ⟨⟨0, hu⟩, ⟨0, hu⟩, 0, by decide, hu⟩⟩, rfl⟩

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

/-- The integer sum of a list's suffix from `t`. -/
abbrev sufI (xs : List Int64) (t : Nat) : Int := (List.map Int64.toInt (List.drop t xs)).sum

/-- A wrapping sum whose every suffix sum is in range is the integer sum. -/
theorem toInt_foldr_add (xs : List Int64)
    (h : ∀ t, t ≤ xs.length → -2 ^ 63 < sufI xs t ∧ sufI xs t < 2 ^ 63) :
    (xs.foldr (· + ·) 0).toInt = (xs.map Int64.toInt).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ih := ih fun t ht => by simpa [sufI] using h (t + 1) (by simp; omega)
    have h0 := h 0 (by simp)
    simp only [sufI, List.drop_zero, List.map_cons, List.sum_cons] at h0
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, Int64.toInt_add, ih, Int.bmod]
    split <;> omega

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

/-- `sum`'s meaning (`rowDens`): every suffix sum in range, no null element, the wrapping sum. -/
abbrev sumDen (xs : List Int64) (w : Int64) : Prop :=
  (∀ t, t ≤ xs.length → -2 ^ 63 < sufI xs t ∧ sufI xs t < 2 ^ 63) ∧ (∀ x ∈ xs, x ≠ Alg.nul) ∧
    w = xs.foldr (· + ·) 0

/-- The definition `⦇[0, plus]⦈ʳ` of `sum` on `TU` from the value `0`, `0` in `TU`: its elements and every suffix sum
    in `TU`, and `sum`'s meaning. -/
theorem plus_iff {TU : Den .long .long} {P : Int64 → Prop} (hU : ∀ x y, TU x y ↔ x = y ∧ P x) (h0 : P 0) :
    ∀ (xs : List Int64) (w : Int64),
      foldrDen (E := .long) (V := .long) (fun _ b => b = 0) (arithDen Ew.add TU) xs w ↔
        (∀ x ∈ xs, P x) ∧ (∀ t ≤ xs.length, P ((xs.drop t).foldr (· + ·) 0)) ∧ sumDen xs w := by
  have hd : ∀ x, (∃ v, TU x v) ↔ P x := fun x =>
    ⟨fun ⟨_, h⟩ => ((hU _ _).1 h).2, fun h => ⟨x, (hU _ _).2 ⟨rfl, h⟩⟩⟩
  intro xs
  induction xs with
  | nil =>
    intro w
    rw [foldrDen_nil]
    constructor
    · rintro rfl
      exact ⟨by simp, fun t _ => by simpa using h0, fun t _ => by simp [sufI], by simp, rfl⟩
    · rintro ⟨-, -, -, -, rfl⟩; rfl
  | cons x xs ih =>
    intro w
    have hA : ∀ v, arithDen Ew.add TU (x, v) w ↔ P x ∧ P v ∧ (x ≠ Alg.nul ∧ v ≠ Alg.nul ∧
        -2 ^ 63 < x.toInt + v.toInt ∧ x.toInt + v.toInt < 2 ^ 63 ∧ w = x + v) ∧ P w := fun v => by
      rw [arithDen_iff]
      constructor
      · rintro ⟨h1, h2, v', hs, hv⟩
        obtain ⟨rfl, hw⟩ := (hU _ _).1 hv
        exact ⟨(hd _).1 h1, (hd _).1 h2, (stepDen_add_iff _ _ _).1 hs, hw⟩
      · rintro ⟨h1, h2, hs, hw⟩
        exact ⟨(hd _).2 h1, (hd _).2 h2, w, (stepDen_add_iff _ _ _).2 hs, (hU _ _).2 ⟨rfl, hw⟩⟩
    rw [foldrDen_cons]
    simp only [ih, hA]
    constructor
    · rintro ⟨v, ⟨hE, hT, hr, hn, rfl⟩, hx, -, ⟨hxn, -, hl, hu, rfl⟩, hPw⟩
      have hI := toInt_foldr_add xs hr
      refine ⟨fun y hy => ?_, fun t ht => ?_, fun t ht => ?_, fun y hy => ?_, rfl⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hx
        · exact hE y hy
      · cases t with
        | zero => simpa using hPw
        | succ t => simpa using hT t (by simpa using ht)
      · cases t with
        | zero => simp only [sufI, List.drop_zero, List.map_cons, List.sum_cons]; rw [← hI]; omega
        | succ t => simpa [sufI] using hr t (by simpa using ht)
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hxn
        · exact hn y hy
    · rintro ⟨hE, hT, hr, hn, rfl⟩
      have hr' : ∀ t, t ≤ xs.length → -2 ^ 63 < sufI xs t ∧ sufI xs t < 2 ^ 63 := fun t ht => by
        simpa [sufI] using hr (t + 1) (by simp; omega)
      have hI := toInt_foldr_add xs hr'
      have hr0 := hr 0 (by simp)
      simp only [sufI, List.drop_zero, List.map_cons, List.sum_cons] at hr0
      have hnul : Alg.nul.toInt = -2 ^ 63 := by decide
      have hvn : xs.foldr (· + ·) 0 ≠ Alg.nul := fun e => by
        have := congrArg Int64.toInt e; rw [hI, hnul] at this
        have := hr' 0 (by simp); simp only [sufI, List.drop_zero] at this; omega
      exact ⟨_, ⟨fun y hy => hE y (List.mem_cons_of_mem _ hy), fun t ht => by simpa using hT (t + 1) (by simp; omega),
        hr', fun y hy => hn y (List.mem_cons_of_mem _ hy), rfl⟩, hE x List.mem_cons_self,
        by simpa using hT 1 (by simp), ⟨hn x List.mem_cons_self, hvn, by rw [hI]; omega, by rw [hI]; omega, rfl⟩,
        by simpa using hT 0 (by simp)⟩

/-- `lengthRow` at `[E] ⟶ ℕ` is the count of its list. -/
theorem Prim.den_lengthRow {E : Obj} :
    Prim.den lengthRow (.arr E) .long [] = fun (xs : List E.El) w => w = Int64.ofNat xs.length := by
  have ho : lengthRow.objs (.arr E) .long = some [E, .long] := by
    simp [Prim.objs, lengthRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == lengthRow.sym) =
      some ⟨RowCode.length, fun _ _ xs w => w = Int64.ofNat xs.length⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `sumRow` at `[ℕ] ⟶ ℕ` is `sumDen`. -/
theorem Prim.den_sumRow : Prim.den sumRow (.arr .long) .long [] = sumDen := by
  have ho : sumRow.objs (.arr .long) .long = some [.long] := by
    simp [Prim.objs, sumRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == sumRow.sym) = some ⟨RowCode.sum, fun _ _ (xs : List Int64) (w : Int64) =>
      (∀ t, t ≤ xs.length → -2 ^ 63 < List.sum (List.map Int64.toInt (List.drop t xs)) ∧
        List.sum (List.map Int64.toInt (List.drop t xs)) < 2 ^ 63) ∧ (∀ x ∈ xs, x ≠ Alg.nul) ∧
        w = xs.foldr (· + ·) 0⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]

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
    -- `⦇[0, plus]⦈ʳ`: the suffix sums of elements of `0…k` rise from `0` to the result, so all are in it
    obtain ⟨hU₀, hU⟩ := hUs u₀ u rfl
    simp only [Tm.den, Tm.argDen, DfnCut.cut, DfnCut.fused, Prim.den_sumRow]
    rw [foldrDen_start]
    simp only [zeroTm_den u₀ ρ hU₀]
    have hsplit : ∀ k (hk : k < x.length), sufI x k = (x[k]'hk).toInt + sufI x (k + 1) := fun k hk => by
      simp only [sufI, List.drop_eq_getElem_cons hk, List.map_cons, List.sum_cons]
    constructor
    · constructor
      · rintro ⟨_, ⟨rfl, h0⟩, hf⟩
        obtain ⟨hE, hT, hs⟩ := (plus_iff hU h0 x w).1 hf
        exact Exists.intro w ⟨Exists.intro x ⟨(Prim.den_mapRow_corefl hU x x).2 ⟨rfl, hE⟩, hs⟩,
          (hU _ _).2 ⟨rfl, by rw [hs.2.2]; simpa using hT 0 (Nat.zero_le _)⟩⟩
      · rintro ⟨w', ⟨y, hy, hs⟩, hw⟩
        obtain ⟨hyx, hE⟩ := (Prim.den_mapRow_corefl hU x y).1 hy
        subst y
        obtain ⟨hww, hPw⟩ := (hU _ _).1 hw
        subst hww
        have hT : ∀ t ≤ x.length, P ((x.drop (x.length - t)).foldr (· + ·) 0) := by
          refine (chain_in hP (fun t => (x.drop (x.length - t)).foldr (· + ·) 0) x.length fun hs' => ?_).2
            (by simpa [hs.2.2] using hPw)
          have hI : ∀ t ≤ x.length, ((x.drop t).foldr (· + ·) 0).toInt = sufI x t := fun t ht =>
            toInt_foldr_add _ fun s hs'' => by
              simpa [sufI, List.drop_drop] using hs.1 (t + s) (by simp at hs''; omega)
          refine ⟨by rw [hI _ (by omega)]; simp [sufI], fun t ht => ?_⟩
          dsimp only
          rw [hI _ (by omega), hI _ (by omega)]
          have hk : x.length - (t + 1) < x.length := by omega
          have e := hsplit _ hk
          have := hs'.1 _ (hE _ (List.getElem_mem hk))
          rw [show x.length - t = x.length - (t + 1) + 1 by omega]
          omega
        have h0 : P 0 := by simpa using hT 0 (Nat.zero_le _)
        exact ⟨0, ⟨rfl, h0⟩, (plus_iff hU h0 x _).2 ⟨hE, fun t ht => by
          simpa [show x.length - (x.length - t) = t by omega] using hT (x.length - t) (by omega), hs⟩⟩
    · intro hall
      have h0 := hall 0
      constructor
      · rintro ⟨_, ⟨rfl, -⟩, hf⟩
        exact ((plus_iff hU h0 x w).1 hf).2.2
      · intro hs
        exact ⟨0, ⟨rfl, h0⟩, (plus_iff hU h0 x w).2 ⟨fun _ _ => hall _, fun _ _ => hall _, hs⟩⟩

/-- **The rows of `dfns` are those of `DfnCut`** (`lengthRow`, `sumRow`, `flatRow`), whose replacement
    `Tm.dfnCut_den` proves: a row given a definition that is not one of them fails here. -/
theorem Prim.dfn_read : dfns.map (·.1) = [lengthRow.sym, sumRow.sym, flatRow.sym] := rfl

end Rel.Lang
