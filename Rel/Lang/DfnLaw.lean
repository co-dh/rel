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

/-- `P` an initial segment `0…k` of ℕ at the object `B`: `InitSeg` at `i64`, the atom ℕ is stored at; none elsewhere. -/
def Seg : (B : Obj) → (B.El → Prop) → Prop
  | .atom .i64, P => InitSeg P
  | _, _ => False

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

/-- `zeroCol t` holds `t`'s word `0`. -/
theorem zeroCol_row {t : QAtomicType} (h : t.ordNum.isSome) (i : Fin (1 : USize).toNat) :
    Vals.row (A := .atom t) (zeroCol t h) i = QAtomicType.ofBits t 0 := by
  obtain ⟨w, hw⟩ : ∃ w, t.width = some w := by cases t <;> first | exact ⟨_, rfl⟩ | exact absurd h (by decide)
  have hu : t ≠ .u1 := by rintro rfl; exact absurd h (by decide)
  have h0 := (Rel.Verify.wordsFoR_closed #[(0 : UInt64)] (n := 1) (by simp)).2.1
  have hi : i.1 = 0 := by have := i.2; simp at this; omega
  rw [Vals.row_atom, Arr.get_word _ h]
  congr 1
  simp only [zeroCol, Arr.mk, Arr.enc, wordsFoR] at h0 ⊢
  rw [Rel.Verify.raw_foR .i64 8 rfl (by decide)] at h0
  rw [Rel.Verify.raw_foR t w hw hu]
  generalize Column.foRBits _ _ _ = f at h0 ⊢
  have hf : f 0 = 0 := by
    have := congrArg (·[0]?) h0
    simpa [Rel.Verify.ofNat_toNat_mod64] using this
  simp [hi, hf]

/-- The base `0` (`zeroTm`): its values are the word `0` of the atom, where it is in its universe. -/
theorem zeroTm_den {t : QAtomicType} (h : t.ordNum.isSome) (u₀ : Tm (.atom t) (.atom t)) (ρ : Val)
    {P : (Obj.atom t).El → Prop} (hU : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) (v : (Obj.atom t).El) :
    (∃ a, (zeroTm h u₀).den ρ a v) ↔ v = QAtomicType.ofBits t 0 ∧ P (QAtomicType.ofBits t 0) := by
  simp only [zeroTm, ↓Tm.ran_den, Tm.ran_den, Tm.den, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, Core.Rel.id, hU,
    zeroCol_row]
  constructor
  · rintro ⟨a, rfl, b, ⟨_, ⟨rfl, hb⟩, _, rfl, -⟩, _, -, _, -, hv⟩
    exact ⟨hv, hb⟩
  · rintro ⟨rfl, h0⟩
    exact ⟨_, rfl, _, ⟨_, ⟨rfl, h0⟩, ⟨0, by simp⟩, rfl, rfl⟩, _, ⟨rfl, h0⟩, ⟨0, by simp⟩, rfl, rfl⟩

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
theorem count_iff {E : Obj} {Te TU : Core.Rel (Obj.El .long) (Obj.El .long)} {P : Int64 → Prop}
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
  have hS : ∀ a x b, (graph Prod.fst ≫ succDen TU : Core.Rel (Obj.El (.prod .long E)) (Obj.El .long)) (a, x) b ↔
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

/-- **The definition `⦇[0, plus]⦈` of `sum` on `TU` from the word `0` is `sum`'s fold kept in `TU`**, at any atom
    `t`, `P` every value or an initial segment `0…k`: its elements and result in `P` and `stepAt t add` folded from
    `0`. At every value nothing is cut; on `0…k` the prefix sums of its elements rise from `0` to the result
    (`chain_in`), so all are in `P` iff it is. -/
theorem plus_iff {t : QAtomicType} {TU : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))} {P : (Obj.atom t).El → Prop}
    (hP : (∀ x, P x) ∨ Seg (.atom t) P) (hU : ∀ x y, TU x y ↔ x = y ∧ P x) (xs : List (Obj.atom t).El)
    (w : (Obj.atom t).El) :
    (∃ v, (v = QAtomicType.ofBits t 0 ∧ P (QAtomicType.ofBits t 0)) ∧
        foldDen (E := .atom t) (V := .atom t) (fun _ b => b = v) (arithDen t Ew.add TU) xs w) ↔
      (∀ x ∈ xs, P x) ∧ P w ∧
        foldDen (E := .atom t) (V := .atom t) (fun _ b => b = QAtomicType.ofBits t 0) (stepAt t Ew.add) xs w := by
  have hd : ∀ x, (∃ v, TU x v) ↔ P x := fun x =>
    ⟨fun ⟨_, h⟩ => ((hU _ _).1 h).2, fun h => ⟨x, (hU _ _).2 ⟨rfl, h⟩⟩⟩
  have hA : ∀ a x b, arithDen t Ew.add TU (a, x) b ↔ P a ∧ P x ∧ stepAt t Ew.add (a, x) b ∧ P b := fun a x b => by
    rw [arithDen_iff]
    constructor
    · rintro ⟨h1, h2, v', hs, hv⟩; obtain ⟨rfl, hw⟩ := (hU _ _).1 hv; exact ⟨(hd _).1 h1, (hd _).1 h2, hs, hw⟩
    · rintro ⟨h1, h2, hs, hw⟩; exact ⟨(hd _).2 h1, (hd _).2 h2, b, hs, (hU _ _).2 ⟨rfl, hw⟩⟩
  constructor
  · rintro ⟨_, ⟨rfl, h0⟩, hf⟩
    obtain ⟨g, hg0, hs, rfl⟩ := (foldDen_iter (X := .atom t) (Y := .atom t) _ xs _ w).1 hf
    have hs := fun s hs' => (hA _ _ _).1 (hs s hs')
    refine ⟨fun x hx => ?_, ?_, (foldDen_iter (X := .atom t) (Y := .atom t) _ xs _ _).2
      ⟨g, hg0, fun s hs' => (hs s hs').2.2.1, rfl⟩⟩
    · obtain ⟨s, hs', rfl⟩ := List.getElem_of_mem hx; exact (hs s hs').2.1
    · rcases Nat.eq_zero_or_pos xs.length with e | e
      · rw [e, hg0]; exact h0
      · have := (hs (xs.length - 1) (by omega)).2.2.2; rwa [show xs.length - 1 + 1 = xs.length by omega] at this
  · rintro ⟨hE, hw, hf⟩
    obtain ⟨g, hg0, hs, rfl⟩ := (foldDen_iter (X := .atom t) (Y := .atom t) _ xs _ w).1 hf
    have hP' : ∀ s ≤ xs.length, P (g s) := by
      rcases hP with hall | hseg
      · exact fun s _ => hall _
      cases t <;> first | exact (hseg : False).elim | skip
      exact (chain_in (.inr hseg) g xs.length fun hI => ⟨by rw [hg0]; decide, fun s hs' => by
        obtain ⟨-, -, h1, h2, e⟩ := (stepDen_add_iff _ _ _).1 (hs s hs')
        have := hI.1 _ (hE _ (List.getElem_mem hs'))
        rw [e, Int64.toInt_add]; simp only [Int.bmod]; split <;> omega⟩).2 hw
    refine ⟨_, ⟨rfl, hg0 ▸ hP' 0 (Nat.zero_le _)⟩, (foldDen_iter (X := .atom t) (Y := .atom t) _ xs _ _).2
      ⟨g, hg0, fun s hs' => (hA _ _ _).2 ⟨hP' s (by omega), hE _ (List.getElem_mem hs'), hs s hs', hP' (s + 1) (by omega)⟩,
        rfl⟩⟩

/-- `lengthRow` at `[E] ⟶ ℕ` is the count of its list. -/
theorem Prim.den_lengthRow {E : Obj} :
    Prim.den lengthRow (.arr E) .long [] = fun (xs : List E.El) w => w = Int64.ofNat xs.length := by
  have ho : ∀ ps, lengthRow.objs (.arr E) .long ps = some [E, .long] := by
    simp [Prim.objs, Option.orElse, lengthRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == lengthRow.sym) =
      some ⟨RowCode.length, fun _ _ xs w => w = Int64.ofNat xs.length⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `sumRow` at `[t] ⟶ t` is `sumAt`'s fold of `stepAt t add` from the word `0`. -/
theorem Prim.den_sumRow {t : QAtomicType} : Prim.den sumRow (.arr (.atom t)) (.atom t) [] =
    foldDen (E := .atom t) (V := .atom t) (fun _ b => b = QAtomicType.ofBits t 0) (stepAt t Ew.add) := by
  have ho : ∀ ps, sumRow.objs (.arr (.atom t)) (.atom t) ps = some [.atom t] := by
    simp [Prim.objs, Option.orElse, sumRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == sumRow.sym) = some ⟨RowCode.sum, fun σ _ => sumAt (σ₁ σ)⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `flatRow` at `I×A ⟶ B` given `R : I ⟶ A×B` is `flatDen`. -/
theorem Prim.den_flatRow {I A B : Obj} (T : Core.Rel (Obj.El I) (Obj.El (.prod A B))) :
    Prim.den flatRow (.prod I A) B [⟨I, .prod A B, T⟩] = flatDen T := by
  have ho : ∀ ps, flatRow.objs (.prod I A) B ps = some [I, A, B] := by
    simp [Prim.objs, Option.orElse, flatRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == flatRow.sym) = some ⟨RowCode.flat, fun σ =>
      Sem.one (X := σ₁ σ) (Y := .prod (σ₂ σ) (σ.getD 2 .long)) flatDen⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- `foldIRow` at `I×[E] ⟶ V` given `e : I ⟶ V×V`, `S : (I×V)×E ⟶ I×V` is `foldIDen`. -/
theorem Prim.den_foldIRow {I E V : Obj} (Te : Core.Rel (Obj.El I) (Obj.El (.prod V V))) (TS : Core.Rel (Obj.El (.prod (.prod I V) E)) (Obj.El (.prod I V))) :
    Prim.den foldIRow (.prod I (.arr E)) V [⟨I, .prod V V, Te⟩, ⟨.prod (.prod I V) E, .prod I V, TS⟩] =
      foldIDen Te TS := by
  have ho : ∀ ps, foldIRow.objs (.prod I (.arr E)) V ps = some [I, V, E] := by
    simp [Prim.objs, Option.orElse, foldIRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == foldIRow.sym) = some ⟨RowCode.foldI, fun σ =>
      Sem.two (X := σ₁ σ) (Y := .prod (σ₂ σ) (σ₂ σ)) (X₂ := .prod (.prod (σ₁ σ) (σ₂ σ)) (σ.getD 2 .long))
        (Y₂ := .prod (σ₁ σ) (σ₂ σ)) foldIDen⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.two]; exact dif_pos ⟨rfl, rfl, rfl, rfl⟩

/-- `F(U)` at `[V] ⟶ [V]`, `U` the coreflexive on `P`: the lists whose elements are all in `P`. -/
theorem Prim.den_mapRow_corefl {V : Obj} {TU : Core.Rel (Obj.El V) (Obj.El V)} {P : V.El → Prop} (hU : ∀ x y, TU x y ↔ x = y ∧ P x)
    (xs ys : List V.El) :
    Prim.den mapRow (.arr V) (.arr V) [⟨V, V, TU⟩] xs ys ↔ ys = xs ∧ ∀ x ∈ xs, P x := by
  have ho : ∀ ps, mapRow.objs (.arr V) (.arr V) ps = some [V, V] := by
    simp [Prim.objs, Option.orElse, mapRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
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
    {P : B.El → Prop} (hP : (∀ x, P x) ∨ Seg B P)
    (hUs : ∀ u₀ u, c.uni = some (u₀, u) → (∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) ∧ ∀ x y, u.den ρ x y ↔ x = y ∧ P x)
    (x : A.El) (hx : Short A x) (w : B.El) :
    (d.den ρ x w ↔ c.cut.den ρ x w) ∧ ((∀ x, P x) → (d.den ρ x w ↔ c.fused.den ρ x w)) := by
  cases c with
  | flat R =>
    -- `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂` is `flatDen` (`Tm.flat_den`), the row's meaning at every object
    have hd := congrFun (congrFun (Tm.flat_den ρ R) x) w
    simp only [DfnCut.cut, DfnCut.fused, ↓Tm.dom_den, Tm.dom_den, Tm.den, Tm.argDen, Prim.den_flatRow] at hd ⊢
    exact ⟨hd.to_iff, fun _ => hd.to_iff⟩
  | foldI e S =>
    -- `(π₁π₁° ∩ π₂⦇ran⟨𝟙,eπ₂⟩, S ∩ π₁π₁π₁°⦈)π₂` is `foldIDen` (`foldIDen_eq`), the row's meaning at every object
    have hd := congrFun (congrFun (foldIDen_eq (e.den ρ) (S.den ρ)).symm x) w
    simp only [DfnCut.cut, DfnCut.fused, ↓Tm.ran_den, Tm.ran_den, Tm.den, Tm.argDen, Prim.den_foldIRow] at hd ⊢
    exact ⟨hd.to_iff, fun _ => hd.to_iff⟩
  | dom R =>
    -- `⟨𝟙,R⟩π₁` keeps `a` with some `b` of `R`: `𝟙 ∩ R R°` (`Prim.den_domRow`), the row's meaning at every object
    have hd : (Tm.comp (.pair .id R) .outl).den ρ x w ↔ (Tm.dom R).den ρ x w := by
      simp only [Tm.dom, Tm.den, Tm.argDen, Prim.den_domRow, Core.Rel.comp, Core.Rel.rpair, Core.Rel.inter,
        Core.Rel.recip, Core.Rel.graph, Core.Rel.id]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨rfl, hb⟩, rfl⟩; exact ⟨rfl, b, hb, hb⟩
      · rintro ⟨rfl, b, hb, -⟩; exact ⟨(x, b), ⟨rfl, hb⟩, rfl⟩
    exact ⟨hd, fun _ => hd⟩
  | ran R =>
    -- `dom(R°)` is `𝟙 ∩ R° R°°` (`Prim.den_domRow` at `R°`), `ranRow`'s meaning (`Prim.den_ranRow`)
    have hd : (Tm.dom (.conv R)).den ρ x w ↔ (Tm.ran R).den ρ x w := by
      simp only [Tm.dom, Tm.ran, Tm.den, Tm.argDen, Prim.den_domRow, Prim.den_ranRow]
    exact ⟨hd, fun _ => hd⟩
  | @nil _ E =>
    -- `Λ(𝟘)` maps every source to the list of no elements, `[]` (`Prim.den_nilRow`)
    have hd : (Tm.lam .zero : Tm A (.arr E)).den ρ x w ↔ (Tm.nil : Tm A (.arr E)).den ρ x w := by
      simp only [Tm.nil, Tm.den, Prim.den_nilRow, lamDen, nilDen]
      constructor
      · rintro ⟨-, h⟩; exact List.eq_nil_iff_forall_not_mem.2 fun b hb => (h b).1 hb
      · rintro rfl; exact ⟨List.Pairwise.nil, fun b => iff_of_false (List.not_mem_nil) fun h => h⟩
    exact ⟨hd, fun _ => hd⟩
  | est Q =>
    -- `∈ \ (Q ∪ 𝟙)°` at `w` under `w ∈ x`: every `c` of `x` has `w Q c` or is `w`, `estDen` of `τ(Q)` read on its
    -- diagonal; the universes `𝟙` drop out since `x` has the column `w`
    have hτ : ∀ a b, (pairTest Q).den ρ (a, b) (a, b) ↔ Q.den ρ a b := fun a b => by
      simp [pairTest, Tm.dom_den, Tm.den, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.graph, Core.Rel.id]
    have hd : (Tm.meet .mem (.ldiv (.conv .mem) (.conv (.join Q .id)) .id .id) : Tm (.arr B) B).den ρ x w ↔
        (Tm.est (pairTest Q)).den ρ x w := by
      rw [Tm.est_den]
      simp only [Tm.den, ldivDen, estDen, hτ, Core.Rel.inter, Core.Rel.recip, Core.Rel.union, Core.Rel.id]
      constructor
      · rintro ⟨hw, hall, -⟩
        exact ⟨hw, fun ⟨c, hc, hne, hq⟩ => (hall c hc).elim hq fun h => hne h.symm⟩
      · rintro ⟨hw, hn⟩
        refine ⟨hw, fun c hc => (Classical.em (Q.den ρ w c)).elim Or.inl fun hq =>
          Or.inr (Classical.byContradiction fun hne => hn ⟨c, hc, fun h => hne h.symm, hq⟩), Or.inl ⟨w, hw⟩⟩
    exact ⟨hd, fun _ => hd⟩
  | @front E Q =>
    -- `∋ − ∋ (Q − Q°)` keeps `c` of `x` that no `b` of `x` beats strictly, `frontDen` of `τ(Q)` on its diagonal
    have hτ : ∀ a b, (pairTest Q).den ρ (a, b) (a, b) ↔ Q.den ρ a b := fun a b => by
      simp [pairTest, Tm.dom_den, Tm.den, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.graph, Core.Rel.id]
    have hd : (Tm.lam (.diff .mem (.comp .mem (.diff Q (.conv Q)))) : Tm (.arr E) (.arr E)).den ρ x w ↔
        (Tm.front (pairTest Q)).den ρ x w := by
      rw [Tm.front_den]
      simp only [Tm.den, frontDen, lamDen, diffDen, hτ, Core.Rel.comp, Core.Rel.recip]
    exact ⟨hd, fun _ => hd⟩
  | length u₀ u =>
    -- `⦇[0, π₁ succ]⦈`: the counts `0…n` rise from `0`, so all are in `P` iff `n` is
    obtain ⟨hU₀, hU⟩ := hUs u₀ u rfl
    have hd := count_iff (zeroTm_den (t := .i64) rfl u₀ ρ hU₀) hU x hx w
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
  | sum h u₀ u =>
    -- `⦇[0, plus]⦈`: `plus_iff` reads the fold kept in the universe as the row cut to it
    obtain ⟨hU₀, hU⟩ := hUs u₀ u rfl
    simp only [Tm.den, Tm.argDen, DfnCut.cut, DfnCut.fused, Prim.den_sumRow]
    rw [foldDen_start]
    simp only [zeroTm_den h u₀ ρ hU₀]
    rw [plus_iff hP hU]
    refine ⟨⟨fun ⟨hE, hw, hf⟩ => ⟨w, ⟨x, (Prim.den_mapRow_corefl hU x x).2 ⟨rfl, hE⟩, hf⟩, (hU _ _).2 ⟨rfl, hw⟩⟩,
      fun ⟨w', ⟨y, hy, hf⟩, hw⟩ => ?_⟩, fun hall => ⟨fun h => h.2.2, fun h => ⟨fun _ _ => hall _, hall _, h⟩⟩⟩
    obtain ⟨rfl, hE⟩ := (Prim.den_mapRow_corefl hU x y).1 hy
    obtain ⟨rfl, hPw⟩ := (hU _ _).1 hw
    exact ⟨hE, hPw, hf⟩


/-! ### Keyed lifting (§e): the law `Prim.keyLift` claims -/

/-- `r` commutes with keying: at the objects `I×v`, given each family `F` keyed, `⟨π₁,Fᴵ⟩` (`keyOf`), it means the
    keyed family of its meaning at each key `i` given the fibres `F i`. What `appliedRowL` needs to run `r` once on
    the keyed families of a program in place of once per key. -/
def Prim.KeyLifts (r : Prim) : Prop :=
  ∀ (I A B : Obj) (fs : List ((X : Obj) × (Y : Obj) × (I.El → Core.Rel (Obj.El X) (Obj.El Y)))),
    Prim.den r (.prod I A) (.prod I B) (fs.map fun ⟨X, Y, F⟩ => ⟨.prod I X, .prod I Y, keyOf F⟩) =
      keyOf fun i => Prim.den r A B (fs.map fun ⟨X, Y, F⟩ => ⟨X, Y, F i⟩)

/-- `star(R) ≜ μX : 𝟙 ∪ R X` commutes with keying (`star_keyOf`); at any other arguments both sides are `𝟘`. -/
theorem Prim.starRow_keyLifts : starRow.KeyLifts := by
  intro I A B fs
  have hf : rowDens.find? (·.1.sym == starRow.sym) = some ⟨RowCode.star, fun σ =>
      Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => Core.Rel.mu fun X => 𝟙 _ ∪ T ≫ X⟩ := rfl
  have ho : ∀ C D ps, starRow.objs C D ps = if D = C then some [C] else none := fun C D ps => by
    by_cases h : D = C <;> simp [h, Prim.objs, starRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups,
      List.eraseDupsBy, List.eraseDupsBy.loop, List.lookup]
  unfold Prim.den; rw [hf]; simp only [ho]
  by_cases hAB : B = A
  · subst hAB; simp only [if_true, RowCode.star, σ₁, List.headD, and_self, dite_true]
    match fs with
    | [] => exact keyOf_zero.symm
    | _ :: _ :: _ => exact keyOf_zero.symm
    | [⟨X, Y, F⟩] =>
      simp only [List.map_cons, List.map_nil, Sem.one]
      by_cases h : X = B ∧ Y = B
      · obtain ⟨rfl, rfl⟩ := h; simp only [and_self, dite_true]; exact star_keyOf F
      · simp only [Obj.prod.injEq, true_and, h, dite_false]; exact keyOf_zero.symm
  · simp only [Obj.prod.injEq, true_and, hAB, if_false]; exact keyOf_zero.symm

/-- **Every row with `keyLift` commutes with keying**: the obligations enumerated from `prims` itself, so a row that
    sets `keyLift` without a proof here fails `rfl`. -/
theorem Prim.keyLifts_ok (r : Prim) (hr : r ∈ prims) (hk : r.keyLift = true) : r.KeyLifts := by
  have e : prims.filter (·.keyLift) = [starRow] := rfl
  have h := List.mem_filter.2 ⟨hr, hk⟩
  rw [e, List.mem_singleton] at h; subst h; exact Prim.starRow_keyLifts

/-- A row given a family as `appliedRowL` runs it, on `⟨π₁,Rᴵ⟩` at `I×v`, means at each key `i` the row given the
    fibre of `R` at `i` (`Prim.keyLifts_ok`): the lifted term denotes the per-key family. -/
theorem Tm.den_keyedRow (ρ : Val) {r : Prim} (hr : r ∈ prims) (hk : r.keyLift = true) {I A B C D : Obj}
    (R : Tm I (.prod A B)) :
    (Tm.arg (.prim r : Tm (.prod I C) (.prod I D))
        (.pair .outl (.arg (.prim flatRow) R) : Tm (.prod I A) (.prod I B))).den ρ =
      keyOf fun i => Prim.den r C D [⟨A, B, fun a b => R.den ρ i (a, b)⟩] := by
  have e := Prim.keyLifts_ok r hr hk I C D [⟨A, B, fun i a b => R.den ρ i (a, b)⟩]
  simp only [List.map_cons, List.map_nil] at e
  rw [← e]
  simp only [Tm.den, Tm.argDen, Prim.den_flatRow]; rfl

end Rel.Lang
