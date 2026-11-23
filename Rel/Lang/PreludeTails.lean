module

public import Rel.Lang.PreludeRows
public import Rel.Lang.DfnLaw
public import Rel.Programs.Prelude

@[expose] public section

/-! `tails : [α] ⟶ [[α]] ≜ ⦇[nil τ, ⟨⟨π₁,π₂head⟩cons,π₂⟩cons]⦈ʳ` (`Programs/Prelude.lean`) means the row `tails`'s
    `rowDens` term, the suffixes of `xs` longest first (B10b): the definition's term is built here, `head` as
    `Tm.at0`. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The step of `tails` on `(x, acc)`, the head of `acc` read by `hd`: `(x :: hd acc) :: acc`. The prelude's body reads
    it by `call head`, `Tm.tailsDef` by `Tm.at0`; the two agree on a non-empty `acc`, the only one the fold reaches. -/
def Tm.tailsStep (B : Obj) (hd : Tm (.arr (.arr B)) (.arr B)) : Tm (.prod B (.arr (.arr B))) (.arr (.arr B)) :=
  .comp (B := .prod (.arr B) (.arr (.arr B)))
    (.pair (.comp (B := .prod B (.arr B)) (.pair .outl (.comp (B := .arr (.arr B)) .outr hd)) (.prim (rowOf "cons")))
      .outr) (.prim (rowOf "cons"))

/-- `tails` at `[B] ⟶ [[B]]`: the right fold from `nil τ` of `Tm.tailsStep` reading the head by `Tm.at0`. -/
def Tm.tailsDef (B : Obj) : Tm (.arr B) (.arr (.arr B)) :=
  .foldr (.comp (B := .arr B) .nil (.prim (rowOf "τ"))) (Tm.tailsStep B Tm.at0)

theorem Prim.den_tails {B : Obj} :
    Prim.den (rowOf "tails") (.arr B) (.arr (.arr B)) [] =
      fun xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.drop k := by
  have hs : (rowOf "tails").sig = ([], .list (.var {} "B"), .list (.list (.var {} "B"))) := rfl
  have ho : (rowOf "tails").objs (.arr B) (.arr (.arr B)) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "tails").sym) = some ⟨RowCode.tails, fun _ _ xs yss =>
      yss = (List.range (xs.length + 1)).map fun k => xs.drop k⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- The step on a non-empty `acc`, wherever `hd` reads the head of a non-empty list. -/
theorem Tm.tailsStep_den (ρ : Val) {B : Obj} (hd : Tm (.arr (.arr B)) (.arr B))
    (hhd : ∀ a as w, hd.den ρ (a :: as) w ↔ w = a) (x : B.El) (acc : List (List B.El)) (hacc : acc ≠ [])
    (w : List (List B.El)) : (Tm.tailsStep B hd).den ρ (x, acc) w ↔ w = (x :: acc.headD []) :: acc := by
  rcases acc with _ | ⟨a, as⟩
  · exact absurd rfl hacc
  simp only [Tm.tailsStep, Tm.den, Prim.den_cons, Core.Rel.comp, Core.Rel.graph, Core.Rel.rpair]
  constructor
  · rintro ⟨b, ⟨⟨b₁, ⟨h1, c, rfl, h2⟩, h3⟩, h4⟩, rfl⟩
    simp [h3, h4, h1, (hhd _ _ _).1 h2]
  · rintro rfl
    exact ⟨(x :: a, a :: as), ⟨⟨(x, a), ⟨rfl, a :: as, rfl, (hhd _ _ _).2 rfl⟩, rfl⟩, rfl⟩, rfl⟩

theorem Tm.tailsSeed_den (ρ : Val) {B : Obj} :
    (Tm.comp (B := .arr B) (A := .arr (.arr B)) Tm.nil (.prim (rowOf "τ"))).den ρ = (fun _ b => b = [[]] : Core.Rel (Obj.El (.arr (.arr B))) (Obj.El (.arr (.arr B)))) := by
  funext a v
  simp [Tm.den, Tm.nil, Prim.den_nilRow, Prim.den_tau, nilDen, Core.Rel.comp]

/-- The fold of `tails`'s step from `[[]]` lists the suffixes, longest first. -/
theorem tails_foldr {α : Type} (xs : List α) : xs.foldr (fun x acc => (x :: acc.headD []) :: acc) [[]] =
    (List.range (xs.length + 1)).map fun k => xs.drop k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldr_cons, ih, List.length_cons]
    simp [List.range_succ_eq_map, Function.comp_def]

/-- **A fold of `tails`'s step means the row**, whatever its seed `e` whose values are `[[]]` alone and whatever its
    head-reader `hd` that reads the head of a non-empty list: the step only meets the non-empty accumulators
    (`foldrDen_foldr` with the invariant `≠ []`). -/
theorem Tm.tailsFold_row (ρ : Val) {B : Obj} (e : Tm (.arr (.arr B)) (.arr (.arr B))) (hd : Tm (.arr (.arr B)) (.arr B))
    (he : ∀ v, (∃ a, e.den ρ a v) ↔ v = [[]]) (hhd : ∀ a as w, hd.den ρ (a :: as) w ↔ w = a)
    (xs : Obj.El (.arr B)) (yss : Obj.El (.arr (.arr B))) :
    (Tm.foldr e (Tm.tailsStep B hd)).den ρ xs yss ↔ Prim.den (rowOf "tails") (.arr B) (.arr (.arr B)) [] xs yss := by
  rw [Prim.den_tails]
  simp only [Tm.den]
  rw [foldrDen_start]
  simp only [he, exists_eq_left]
  exact (foldrDen_foldr (TS := (Tm.tailsStep B hd).den ρ) (I := fun a => a ≠ [])
    (f := fun x acc => (x :: acc.headD []) :: acc) (fun x a ha w => Tm.tailsStep_den ρ hd hhd x a ha w)
    (fun _ _ _ => List.cons_ne_nil _ _) xs [[]] (List.cons_ne_nil _ _) yss).trans (by rw [tails_foldr])

/-- **The definition of `tails` means the row**: the suffixes of `xs`, longest first. -/
theorem Tm.tailsDef_row (ρ : Val) {B : Obj} (xs : Obj.El (.arr B)) (yss : Obj.El (.arr (.arr B))) :
    (Tm.tailsDef B).den ρ xs yss ↔ Prim.den (rowOf "tails") (.arr B) (.arr (.arr B)) [] xs yss :=
  Tm.tailsFold_row ρ _ Tm.at0 (fun v => by rw [Tm.tailsSeed_den]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨[], h⟩⟩)
    (fun a as w => by rw [Tm.at0_den]; simp [eq_comm]) xs yss


theorem Tm.tailsDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.arr (Obj.atom .general)).inst ph σ) ((Obj.arr (Obj.arr (Obj.atom .general))).inst ph σ)}
    (ht : Rel.Programs.prelude.tails.body.instObj ph σ = .ok t') (xs yss) :
    t'.den ρ xs yss ↔ Prim.den (rowOf "tails") _ _ [] xs yss := by
  obtain rfl := Except.ok.inj ht
  refine Tm.tailsFold_row ρ _ _ ?_ ?_ xs yss
  · intro v
    simp only [Tm.den, Tm.argDen, cast_eq]
    erw [Prim.den_ranRow, Prim.den_nilRow, Prim.den_tau]
    simp only [Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, nilDen]
    have i : Fin (USize.ofNat 1).toNat := ⟨0, by simp [USize.toNat_ofNat]⟩
    constructor
    · rintro ⟨_, rfl, -, -, _, -, _, rfl, rfl⟩; rfl
    · rintro rfl
      exact ⟨_, rfl, _, ⟨_, ⟨i, rfl, rfl⟩, _, rfl, rfl⟩, _, ⟨i, rfl, rfl⟩, _, rfl, rfl⟩
  · intro a as w
    simp only [Gen.atom_zero, Tm.den, Tm.argDen, cast_eq]
    have hu : Rep.rep (Gen.relV (.atom .i64) (.atom .i64) (USize.ofNat 1) (zeroCol .i64 rfl, true)
        (zeroCol .i64 rfl, true)).fst = (Tm.uni (A := .atom .i64) (zeroCol .i64 rfl)).den ρ := by
      funext x y; apply propext
      refine (Tm.relV_den ρ (zeroCol .i64 rfl, true) (zeroCol .i64 rfl, true) x y).trans ?_
      simp only [Tm.den, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
      exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h1.symm, h2.symm⟩, fun ⟨i, h1, h2⟩ => ⟨i, h1.symm, h2.symm⟩⟩
    rw [hu]
    exact (Tm.at0_den ρ (a :: as) w).trans (by simp)

end Rel.Lang
