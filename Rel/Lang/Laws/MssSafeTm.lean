import Rel.Lang.Laws.MssSafe
import Rel.Lang.PreludeRows

/-! # `safe` and the segment sum, read through the denotation

`safe ≜ 𝟙 − dom(suffix prefix (𝟙 − dom(sum)))` keeps the lists every segment of which has a sum
(`Tm.safeG_den`); `(𝟙÷∋)E(suffix)E(IN)est(Q)` reads `IN` only at the suffixes of its argument (`Tm.outer_congr`). -/

namespace Rel.Lang
open Rel.Kernel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Prim.den_suffix {B : Obj} : Prim.den (rowOf "suffix") (.arr B) (.arr B) [] = splitDen false B.El := by
  have hs : (rowOf "suffix").sig = ([], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have ho : (rowOf "suffix").objs (.arr B) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "suffix").sym) =
      some ⟨RowCode.suffix, fun σ _ => splitDen false (σ₁ σ).El⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_prefix {B : Obj} : Prim.den (rowOf "prefix") (.arr B) (.arr B) [] = splitDen true B.El := by
  have hs : (rowOf "prefix").sig = ([], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have ho : (rowOf "prefix").objs (.arr B) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "prefix").sym) =
      some ⟨RowCode.prefix, fun σ _ => splitDen true (σ₁ σ).El⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Tm.safeG_den (ρ : Val) {B : Obj} (Sum : Tm B.arr B) (xs xs' : B.arr.El) :
    (Tm.id.diff ((Tm.prim domRow : Tm B.arr B.arr).arg
      (Tm.comp (Tm.comp (Tm.prim (rowOf "suffix") : Tm B.arr B.arr) (Tm.prim (rowOf "prefix")))
        (Tm.id.diff ((Tm.prim domRow : Tm B.arr B.arr).arg Sum))))).den ρ xs xs' ↔
      xs = xs' ∧ SumGood (Sum.den ρ) xs := by
  simp only [Tm.den, Tm.argDen, Prim.den_domRow, Prim.den_suffix, Prim.den_prefix, Core.Rel.diff, Core.Rel.comp,
    Core.Rel.inter, Core.Rel.id, Core.Rel.recip, splitDen_iff, Bool.false_eq_true, if_false, if_true]
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, fun b hb => ?_⟩
    obtain ⟨t, hp, hs⟩ := List.infix_iff_prefix_suffix.1 hb
    refine Classical.byContradiction fun hno => h ⟨rfl, b, ⟨b, ⟨t, hs, hp⟩, rfl, ?_⟩, b, ⟨t, hs, hp⟩, rfl, ?_⟩
    all_goals rintro ⟨-, c, hc, -⟩; exact hno ⟨c, hc⟩
  · rintro ⟨rfl, hg⟩
    refine ⟨rfl, ?_⟩
    rintro ⟨-, b, ⟨b1, ⟨t, ht, hp⟩, rfl, hn⟩, -⟩
    obtain ⟨w, hw⟩ := hg b1 (List.infix_iff_prefix_suffix.2 ⟨t, hp, ht⟩)
    exact hn ⟨rfl, w, hw, hw⟩

/-- The prelude's `sum` over `i64` at the universe `Ut` of its sums, as the program's `sum` call elaborates, its seed
    the one-row table `T`. -/
def Tm.sumTm (T : Tab .one (.atom .i64)) (Ut : Tm (.atom .i64) (.atom .i64)) : Tm (.arr (.atom .i64)) (.atom .i64) :=
  (Tm.call [0] `Rel.Programs.prelude.sum (some `Rel.Programs.prelude.sum.conv) []
    (Tm.fold (Tm.ran (Tm.val T)) (Tm.cut2 (arithRow "plus") (Tm.var 0)))).arg Ut

theorem Tm.sumTm_den (ρ : Val) (T : Tab .one (.atom .i64)) (Ut : Tm (.atom .i64) (.atom .i64))
    (hU : ∀ x y, Ut.den ρ x y → x = y) :
    (Tm.sumTm T Ut).den ρ = foldDen ((Tm.ran (Tm.val T)).den ρ) (arithDen .i64 Ew.add (Ut.den ρ)) := by
  simp only [Tm.sumTm, Tm.den, Tm.argDen, Val.args]
  have hv : Tm.den (Val.empty.bind 0 (Ut.den ρ)) (Tm.var 0 : Tm (.atom .i64) (.atom .i64)) = Ut.den ρ := rfl
  rw [Tm.cut2_plus_den _ (Tm.var 0) (by rw [hv]; exact hU), hv, Tm.ran_den, Tm.ran_den]
  rfl

/-- `(𝟙÷∋)E(suffix)E(IN)est(Q)` reads `IN` only at the suffixes of its argument: the term `E(IN)` is `Λ(∋ Λ(IN) est)`,
    and the set `Λ(suffix)` holds the suffixes alone. -/
theorem Tm.outer_congr (ρ : Val) {B : Obj} (EST IN1 IN2 : Tm B.arr B) (xs : B.arr.El)
    (h : ∀ s, s <:+ xs → ∀ w, IN1.den ρ s w ↔ IN2.den ρ s w) (w : B.El) :
    (Tm.comp (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix") : Tm B.arr B.arr))
      (Tm.lam (Tm.comp Tm.mem (Tm.comp (Tm.lam IN1) EST)))) EST).den ρ xs w ↔
    (Tm.comp (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix") : Tm B.arr B.arr))
      (Tm.lam (Tm.comp Tm.mem (Tm.comp (Tm.lam IN2) EST)))) EST).den ρ xs w := by
  simp only [Tm.den, Core.Rel.comp]
  refine exists_congr fun L => and_congr_left' (exists_congr fun ys => and_congr_right fun hys => ?_)
  have hs : ∀ s, s ∈ ys → s <:+ xs := fun s hs => by
    have := ((lamDen_iff _ _ _).1 hys).2 s |>.1 hs
    simpa [Prim.den_suffix, splitDen_iff] using this
  simp only [lamDen_iff]
  refine and_congr_right fun _ => forall_congr' fun b => iff_congr Iff.rfl ?_
  have hm : ∀ (ys : B.arr.arr.El) (s : B.arr.El), memDen ys s ↔ s ∈ ys := fun _ _ => Iff.rfl
  simp only [Core.Rel.comp, hm]
  refine exists_congr fun s => and_congr_right fun hsm => exists_congr fun L' => and_congr_left' ?_
  rw [lamDen_iff, lamDen_iff]
  exact and_congr_right fun _ => forall_congr' fun b' => iff_congr Iff.rfl (h s (hs s hsm) b')

end Rel.Lang
