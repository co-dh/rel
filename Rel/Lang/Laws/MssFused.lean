import Rel.Lang.Laws.MssSafeTm
import Rel.Lang.Laws.Map
import Rel.RepAtomBound

/-! # `safe shape = safe fused` on the program `mss`

`prefix sum` fused into the fold `⦇[zero, ⊤zero ∪ plus]⦈ʳ` (`Tm.prefixFuse_good_den`) at every suffix of a `safe` list:
there each segment has a sum, so `plus` commutes with the seed and associates (`foldAdd_hc`, `foldAdd_ha`), the sums
being exact on a universe whose words stay below `2 ^ 62` (`Bnd`). -/

namespace Rel.Lang
open Rel.Kernel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `safe ≜ 𝟙 − dom(suffix prefix (𝟙 − dom(sum)))`. -/
abbrev Tm.safeTm {B : Obj} (Sum : Tm B.arr B) : Tm B.arr B.arr :=
  Tm.id.diff ((Tm.prim domRow : Tm B.arr B.arr).arg
    (Tm.comp (Tm.comp (Tm.prim (rowOf "suffix") : Tm B.arr B.arr) (Tm.prim (rowOf "prefix")))
      (Tm.id.diff ((Tm.prim domRow : Tm B.arr B.arr).arg Sum))))

/-- `(𝟙÷∋)E(suffix)E(IN)est(Q)` after `safe`, its `est(Q)` written `EST`. -/
abbrev Tm.outerTm {B : Obj} (IN EST : Tm B.arr B) : Tm B.arr B :=
  Tm.comp (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix") : Tm B.arr B.arr))
    (Tm.lam (Tm.comp Tm.mem (Tm.comp (Tm.lam IN) EST)))) EST

theorem Tm.safeComp_den (ρ : Val) {B : Obj} (Sum : Tm B.arr B) (O : Tm B.arr B) (xs : B.arr.El) (w : B.El) :
    (Tm.comp (Tm.safeTm Sum) O).den ρ xs w ↔ SumGood (Sum.den ρ) xs ∧ O.den ρ xs w := by
  simp only [Tm.den, Core.Rel.comp]
  constructor
  · rintro ⟨xs', hG, ho⟩
    obtain ⟨rfl, hg⟩ := (Tm.safeG_den ρ Sum xs xs').1 hG
    exact ⟨hg, ho⟩
  · rintro ⟨hg, ho⟩
    exact ⟨xs, (Tm.safeG_den ρ Sum xs xs).2 ⟨rfl, hg⟩, ho⟩

/-- The rows of the range literal `-10…20` stay below `2 ^ 62` (`Gen.atom_get_bound`, from the header alone). -/
theorem Gen.atom_range_bnd (p : String) (hp : (Gen.unhex p).size ≤ 640) (i : Fin (USize.ofNat 31).toNat) :
    Bnd ((Lang.Gen.atom .i64 (USize.ofNat 31)
      "f6ffffffffffffff140000000000000000000000000000009b0000000000000000000000000000801f000000000000000a0000000000000005"
      p).1.get i) := by
  obtain ⟨h1, h2⟩ := Lang.Gen.atom_get_bound unhex_rangeMd (by rw [rangeMd_nblk, rangeMd_blk, USize.toNat_ofNat']; rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide)
    rangeMd_lgOk rangeMd_nul (by rw [rangeMd_start]; exact hp) (-10) 21 (by decide) (by decide) rangeMd_rows i
  exact ⟨by omega, by omega⟩

/-- `Gen.atom_range_bnd` for a universe `U` known to be that column: the form the elaborated `Tm.uni` presents. -/
theorem Gen.atom_range_bnd_row {U : Vals (.atom .i64) (USize.ofNat 31)} (p : String) (hp : (Gen.unhex p).size ≤ 640)
    (hU : U = (Lang.Gen.atom .i64 (USize.ofNat 31)
      "f6ffffffffffffff140000000000000000000000000000009b0000000000000000000000000000801f000000000000000a0000000000000005"
      p).1) (i : Fin (USize.ofNat 31).toNat) : Bnd (U.row i) := by
  subst hU; exact Gen.atom_range_bnd p hp i

/-- **`safe shape = safe fused`**: on a `safe` list `prefix sum` and the fold `⦇[zero, ⊤zero ∪ plus]⦈ʳ` agree at every
    suffix, so the outer `(𝟙÷∋)E(suffix)E(·)est(≥)` agrees. `T` is the one-row table of `zero`, `U` the universe of the
    sums, its words below `2 ^ 62`, `EST` the `est(≥)`. -/
theorem Tm.toFused_den {T : Tab .one (.atom .i64)} {m : USize} {U : Vals (.atom .i64) m}
    {EST : Tm (.arr (.atom .i64)) (.atom .i64)}
    (hn : T.n.toNat = 1 := by first | decide | simp [Rel.Lang.Gen.relV, Rel.Lang.USize.toNat_ofNat_lt])
    (hb : ∀ i, Bnd (U.row i) := by intro i; exact Rel.Lang.Gen.atom_range_bnd_row _ (by decide +kernel) rfl i)
    (ρ : Val) :
    Tm.den ρ (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U)))
      (Tm.outerTm (Tm.comp (Tm.prim (rowOf "prefix")) (Tm.sumTm T (Tm.uni U))) EST)) =
    Tm.den ρ (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U)))
      (Tm.outerTm (Tm.foldr (Tm.ran (Tm.val T))
        (.join (.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) (Tm.val T))
          (Tm.cut2 (arithRow "plus") (Tm.uni U)))) EST)) := by
  have hUb : ∀ a b, (Tm.uni U).den ρ a b → a = b ∧ Bnd a := by
    rintro a b ⟨i, rfl, rfl⟩
    exact ⟨rfl, hb i⟩
  have hU : ∀ a b, (Tm.uni U).den ρ a b → a = b := fun a b h => (hUb a b h).1
  obtain ⟨z, hz0⟩ := Tab.entire_of_one T hn ()
  have hz : ∀ u, (∃ a, (Tm.ran (Tm.val T)).den ρ a u) ↔ u = z := fun u =>
    (Tm.ran_seed_iff ρ (Tm.val T) u).trans
      ⟨fun ⟨t, ht⟩ => Tab.simple_of_one T hn t u z ht hz0, fun h => h ▸ ⟨(), hz0⟩⟩
  have hS := Tm.cut2_plus_den ρ (Tm.uni U) hU
  have hSum := Tm.sumTm_den ρ T (Tm.uni U) hU
  funext xs w; apply propext
  rw [Tm.safeComp_den, Tm.safeComp_den]
  refine and_congr_right fun hg => Tm.outer_congr ρ EST _ _ xs (fun s hs v => ?_) w
  have hgs : SumGood (foldDen ((Tm.ran (Tm.val T)).den ρ) (arithDen .i64 Ew.add ((Tm.uni U).den ρ))) s := by
    rw [hSum] at hg; exact hg.infix hs.isInfix
  have := Tm.prefixFuse_good_den ρ (Tm.val T) (Tm.cut2 (arithRow "plus") (Tm.uni U))
    (SumGood (foldDen ((Tm.ran (Tm.val T)).den ρ) (arithDen .i64 Ew.add ((Tm.uni U).den ρ))))
    (fun ys zs h => SumGood.prefix ys zs h) (fun x xs h => SumGood.tail x xs h)
    (fun x _ w => by rw [hS]; exact foldAdd_hc hUb _ x w)
    (fun x ys y hg v w hv => by rw [hS] at hv ⊢; exact foldAdd_ha hUb hz x y ys hg v w hv) s hgs v
  simp only [Tm.den, Core.Rel.comp] at this ⊢
  rw [hSum, hS] at *
  exact this

end Rel.Lang
