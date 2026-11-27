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

/-- `n ≤ k` for a size written `USize.ofNat k`: the platform's word size is a case split, `k` below `2 ^ 32` in both. -/
macro "bnd_size" : tactic =>
  `(tactic| first | decide +kernel | (rw [USize.toNat_ofNat']; rcases System.Platform.numBits_eq with h | h <;>
    rw [h] <;> (decide +kernel)))

/-- **Every row of a generated `i64` literal stays below `2 ^ 62`**, from its header text `m` alone (each block's base and
base plus `ones w`, `decide +kernel`) and the size of its pack text `p`: no row is decoded and no string is compared. -/
theorem Gen.atom_bnd {n : USize} {m p : List String} {hw : QAtomicType.i64.width.isSome = true}
    (h1 : n.toNat ≤ Column.blk (Gen.unhex m) * Column.nblk (Gen.unhex m) := by bnd_size)
    (h2 : Column.lgOk (Gen.unhex m) = true := by decide +kernel)
    (h3 : (Array.range (Column.nblk (Gen.unhex m))).any (Column.nulAt (Gen.unhex m)) = false := by decide +kernel)
    (h4 : (p.map fun s => s.utf8ByteSize / 2).sum ≤ Column.blockStart (Gen.unhex m) (Column.nblk (Gen.unhex m)) := by decide +kernel)
    (h5 : ∀ b < Column.nblk (Gen.unhex m), -2 ^ 62 + 1 ≤ (Column.baseAt (Gen.unhex m) b).toInt64.toInt ∧
      (Column.baseAt (Gen.unhex m) b).toInt64.toInt + (Column.ones (Column.widthAt (Gen.unhex m) b)).toNat ≤ 2 ^ 62 - 1 :=
      by decide +kernel)
    (i : Fin n.toNat) : Bnd ((Lang.Gen.atom .i64 n m p hw).1.get i) := by
  obtain ⟨g1, g2⟩ := Lang.Gen.atom_get_bound rfl h1 h2 h3 (by rw [Gen.unhex_size]; exact h4) (-2 ^ 62 + 1) (2 ^ 62 - 1) (by decide) (by decide) h5 i
  exact ⟨by omega, by omega⟩

/-- **`safe shape = safe fused`**: on a `safe` list `prefix sum` and the fold `⦇[zero, ⊤zero ∪ plus]⦈ʳ` agree at every
    suffix, so the outer `(𝟙÷∋)E(suffix)E(·)est(≥)` agrees. `T` is the one-row table of `zero`, `U` the universe of the
    sums, its words below `2 ^ 62`, `EST` the `est(≥)`. -/
theorem Tm.toFused_den {T : Tab .one (.atom .i64)} {n : USize} {m p : List String} {hw : QAtomicType.i64.width.isSome = true}
    {EST : Tm (.arr (.atom .i64)) (.atom .i64)}
    (hn : T.n.toNat = 1 := by first | decide | simp [Rel.Lang.Gen.relV, Rel.Lang.USize.toNat_ofNat_lt])
    (hb : ∀ U : Vals (.atom .i64) n, U = (Gen.atom .i64 n m p hw).1 → ∀ i, Bnd (U.row i) := by
      intro U hU i; subst hU; exact Rel.Lang.Gen.atom_bnd (i := i))
    (ρ : Val) :
    Tm.den ρ (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni (Gen.atom .i64 n m p hw).1)))
      (Tm.outerTm (Tm.comp (Tm.prim (rowOf "prefix")) (Tm.sumTm T (Tm.uni (Gen.atom .i64 n m p hw).1))) EST)) =
    Tm.den ρ (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni (Gen.atom .i64 n m p hw).1)))
      (Tm.outerTm (Tm.foldr (Tm.ran (Tm.val T))
        (.join (.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) (Tm.val T))
          (Tm.cut2 (arithRow "plus") (Tm.uni (Gen.atom .i64 n m p hw).1)))) EST)) := by
  obtain ⟨U, hUe⟩ : ∃ U : Vals (.atom .i64) n, U = (Gen.atom .i64 n m p hw).1 := ⟨_, rfl⟩
  rw [← hUe] at ⊢
  replace hb := hb U hUe
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
