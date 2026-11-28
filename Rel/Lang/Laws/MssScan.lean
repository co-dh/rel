import Rel.Lang.MssScan
import Rel.Lang.Laws.MssGreedy

/-! # `safe greedy = safe scan` on the program `mss`

`Tm.toScan_den` (Rel/Lang/MssScan) is the law for a generic guard, seed and step; here its premises are discharged for
the guard `safe`, the seed `zero` and the step `oplus = (𝟙N × 𝟙N) (𝟙÷∋)E(⊤zero ∪ plus)est(≥)`. The one premise that
reads more than the universe `U` of `N` is `hG`: on a `safe` list `⦇[zero, oplus]⦈ʳ` has a value, because each element
and each fold value lies in `U`, so the pair lies in the universe of `N×N`, which the elaborator writes as the product
of the two universes (`Tm.prodUni`, `Tm.prodUni_den`): no pair is checked. -/

namespace Rel.Lang
open Rel.Kernel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The program's `oplus`: `(𝟙÷∋)E(⊤zero ∪ plus)est(≥)` behind the universe `𝟙N × 𝟙N` of `N×N`. -/
abbrev Tm.mssOP (T : Tab .one (.atom .i64)) {n : USize} (U : Vals (.atom .i64) n) :
    Tm (.prod (.atom .i64) (.atom .i64)) (.atom .i64) :=
  Tm.comp (Tm.prodUni (Tm.uni U) (Tm.uni U)) (Tm.comp (Tm.lam (Tm.mssS T U)) (Tm.mssEst U))

/-- **`safe greedy = safe scan`** at `Tm.den`, for the one-row seed table `T` (`hn`) and the universe `U` of `N` (words
    below `2 ^ 62`, `hb`, holding the seed, `hz0`): the premises of `Tm.toScan_den` at the guard `safe`, the seed
    `zero` and the step `oplus`. -/
theorem Tm.toScanAt_den {T : Tab .one (.atom .i64)} {n : USize} (U : Vals (.atom .i64) n)
    (hn : T.n.toNat = 1) (hb : ∀ i, Bnd (U.row i)) (ρ : Val)
    (hz0 : ∀ z, (Tm.val T).den ρ () z → (Tm.uni U).den ρ z z) :
    (Tm.comp (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U))) (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix")))
        (Tm.lam (Tm.comp Tm.mem (Tm.foldr (Tm.ran (Tm.val T)) (Tm.mssOP T U)))))) (Tm.mssEst U)).den ρ =
      (Tm.comp (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U))) (Tm.comp (Tm.foldr (Tm.ran (Tm.comp (Tm.val T)
          (.pair .id (.lam .id))))
        (.pair (.comp (.pair (.comp .outl .id) (.comp .outr .outl)) (Tm.mssOP T U))
          (.lam (.join (.comp (.pair (.comp .outl .id) (.comp .outr .outl)) (Tm.mssOP T U))
            (.comp (.comp .outr .outr) .mem)))))
        .outr)) (Tm.mssEst U)).den ρ := by
  have hUb : ∀ a b : Obj.El (.atom .i64), (Tm.uni U).den ρ a b → a = b ∧ Bnd a := by
    rintro a b ⟨i, rfl, rfl⟩
    exact ⟨rfl, hb i⟩
  have hU : ∀ a b, (Tm.uni U).den ρ a b → a = b := fun a b h => (hUb a b h).1
  obtain ⟨z, hz0'⟩ := Tab.entire_of_one T hn ()
  have hz : ∀ u, (∃ a, (Tm.ran (Tm.val T)).den ρ a u) ↔ u = z := fun u =>
    (Tm.ran_seed_iff ρ (Tm.val T) u).trans
      ⟨fun ⟨t, ht⟩ => Tab.simple_of_one T hn t u z ht hz0', fun h => h ▸ ⟨(), hz0'⟩⟩
  have hzU : (Tm.uni U).den ρ z z := hz0 z hz0'
  have hS := Tm.cut2_plus_den ρ (Tm.uni U) hU
  have hSum := Tm.sumTm_den ρ T (Tm.uni U) hU
  have hT : ∀ x u w, (Tm.mssS T U).den ρ (x, u) w ↔ w = z ∨ arithDen .i64 Ew.add ((Tm.uni U).den ρ) (x, u) w :=
    fun x u w => by
    change ((Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) (Tm.val T) : Tm (Obj.prod _ _) _).den ρ (x, u) w ∨
      (Tm.cut2 (arithRow "plus") (Tm.uni U)).den ρ (x, u) w) ↔ _
    rw [Tm.topSeed_den, hS]
    refine or_congr ?_ Iff.rfl
    rw [← hz w, Tm.ran_seed_iff]
  -- every value of the step lies in `U`, and `≥` is a total order there
  have hX : ∀ p c, (Tm.mssS T U).den ρ p c → (Tm.uni U).den ρ c c := fun ⟨x, u⟩ c h => by
    rcases (hT x u c).1 h with rfl | h
    · exact hzU
    · exact ((arithAdd_iff hUb _ _ _).1 h).2.2.1
  have hq := qtDen_estQ ρ (Tm.mssR U)
  have hR := Tm.mssR_den ρ U
  have ht : ∀ b c, (Tm.uni U).den ρ b b → (Tm.uni U).den ρ c c →
      qtDen ((Tm.dom (.meet .outr (.comp .outl (Tm.mssR U)))).den ρ) b c ∨
        qtDen ((Tm.dom (.meet .outr (.comp .outl (Tm.mssR U)))).den ρ) c b := fun b c hb hc => by
    rw [hq]
    rcases Int.le_total c.toInt b.toInt with h | h
    · exact Or.inl ((hR b c).2 ⟨hb, hc, h⟩)
    · exact Or.inr ((hR c b).2 ⟨hc, hb, h⟩)
  have htr : ∀ b c d, (Tm.uni U).den ρ b b → (Tm.uni U).den ρ c c → (Tm.uni U).den ρ d d →
      qtDen ((Tm.dom (.meet .outr (.comp .outl (Tm.mssR U)))).den ρ) b c →
      qtDen ((Tm.dom (.meet .outr (.comp .outl (Tm.mssR U)))).den ρ) c d →
      qtDen ((Tm.dom (.meet .outr (.comp .outl (Tm.mssR U)))).den ρ) b d := fun b c d hb _ hd h1 h2 => by
    rw [hq] at h1 h2 ⊢
    obtain ⟨-, -, h1⟩ := (hR b c).1 h1
    obtain ⟨-, -, h2⟩ := (hR c d).1 h2
    exact (hR b d).2 ⟨hb, hd, by omega⟩
  have has : ∀ b c, (Tm.uni U).den ρ b b → (Tm.uni U).den ρ c c →
      qtDen ((Tm.dom (.meet .outr (.comp .outl (Tm.mssR U)))).den ρ) b c →
      qtDen ((Tm.dom (.meet .outr (.comp .outl (Tm.mssR U)))).den ρ) c b → b = c := fun b c _ _ h1 h2 => by
    rw [hq] at h1 h2
    obtain ⟨-, -, h1⟩ := (hR b c).1 h1
    obtain ⟨-, -, h2⟩ := (hR c b).1 h2
    exact Int64.toInt_inj.1 (by omega)
  have hOP : ∀ p w, (Tm.mssOP T U).den ρ p w ↔ ((Tm.uni U).den ρ p.1 p.1 ∧ (Tm.uni U).den ρ p.2 p.2) ∧
      (lamDen ((Tm.mssS T U).den ρ) ≫ estDen ((Tm.dom (.meet .outr (.comp .outl (Tm.mssR U)))).den ρ)) p w :=
    fun p w => by
    simp only [Tm.mssEst,Tm.prodUni_den ρ _ _ hU hU, Tm.den, Tm.est_den, Core.Rel.comp, Core.Rel.rprodMap]
    constructor
    · rintro ⟨p', ⟨h1, h2⟩, h⟩
      obtain rfl : p = p' := Prod.ext (hU _ _ h1) (hU _ _ h2)
      exact ⟨⟨h1, h2⟩, h⟩
    · rintro ⟨h0, h⟩; exact ⟨p, h0, h⟩
  refine Tm.toScan_den (by decide) ρ (fun a b h => ((Tm.safeG_den ρ _ a b).1 h).1) ?_
    (fun x y ⟨m, hm⟩ ⟨m', hm'⟩ => Tab.simple_of_one T hn () x y hm hm')
    (fun p w w' h h' => lamEst_simple _ _ _ has hX p w w' ((hOP p w).1 h).2 ((hOP p w').1 h').2)
  -- on a `safe` list each element lies in `U` (the segment `[x]` has a sum), so the fold has a value
  intro xs hg
  have hgx : SumGood (foldDen ((Tm.ran (Tm.val T)).den ρ) (arithDen .i64 Ew.add ((Tm.uni U).den ρ))) xs := by
    have := ((Tm.safeG_den ρ _ xs xs).1 hg).2; rwa [hSum] at this
  have hxs : ∀ x ∈ xs, (Tm.uni U).den ρ x x := fun x hx => by
    obtain ⟨w, hw⟩ := hgx [x] (by obtain ⟨s, t, rfl⟩ := List.append_of_mem hx; exact ⟨s, t, by simp⟩)
    exact (foldAdd_facts hUb hz _ w hw).2.1 x List.mem_cons_self
  obtain ⟨a, ha⟩ := (hz z).2 rfl
  obtain ⟨g, hg, -⟩ := foldrDen_entire_on (fun x => (Tm.uni U).den ρ x x) (fun x => (Tm.uni U).den ρ x x)
    ((Tm.ran (Tm.val T)).den ρ) ((Tm.mssOP T U).den ρ) ⟨a, z, ha, hzU⟩ (fun x u hx hu => by
      obtain ⟨w, hw⟩ := lamEst_entire _ _ _ ht htr hX (fun p => lamDen_of_flat (by decide) _ p)
        (fun ⟨x, u⟩ => ⟨z, (hT x u z).2 (Or.inl rfl)⟩) (x, u)
      obtain ⟨ys, hy, he⟩ := hw
      exact ⟨w, (hOP _ w).2 ⟨⟨hx, hu⟩, ys, hy, he⟩, hX _ _ ((estDen_lam _ hy w).1 he).1⟩) xs hxs
  exact ⟨g, hg⟩

/-- **`safe greedy = safe scan` on the program `mss`**: `Tm.toScanAt_den` at the literals the program elaborates. `T` is
    the one-row table of `zero` (value column at `m0 p0`), `U` the universe of `N` (`m p`, words below `2 ^ 62` by `hb`,
    holding `zero` by `hz0`). -/
theorem Tm.toScanMss_den {n : USize} {m p m0 p0 : List String}
    {hw hw0 : QAtomicType.i64.width.isSome = true}
    (hb : ∀ U : Vals (.atom .i64) n, U = (Gen.atom .i64 n m p hw).1 → ∀ i, Bnd (U.row i) := by
      intro U hU i; subst hU; exact Rel.Lang.Gen.atom_bnd (i := i))
    (hz0 : ∀ i : Fin (USize.ofNat 1).toNat, ∃ j : Fin n.toNat,
      (Gen.atom .i64 n m p hw).1.get j = (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0).1.get i := by
      atom_mem)
    (ρ : Val) :
    let T := (Gen.relV Obj.one (.atom .i64) (USize.ofNat 1) (Gen.oneV false (USize.ofNat 1))
      (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0)).1
    let U := (Gen.atom .i64 n m p hw).1
    (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U))) (Tm.comp (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix")))
        (Tm.lam (Tm.comp Tm.mem (Tm.foldr (Tm.ran (Tm.val T)) (Tm.mssOP T U))))) (Tm.mssEst U))).den ρ =
      (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U))) (Tm.comp (Tm.comp (Tm.foldr (Tm.ran (Tm.comp (Tm.val T)
          (.pair .id (.lam .id))))
        (.pair (.comp (.pair (.comp .outl .id) (.comp .outr .outl)) (Tm.mssOP T U))
          (.lam (.join (.comp (.pair (.comp .outl .id) (.comp .outr .outl)) (Tm.mssOP T U))
            (.comp (.comp .outr .outr) .mem)))))
        .outr) (Tm.mssEst U))).den ρ := by
  intro T U
  -- the program nests `safe (X est)`; `Tm.toScanAt_den` states `(safe X) est`
  have hA : ∀ {A B C D : Obj} (P : Tm A B) (Q : Tm B C) (R : Tm C D),
      (Tm.comp P (Tm.comp Q R)).den ρ = (Tm.comp (Tm.comp P Q) R).den ρ := fun _ _ _ => (Core.Rel.comp_assoc _ _ _).symm
  rw [hA, hA]
  refine Tm.toScanAt_den U (by simp [T, Gen.relV]) (hb U rfl) ρ ?_
  · intro z hz
    obtain ⟨i, -, rfl⟩ := (Tm.relV_den ρ _ _ _ _).1 hz
    obtain ⟨j, hj⟩ := hz0 i
    have hj' : ValsB.row (o := false) (A := .atom .i64) (Gen.atom .i64 n m p hw).1 j =
        ValsB.row (o := false) (A := .atom .i64) (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0).1 i := by
      rw [Vals.row_atom, Vals.row_atom]; exact hj
    exact ⟨j, hj'.symm, hj'.symm⟩

end Rel.Lang
