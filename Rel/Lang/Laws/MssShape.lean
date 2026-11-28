import Rel.Lang.MssScan
import Rel.Lang.Laws.MssEst
import Rel.Lang.Laws.MssGreedy

/-! # `mss = shape` on the program `mss`

`(𝟙÷∋)E(suffix prefix sum)est(≥) = (𝟙÷∋)E(suffix)E((𝟙÷∋)E(prefix sum)est(≥))est(≥)`: `absorption` and `Eunion` turn the
left side into `sets E(∋) est(≥)`, `estUnion` (`Tm.estUnion_den`) into `sets E(est(≥)) est(≥)`, and `Ecomp` folds that into
the right side. The three laws need `Λ(suffix)`, `Λ(prefix sum)` and `Λ(suffix Λ(prefix sum))` to have an array at every
point, which holds with no guard: the target of `sum` is the finite `i64`, the suffixes of a list are finitely many. -/

namespace Rel.Lang
open Rel.Kernel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `toShape` on relations: `S` is `suffix`, `P` is `prefix sum`, `E` an extreme; `hE` is `estUnion` unfolded. -/
theorem toShape_rel {X Y B : Obj} (S : Core.Rel (Obj.El X) (Obj.El (.arr Y))) (P : Core.Rel (Obj.El (.arr Y)) (Obj.El B))
    (E : Core.Rel (Obj.El (.arr B)) (Obj.El B))
    (hS : ∀ a, ∃ ys, lamDen S a ys) (hP : ∀ a, ∃ ys, lamDen P a ys)
    (hT : ∀ a, ∃ ys, lamDen (S ≫ lamDen P) a ys)
    (hE : ((lamDen S ≫ lamDen (memDen ≫ lamDen P)) ≫ lamDen (memDen ≫ memDen)) ≫ E =
      ((lamDen S ≫ lamDen (memDen ≫ lamDen P)) ≫ lamDen (memDen ≫ E)) ≫ E) :
    lamDen (S ≫ P) ≫ E = lamDen S ≫ lamDen (memDen ≫ (lamDen P ≫ E)) ≫ E := by
  have e1 := lamDen_comp_lam_mem S (lamDen P) hS
  have e2 : lamDen (S ≫ P) = (lamDen S ≫ lamDen (memDen ≫ lamDen P)) ≫ lamDen (memDen ≫ memDen) := by
    rw [← lamDen_comp_lam_mem S P hS, Core.Rel.comp_assoc]
    exact congrArg (lamDen S ≫ ·) (EDen_union P hP)
  have e3 := lamDen_comp_lam_mem (S ≫ lamDen P) E hT
  have e4 := lamDen_comp_lam_mem S (lamDen P ≫ E) hS
  rw [e2, hE, e1, e3, ← Core.Rel.comp_assoc, e4]
  simp only [Core.Rel.comp_assoc]

/-- `Λ(suffix Λ(P))` has an array at every list of a flat object `B`, `P` having a value array at every list. -/
theorem lamSuffixLam_total {B C : Obj} (hC : C.flat = true)
    (P : Core.Rel (Obj.El (.arr B)) (Obj.El C)) (hP : ∀ a, ∃ ys, lamDen P a ys) (xs : List B.El) :
    ∃ ys, lamDen (A := .arr B) (B := .arr C) (splitDen false B.El ≫ lamDen P) xs ys := by
  classical
  refine lamDen_total (A := .arr B) (B := .arr C) _ xs
    (((List.range (xs.length + 1)).map xs.drop).map fun s => Classical.choose (hP s)) (fun b ⟨s, hs, hb⟩ => ?_)
    fun b c _ _ e => arr_key_inj C b c (fun x _ y _ e' => Obj.key_inj_of_flat C hC x y e') e
  have h : s <:+ xs := by simpa [splitDen_iff] using hs
  have h := List.suffix_iff_eq_drop.1 h
  refine List.mem_map.2 ⟨s, List.mem_map.2 ⟨_, List.mem_range.2 (by omega), h.symm⟩, ?_⟩
  exact lamDen_unique P (Classical.choose_spec (hP s)) hb

/-- **`toShape` on the program `mss`**: `mss = shape`, with the same literals as `Tm.estUnion_den` (`T` the one-row table
    of `zero`, `U` the universe of the sums). No guard: no premise past those of `estUnion`. -/
theorem Tm.toShape_den {n : USize} {m p m0 p0 : List String} {hw : QAtomicType.i64.width.isSome = true}
    {hw0 : QAtomicType.i64.width.isSome = true}
    (hb : ∀ U : Vals (.atom .i64) n, U = (Gen.atom .i64 n m p hw).1 → ∀ i, Bnd (U.row i) := by
      intro U hU i; subst hU; exact Rel.Lang.Gen.atom_bnd (i := i))
    (hz0 : ∀ i : Fin (USize.ofNat 1).toNat, ∃ j : Fin n.toNat,
      (Gen.atom .i64 n m p hw).1.get j = (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0).1.get i := by
      atom_mem)
    (ρ : Val) :
    let T := (Gen.relV Obj.one (.atom .i64) (USize.ofNat 1) (Gen.oneV false (USize.ofNat 1))
      (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0)).1
    let U := (Gen.atom .i64 n m p hw).1
    Tm.den ρ (Tm.comp (Tm.lam (Tm.comp (Tm.comp (Tm.prim (rowOf "suffix") : Tm (.arr (.atom .i64)) (.arr (.atom .i64)))
        (Tm.prim (rowOf "prefix"))) (Tm.sumTm T (Tm.uni U))))
      (Tm.est (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U)))))) =
    Tm.den ρ (Tm.outerTm (Tm.comp (Tm.prim (rowOf "prefix") : Tm (.arr (.atom .i64)) (.arr (.atom .i64)))
      (Tm.sumTm T (Tm.uni U))) (Tm.est (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U)))))) := by
  have hE := Tm.estUnion_den (hb := hb) (hz0 := hz0) ρ
  dsimp only at hE ⊢
  generalize (Gen.relV Obj.one (.atom .i64) (USize.ofNat 1) (Gen.oneV false (USize.ofNat 1))
    (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0)).1 = T at hE ⊢
  generalize (Gen.atom .i64 n m p hw).1 = U at hE ⊢
  generalize Tm.est (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U)))) = EST at hE ⊢
  simp only [Tm.den, Prim.den_suffix, Prim.den_prefix] at hE ⊢
  let Sf : Core.Rel (Obj.El (.arr (.atom .i64))) (Obj.El (.arr (.atom .i64))) := splitDen false (Obj.atom .i64).El
  let Sp : Core.Rel (Obj.El (.arr (.atom .i64))) (Obj.El (.arr (.atom .i64))) := splitDen true (Obj.atom .i64).El
  have hP : ∀ a, ∃ ys, lamDen (Sp ≫ Tm.den ρ (Tm.sumTm T (Tm.uni U))) a ys :=
    fun a => lamDen_of_flat (B := .atom .i64) rfl _ a
  have key := toShape_rel Sf (Sp ≫ Tm.den ρ (Tm.sumTm T (Tm.uni U))) (Tm.den ρ EST)
    (lamSuffix_total (B := .atom .i64) rfl) hP
    (lamSuffixLam_total (B := .atom .i64) (C := .atom .i64) rfl _ hP) hE
  simp only [Core.Rel.comp_assoc] at key ⊢
  exact key

/-- `(𝟙÷∋)E(suffix)E(J)est(Q)` reads `J` only at the suffixes of its argument (`Tm.outer_congr` is `J = Λ(IN) est`). -/
theorem Tm.outerJ_congr (ρ : Val) {B : Obj} (EST J1 J2 : Tm B.arr B) (xs : B.arr.El)
    (h : ∀ s, s <:+ xs → ∀ w, J1.den ρ s w ↔ J2.den ρ s w) (w : B.El) :
    (Tm.comp (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix") : Tm B.arr B.arr)) (Tm.lam (Tm.comp Tm.mem J1))) EST).den ρ xs w ↔
    (Tm.comp (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix") : Tm B.arr B.arr)) (Tm.lam (Tm.comp Tm.mem J2))) EST).den ρ xs w := by
  simp only [Tm.den, Core.Rel.comp]
  refine exists_congr fun L => and_congr_left' (exists_congr fun ys => and_congr_right fun hys => ?_)
  have hs : ∀ s, s ∈ ys → s <:+ xs := fun s hs => by
    have := ((lamDen_iff _ _ _).1 hys).2 s |>.1 hs
    simpa [Prim.den_suffix, splitDen_iff] using this
  have hm : ∀ (ys : B.arr.arr.El) (s : B.arr.El), memDen ys s ↔ s ∈ ys := fun _ _ => Iff.rfl
  simp only [lamDen_iff, Core.Rel.comp, hm]
  exact and_congr_right fun _ => forall_congr' fun b => iff_congr Iff.rfl
    (exists_congr fun s => and_congr_right fun hsm => h s (hs s hsm) b)

/-- A fold stays inside an invariant `I` of its values, the elements in `J`. -/
theorem foldrDen_inv {E V : Obj} (Z : Core.Rel (Obj.El V) (Obj.El V)) (S : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (I : V.El → Prop) (J : E.El → Prop) (hZ : ∀ u, (∃ a, Z a u) → I u)
    (hS : ∀ x u w, J x → I u → S (x, u) w → I w) :
    ∀ xs : List E.El, (∀ x ∈ xs, J x) → ∀ w, foldrDen Z S xs w → I w
  | [], _, w, h => hZ w ((foldrDen_empty ..).1 h)
  | x :: xs, hx, w, h => by
    obtain ⟨u, hu, hs⟩ := (foldrDen_cons ..).1 h
    exact hS x u w (hx x List.mem_cons_self)
      (foldrDen_inv Z S I J hZ hS xs (fun y hy => hx y (List.mem_cons_of_mem _ hy)) u hu) hs

/-- Two folds agree where their seeds agree and their steps agree on arguments inside the invariant `I`, `J`. -/
theorem foldrDen_congr_inv {E V : Obj} (Z Z' : Core.Rel (Obj.El V) (Obj.El V))
    (S S' : Core.Rel (Obj.El (.prod E V)) (Obj.El V)) (I : V.El → Prop) (J : E.El → Prop)
    (hZ : ∀ u, (∃ a, Z a u) ↔ (∃ a, Z' a u)) (hZI : ∀ u, (∃ a, Z a u) → I u)
    (hSI : ∀ x u w, J x → I u → S (x, u) w → I w) (hS : ∀ x u w, J x → I u → (S (x, u) w ↔ S' (x, u) w)) :
    ∀ xs : List E.El, (∀ x ∈ xs, J x) → ∀ w, foldrDen Z S xs w ↔ foldrDen Z' S' xs w
  | [], _, w => by rw [foldrDen_empty, foldrDen_empty]; exact hZ w
  | x :: xs, hx, w => by
    rw [foldrDen_cons, foldrDen_cons]
    have hx' := hx x List.mem_cons_self
    have ih := foldrDen_congr_inv Z Z' S S' I J hZ hZI hSI hS xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    refine exists_congr fun u => ?_
    constructor
    · rintro ⟨hu, hs⟩
      exact ⟨(ih u).1 hu, (hS x u w hx' (foldrDen_inv Z S I J hZI hSI xs (fun y hy => hx y (List.mem_cons_of_mem _ hy)) u hu)).1 hs⟩
    · rintro ⟨hu, hs⟩
      exact ⟨(ih u).2 hu, (hS x u w hx' (foldrDen_inv Z S I J hZI hSI xs (fun y hy => hx y (List.mem_cons_of_mem _ hy)) u ((ih u).2 hu))).2 hs⟩

/-- **`toGreedy` on the program `mss`**: `safe fused = safe greedy`. Each suffix `s` of a `safe` list is `safe`, so
    `Tm.greedyMss_den` at `s` turns `Λ(⦇S⦈) est` into `⦇Λ(zero) est, Λ(S) est⦈`; there the seed `Λ(zero) est` is `zero`
    and the cast `ran⟨U, ⊤U⟩` in front of `oplus` is the identity, the list's elements and the fold's values being in `U`. -/
theorem Tm.toGreedy_den {n : USize} {m p m0 p0 : List String} {hw : QAtomicType.i64.width.isSome = true}
    {hw0 : QAtomicType.i64.width.isSome = true}
    (hb : ∀ U : Vals (.atom .i64) n, U = (Gen.atom .i64 n m p hw).1 → ∀ i, Bnd (U.row i) := by
      intro U hU i; subst hU; exact Rel.Lang.Gen.atom_bnd (i := i))
    (hz0 : ∀ i : Fin (USize.ofNat 1).toNat, ∃ j : Fin n.toNat,
      (Gen.atom .i64 n m p hw).1.get j = (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0).1.get i := by
      atom_mem)
    (ρ : Val) :
    let T := (Gen.relV Obj.one (.atom .i64) (USize.ofNat 1) (Gen.oneV false (USize.ofNat 1))
      (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0)).1
    let U := (Gen.atom .i64 n m p hw).1
    Tm.den ρ (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U)))
      (Tm.outerTm (Tm.foldr (Tm.ran (Tm.val T)) (Tm.mssS T U)) (Tm.mssEst U))) =
    Tm.den ρ (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U)))
      (Tm.comp (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix") : Tm (.arr (.atom .i64)) (.arr (.atom .i64))))
        (Tm.lam (Tm.comp Tm.mem (Tm.foldr (Tm.ran (Tm.val T))
          (Tm.comp (Tm.ran (Tm.pair (Tm.uni U) (Tm.top (Tm.uni U))))
            (Tm.comp (Tm.lam (Tm.mssS T U)) (Tm.mssEst U)))))))
        (Tm.mssEst U))) := by
  have hGM := Tm.greedyMss_den (hb := hb) (hz0 := hz0) ρ
  dsimp only at hGM ⊢
  rw [Tm.guardLam_den] at hGM
  obtain ⟨T, hTe⟩ : ∃ T, T = (Gen.relV Obj.one (.atom .i64) (USize.ofNat 1) (Gen.oneV false (USize.ofNat 1))
    (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0)).1 := ⟨_, rfl⟩
  obtain ⟨U, hUe⟩ : ∃ U, U = (Gen.atom .i64 n m p hw).1 := ⟨_, rfl⟩
  rw [← hTe, ← hUe] at hGM ⊢
  rw [← hUe] at hz0
  have hn : T.n.toNat = 1 := by rw [hTe]; simp [Gen.relV]
  replace hb := hb U hUe
  have hUb : ∀ a b : Obj.El (.atom .i64), (Tm.uni U).den ρ a b → a = b ∧ Bnd a := by
    rintro a b ⟨i, rfl, rfl⟩
    exact ⟨rfl, hb i⟩
  have hU : ∀ a b, (Tm.uni U).den ρ a b → a = b := fun a b h => (hUb a b h).1
  obtain ⟨z, hz0'⟩ := Tab.entire_of_one T hn ()
  have hz1 : ∀ v, (Tm.val T).den ρ () v ↔ v = z := fun v =>
    ⟨fun h => Tab.simple_of_one T hn () v z h hz0', fun h => h ▸ hz0'⟩
  have hz : ∀ u, (∃ a, (Tm.ran (Tm.val T)).den ρ a u) ↔ u = z := fun u =>
    (Tm.ran_seed_iff ρ (Tm.val T) u).trans ⟨fun ⟨_, ht⟩ => (hz1 u).1 ht, fun h => ⟨(), (hz1 u).2 h⟩⟩
  have hzU : (Tm.uni U).den ρ z z := by
    have hv : (Tm.val T).den ρ () z := hz0'
    rw [hTe] at hv
    obtain ⟨i, -, rfl⟩ := (Tm.relV_den ρ _ _ _ _).1 hv
    obtain ⟨j, hj⟩ := hz0 i
    have hj' : ValsB.row (o := false) (A := .atom .i64) U j =
        ValsB.row (o := false) (A := .atom .i64) (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0).1 i := by
      rw [Vals.row_atom, Vals.row_atom]; exact hj
    exact ⟨j, hj'.symm, hj'.symm⟩
  have hSum := Tm.sumTm_den ρ T (Tm.uni U) hU
  have hT := Tm.mssS_iff ρ T U hU hz
  have hSU : ∀ x u w, (Tm.mssS T U).den ρ (x, u) w → (Tm.uni U).den ρ w w := fun x u w h => by
    rcases (hT x u w).1 h with rfl | h
    · exact hzU
    · exact ((arithAdd_iff hUb _ _ _).1 h).2.2.1
  have hEst : ∀ ys w, (Tm.mssEst U).den ρ ys w → w ∈ ys := fun ys w h => by
    rw [Tm.mssEst, Tm.est_den] at h; exact ((estDen_iff _ ys w).1 h).1
  -- the seed `Λ(zero) est(≥)` is `zero`: `Λ(zero)` is `[z]`
  have hseed : ∀ u, (∃ a, (Tm.ran (Tm.comp (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)
      (Tm.comp (Tm.lam (Tm.val T)) (Tm.mssEst U)))).den ρ a u) ↔ u = z := fun u => by
    rw [Tm.ran_seed_iff, Tm.uni_one_comp]
    constructor
    · rintro ⟨_, ys, hl, he⟩
      exact (hz1 u).1 ((((lamDen_iff _ _ _).1 hl).2 u).1 (hEst ys u he))
    · rintro rfl
      refine ⟨(), [u], (lamDen_iff _ _ _).2 ⟨List.pairwise_singleton _ _, fun b => ?_⟩, ?_⟩
      · rw [List.mem_singleton, hz1]
      · rw [Tm.mssEst, Tm.est_den, estDen_iff]; simp
  -- every element of a `safe` list is in `U`: `[x]` is one of its segments
  have hgood : ∀ s, SumGood ((Tm.sumTm T (Tm.uni U)).den ρ) s → ∀ x ∈ s, (Tm.uni U).den ρ x x := fun s hg x hx => by
    obtain ⟨a, b, rfl⟩ := List.append_of_mem hx
    rw [hSum] at hg
    obtain ⟨w, hw⟩ := hg [x] ⟨a, b, by simp⟩
    exact (foldAdd_facts hUb hz _ w hw).2.1 x List.mem_cons_self
  funext xs w; apply propext
  rw [Tm.safeComp_den, Tm.safeComp_den]
  refine and_congr_right fun hg => Tm.outerJ_congr ρ (Tm.mssEst U) _ _ xs (fun s hs v => ?_) w
  have hgs := hg.infix hs.isInfix
  have h1 := Eq.to_iff (congrFun (congrFun hGM s) v)
  rw [Tm.safeComp_den, Tm.safeComp_den] at h1
  refine (and_congr_right_iff.1 h1 hgs).trans ?_
  refine foldrDen_congr_inv _ _ _ _ (fun u => (Tm.uni U).den ρ u u) (fun x => (Tm.uni U).den ρ x x)
    (fun u => (hseed u).trans (hz u).symm) (fun u h => ((hseed u).1 h) ▸ hzU)
    (fun x u w _ _ ⟨ys, hl, he⟩ => hSU x u w ((((lamDen_iff _ _ _).1 hl).2 w).1 (hEst ys w he)))
    (fun x u w hx hu => ⟨fun h => ⟨(x, u), (Tm.ran_den' ρ _ _ _).2 ⟨rfl, x, show _ ∧ _ from ⟨hx, u, trivial, hu⟩⟩, h⟩,
      fun ⟨q, hq, h⟩ => ((Tm.ran_den' ρ _ _ _).1 hq).1 ▸ h⟩) s (hgood s hgs) v

end Rel.Lang
