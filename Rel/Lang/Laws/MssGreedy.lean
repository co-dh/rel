import Rel.Lang.Laws.GreedyFold
import Rel.Lang.Laws.MssFused
import Rel.Lang.Laws.LamTotal
import Rel.Lang.Laws.MssEst

/-! # `safe (𝟙÷∋)E(⦇S⦈)est(≥) = safe ⦇(𝟙÷∋)E(S)est(≥)⦈` on the program `mss`

`Tm.greedyFold_den` (GreedyFold) is the greedy law for a right fold under a tail-closed guard; here its premises are
discharged for `S = ⊤zero ∪ plus` over `≥` on a bounded `i64` universe, the guard being `safe`. The elaborator fuses
the guard into `Λ`: `safe (𝟙÷∋)E(F)est(R)` is `Λ(safe Λ(𝟙) ∋ F) est(R)` (`Tm.guardLam_den`). -/

namespace Rel.Lang
open Rel.Kernel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `G Λ(𝟙) Λ(∋ F) est = G Λ(F) est`: `(𝟙÷∋)E(F)est` is `Λ(𝟙) E(F) est`, and `Λ(𝟙) E(F) = Λ(F)` (`lamDen_id_EDen`). -/
theorem Tm.guardLam_den {E V : Obj} (ρ : Val) (G : Tm (.arr E) (.arr E)) (F : Tm (.arr E) V) (EST : Tm (.arr V) V) :
    (Tm.comp (Tm.comp (Tm.comp G (Tm.lam Tm.id)) (Tm.lam (Tm.comp Tm.mem F))) EST).den ρ =
      (Tm.comp G (Tm.comp (Tm.lam F) EST)).den ρ := by
  have h : lamDen (𝟙 _) ≫ EDen (F.den ρ) = lamDen (F.den ρ) := lamDen_id_EDen _
  simp only [Tm.den]
  rw [Core.Rel.comp_assoc, Core.Rel.comp_assoc, ← Core.Rel.comp_assoc (lamDen _)]
  exact congrArg (fun R => _ ≫ R ≫ _) h


theorem Tm.uni_iff {B : Obj} {n : USize} (ρ : Val) (U : Vals B n) (a b : B.El) :
    (Tm.uni U).den ρ a b ↔ ∃ i, a = U.row i ∧ b = U.row i := Iff.rfl

/-- The prelude's `≥` at the universe `U`, as the program's `est(≥)` elaborates. -/
abbrev Tm.mssR {n : USize} (U : Vals (.atom .i64) n) : Tm (.atom .i64) (.atom .i64) :=
  (Tm.call [0] `Rel.Programs.prelude.«≥» (some `Rel.Programs.prelude.«≥».conv) [.atom .i64]
    (Tm.leq (.var 0)).conv).arg (Tm.uni U)

theorem Tm.mssR_den {n : USize} (ρ : Val) (U : Vals (.atom .i64) n) (b c : Int64) :
    (Tm.mssR U).den ρ b c ↔ (Tm.uni U).den ρ b b ∧ (Tm.uni U).den ρ c c ∧ c.toInt ≤ b.toInt := by
  simp only [Tm.leq, Tm.den, Tm.argDen, Val.args, Val.bind, if_true, and_self, dif_pos,
    Prim.den_cmpRelRow_le]
  show leqDen .i64 _ c b ↔ _
  rw [leqDen_iff]
  simp only [leAt, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, Int64.le_iff_toInt_le]
  constructor
  · rintro ⟨⟨v, i, h1, h2⟩, ⟨w, j, h3, h4⟩, h5⟩; exact ⟨⟨j, h3, h3⟩, ⟨i, h1, h1⟩, h5⟩
  · rintro ⟨⟨j, h3, -⟩, ⟨i, h1, -⟩, h5⟩; exact ⟨⟨_, i, h1, rfl⟩, ⟨_, j, h3, rfl⟩, h5⟩

/-- The seed `uni(1)` composed in front of a value of `1` changes nothing. -/
theorem Tm.uni_one_comp {B : Obj} (ρ : Val) (X : Tm .one B) :
    (Tm.comp (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst) X).den ρ = X.den ρ := by
  funext a b; apply propext
  simp only [Tm.den, Core.Rel.comp]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(), ⟨⟨0, by simp⟩, rfl, rfl⟩, h⟩⟩

/-- `dom(Λ(X)) = 𝟙` where the target of `X` is the finite `i64`. -/
theorem Tm.dom_lam_i64 {A : Obj} (ρ : Val) (X : Tm A (.atom .i64)) : (Tm.dom (Tm.lam X)).den ρ = (Tm.id : Tm A A).den ρ := by
  rw [Tm.dom_den]
  exact dom_of_entire fun a => lamDen_of_flat (B := .atom .i64) rfl _ a

theorem Tm.foldr_den_congr {E V : Obj} (ρ : Val) (G : Tm (.arr E) (.arr E)) {s s' : Tm V V} {S : Tm (.prod E V) V}
    (h : s.den ρ = s'.den ρ) : (Tm.comp G (Tm.foldr s S)).den ρ = (Tm.comp G (Tm.foldr s' S)).den ρ := by
  simp only [Tm.den]; rw [h]

/-- The step `⊤zero ∪ plus` of the program's fold, the `plus` cut to the universe `U`. -/
abbrev Tm.mssS (T : Tab .one (.atom .i64)) {n : USize} (U : Vals (.atom .i64) n) :
    Tm (.prod (.atom .i64) (.atom .i64)) (.atom .i64) :=
  .join (.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) (Tm.val T)) (Tm.cut2 (arithRow "plus") (Tm.uni U))

/-- The program's `est(≥)`. -/
abbrev Tm.mssEst {n : USize} (U : Vals (.atom .i64) n) : Tm (.arr (.atom .i64)) (.atom .i64) :=
  Tm.est (Tm.dom (Tm.meet Tm.outr (Tm.comp Tm.outl (Tm.mssR U))))

/-- The fold value of a list is the seed plus the sum of one of its prefixes. -/
theorem foldr_prefix {TU Te : Core.Rel (Obj.El (.atom .i64)) (Obj.El (.atom .i64))} (hU : ∀ a b, TU a b → a = b ∧ Bnd a)
    {z : Int64} (hz : ∀ u, (∃ a, Te a u) ↔ u = z) :
    ∀ (xs : List Int64) (u : Int64), foldrDen (E := .atom .i64) (V := .atom .i64) Te
      (fun p w => w = z ∨ arithDen .i64 Ew.add TU p w) xs u → ∃ k, u.toInt = z.toInt + ysum (xs.take k)
  | [], u, h => ⟨0, by obtain rfl := (hz u).1 ((foldrDen_empty ..).1 h); simp [ysum]⟩
  | x :: xs, u, h => by
    obtain ⟨v, hv, hs⟩ := (foldrDen_cons ..).1 h
    rcases hs with rfl | hs
    · exact ⟨0, by simp [ysum]⟩
    · obtain ⟨k, hk⟩ := foldr_prefix hU hz xs v hv
      obtain ⟨-, -, -, h4⟩ := (arithAdd_iff hU _ _ _).1 hs
      exact ⟨k + 1, by rw [List.take_succ_cons, ysum_cons]; omega⟩

/-- **`safe (𝟙÷∋)E(⦇[zero, ⊤zero ∪ plus]⦈ʳ)est(≥) = safe ⦇[(𝟙÷∋)E(zero)est(≥), (𝟙÷∋)E(⊤zero ∪ plus)est(≥)]⦈ʳ`** on the
    program `mss`: `Tm.greedyFold_den` at the guard `safe`, `R = ≥` on the universe `U` (a total order on its words),
    and `S = ⊤zero ∪ plus` monotone on `≥` between fold values of a `safe` tail: the fold value of `xs` is the seed plus
    a prefix sum, so `x + u` for a larger `u` is a segment sum of `x :: xs`, a member of `U`. `hz0`: the seed is a
    word of `U`. -/
theorem Tm.greedyMss_den {n : USize} {m p m0 p0 : List String} {hw : QAtomicType.i64.width.isSome = true}
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
    Tm.den ρ (Tm.comp (Tm.comp (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U))) (Tm.lam Tm.id))
        (Tm.lam (Tm.comp Tm.mem (Tm.foldr (Tm.ran (Tm.val T)) (Tm.mssS T U))))) (Tm.mssEst U)) =
    Tm.den ρ (Tm.comp (Tm.safeTm (Tm.sumTm T (Tm.uni U)))
      (Tm.foldr (Tm.ran (Tm.comp (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)
          (Tm.comp (Tm.lam (Tm.val T)) (Tm.mssEst U))))
        (Tm.comp (Tm.lam (Tm.mssS T U)) (Tm.mssEst U)))) := by
  intro T U
  have hn : T.n.toNat = 1 := by simp [T, Gen.relV]
  replace hb := hb U rfl
  have hUb : ∀ a b : Obj.El (.atom .i64), (Tm.uni U).den ρ a b → a = b ∧ Bnd a := by
    rintro a b ⟨i, rfl, rfl⟩
    exact ⟨rfl, hb i⟩
  have hU : ∀ a b, (Tm.uni U).den ρ a b → a = b := fun a b h => (hUb a b h).1
  obtain ⟨z, hz0'⟩ := Tab.entire_of_one T hn ()
  have hz : ∀ u, (∃ a, (Tm.ran (Tm.val T)).den ρ a u) ↔ u = z := fun u =>
    (Tm.ran_seed_iff ρ (Tm.val T) u).trans
      ⟨fun ⟨t, ht⟩ => Tab.simple_of_one T hn t u z ht hz0', fun h => h ▸ ⟨(), hz0'⟩⟩
  have hzU : (Tm.uni U).den ρ z z := by
    have hv : (Tm.val T).den ρ () z := hz0'
    obtain ⟨i, -, rfl⟩ := (Tm.relV_den ρ _ _ _ _).1 hv
    obtain ⟨j, hj⟩ := hz0 i
    have hj' : ValsB.row (o := false) (A := .atom .i64) (Gen.atom .i64 n m p hw).1 j =
        ValsB.row (o := false) (A := .atom .i64) (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0).1 i := by
      rw [Vals.row_atom, Vals.row_atom]; exact hj
    exact ⟨j, hj'.symm, hj'.symm⟩
  have hS := Tm.cut2_plus_den ρ (Tm.uni U) hU
  have hSum := Tm.sumTm_den ρ T (Tm.uni U) hU
  have hT : ∀ x u w, (Tm.mssS T U).den ρ (x, u) w ↔ w = z ∨ arithDen .i64 Ew.add ((Tm.uni U).den ρ) (x, u) w := fun x u w => by
    change ((Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) (Tm.val T) : Tm (Obj.prod _ _) _).den ρ (x, u) w ∨
      (Tm.cut2 (arithRow "plus") (Tm.uni U)).den ρ (x, u) w) ↔ _
    rw [Tm.topSeed_den, hS]
    refine or_congr ?_ Iff.rfl
    rw [← hz w, Tm.ran_seed_iff]
  have hG : ∀ a b, (Tm.safeTm (Tm.sumTm T (Tm.uni U))).den ρ a b → a = b := fun a b h => ((Tm.safeG_den ρ _ a b).1 h).1
  have hGd : ∀ xs, (Tm.safeTm (Tm.sumTm T (Tm.uni U))).den ρ xs xs ↔ SumGood (foldDen ((Tm.ran (Tm.val T)).den ρ)
      (arithDen .i64 Ew.add ((Tm.uni U).den ρ))) xs := fun xs => by
    rw [Tm.safeG_den, hSum]; exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  have hR := Tm.mssR_den ρ U
  have hUm : ∀ xs, SumGood (foldDen ((Tm.ran (Tm.val T)).den ρ) (arithDen .i64 Ew.add ((Tm.uni U).den ρ))) xs →
      ∀ u, foldrDen ((Tm.ran (Tm.val T)).den ρ) (Tm.den ρ (Tm.mssS T U)) xs u → (Tm.uni U).den ρ u u := by
    intro xs
    induction xs with
    | nil => intro _ u h; obtain rfl := (hz u).1 ((foldrDen_empty ..).1 h); exact hzU
    | cons x xs ih =>
      intro hg u h
      obtain ⟨v, hv, hs⟩ := (foldrDen_cons ..).1 h
      rcases (hT x v u).1 hs with rfl | hs
      · exact hzU
      · exact ((arithAdd_iff hUb _ _ _).1 hs).2.2.1
  rw [Tm.guardLam_den]
  have hTS : Tm.den ρ (Tm.mssS T U) = fun p w => w = z ∨ arithDen .i64 Ew.add ((Tm.uni U).den ρ) p w :=
    funext fun ⟨x, u⟩ => funext fun w => propext (hT x u w)
  have hseed : (Tm.ran (Tm.comp (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)
        (Tm.comp (Tm.lam (Tm.val T)) (Tm.mssEst U)))).den ρ = (Tm.ran (Tm.comp (Tm.lam (Tm.val T)) (Tm.mssEst U))).den ρ := by
    rw [Tm.ran_den, Tm.ran_den, Tm.uni_one_comp]
  rw [Tm.foldr_den_congr ρ _ hseed]
  refine Tm.greedyFold_den ρ (fun a => (Tm.uni U).den ρ a a) hG
    (fun x xs hg => (hGd _).2 (SumGood.tail x xs ((hGd _).1 hg)))
    (fun b c hb hc => ?_) (fun b c d hb hc hd h1 h2 => ?_) (fun b c hb hc h1 h2 => ?_)
    (fun xs hg u h => hUm xs ((hGd _).1 hg) u h) (fun x xs hg u u' c hu hu' hR' hs => ?_)
    (Tm.dom_lam_i64 ρ _) (Tm.dom_lam_i64 ρ _) (Tm.dom_lam_i64 ρ _)
  · rcases Int.le_total c.toInt b.toInt with h | h
    · exact Or.inl ((hR b c).2 ⟨hb, hc, h⟩)
    · exact Or.inr ((hR c b).2 ⟨hc, hb, h⟩)
  · obtain ⟨-, -, h1⟩ := (hR b c).1 h1
    obtain ⟨-, -, h2⟩ := (hR c d).1 h2
    exact (hR b d).2 ⟨hb, hd, by omega⟩
  · obtain ⟨-, -, h1⟩ := (hR b c).1 h1
    obtain ⟨-, -, h2⟩ := (hR c b).1 h2
    exact Int64.toInt_inj.1 (by omega)
  · have hgx := (hGd _).1 hg
    have hgs := SumGood.tail x xs hgx
    change foldrDen _ (Tm.den ρ (Tm.mssS T U)) xs u at hu
    rcases (hT x u' c).1 hs with hc | hs'
    · exact ⟨z, (hT x u z).2 (Or.inl rfl), hc ▸ (hR z z).2 ⟨hzU, hzU, Int.le_refl _⟩⟩
    · obtain ⟨hxU, hu'U, hcU, hceq⟩ := (arithAdd_iff hUb x u' c).1 hs'
      have huU := hUm xs hgs u hu
      obtain ⟨k, hk⟩ := foldr_prefix hUb hz xs u (hTS ▸ hu)
      obtain ⟨w, hw⟩ := hgx (x :: xs.take k) ⟨[], xs.drop k, by simp⟩
      obtain ⟨h1, h2, h3⟩ := foldAdd_facts hUb hz _ w hw
      have hwU := h3 (List.cons_ne_nil _ _)
      have hxU' := h2 x List.mem_cons_self
      obtain ⟨-, -, hle⟩ := (hR u u').1 hR'
      have hwe : w.toInt = x.toInt + u.toInt := by rw [h1, ysum_cons]; omega
      exact ⟨w, (hT x u w).2 (Or.inr ((arithAdd_iff hUb x u w).2 ⟨hxU', huU, hwU, hwe⟩)),
        (hR w c).2 ⟨hwU, hcU, by omega⟩⟩

end Rel.Lang
