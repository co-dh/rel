import Rel.Lang.Laws.MssFused
import Rel.Lang.Laws.EstUnion
import Rel.RepSymRank
import Rel.Lang.Laws.LamTotal
import Rel.Lang.DfnLaw

/-! # `estUnion` on the program `mss`

`E(∋)est(≥)` after `sets ≜ (𝟙÷∋)E(suffix)E((𝟙÷∋)E(prefix sum))`: every set `Λ(prefix sum)` of a suffix holds the sum
`z` of `[]`, so no member is empty, and `≥` is a total preorder on the universe `U` the sums lie in; then
`estUnion_den` applies. -/

namespace Rel.Lang
open Rel.Kernel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The pair test of `est(R)`: `dom(π₂ ∩ π₁R)` holds at `(b, c)` exactly where `R` holds from `b` to `c`. -/
theorem Tm.estTest_den (ρ : Val) {B : Obj} (R : Tm B B) (b c : B.El) :
    (Tm.dom (Tm.outr.meet (Tm.outl.comp R))).den ρ (b, c) (b, c) ↔ R.den ρ b c := by
  rw [Tm.dom_den']
  simp only [Tm.den, Core.Rel.inter, Core.Rel.comp, true_and]
  constructor
  · rintro ⟨y, h1, ⟨x, hx, h2⟩⟩
    obtain rfl : y = c := h1
    obtain rfl : x = b := hx
    exact h2
  · intro h
    exact ⟨c, rfl, b, rfl, h⟩

/-- The prelude `≥` at the universe `U`: `≤` on `U`, read backwards. -/
theorem Tm.geq_den {t : QAtomicType} {m : USize} (ρ : Val) (U : Vals (.atom t) m) (b c : (Obj.atom t).El) :
    Tm.den ρ ((Tm.call [0] `Rel.Programs.prelude.«≥» (some `Rel.Programs.prelude.«≥».conv) [.atom t]
      (Tm.leq (.var 0)).conv).arg (Tm.uni U)) b c ↔ leqDen t ((Tm.uni U).den ρ) c b := by
  simp only [Tm.leq, Tm.den, Tm.argDen, Val.args, Val.bind, if_true, and_self, dif_pos,
    Prim.den_cmpRelRow_le]
  exact Iff.rfl

/-- The sets `Λ(suffix)E(Λ(prefix P))` of a list `a`: each member `xs` is the set of the `P`-values of the prefixes of a
suffix `s` of `a`. -/
theorem Tm.sets_den (ρ : Val) {B C : Obj} (P : Tm B.arr C) (a : B.arr.El) (xss : C.arr.arr.El)
    (h : (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix") : Tm B.arr B.arr))
      (Tm.lam (Tm.comp Tm.mem (Tm.lam (Tm.comp (Tm.prim (rowOf "prefix") : Tm B.arr B.arr) P))))).den ρ a xss) :
    ∀ xs ∈ xss, ∃ s, s <:+ a ∧ ∀ b, b ∈ xs ↔ ∃ pre, pre <+: s ∧ P.den ρ pre b := by
  simp only [Tm.den, Core.Rel.comp] at h
  obtain ⟨L, hL, hx⟩ := h
  intro xs hxs
  obtain ⟨-, hm⟩ := (lamDen_iff _ _ _).1 hx
  obtain ⟨s, hs, hxs'⟩ := (hm xs).1 hxs
  refine ⟨s, by simpa [Prim.den_suffix, splitDen_iff] using ((lamDen_iff _ _ _).1 hL).2 s |>.1 hs, fun b => ?_⟩
  rw [((lamDen_iff _ _ _).1 hxs').2 b]
  simp [Core.Rel.comp, Prim.den_prefix, splitDen_iff]

/-- `≥` at the universe `U` of `i64` words, as the program elaborates it. -/
abbrev Tm.geqTm (U : Vals (.atom .i64) n) : Tm (.atom .i64) (.atom .i64) :=
  (Tm.call [0] `Rel.Programs.prelude.«≥» (some `Rel.Programs.prelude.«≥».conv) [.atom .i64]
    (Tm.leq (.var 0)).conv).arg (Tm.uni U)

/-- `sets ≜ (𝟙÷∋)E(suffix)E((𝟙÷∋)E(prefix sum))`, as the program elaborates it. -/
abbrev Tm.setsTm (T : Tab .one (.atom .i64)) (U : Vals (.atom .i64) n) : Tm (.arr (.atom .i64)) (.arr (.arr (.atom .i64))) :=
  Tm.comp (Tm.lam (Tm.prim (rowOf "suffix") : Tm (.arr (.atom .i64)) (.arr (.atom .i64))))
    (Tm.lam (Tm.comp Tm.mem (Tm.lam (Tm.comp (Tm.prim (rowOf "prefix") : Tm (.arr (.atom .i64)) (.arr (.atom .i64)))
      (Tm.sumTm T (Tm.uni U))))))

/-- `hz0` for a one-row literal `Gen.atom _ (USize.ofNat 1) …`: its row `0` is some row of the universe literal, by
`Gen.atom_row_mem`, the position found by deciding the bounded search on `foRBits` of both headers once `n.toNat` is a
literal (`USize.toNat_ofNat_lt`), so no `USize.ofNat k` is reduced by the kernel. -/
macro "atom_mem" : tactic =>
  `(tactic| (intro ⟨i, hi⟩
             have h0 : i = 0 := by rw [Rel.Lang.USize.toNat_ofNat_lt (by decide)] at hi; omega
             subst h0
             refine Rel.Lang.Gen.atom_row_mem (by bnd_size) (by decide +kernel) (by decide +kernel) (by bnd_size)
               (by decide +kernel) (by decide +kernel) 0 hi ?_
             rw [Rel.Lang.USize.toNat_ofNat_lt (by decide)]
             decide +kernel))

/-- **`estUnion` on `mss`**: `sets E(∋) est(≥) = sets E(est(≥)) est(≥)`. `T` is the one-row table of `zero`, `U` the
    universe of the sums (words below `2 ^ 62`), `hz0` that `zero` lies in it. -/
theorem Tm.estUnionSets_den {T : Tab .one (.atom .i64)} {n : USize}  (U : Vals (.atom .i64) n)
    (hn : T.n.toNat = 1) (hb : ∀ i, Bnd (U.row i))
    (ρ : Val) (hz0 : ∀ z, (Tm.val T).den ρ () z → (Tm.uni U).den ρ z z) :
    Tm.den ρ (Tm.comp (Tm.comp (Tm.setsTm T U) (Tm.lam (Tm.comp Tm.mem Tm.mem)))
      (Tm.est (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U)))))) =
    Tm.den ρ (Tm.comp (Tm.comp (Tm.setsTm T U) (Tm.lam (Tm.comp Tm.mem
      (Tm.est (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U))))))))
      (Tm.est (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U)))))) := by
  have hUb : ∀ a b, (Tm.uni U).den ρ a b → a = b ∧ Bnd a := by
    rintro a b ⟨i, rfl, rfl⟩
    exact ⟨rfl, hb i⟩
  have hU : ∀ a b, (Tm.uni U).den ρ a b → a = b := fun a b h => (hUb a b h).1
  obtain ⟨z, hz0'⟩ := Tab.entire_of_one T hn ()
  have hz : ∀ u, (∃ a, (Tm.ran (Tm.val T)).den ρ a u) ↔ u = z := fun u =>
    (Tm.ran_seed_iff ρ (Tm.val T) u).trans
      ⟨fun ⟨t, ht⟩ => Tab.simple_of_one T hn t u z ht hz0', fun h => h ▸ ⟨(), hz0'⟩⟩
  have hSum := Tm.sumTm_den ρ T (Tm.uni U) hU
  -- every value of a prefix sum lies in `U`
  have hmem : ∀ pre b, (Tm.sumTm T (Tm.uni U)).den ρ pre b → (Tm.uni U).den ρ b b := by
    intro pre b h
    rw [hSum] at h
    by_cases e : pre = []
    · subst e
      obtain rfl := (hz b).1 ((foldDen_empty ..).1 h)
      exact hz0 _ hz0'
    · exact (foldAdd_facts hUb hz pre b h).2.2 e
  have hW : ∀ b c, (Tm.uni U).den ρ b b → (Tm.uni U).den ρ c c →
      ((Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U)))).den ρ (b, c) (b, c) ↔ c ≤ b) := fun b c hb hc => by
    rw [Tm.estTest_den, Tm.geq_den, leqDen_iff]
    exact ⟨fun h => h.2.2, fun h => ⟨⟨c, hc⟩, ⟨b, hb⟩, h⟩⟩
  -- the elements of a member `xs` are sums, hence in `U`, and `xs` holds the sum `z` of `[]`
  have hxs : ∀ a xss, (Tm.setsTm T U).den ρ a xss → ∀ xs ∈ xss, xs ≠ [] ∧ ∀ b ∈ xs, (Tm.uni U).den ρ b b := by
    intro a xss h xs hx
    obtain ⟨s, -, hs⟩ := Tm.sets_den ρ _ a xss h xs hx
    refine ⟨fun e => ?_, fun b hbx => ?_⟩
    · have : z ∈ xs := (hs z).2 ⟨[], List.nil_prefix, by
        rw [hSum]; exact (foldDen_empty ..).2 ((hz z).2 rfl |> fun ⟨a, ha⟩ => ⟨a, ha⟩)⟩
      simp [e] at this
    · obtain ⟨pre, -, hp⟩ := (hs b).1 hbx
      exact hmem pre b hp
  refine Tm.estUnionAt_den ρ (fun a xss h xs hx => (hxs a xss h xs hx).1)
    (fun a xss h xs hx b hbx => ?_) (fun a xss h xs hx zs hzs b hbx c hc => ?_)
    (fun a xss h xs hx ys hy zs hzs b hbx c hc d hd => ?_) (fun a xss h => ?_)
  · have := (hxs a xss h xs hx).2 b hbx
    exact (hW b b this this).2 (Int64.le_refl _)
  · have hb' := (hxs a xss h xs hx).2 b hbx
    have hc' := (hxs a xss h zs hzs).2 c hc
    rcases Int64.le_total c b with e | e
    · exact .inl ((hW b c hb' hc').2 e)
    · exact .inr ((hW c b hc' hb').2 e)
  · have hb' := (hxs a xss h xs hx).2 b hbx
    have hc' := (hxs a xss h ys hy).2 c hc
    have hd' := (hxs a xss h zs hzs).2 d hd
    intro h1 h2
    exact (hW b d hb' hd').2 (Int64.le_trans ((hW c d hc' hd').1 h2) ((hW b c hb' hc').1 h1))
  · exact lamDen_of_flat (by decide) _ _

/-- **`estUnion` on the program `mss`**: `T` is the one-row table literal of `zero` (its value column `Gen.atom` at `m0 p0`),
    `U` the universe `Gen.atom .i64 n m p` of the sums, its words below `2 ^ 62` (`Gen.atom_bnd`) and holding the
    value of `zero` (`hz0`, by the kernel on the literals). -/
theorem Tm.estUnion_den {n : USize} {m p m0 p0 : List String} {hw : QAtomicType.i64.width.isSome = true}
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
    Tm.den ρ (Tm.comp (Tm.comp (Tm.setsTm T U) (Tm.lam (Tm.comp Tm.mem Tm.mem)))
      (Tm.est (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U)))))) =
    Tm.den ρ (Tm.comp (Tm.comp (Tm.setsTm T U) (Tm.lam (Tm.comp Tm.mem
      (Tm.est (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U))))))))
      (Tm.est (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.geqTm U)))))) := by
  intro T U
  refine Tm.estUnionSets_den U (by simp [T, Gen.relV]) (hb U rfl) ρ ?_
  intro z hz
  obtain ⟨i, -, rfl⟩ := (Tm.relV_den ρ _ _ _ _).1 hz
  obtain ⟨j, hj⟩ := hz0 i
  have hj' : ValsB.row (o := false) (A := .atom .i64) (Gen.atom .i64 n m p hw).1 j =
      ValsB.row (o := false) (A := .atom .i64) (Gen.atom .i64 (USize.ofNat 1) m0 p0 hw0).1 i := by
    rw [Vals.row_atom, Vals.row_atom]; exact hj
  exact ⟨j, hj'.symm, hj'.symm⟩

end Rel.Lang
