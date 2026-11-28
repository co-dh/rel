module

public import Rel.Lang.PlanSpecComp

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `compCutsB` builds `Tab.compCuts` (PLAN-THM-E9c)

`compCutsB` is the `some` branch of `compCuts` kernel for kernel: `prefixB` of the widths, the `mapB`s of `win`, `big`,
`prev`, the `gatherB`s of `pw`, `pb`, the `mapB`s of `cut`, `prefixB` of the cuts masked at row `0`, then `scatterB` and
`gatherB` of each row's block. `compCuts` reads the block count as `lastCount`, the plan reads the last word: they
agree because the masked cuts are bits, so the word is at most `K < 2^63`. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel Rel.Verify

/-- A post chain whose `Op`s read back from their registers reads back from its register. -/
theorem opChain_get_put (l : List (Kernel.Op × UInt64))
    (h : ∀ p ∈ l, (Reg.get? (Reg.put p.1) : Option Kernel.Op) = some p.1) :
    (Reg.get? (Reg.put l) : Option (List (Kernel.Op × UInt64))) = some l := by
  have e : (Reg.put l : Val) = (l.map Reg.put).foldr (fun v c => .ctor 1 #[v, c] #[]) (.ctor 0 #[] #[]) := by
    rw [List.foldr_map]; rfl
  rw [e, listGet?_foldr]; clear e
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨o, w⟩ := p
    have hp : (Reg.get? (Reg.put (o, w)) : Option (Kernel.Op × UInt64)) = some (o, w) := by
      show (do pure (← Reg.get? (Reg.put o), ← Reg.get? (Val.u64 w))) = _
      rw [h _ (List.mem_cons_self ..)]; rfl
    rw [List.map_cons, List.mapM_cons, hp, ih fun q hq => h q (List.mem_cons_of_mem _ hq)]; rfl

/-- **`compCutsB` builds `Tab.compCuts`' blocks**: `nr` holds `R.n = nv`, the registers `x1 … x8` hold `compGroups`'
    answer, and `compCuts bound` of it answers `some (nb, bid)` (the caller tests `bound < T`); `hK` (the group count
    below `2^63`, `compGroups`' bound on its rows) makes the last word of the cuts' prefix sum the count `lastCount`
    reads. `kk` continues with a register holding the block count `nb` and one holding `bid`. -/
theorem compCutsB_builds {bound : Nat} {nv Nv Kv : USize} {pv gv fv cRv cSv wv : Enc} {nb : Nat}
    {bid : Arr .i64 nv} {fg : Array Fun × Array Fun} {rs : Array Val} {nr x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {kk : Nat × Nat → Bld (Array Nat)} {out : Array Val} (hn : rs[nr]? = some (.size nv))
    (hx : [x1, x2, x3, x4, x5, x6, x7, x8].mapM (fun i => rs[i]?) = some [.size Nv, Reg.put pv, Reg.put gv,
      Reg.put fv, .size Kv, Reg.put cRv, Reg.put cSv, Reg.put wv]) (hK : Kv.toNat < 2 ^ 63)
    (hC : Tab.compCuts bound nv (Nv, pv, gv, fv, Kv, cRv, cSv, wv) = .ok (some (nb, bid))) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (a b : Nat) (R : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Extends rs R → R[a]? = some (.size nb.toUSize) → R[b]? = some (Reg.put bid.enc) →
      ∃ fg', Builds abiOf fg2 fg' (kk (a, b)) R out) :
    ∃ fg', Builds abiOf fg fg' (compCutsB bound nr (x1, x2, x3, x4, x5, x6, x7, x8) >>= kk) rs out := by
  -- `compCuts`' kernel answers, in its order
  unfold Tab.compCuts at hC
  dsimp only at hC
  split at hC
  · cases hC
  rename_i P hP
  split at hC
  · cases hC
  obtain ⟨win, hwin, hC⟩ := except_bind_ok hC
  obtain ⟨big, hbig, hC⟩ := except_bind_ok hC
  obtain ⟨prev, hprev, hC⟩ := except_bind_ok hC
  obtain ⟨pw, hpw, hC⟩ := except_bind_ok hC
  obtain ⟨pb, hpb, hC⟩ := except_bind_ok hC
  obtain ⟨c1, hc1, hC⟩ := except_bind_ok hC
  obtain ⟨c2, hc2, hC⟩ := except_bind_ok hC
  obtain ⟨cut, hcut, hC⟩ := except_bind_ok hC
  obtain ⟨y, hy, hC⟩ := except_bind_ok hC
  obtain ⟨a, ha, hC⟩ := except_bind_ok hC
  split at hC
  · cases hC
  rename_i I hI
  obtain ⟨sc, hsc, hC⟩ := except_bind_ok hC
  obtain ⟨rowG, hrowG, hC⟩ := except_bind_ok hC
  obtain ⟨bid', hbid, hC⟩ := except_bind_ok hC
  simp only [Pure.pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hC
  obtain ⟨hnb, rfl⟩ := hC
  have hbe : kgather nv rowG Kv I = .ok bid'.enc := by
    simp only [Arr.gather] at hbid
    split at hbid
    · next o ho => cases hbid; exact ho
    · cases hbid
  -- the count: the masked cuts are bits, so the last word of their prefix sum is at most `K`
  obtain ⟨z0, r0, hz0, hk0, hr0e⟩ := colPrefix_kscan hP
  obtain ⟨z1, r1, hz1, hk1, hr1e⟩ := colPrefix_kscan hI
  have hr0 : Kv ≠ 0 → r0.2.isSome :=
    kscan_last_isSome (w := 8) rfl (kscanStream_ne (by decide) _ _ _) (colPrefix_hF hz0 (Or.inl rfl)) hk0
  have hr1 : Kv ≠ 0 → r1.2.isSome :=
    kscan_last_isSome (w := 8) rfl (kscanStream_ne (by decide) _ _ _) (colPrefix_hF hz1 (Or.inl rfl)) hk1
  let wa : Nat → Nat := fun G => ((Enc.raw .i64 Kv a)[G]?.getD 0).toNat
  have hab : ∀ G < Kv.toNat, wa G ≤ 1 := by
    intro G hG
    have e1 := (colMap_post hy).2 G hG
    have e2 := (colMap_raw ha).2.2.2 G hG
    simp only [Kernel.Op.eval, Except.ok.injEq] at e1 e2
    simp only [wa, ← e2, ← e1, UInt64.toNat_and]
    refine Nat.le_trans Nat.and_le_right ?_
    unfold Kernel.Op.w; split <;> decide
  have hsum := colPrefix_add_sum hI wa (fun G _ => by simp [wa])
  have hle : ∀ m ≤ Kv.toNat, ((List.range m).map wa).sum ≤ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]; rw [List.sum_append_nat]; simp only [List.sum_cons, List.sum_nil]
      have := hab m (by omega); have := ih (by omega)
      omega
  have hlt : 0 < Kv.toNat → ((Enc.raw .i64 Kv I)[Kv.toNat - 1]?.getD 0).toNat < 2 ^ 63 := by
    intro hk
    rw [hsum _ (by omega), Nat.sub_add_cancel hk]
    have := hle _ (Nat.le_refl _)
    rw [toNat_toUInt64 (by omega)]
    omega
  have hcl := colPrefix_closed hI
  obtain ⟨x, hx0⟩ : ∃ x, lastCount Kv I hcl.2.1 hcl.2.2 = x := ⟨_, rfl⟩
  rw [hx0] at hnb
  subst hnb
  have hlast : (if Kv = 0 then 0 else (r1.2.getD 0).toUSize + 0) + 1 = (x + 1).toUSize := by
    have hf : ∃ md pk, I = .foR md pk := hr1e ▸ kscan_foR hk1
    by_cases h0 : Kv = 0
    · have := lastCount_eq hcl.2.1 hcl.2.2 hf (x := 0) (by omega) (fun h => by simp [h0] at h) (fun _ => rfl)
      rw [hx0] at this; subst this; simp [h0]
    · have hk : 0 < Kv.toNat := by
        have : Kv.toNat ≠ 0 := fun h => h0 (USize.toNat_inj.mp (by simpa using h))
        omega
      have hl := kscan_last (w := 8) rfl (kscanStream_ne (by decide) _ _ _) (colPrefix_hF hz1 (Or.inl rfl)) hk1
      rw [hr1e] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      have := lastCount_eq hcl.2.1 hcl.2.2 hf (x := ((Enc.raw .i64 Kv I)[Kv.toNat - 1]?.getD 0).toNat) (hlt hk)
        (fun _ => by simp) (fun h => absurd h (by omega))
      rw [hx0] at this
      rw [if_neg h0, hl, this, USize.add_zero, ← USize.ofNat_uInt64ToNat, Nat.toUSize, USize.ofNat_add]
      rfl
  -- the registers
  obtain ⟨hx1, hx'⟩ := mapM_get_cons hx
  obtain ⟨hx2, hx'⟩ := mapM_get_cons hx'
  obtain ⟨hx3, hx'⟩ := mapM_get_cons hx'
  obtain ⟨-, hx'⟩ := mapM_get_cons hx'
  obtain ⟨hx5, hx'⟩ := mapM_get_cons hx'
  obtain ⟨-, hx'⟩ := mapM_get_cons hx'
  obtain ⟨-, hx'⟩ := mapM_get_cons hx'
  obtain ⟨hx8, -⟩ := mapM_get_cons hx'
  obtain ⟨fwin, hwin'⟩ := colMap_kscan hwin
  obtain ⟨fbig, hbig'⟩ := colMap_kscan hbig
  obtain ⟨fprev, hprev'⟩ := colMap_kscan hprev
  obtain ⟨fc1, hc1'⟩ := colMap_kscan hc1
  obtain ⟨fc2, hc2'⟩ := colMap_kscan hc2
  obtain ⟨fcut, hcut'⟩ := colMap_kscan hcut
  obtain ⟨fy, hy'⟩ := colMap_kscan hy
  obtain ⟨fa, ha'⟩ := colMap_kscan ha
  have hgp := fun l h => opChain_get_put l h
  unfold compCutsB
  dsimp only
  simp only [bind_assoc]
  refine prefixB_builds (by rop) hx5 hx8 hz0 hk0 hr0 hfo ?_
  intro fg2 p0 l0 ys he hf ho hp0 _
  rw [hr0e] at hp0
  have hm0 : Extends rs (rs ++ ys) := fun h => get_app h
  up hm0 [hn hx1 hx2 hx3 hx5]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hx5 hp0 (enc_get_put _) hp0 (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop)
    (hgp _ (by intro q hq; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq; rcases hq with (rfl | rfl) | rfl <;> rop)) hwin') fun win' R1 hw1 m1 => ?_
  up m1 [hn hx1 hx2 hx3 hx5]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hx5 (m1 (get_app hx8)) (enc_get_put _)
    (m1 (get_app hx8)) (enc_get_put _) (by rop) (qtype_get_put _) (qtype_get_put _) (by rop)
    (hgp _ (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; rop)) hbig')
    fun big' R2 hb2 m2 => ?_
  up m2 [hn hx1 hx2 hx3 hx5 hw1]
  refine Builds.bind1F Free.posB posB_builds fun pos R3 hpos m3 => ?_
  up m3 [hn hx1 hx2 hx3 hx5 hw1 hb2]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hx5 hpos (enc_get_put _) hpos (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop)
    (hgp _ (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl <;> rop)) hprev') fun prev' R4 hpr4 m4 => ?_
  up m4 [hn hx1 hx2 hx3 hx5 hw1 hb2 hpos]
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hx5 hpr4 hx5 hw1 hpw) fun pw' R5 hpw5 m5 => ?_
  up m5 [hn hx1 hx2 hx3 hx5 hw1 hb2 hpos hpr4]
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hx5 hpr4 hx5 hb2 hpb) fun pb' R6 hpb6 m6 => ?_
  up m6 [hn hx1 hx2 hx3 hx5 hw1 hb2 hpos hpw5]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hx5 hw1 (enc_get_put _) hpw5 (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hc1') fun c1' R7 hc7 m7 => ?_
  up m7 [hn hx1 hx2 hx3 hx5 hb2 hpos hpb6]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hx5 hb2 (enc_get_put _) hpb6 (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hc2') fun c2' R8 hc8 m8 => ?_
  up m8 [hn hx1 hx2 hx3 hx5 hpos hc7]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hx5 hc7 (enc_get_put _) hc8 (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hcut') fun cut' R9 hcut9 m9 => ?_
  up m9 [hn hx1 hx2 hx3 hx5 hpos]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hx5 hpos (enc_get_put _) hpos (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop)
    (hgp _ (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; rop)) hy')
    fun y' R10 hy10 m10 => ?_
  up m10 [hn hx1 hx2 hx3 hx5 hpos hcut9]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hx5 hcut9 (enc_get_put _) hy10 (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) ha') fun a' R11 ha11 m11 => ?_
  up m11 [hn hx1 hx2 hx3 hx5 hpos]
  refine prefixB_builds (by rop) hx5 ha11 hz1 hk1 hr1 ho ?_
  intro fg3 i1 l1 ys1 he1 hf1 ho1 hi1 hl1
  rw [hr1e] at hi1
  have hm12 : Extends R11 (R11 ++ ys1) := fun h => get_app h
  up hm12 [hn hx1 hx2 hx3 hx5 hpos]
  refine Builds.bind1F (Free.scatterB _ _ _ _ _ _) (scatterB_builds hx1 hx2 hx3 hx1 (by rop) hsc)
    fun s R13 hs13 m13 => ?_
  up m13 [hn hx1 hx5 hpos hi1 hl1]
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hn hpos hx1 hs13 hrowG) fun g' R14 hg14 m14 => ?_
  up m14 [hn hx5 hi1 hl1]
  simp only [pure_bind]
  refine Builds.bind1F₂ (Free.lit _) (fun _ => Free.call1 _ _) (succB_builds hl1) fun nbr R15 hnb15 m15 => ?_
  up m15 [hn hx5 hi1 hg14]
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hn hg14 hx5 hi1 hbe) fun br R16 hb16 m16 => ?_
  up m16 [hnb15]
  rw [hlast] at hnb15
  exact hkk fg3 nbr br R16 (FExt.trans he he1) (hf.trans hf1) ho1
    (fun h => m16 (m15 (m14 (m13 (hm12 (m11 (m10 (m9 (m8 (m7 (m6 (m5 (m4 (m3 (m2 (m1 (hm0 h))))))))))))))))) hnb15 hb16

end Rel.Lang.Plan
