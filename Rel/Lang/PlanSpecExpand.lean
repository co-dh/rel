module

public import Rel.Lang.PlanSpecConcat
public import Rel.Lang.PlanSpecPrefix

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `expandB` builds the kernel chain of `expand`

`expandB` is `expand`'s chain of kernels inside one `funW`: `prefixB` twice (`colPrefix`), `mapB` (`colMap .sub`),
`scatterB`, `gatherB`. Every kernel answer is a premise, as in `prefixB_builds`, and each is the answer `expand` binds:
`hz0 hk0` its first `colPrefix .add`, `ho` its `colMap .sub K P w`, `hsc` its `kscatter .max`, `hz1 hk1` its
`colPrefix .max`, `hG` its first `kgather`, `hg1 hu` the `kgather` and `colMap .sub` of the offset `u`.
`expand` reads its count `T` as `lastCount`, the last word clamped at `2^63`, where `expandB` reads the word itself
(`hT`), so the two agree where the word is below `2^63`. Not covered: the bridge from `expand K w = .ok (T, G, u)` to
these premises, and `groupsB`: its `funW` body reads the outer registers `R.n` and `K`, and `funW_builds` takes `Typed
rs.size`, a body reading no register below its own (`Typed.mapB` needs `m ≤ n`), so it needs a `funW_builds` with
captured registers first. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

theorem Free.mapB (op : Kernel.Op) (n a b : Nat) (t s : QAtomicType) (pre post : List (Kernel.Op × UInt64)) :
    Free (Plan.mapB op n a b t s pre post) := by
  unfold Plan.mapB Plan.srcB; free

theorem Free.scatterB (op : Kernel.Op) (rows dst x cells : Nat) (fill : UInt64) :
    Free (Plan.scatterB op rows dst x cells fill) := by
  unfold Plan.scatterB; free

theorem Free.gatherB (m ix n x : Nat) : Free (Plan.gatherB m ix n x) := by
  unfold Plan.gatherB; free

theorem Free.posB : Free Plan.posB := by unfold Plan.posB; free

/-- `gatherB` in the shape `Builds.bind1F` reads. -/
theorem gatherB_builds1 {fg : Array Fun × Array Fun} {rs : Array Val} {m ix n e : Nat} {mv nv : USize}
    {iv ev ov : Enc} (hm : rs[m]? = some (.size mv)) (hi : rs[ix]? = some (Reg.put iv)) (hn : rs[n]? = some (.size nv))
    (he : rs[e]? = some (Reg.put ev)) (hk : kgather mv iv nv ev = .ok ov) :
    Builds abiOf fg fg (do let r ← gatherB m ix n e; Pure.pure #[r]) rs #[Reg.put ov] := by
  exact gatherB_builds (c := fun r => Pure.pure #[r]) hm hi hn he hk (Builds.pure fun who => by simp [reg]; rfl)

theorem posB_builds {fg : Array Fun × Array Fun} {rs : Array Val} :
    Builds abiOf fg fg (do let r ← posB; Pure.pure #[r]) rs #[Reg.put (Enc.pos : Enc)] := by
  unfold posB
  exact Builds.lit (Builds.pure fun who => by simp [reg]; rfl)

/-- `call1 USize.add` of a size register and the literal `1`. -/
theorem succB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {T : Nat} {Tv : USize}
    (hT : rs[T]? = some (.size Tv)) :
    Builds abiOf fg fg (do let r ← (do let c ← lit (.size 1); call1 (kernel% USize.add) #[T, c]); Pure.pure #[r]) rs
      #[.size (Tv + 1)] := by
  simp only [bind_assoc]
  refine Builds.litG fun c R hc m => ?_
  refine Builds.call1G (vs := #[.size Tv, .size 1]) (v := .size (Tv + 1)) (by abiK) (by rop) ?_ ?_ rfl
    fun r R1 hr1 m1 => Builds.pure fun who => ?_
  · rw [List.mapM_toArray]; simp [reg, hc, m hT]; rfl
  · simp [arg]; rfl
  · simp [reg, hr1]; rfl

/-- **`expandB` builds `expand`**: `K` holds the group count `Kv`, `w` the widths `wv`. The kernel answers are the
    premises: `colPrefix .add` (`z0`, `r0`; `Tv` its last word, as `prefixB` reads it), `colMap .sub` (`oc`), `kscatter
    .max` (`sc`), `colPrefix .max` over `Tv + 1` (`z1`, `r1`), the two `kgather`s (`G0`, `g1`) and the last `colMap .sub`
    (`uc`); `kk` continues with registers holding `Tv`, `G0`, `uc`. -/
theorem expandB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {K w : Nat} {Kv Tv : USize}
    {wv z0 oc z1 sc G0 g1 uc : Enc} {r0 r1 : Enc × Option UInt64} {of f2 : Option UInt64}
    {kk : Nat × Nat × Nat → Bld (Array Nat)} {out : Array Val}
    (hK : rs[K]? = some (.size Kv)) (hw : rs[w]? = some (Reg.put wv))
    (hz0 : colConst Kv 0 = .ok z0)
    (hk0 : kscan .add false .i64 .i64 Kv (some z0) [(Kv, z0), (Kv, wv)] [] [] = .ok r0) (hr0 : Kv ≠ 0 → r0.2.isSome)
    (hT : Tv = if Kv = 0 then 0 else (r0.2.getD 0).toUSize + 0)
    (ho : kscan .sub false .i64 .i64 Kv none [(Kv, r0.1), (Kv, wv)] [] [] = .ok (oc, of))
    (hsc : kscatter .max Kv oc .pos (Tv + 1) 0 = .ok sc)
    (hz1 : colConst (Tv + 1) 0 = .ok z1)
    (hk1 : kscan .max false .i64 .i64 (Tv + 1) (some z1) [(Tv + 1, z1), (Tv + 1, sc)] [] [] = .ok r1)
    (hr1 : Tv + 1 ≠ 0 → r1.2.isSome) (hG : kgather Tv .pos (Tv + 1) r1.1 = .ok G0)
    (hg1 : kgather Tv G0 Kv oc = .ok g1)
    (hu : kscan .sub false .i64 .i64 Tv none [(Tv, .pos), (Tv, g1)] [] [] = .ok (uc, f2)) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (ys : Array Val) (a b c : Nat), (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → [a, b, c].mapM (fun i => (rs ++ ys)[i]?) =
        some [.size Tv, Reg.put G0, Reg.put uc] → ∃ fg', Builds abiOf fg2 fg' (kk (a, b, c)) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (expandB K w >>= kk) rs out := by
  unfold expandB
  rw [bind_assoc]
  refine funW_builds (k := 2) (pv := #[.size Kv, Reg.put wv]) (o := #[.size Tv, Reg.put G0, Reg.put uc])
    (fun _ => reads_of (by simp [hK, hw])) rfl ?_ ?_ (fun n ws => ?_) hfo ?_
  · rw [show List.range' (rs.size + 1) [w].length = [rs.size + 1] from rfl]
    dsimp only
    have hn' : (rs ++ #[Val.size Kv, Reg.put wv])[rs.size]? = some (.size Kv) := by simp
    have hw' : (rs ++ #[Val.size Kv, Reg.put wv])[rs.size + 1]? = some (Reg.put wv) := by simp
    rw [bind_assoc]
    simp only [bind_assoc, pure_bind]
    refine prefixB_builds (nv := Kv) (av := wv) (z := z0) (r := r0) (by rop) hn' hw' hz0 hk0 hr0 hfo ?_
    intro fg2 P Tr ys he hf hfo2 hP hTr
    rw [← hT] at hTr
    have hn1 := get_app (xs := ys) hn'
    have hw1 := get_app (xs := ys) hw'
    refine Builds.bind1F₂ (Free.lit _) (fun _ => Free.call1 _ _) (succB_builds hTr) fun T1 R2 hT1 hE2 => ?_
    up hE2 [hn1 hw1 hP hTr]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hn1 hP (enc_get_put _)
      hw1 (enc_get_put _) (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) ho)
      fun o R3 ho3 hE3 => ?_
    up hE3 [hn1 hTr hT1]
    refine Builds.bind1F Free.posB posB_builds fun pa R4 hpa hE4 => ?_
    up hE4 [hn1 hTr hT1 ho3]
    refine Builds.bind1F Free.posB posB_builds fun pb R5 hpb hE5 => ?_
    up hE5 [hn1 hTr hT1 ho3 hpa]
    refine Builds.bind1F (Free.scatterB _ _ _ _ _ _) (scatterB_builds hn1 ho3 hpb hT1 (by rop) hsc)
      fun s R6 hs6 hE6 => ?_
    up hE6 [hn1 hTr hT1 ho3 hpa]
    refine prefixB_builds (nv := Tv + 1) (av := sc) (z := z1) (r := r1) (by rop) hT1 hs6 hz1 hk1 hr1 hfo2 ?_
    intro fg3 P1 l1 ys1 he1 hf1 hfo3 hP1 hl1
    have ga : Extends R6 (R6 ++ ys1) := fun h => get_app h
    up ga [hn1 hTr hT1 ho3 hpa]
    refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hTr hpa hT1 hP1 hG) fun G R8 hG8 hE8 => ?_
    up hE8 [hn1 hTr ho3]
    refine Builds.bind1F Free.posB posB_builds fun pc R9 hpc hE9 => ?_
    up hE9 [hn1 hTr ho3 hG8]
    refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hTr hG8 hn1 ho3 hg1) fun g R10 hg10 hE10 => ?_
    up hE10 [hTr hpc hG8]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hTr hpc (enc_get_put _) hg10
      (enc_get_put _) (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hu) fun u R11 hu11 hE11 => ?_
    up hE11 [hTr hG8]
    exact ⟨fg3, Builds.answerRegs ⟨rfl, [G, u], rfl, rfl⟩ (tabsRegs_eq _) fun _ =>
      reads_of (by simp [TabB.regs, Cols.regs, Col.regs, hTr, hG8, hu11])⟩
  · rw [show List.range' (rs.size + 1) [w].length = [rs.size + 1] from rfl]
    dsimp only
    refine (Typed.prefixB (Nat.le_refl _) (Nat.le_succ _)).bind fun p hp => ?_
    obtain ⟨P, Tr⟩ := p
    obtain ⟨hP, hTr⟩ := hp
    dsimp only at hP hTr ⊢
    refine (Typed.lit _).bind fun c hc => ?_
    refine (Typed.call1 (by intro a ha; simp at ha; omega)).bind fun T1 hT1 => ?_
    refine (Typed.mapB (Nat.le_refl _) hP (Nat.le_succ _)).bind fun o ho => ?_
    refine Typed.posB.bind fun pa hpa => ?_
    refine Typed.posB.bind fun pb hpb => ?_
    refine Typed.scatterB.bind fun s hs => ?_
    refine (Typed.prefixB hT1 hs).bind fun q hq => ?_
    refine Typed.gatherB.bind fun G hG => ?_
    refine Typed.posB.bind fun pc hpc => ?_
    refine Typed.gatherB.bind fun g hg => ?_
    refine (Typed.mapB hTr hpc hg).bind fun u hu => ?_
    exact Typed.pure trivial
  · dsimp only
    split
    · refine (Grows.prefixB _ _ _).bind fun p => ?_
      obtain ⟨P, Tr⟩ := p
      exact (Grows.lit _).bind fun c => (Grows.call1 _ _).bind fun T1 => (Grows.mapB _ _ _ _ _ _ _ _).bind fun o =>
        Grows.posB.bind fun _ => Grows.posB.bind fun _ => (Grows.scatterB _ _ _ _ _ _).bind fun _ =>
        (Grows.prefixB _ _ _).bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ => Grows.posB.bind fun _ =>
        (Grows.gatherB _ _ _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => Grows.pure _
    · exact Grows.throw _
  · intro fg2 m es ys he hf ho hlen hread
    match es, hlen with
    | [g, u], _ =>
      simp only [pure_bind]
      exact hkk fg2 ys m g u he hf ho hread

end Rel.Lang.Plan
