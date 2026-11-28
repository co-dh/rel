module

public import Rel.Lang.PlanSpecExpand
public import Rel.Lang.PlanSpecSelect

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `compFromB`, `compB` build `Tab.compExpand`, `Tab.compOne` (PLAN-THM-E8)

`compFromB` is `compExpand`'s chain: `expandB` of the widths, the four `kgather`/`colMap` chains of the `R` and `S`
input rows inside one `funW` (the captured `N`, `p`, `R.n` are read from the enclosing block, as in `groupsW`), then
`gatherCols` of both sides and `canonT`. The `.sub` of `S`'s row by the constant `R.n` is `colMap .first` with the post
step `(.add, 0 - n)` in `compExpand`: the two agree by `colMap_const_eq`. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel Rel.Verify

theorem Grows.expandB (K w : Nat) : Grows (Plan.expandB K w) := by
  unfold Plan.expandB
  refine (Grows.funW fun n ws => ?_).bind fun p => ?_
  · dsimp only
    split
    · refine (Grows.prefixB _ _ _).bind fun p => ?_
      obtain ⟨P, Tr⟩ := p
      exact (Grows.lit _).bind fun c => (Grows.call1 _ _).bind fun T1 => (Grows.mapB _ _ _ _ _ _ _ _).bind fun o =>
        Grows.posB.bind fun _ => Grows.posB.bind fun _ => (Grows.scatterB _ _ _ _ _ _).bind fun _ =>
        (Grows.prefixB _ _ _).bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ => Grows.posB.bind fun _ =>
        (Grows.gatherB _ _ _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => Grows.pure _
    · exact Grows.throw _
  · obtain ⟨T, es⟩ := p
    split
    · exact Grows.pure _
    · exact Grows.throw _

theorem Typed.expandB {m K w : Nat} (hK : m ≤ K) (hw : m ≤ w) :
    Typed m (fun r : Nat × Nat × Nat => m ≤ r.1 ∧ m ≤ r.2.1 ∧ m ≤ r.2.2) (Plan.expandB K w) := by
  unfold Plan.expandB
  refine (Typed.funW hK (ws := [w]) (by simpa [AllGe] using hw) fun n ws hn hws => ?_).bind fun p hp => ?_
  · dsimp only
    split
    · rename_i w'
      have hw' : m ≤ w' := hws w' (by simp)
      refine (Typed.prefixB hn hw').bind fun p hp => ?_
      obtain ⟨P, Tr⟩ := p
      obtain ⟨hP, hTr⟩ := hp
      dsimp only at hP hTr ⊢
      refine (Typed.lit _).bind fun c hc => ?_
      refine (Typed.call1 (by intro a ha; simp at ha; omega)).bind fun T1 hT1 => ?_
      refine (Typed.mapB hn hP hw').bind fun o ho => ?_
      refine Typed.posB.bind fun pa hpa => ?_
      refine Typed.posB.bind fun pb hpb => ?_
      refine Typed.scatterB.bind fun s hs => ?_
      refine (Typed.prefixB hT1 hs).bind fun q hq => ?_
      refine Typed.gatherB.bind fun G hG => ?_
      refine Typed.posB.bind fun pc hpc => ?_
      refine Typed.gatherB.bind fun g hg => ?_
      refine (Typed.mapB hTr hpc hg).bind fun u hu => ?_
      exact Typed.pure ⟨hTr, by simp [AllGe]; exact ⟨hG, hu⟩⟩
    · exact Typed.throw _
  · obtain ⟨T, es⟩ := p
    obtain ⟨hT, hes⟩ := hp
    match es, hes with
    | [G, u], hes => exact Typed.pure ⟨hT, hes G (by simp), hes u (by simp)⟩
    | [], _ | [_], _ | _ :: _ :: _ :: _, _ => exact Typed.throw _


/-- `compFromB`'s plan function body (its `funW` argument, copied so `Typed` and `Grows` can name it; the proof of
    `compFromB_builds` checks the copy by defeq): `nr` is `R.n`, `N` and `p` the sorted rows' count and permutation, all
    read from the enclosing block as `groupsW` does. -/
def compW (nr N p : Nat) (K : Nat) (ws : List Nat) : Bld (Nat × List Nat) := do
  let [f, cR, cS, w] := ws | throw "compOne: not four columns"
  let (T, G, u) ← expandB K w
  let ft ← gatherB T G K f
  let ct ← gatherB T G K cS
  let iR ← gatherB T (← mapB .add T ft (← mapB .div T u ct)) N p
  let qS ← mapB .add T (← mapB .add T ft (← gatherB T G K cR)) (← mapB .mod T u ct)
  pure (T, [iR, ← mapB .sub T (← gatherB T qS N p) (← constB T (← call1 (kernel% USize.toUInt64) #[nr]))])

theorem Grows.compW (nr N p K : Nat) (ws : List Nat) : Grows (Plan.compW nr N p K ws) := by
  unfold Plan.compW
  split
  · refine (Grows.expandB _ _).bind fun q => ?_
    obtain ⟨T, G, u⟩ := q
    dsimp only
    exact (Grows.gatherB _ _ _ _).bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ =>
      (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
      (Grows.gatherB _ _ _ _).bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ =>
      (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
      (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ =>
      (Grows.call1 _ _).bind fun _ => (Grows.constB _ _).bind fun _ =>
      (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => Grows.pure _
  · exact Grows.throw _

theorem Typed.compW {m n : Nat} {ws : List Nat} (nr N p : Nat) (hn : m ≤ n) (hws : AllGe m ws) :
    Typed m (fun r => m ≤ r.1 ∧ AllGe m r.2) (Plan.compW nr N p n ws) := by
  unfold Plan.compW
  match ws, hws with
  | [f, cR, cS, w], hws =>
    have hw : m ≤ w := hws w (by simp)
    dsimp only
    refine (Typed.expandB hn hw).bind fun q hq => ?_
    obtain ⟨T, G, u⟩ := q
    obtain ⟨hT, hG, hu⟩ := hq
    dsimp only at hT hG hu ⊢
    refine Typed.gatherB.bind fun ft hft => ?_
    refine Typed.gatherB.bind fun ct hct => ?_
    refine (Typed.mapB hT hu hct).bind fun l1 hl1 => ?_
    refine (Typed.mapB hT hft hl1).bind fun l2 hl2 => ?_
    refine Typed.gatherB.bind fun iR hiR => ?_
    refine Typed.gatherB.bind fun m1 hm1 => ?_
    refine (Typed.mapB hT hft hm1).bind fun m2 hm2 => ?_
    refine (Typed.mapB hT hu hct).bind fun m3 hm3 => ?_
    refine (Typed.mapB hT hm2 hm3).bind fun q hq => ?_
    refine Typed.gatherB.bind fun pq hpq => ?_
    refine Typed.u64B.bind fun nn hnn => ?_
    refine Typed.constB.bind fun kc hkc => ?_
    refine (Typed.mapB hT hpq hkc).bind fun s hs => ?_
    exact Typed.pure ⟨hT, by intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption⟩
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | _ :: _ :: _ :: _ :: _ :: _, _ => exact Typed.throw _

/-- **`compFromB` builds `Tab.compExpand`**: `R'`, `S'` hold `R`, `S` in `rs`, the registers `x1 … x8` hold
    `compGroups`' answer, `R.compExpand S` of it answers `T'`; `kk` continues with a table of `R'`'s key shape and
    `S'`'s value shape whose registers hold `T'`. The kernel facts `compExpand` leaves open are premises: `hwn hlt`
    (`expandB_spec`'s), `hsub` (the `.sub` of `S`'s row by the constant `R.n`, which `compExpand` writes as one
    `colMap .first` with a post step), and `hcn` (`canonT_builds`'s, for the table `canon` is taken of). -/
def CompFromSpec (A B C : Obj) : Prop := ∀ {R : Tab A B} {S : Tab B C} {T' : Tab A C} {R' S' : TabB}
    {fg : Array Fun × Array Fun} {rs : Array Val} {Nv Kv : USize} {pv gv fv cRv cSv wv : Enc}
    {x1 x2 x3 x4 x5 x6 x7 x8 : Nat} {kk : TabB → Bld (Array Nat)} {out : Array Val},
    ColsOf A R'.key → ColsOf B R'.val → ColsOf B S'.key → ColsOf C S'.val →
    R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
    S'.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
    [x1, x2, x3, x4, x5, x6, x7, x8].mapM (fun i => rs[i]?) = some [.size Nv, Reg.put pv, Reg.put gv, Reg.put fv,
      .size Kv, Reg.put cRv, Reg.put cSv, Reg.put wv] →
    R.compExpand S (Nv, pv, gv, fv, Kv, cRv, cSv, wv) = .ok T' → hasNul wv = false →
    (∀ P, colPrefix .add Kv wv = .ok P → 0 < Kv.toNat → ((P.raw .i64 Kv)[Kv.toNat - 1]?.getD 0).toNat < 2 ^ 63) →
    (∀ T pq e k, colMap .first T pq pq .i64 .i64 [] [(.add, 0 - R.n.toUInt64)] = .ok e →
      colConst T R.n.toUInt64 = .ok k → ∃ o, colMap .sub T pq k = .ok o) →
    (∀ W : Tab A C, W.canon = .ok T' → W.n.toNat ≤ 2 ^ 63 ∧ ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) W.n 0 = .ok z ∧
      ∀ es vs p k g f, ValsB.cols (A := .prod A C) (W.key, W.val) = .ok es → kasc W.n es = .ok (vs, p) →
        kseen W.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
        ∃ r, kscan .max false .i64 .i64 W.n (some z) [(W.n, z), (W.n, g)] [] [] = .ok r) →
    Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape R'.key → Cols.shape W.val = Cols.shape S'.val →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (compFromB R' S' (x1, x2, x3, x4, x5, x6, x7, x8) >>= kk) rs out

theorem compFromB_builds (A B C : Obj) : CompFromSpec A B C := by
  intro R S T' R' S' fg rs Nv Kv pv gv fv cRv cSv wv x1 x2 x3 x4 x5 x6 x7 x8 kk out hRk hRv hSk hSv hR hS hx hE hwn hlt
    hsub hcn hfo hkk
  unfold Tab.compExpand at hE
  dsimp only at hE
  obtain ⟨⟨Tv, G0, uc⟩, hex, hE⟩ := except_bind_ok hE
  obtain ⟨ft, hft, hE⟩ := except_bind_ok hE
  obtain ⟨ct, hct, hE⟩ := except_bind_ok hE
  obtain ⟨a1, ha1, hE⟩ := except_bind_ok hE
  obtain ⟨a2, ha2, hE⟩ := except_bind_ok hE
  obtain ⟨iR, hiR, hE⟩ := except_bind_ok hE
  obtain ⟨b1, hb1, hE⟩ := except_bind_ok hE
  obtain ⟨b2, hb2, hE⟩ := except_bind_ok hE
  obtain ⟨b3, hb3, hE⟩ := except_bind_ok hE
  obtain ⟨qS, hqS, hE⟩ := except_bind_ok hE
  obtain ⟨pq, hpq, hE⟩ := except_bind_ok hE
  obtain ⟨iS, hiS, hE⟩ := except_bind_ok hE
  obtain ⟨y1, hy1, hE⟩ := except_bind_ok hE
  obtain ⟨y2, hy2, hE⟩ := except_bind_ok hE
  -- the plan's `.sub` against the constant column answers `compExpand`'s one `colMap .first` with a post step
  obtain ⟨kc, hkc⟩ : ∃ kc, colConst Tv R.n.toUInt64 = .ok kc :=
    let ⟨md, pk, h⟩ := Rel.colConst_ok Tv R.n.toUInt64; ⟨_, h⟩
  obtain ⟨o, ho⟩ := hsub Tv pq iS kc hiS hkc
  obtain rfl : iS = o := (colMap_const_eq hkc ho hiS
    (fun w _ h => by rw [← h]; exact congrArg Except.ok (neg_add_word w _).symm)).symm
  obtain ⟨f1, ho1⟩ := colMap_kscan ho
  obtain ⟨fa1, ha1'⟩ := colMap_kscan ha1
  obtain ⟨fa2, ha2'⟩ := colMap_kscan ha2
  obtain ⟨fb2, hb2'⟩ := colMap_kscan hb2
  obtain ⟨fb3, hb3'⟩ := colMap_kscan hb3
  obtain ⟨fq, hqS'⟩ := colMap_kscan hqS
  have hRe : R'.regs = R'.n :: (Cols.regs R'.key ++ Cols.regs R'.val) := by simp [TabB.regs, Cols.regs_append]
  have hSe : S'.regs = S'.n :: (Cols.regs S'.key ++ Cols.regs S'.val) := by simp [TabB.regs, Cols.regs_append]
  rw [hRe] at hR
  rw [hSe] at hS
  obtain ⟨hRn, hR⟩ := mapM_get_cons hR
  obtain ⟨hSn, hS⟩ := mapM_get_cons hS
  obtain ⟨hRk', -⟩ := mapM_split (ColsOf.regs_length hRk R.key) hR
  obtain ⟨-, hSv'⟩ := mapM_split (ColsOf.regs_length hSk S.key) hS
  obtain ⟨hx1, hx⟩ := mapM_get_cons hx
  obtain ⟨hx2, hx⟩ := mapM_get_cons hx
  obtain ⟨-, hx⟩ := mapM_get_cons hx
  obtain ⟨hx4, hx⟩ := mapM_get_cons hx
  obtain ⟨hx5, hx⟩ := mapM_get_cons hx
  obtain ⟨hx6, hx⟩ := mapM_get_cons hx
  obtain ⟨hx7, hx⟩ := mapM_get_cons hx
  obtain ⟨hx8, -⟩ := mapM_get_cons hx
  obtain ⟨hcN, z, hcz, hcs⟩ := hcn ⟨Tv, y1, y2⟩ hE
  unfold compFromB
  dsimp only
  simp only [bind_assoc]
  let pv5 : Array Val := #[.size Kv, Reg.put fv, Reg.put cRv, Reg.put cSv, Reg.put wv]
  refine funW_builds (k := 2) (pv := pv5) (o := #[.size Tv, Reg.put iR, Reg.put iS])
    (fun _ => reads_of (by simp [pv5, hx4, hx5, hx6, hx7, hx8])) rfl ?_ ?_ (fun n ws => ?_) hfo ?_
  · rw [show List.range' (rs.size + 1) [x4, x6, x7, x8].length =
      [rs.size + 1, rs.size + 2, rs.size + 3, rs.size + 4] from rfl]
    dsimp only
    simp only [bind_assoc, pure_bind]
    have hK1 : (rs ++ pv5)[rs.size]? = some (.size Kv) := by simp [pv5]
    have hf1 : (rs ++ pv5)[rs.size + 1]? = some (Reg.put fv) := by simp [pv5]
    have hc1 : (rs ++ pv5)[rs.size + 2]? = some (Reg.put cRv) := by simp [pv5]
    have hs1 : (rs ++ pv5)[rs.size + 3]? = some (Reg.put cSv) := by simp [pv5]
    have hw1 : (rs ++ pv5)[rs.size + 4]? = some (Reg.put wv) := by simp [pv5]
    have hNr := get_app (xs := pv5) hx1
    have hpr := get_app (xs := pv5) hx2
    have hRn := get_app (xs := pv5) hRn
    refine expandB_spec hK1 hw1 hwn hlt hex hfo ?_
    intro fg2 ys a b c he hf ho hread
    obtain ⟨hTr, hread⟩ := mapM_get_cons hread
    obtain ⟨hG, hread⟩ := mapM_get_cons hread
    obtain ⟨hu, -⟩ := mapM_get_cons hread
    have hK1 := get_app (xs := ys) hK1
    have hf1 := get_app (xs := ys) hf1
    have hc1 := get_app (xs := ys) hc1
    have hs1 := get_app (xs := ys) hs1
    have hNr := get_app (xs := ys) hNr
    have hpr := get_app (xs := ys) hpr
    have hRn := get_app (xs := ys) hRn
    dsimp only
    refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hTr hG hK1 hf1 hft) fun ft' R1 hft1 hE1 => ?_
    up hE1 [hTr hG hu hK1 hc1 hs1 hNr hpr hRn]
    refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hTr hG hK1 hs1 hct) fun ct' R2 hct2 hE2 => ?_
    up hE2 [hTr hG hu hK1 hc1 hNr hpr hRn hft1]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hTr hu (enc_get_put _) hct2 (enc_get_put _)
      (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) ha1') fun l1 R3 hl3 hE3 => ?_
    up hE3 [hTr hG hu hK1 hc1 hNr hpr hRn hft1 hct2]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hTr hft1 (enc_get_put _) hl3 (enc_get_put _)
      (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) ha2') fun l2 R4 hl4 hE4 => ?_
    up hE4 [hTr hG hu hK1 hc1 hNr hpr hRn hft1 hct2]
    refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hTr hl4 hNr hpr hiR) fun iR' R5 hiR5 hE5 => ?_
    up hE5 [hTr hG hu hK1 hc1 hNr hpr hRn hft1 hct2]
    refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hTr hG hK1 hc1 hb1) fun m1 R6 hm6 hE6 => ?_
    up hE6 [hTr hu hNr hpr hRn hft1 hct2 hiR5]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hTr hft1 (enc_get_put _) hm6 (enc_get_put _)
      (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hb2') fun m2 R7 hm7 hE7 => ?_
    up hE7 [hTr hu hNr hpr hRn hct2 hiR5]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hTr hu (enc_get_put _) hct2 (enc_get_put _)
      (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hb3') fun m3 R8 hm8 hE8 => ?_
    up hE8 [hTr hNr hpr hRn hiR5 hm7]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hTr hm7 (enc_get_put _) hm8 (enc_get_put _)
      (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hqS') fun q R9 hq9 hE9 => ?_
    up hE9 [hTr hNr hpr hRn hiR5]
    refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hTr hq9 hNr hpr hpq) fun pq' R10 hpq10 hE10 => ?_
    up hE10 [hTr hRn hiR5]
    refine Builds.bind1F (Free.call1 _ _) (u64B_builds hRn) fun nn R11 hnn hE11 => ?_
    up hE11 [hTr hiR5 hpq10]
    refine Builds.bind1F (Free.constB _ _) (constB_builds hTr hnn (by rw [← Rel.colConst_eq]; exact hkc)) fun kc' R12 hkc12 hE12 => ?_
    up hE12 [hTr hiR5 hpq10]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hTr hpq10 (enc_get_put _) hkc12 (enc_get_put _)
      (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) ho1) fun s R13 hs13 hE13 => ?_
    up hE13 [hTr hiR5]
    exact ⟨fg2, Builds.answerRegs ⟨rfl, [iR', s], rfl, rfl⟩ (tabsRegs_eq _) fun _ =>
      reads_of (by simp [TabB.regs, Cols.regs, Col.regs, hTr, hiR5, hs13])⟩
  · rw [show List.range' (rs.size + 1) [x4, x6, x7, x8].length =
      [rs.size + 1, rs.size + 2, rs.size + 3, rs.size + 4] from rfl]
    have hws : AllGe rs.size [rs.size + 1, rs.size + 2, rs.size + 3, rs.size + 4] := by
      intro a ha; simp at ha; omega
    exact (Typed.compW R'.n x1 x2 (Nat.le_refl _) hws).mono fun _ _ => trivial
  · exact Grows.compW _ _ _ _ _
  · intro fg2 m es ys he hf ho hlen hread
    match es, hlen with
    | [iRr, iSr], _ =>
      have hread' : (m :: [iRr, iSr]).mapM (fun i => (rs ++ ys)[i]?) =
          some [.size Tv, Reg.put iR, Reg.put iS] := hread
      obtain ⟨hm, hread'⟩ := mapM_get_cons hread'
      obtain ⟨hiR', hread'⟩ := mapM_get_cons hread'
      obtain ⟨hiS', -⟩ := mapM_get_cons hread'
      simp only [bind_assoc, pure_bind]
      refine gatherCols_builds A (x := R.key) (y := y1) hRk (mapM_get_app hRk') hm hiR' (get_app hRn) hy1 ho ?_
      intro fg3 cs1 ys1 he1 hf1 ho1 hs1 hr1
      refine gatherCols_builds C (x := S.val) (y := y2) hSv (mapM_get_app (mapM_get_app hSv')) (get_app hm)
        (get_app hiS') (get_app (get_app hSn)) hy2 ho1 ?_
      intro fg4 cs2 ys2 he2 hf2 ho2 hs2 hr2
      refine canonT_builds (R := ⟨Tv, y1, y2⟩) (R' := T') (T := ⟨m, cs1, cs2⟩) (ColsOf.shape A hRk hs1)
        (ColsOf.shape C hSv hs2) ?_ hE hcN hcz hcs ho2 ?_
      · simp only [TabB.regs, Cols.regs_append]
        refine omapM_cons.mpr ⟨_, _, get_app (get_app hm), ?_, rfl⟩
        rw [List.mapM_append, mapM_get_app hr1, hr2]
        rfl
      · intro fg5 U ys3 he3 hf3 ho3 hsk hsv hreg
        have e : ((((rs ++ ys) ++ ys1) ++ ys2) ++ ys3) = rs ++ (((ys ++ ys1) ++ ys2) ++ ys3) := by
          simp only [Array.append_assoc]
        rw [e] at hreg ⊢
        obtain ⟨e1, h1⟩ := he
        obtain ⟨e2, h2⟩ := he1
        obtain ⟨e3, h3⟩ := he2
        obtain ⟨e4, h4⟩ := he3
        exact hkk fg5 U _ ⟨e1 ++ (e2 ++ (e3 ++ e4)), by rw [h4, h3, h2, h1]; simp only [Array.append_assoc]⟩
          (hf.trans (hf1.trans (hf2.trans hf3))) ho3 (hsk.trans hs1)
          (hsv.trans hs2) hreg

/-! ### `compB`: `funT` of `groupsB` then `compFromB` -/

/-- `groupsW`'s answer registers lie above `m`, where its group count `K` and rows `N` do. -/
theorem Typed.groupsWOut {m nr K N : Nat} {ws : List Nat} (hK : m ≤ K) (hN : m ≤ N) (hws : AllGe m ws) :
    Typed m (fun r => m ≤ r.1 ∧ AllGe m r.2) (Plan.groupsW nr K N ws) := by
  unfold Plan.groupsW
  match ws, hws with
  | [g, p], hws =>
    have hp := hws p (by simp)
    dsimp only
    refine Typed.u64B.bind fun w _ => Typed.constB.bind fun nR hnR => (Typed.mapB hN hp hnR).bind fun o ho =>
      Typed.scatterB.bind fun cR hcR => Typed.wordsB.bind fun one _ => Typed.scatterB.bind fun sc hsc =>
      (Typed.mapBAny hsc hcR).bind fun cS hcS => (Typed.mapBAny hcR hcS).bind fun wv hwv =>
      Typed.pure ⟨hK, by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> assumption⟩
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => exact Typed.throw _

theorem Grows.groupsB (R S : TabB) : Grows (Plan.groupsB R S) := by
  unfold Plan.groupsB
  refine (Grows.catB _ _).bind fun p => ?_
  obtain ⟨n, off⟩ := p
  refine (Grows.concatB (Col.sizes R.val + 1) _ _ _ _ _ _ (Nat.lt_succ_self _)).bind fun _ =>
    (Grows.ascSeenB _ _).bind fun q => ?_
  obtain ⟨K, g, f, p⟩ := q
  refine (Grows.funW fun n ws => Grows.groupsW _ _ _ _).bind fun q => ?_
  obtain ⟨T, es⟩ := q
  split
  · exact Grows.pure _
  · exact Grows.throw _

/-- The eight registers `groupsB` answers, as a list. -/
def reg8 (x : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) : List Nat :=
  [x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2]

theorem Typed.groupsB {m : Nat} {R S : TabB} (hR : AllGe m R.regs) (hS : AllGe m S.regs) :
    Typed m (fun x => AllGe m (reg8 x)) (Plan.groupsB R S) := by
  have hRn : m ≤ R.n := hR _ (by simp [TabB.regs])
  have hSn : m ≤ S.n := hS _ (by simp [TabB.regs])
  have hRv : AllGe m (Cols.regs R.val) := fun a ha => hR a (by simp [TabB.regs, Cols.regs_append, ha])
  have hSk : AllGe m (Cols.regs S.key) := fun a ha => hS a (by simp [TabB.regs, Cols.regs_append, ha])
  unfold Plan.groupsB
  refine (Typed.catB hRn hSn).bind fun p hp => ?_
  obtain ⟨n, off⟩ := p
  obtain ⟨hn, hoff⟩ := hp
  dsimp only at hn hoff ⊢
  refine ((Typed.concatBOf (S := []) (Col.sizes R.val + 1) n R.n S.n off R.val S.key (Nat.lt_succ_self _) (.inl hn)
    hRn hSn hRv hSk).mono fun r h a ha => (h a ha).resolve_right (by simp)).bind fun cs hcs => ?_
  refine (Typed.ascSeenB cs hn hcs).bind fun q hq => ?_
  obtain ⟨K, g, f, p⟩ := q
  obtain ⟨hK, hg, hf, hp⟩ := hq
  dsimp only at hK hg hf hp ⊢
  refine (Typed.funW hn (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption)
    fun n' ws hn' hws => Typed.groupsWOut hK hn' hws).bind fun q hq => ?_
  obtain ⟨T, es⟩ := q
  obtain ⟨hT, hes⟩ := hq
  match es, hes with
  | [cR, cS, w], hes =>
    refine Typed.pure ?_
    intro a ha
    simp only [reg8, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | assumption | exact hes _ (by simp)
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => exact Typed.throw _

theorem Grows.compFromB (R S : TabB) (x : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
    Grows (Plan.compFromB R S x) := by
  obtain ⟨N, p, g, f, K, cR, cS, w⟩ := x
  unfold Plan.compFromB
  dsimp only
  refine (Grows.funW fun n ws => Grows.compW _ _ _ _ _).bind fun q => ?_
  obtain ⟨T, es⟩ := q
  split
  · exact (Grows.gatherCols _ _ _ _).bind fun _ => (Grows.gatherCols _ _ _ _).bind fun _ => Grows.canonT _
  · exact Grows.throw _

theorem Typed.compFromB {m : Nat} {R S : TabB} (hR : AllGe m R.regs) (hS : AllGe m S.regs)
    {x : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat} (hx : AllGe m (reg8 x)) :
    Typed m (fun U => AllGe m U.regs) (Plan.compFromB R S x) := by
  have hRn : m ≤ R.n := hR _ (by simp [TabB.regs])
  have hSn : m ≤ S.n := hS _ (by simp [TabB.regs])
  have hRk : AllGe m (Cols.regs R.key) := fun a ha => hR a (by simp [TabB.regs, Cols.regs_append, ha])
  have hSv : AllGe m (Cols.regs S.val) := fun a ha => hS a (by simp [TabB.regs, Cols.regs_append, ha])
  obtain ⟨N, p, g, f, K, cR, cS, w⟩ := x
  simp only [reg8, AllGe, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  obtain ⟨-, -, -, hf, hK, hcR, hcS, hw⟩ := hx
  unfold Plan.compFromB
  dsimp only
  refine (Typed.funW hK (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> assumption)
    fun n' ws hn' hws => Typed.compW R.n N p hn' hws).bind fun q hq => ?_
  obtain ⟨T, es⟩ := q
  obtain ⟨hT, hes⟩ := hq
  match es, hes with
  | [iR, iS], hes =>
    refine (Typed.gatherCols hT R.n R.key hRn hRk).bind fun ks hks =>
      (Typed.gatherCols hT S.n S.val hSn hSv).bind fun vs hvs => (Typed.canonT _ ?_)
    intro a ha
    simp only [TabB.regs, Cols.regs_append, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ha | ha
    · exact hT
    · exact hks a ha
    · exact hvs a ha
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => exact Typed.throw _

/-- The body of `compB`'s plan function (`funT [R, S]`). -/
def compBody (R S : TabB) : Bld TabB := do compFromB R S (← groupsB R S)

theorem compOneB_eq (R S : TabB) :
    compOneB R S = funT [R, S] (fun | [R, S] => compBody R S | _ => throw "comp: not two tables") := rfl

theorem Grows.compBody (R S : TabB) : Grows (Plan.compBody R S) :=
  (Grows.groupsB R S).bind fun x => Grows.compFromB R S x

theorem Typed.compBody {m : Nat} {R S : TabB} (hR : AllGe m R.regs) (hS : AllGe m S.regs) :
    Typed m (fun U => AllGe m U.regs) (Plan.compBody R S) :=
  (Typed.groupsB hR hS).bind fun x hx => Typed.compFromB hR hS hx

/-- The kernel facts `compGroups` and `compExpand` leave open, for the groups `x` of `R ≫ S`: the premises of
    `groupsB_builds` (`GroupsSpec`) and of `compFromB_builds` (`CompFromSpec`) that read `x`. -/
def CompPre (A B C : Obj) (R : Tab A B) (S : Tab B C) : Prop :=
  ∀ N p g f K cR cS wc, R.compGroups S = .ok (N, p, g, f, K, cR, cS, wc) →
    (∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) N 0 = .ok z ∧
      ∃ r, kscan .max false .i64 .i64 N (some z) [(N, z), (N, g)] [] [] = .ok r) ∧
    (∃ k, colConst N R.n.toUInt64 = .ok k ∧ ∃ o, colMap .lt N p k = .ok o) ∧ hasNul wc = false ∧
    (∀ P, colPrefix .add K wc = .ok P → 0 < K.toNat → ((P.raw .i64 K)[K.toNat - 1]?.getD 0).toNat < 2 ^ 63)

/-- The kernel facts of `CompFromSpec` that read no `compGroups` answer: `hsub` and `hcn` of it. -/
def CompPost (A B C : Obj) (R : Tab A B) (T' : Tab A C) : Prop :=
  (∀ T pq e k, colMap .first T pq pq .i64 .i64 [] [(.add, 0 - R.n.toUInt64)] = .ok e →
      colConst T R.n.toUInt64 = .ok k → ∃ o, colMap .sub T pq k = .ok o) ∧
  (∀ W : Tab A C, W.canon = .ok T' → W.n.toNat ≤ 2 ^ 63 ∧ ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) W.n 0 = .ok z ∧
      ∀ es vs p k g f, ValsB.cols (A := .prod A C) (W.key, W.val) = .ok es → kasc W.n es = .ok (vs, p) →
        kseen W.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
        ∃ r, kscan .max false .i64 .i64 W.n (some z) [(W.n, z), (W.n, g)] [] [] = .ok r)

/-- **`compBody` builds `Tab.compOne`**: `R'`, `S'` hold `R`, `S` in `rs`, `R.compOne S = T'`; `kk` continues with a
    table of `R'`'s key shape and `S'`'s value shape whose registers hold `T'` (in any extension of `rs`). -/
def CompBodySpec (A B C : Obj) : Prop := ∀ {R : Tab A B} {S : Tab B C} {T' : Tab A C} {R' S' : TabB}
    {fg : Array Fun × Array Fun} {rs : Array Val} {kk : TabB → Bld (Array Nat)} {out : Array Val},
    ColsOf A R'.key → ColsOf B R'.val → ColsOf B S'.key → ColsOf C S'.val →
    R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
    S'.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
    R.compOne S = .ok T' → CompPre A B C R S → CompPost A B C R T' → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (U : TabB) (Rn : Array Val), Extends rs Rn → (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Cols.shape U.key = Cols.shape R'.key → Cols.shape U.val = Cols.shape S'.val →
      U.regs.mapM (fun i => Rn[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk U) Rn out) →
    ∃ fg', Builds abiOf fg fg' (compBody R' S' >>= kk) rs out

theorem compBody_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A B C : Obj) : CompBodySpec A B C := by
  intro R S T' R' S' fg rs kk out hRk hRv hSk hSv hR hS hOne hpre hpost hfo hkk
  unfold Tab.compOne at hOne
  obtain ⟨⟨N, p, g, f, K, cR, cS, wc⟩, hG, hE⟩ := except_bind_ok hOne
  obtain ⟨hz, hn, hwn, hlt⟩ := hpre _ _ _ _ _ _ _ _ hG
  unfold compBody
  simp only [bind_assoc]
  refine groupsB_builds hc h63 A B C hRk hRv hSk hSv hR hS hG hz hn hfo ?_
  intro fg2 Rn a b c d e f' g' h he hf ho hext hread
  refine compFromB_builds A B C hRk hRv hSk hSv (mapM_extends hext hR) (mapM_extends hext hS) hread hE hwn hlt
    hpost.1 hpost.2 ho ?_
  intro fg3 U ys he3 hf3 ho3 hsk hsv hreg
  obtain ⟨e1, h1⟩ := he
  obtain ⟨e2, h2⟩ := he3
  exact hkk fg3 U (Rn ++ ys) (fun h => get_app (hext h)) ⟨e1 ++ e2, by rw [h2, h1, Array.append_assoc]⟩
    (hf.trans hf3) ho3 hsk hsv hreg

/-- **`compB` builds `Tab.compOne`**: the tables `R'`, `S'` hold `R`, `S` in `rs`; `kk` continues with a table of
    `R'`'s key shape and `S'`'s value shape whose registers hold `T'`. -/
def CompSpec (A B C : Obj) : Prop := ∀ {R : Tab A B} {S : Tab B C} {T' : Tab A C} {R' S' : TabB}
    {fg : Array Fun × Array Fun} {rs : Array Val} {kk : TabB → Bld (Array Nat)} {out : Array Val},
    ColsOf A R'.key → ColsOf B R'.val → ColsOf B S'.key → ColsOf C S'.val →
    R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
    S'.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
    R.compOne S = .ok T' → CompPre A B C R S → CompPost A B C R T' → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape R'.key → Cols.shape W.val = Cols.shape S'.val →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (compOneB R' S' >>= kk) rs out

theorem compOneB_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A B C : Obj) : CompSpec A B C := by
  intro R S T' R' S' fg rs kk out hRk hRv hSk hSv hR hS hone hpre hpost hfo hkk
  have hlR := mapM_get_length hR
  have hlS := mapM_get_length hS
  obtain ⟨R1, S1, hUs, hsR1, hsR2, hsS1, hsS2, hr1, hs1⟩ := tabsAt_two R' S' rs.size
  let pv : List Val := (.size R.n :: (R.key.regVals ++ R.val.regVals)) ++ (.size S.n :: (S.key.regVals ++ S.val.regVals))
  have hpl : (R'.regs ++ S'.regs).length = pv.length := by rw [List.length_append, hlR, hlS]; simp [pv]; omega
  have hA : tabsRegs [R', S'] = Pure.pure (R'.regs ++ S'.regs) := by rw [tabsRegs_eq]; simp
  have ha : ∀ who, (R'.regs ++ S'.regs).toArray.mapM (reg rs who) = .ok pv.toArray := fun _ =>
    reads_of (by rw [List.mapM_append, hR, hS]; rfl)
  have g : (R1.regs ++ S1.regs).mapM (fun i => (rs ++ pv.toArray)[i]?) = some pv := by
    rw [hr1, hs1, List.range'_append_1, ← List.length_append, hpl]
    exact mapM_range_append rs pv
  obtain ⟨gR, gS⟩ := mapM_split (by rw [hr1, List.length_range', hlR]) g
  have e1 : R1.regs = R1.n :: (Cols.regs R1.key ++ Cols.regs R1.val) := by simp [TabB.regs, Cols.regs_append]
  have e2 : S1.regs = S1.n :: (Cols.regs S1.key ++ Cols.regs S1.val) := by simp [TabB.regs, Cols.regs_append]
  let P : TabB → Prop := fun W => Cols.shape W.key = Cols.shape R'.key ∧ Cols.shape W.val = Cols.shape S'.val
  let o : Array Val := (Val.size T'.n :: (T'.key.regVals ++ T'.val.regVals)).toArray
  have hB : ∃ fg1, Builds abiOf fg fg1 (compBody R1 S1 >>= answerRegs P) (rs ++ pv.toArray) o := by
    refine compBody_builds hc h63 A B C (R := R) (S := S) (T' := T') (ColsOf.shape A hRk hsR1)
      (ColsOf.shape B hRv hsR2) (ColsOf.shape B hSk hsS1) (ColsOf.shape C hSv hsS2) gR gS hone hpre hpost hfo ?_
    intro fg4 U' ys3 he4 hf4 ho4 hs4 hs5 hs6 hr4
    refine ⟨fg4, Builds.answerRegs (P := P) ⟨hs5.trans hsR1, hs6.trans hsS2⟩ (tabsRegs_eq _) fun _ => ?_⟩
    simpa [o] using reads_of hr4
  obtain ⟨fg1, ⟨a1, ha1⟩, hb1, hB1⟩ := hB
  have hm1 : AllGe rs.size R1.regs := fun a ha => by rw [hr1, List.mem_range'_1] at ha; omega
  have hm2 : AllGe rs.size S1.regs := fun a ha => by rw [hs1, List.mem_range'_1] at ha; omega
  have hTy : Typed rs.size (fun _ => True) (compBody R1 S1) := (Typed.compBody hm1 hm2).mono fun _ _ => trivial
  obtain ⟨ctys, hcl⟩ := Typed.cloTys (fg := fg) (fg1 := fg1) (k := (R'.regs ++ S'.regs).length) hTy
  rw [compOneB_eq]
  refine funT_builds (P := P) (Us := [R1, S1]) (ctys := ctys) (o := o) hA ha hUs (hB1 #[]) hfo ?_
    (fun U body xs R rtys h _ hR hy is => hcl U body _ R rtys h hR hy is) ?_
  · intro Ts
    rcases Ts with _ | ⟨T1, _ | ⟨T2, _ | ⟨T3, Ts⟩⟩⟩ <;> try exact Grows.throw _
    exact Grows.compBody T1 T2
  · intro U' ⟨hsk, hsv⟩ fg2 Rr V ys he hf ho' hRr hV
    obtain ⟨AU, YU, u1, -, -, u4⟩ := tab_spec U'
    rw [tabsRegs_eq] at u1
    obtain rfl := (pure_inj u1).symm
    have hl : Rr.toList.length = ([U'].flatMap TabB.regs).length := by
      have h1 := mapM_ok_size (hRr "")
      have k1 := ColsOf.regs_length (ColsOf.shape A hRk hsk) T'.key
      have k2 := ColsOf.regs_length (ColsOf.shape C hSv hsv) T'.val
      simp only [o, List.size_toArray, List.length_cons, List.length_append] at h1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TabB.regs, Cols.regs_append, List.length_cons,
        List.length_append, Array.length_toList, k1, k2]
      omega
    obtain ⟨V', f1, f2, -, f4, f5⟩ := u4 Rr.toList [] (by simpa using hl)
    rw [List.append_nil] at f1
    obtain rfl : V = V' := by
      have := pure_inj (hV.symm.trans f1); simp only [Prod.mk.injEq, List.cons.injEq, and_true] at this; exact this
    rw [tabsRegs_eq] at f2
    have f2' := pure_inj f2
    have hread := holds_of_reg (hRr "")
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at f2'
    rw [← f2'] at hread
    obtain ⟨e1', he1⟩ := he
    exact hkk fg2 V ys ⟨a1 ++ e1', by rw [he1, ha1, Array.append_assoc]⟩ (by rw [hf]; exact hb1) ho'
      (f4.trans hsk) (f5.trans hsv) (by simpa [o] using hread)

end Rel.Lang.Plan
