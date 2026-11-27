module

public import Rel.Lang.PlanSpecCat

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `funW`, `prefixB`, `groupFoldB` build what `colPrefix` and `groupFold` answer

`funW` is `funV` of a table of word columns, so `funW_builds` is `funV_builds` at `⟨n, ws.map atom, []⟩`, as
`funC_builds` is `funT_builds` at one column. `prefixB` is `colPrefix`'s `kscan` (`scanB_builds`) and its last word
(`lastB_builds`); `groupFoldB` is `seenSeg`'s `kscatter`, `groupFold`'s `kscan` and `kscatter` (`scatterB_builds`,
`scanB_builds`). Both build their constant columns with `constB`, a `kscatter` of no row from `wordsFoR #[]` where
`colConst` passes `.pos`, so their lemmas take the kernel answers as premises, as `seenB_builds` does. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- `kscatter` of no rows ignores its index and value columns, so `colConst` is the `wordsFoR #[]` form `constB` builds. -/
theorem colConst_eq (n : USize) (w : UInt64) :
    colConst n w = kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) n w := by
  have h0 : ∀ s, foRWords s 0 (wordsFoR #[]) = .ok #[] := fun s => by
    rw [(Verify.foRWords_valid _ 0 _).1 (Verify.wordsFoR_closed #[] (n := 0) rfl).1,
      (Verify.wordsFoR_closed #[] (n := 0) rfl).2.1]
  have h1 : ∀ s, foRWords s 0 .pos = .ok #[] := fun s => by
    rw [(Verify.foRWords_valid _ 0 _).1 (show Enc.Valid 0 .pos from trivial)]; simp [Enc.raw]
  have hp : hasNul .pos = false := rfl
  unfold colConst kscatter
  simp [h0, h1, noNul, hp, Verify.hasNul_wordsFoR]

/-- A column list of the shape of `es.map (.atom p t ·)` is `es'.map (.atom p t ·)`, `es'` as long as `es`. -/
theorem Cols.shape_atoms {p} {t : QAtomicType} : ∀ {cs : Cols} {es : List Nat},
    Cols.shape cs = Cols.shape (es.map (Col.atom p t ·)) → ∃ es' : List Nat, cs = es'.map (Col.atom p t ·) ∧ es'.length = es.length
  | [], [], _ => ⟨[], rfl, rfl⟩
  | c :: cs, e :: es, h => by
    simp only [List.map_cons, Cols.shape, Col.shape, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨es', rfl, hl⟩ := Cols.shape_atoms h2
    cases c with
    | atom p' t' e' =>
      simp only [Col.shape, Col.atom.injEq] at h1
      obtain ⟨rfl, rfl, -⟩ := h1
      exact ⟨e' :: es', rfl, by simp [hl]⟩
    | arr => simp [Col.shape] at h1
    | sum => simp [Col.shape] at h1
  | [], _ :: _, h => by simp [Cols.shape] at h
  | _ :: _, [], h => by simp [Cols.shape] at h

theorem Cols.regs_atoms {p} {t : QAtomicType} : ∀ es : List Nat, Cols.regs (es.map (Col.atom p t ·)) = es
  | [] => rfl
  | e :: es => by simp [Cols.regs, Col.regs, Cols.regs_atoms es]

theorem Cols.regs_mem {c : Col} : ∀ {X : Cols}, c ∈ X → ∀ a ∈ Col.regs c, a ∈ Cols.regs X
  | _ :: _, .head _, a, h => by simp [Cols.regs, h]
  | _ :: _, .tail _ hc, a, h => by simp [Cols.regs, Cols.regs_mem hc a h]

/-- A reader of atom columns' registers answers them on atom columns. -/
theorem mapM_atoms {p} {t : QAtomicType} {f : Col → Bld Nat} :
    ∀ es : List Nat, (∀ e, f (.atom p t e) = Pure.pure e) → (es.map (Col.atom p t ·)).mapM f = Pure.pure es
  | [], _ => rfl
  | e :: es, hf => by simp only [List.map_cons, List.mapM_cons, hf, mapM_atoms es hf, pure_bind]

/-- **`funW` builds**: `funV_builds` at the table `⟨n, ws.map atom, []⟩`. The body `b` reads the count at `rs.size`
    and the words at the registers after it, and answers a size and `k` words, its registers holding `o`; `kk`
    continues with the size register and the `k` word registers `funW` hands back, holding `o`. -/
theorem funW_builds {abi : String → Option Kernel} {fg : Array Fun × Array Fun} {n : Nat} {ws : List Nat}
    {b : Nat → List Nat → Bld (Nat × List Nat)} {kk : Nat × List Nat → Bld (Array Nat)} {rs pv o out : Array Val}
    {k : Nat} (ha : ∀ who, (n :: ws).toArray.mapM (reg rs who) = .ok pv) (ho : o.size = k + 1)
    (hB : ∃ fg1, Builds abi fg fg1 ((do
        let (m, xs) ← b rs.size (List.range' (rs.size + 1) ws.length)
        Pure.pure (⟨m, xs.map (Col.atom "" .i64 ·), []⟩ : TabB)) >>=
      answerRegs fun U => U.val = [] ∧ ∃ es : List Nat, U.key = es.map (Col.atom "" .i64 ·) ∧ es.length = k) (rs ++ pv) o)
    (hT : Typed rs.size (fun _ => True) (b rs.size (List.range' (rs.size + 1) ws.length)))
    (hb : ∀ n ws, Grows (b n ws)) (hfo : Ordered fg.1)
    (hk : ∀ (fg2 : Array Fun × Array Fun) (m : Nat) (es : List Nat) (ys : Array Val), (∃ a, fg2.1 = fg.1 ++ a) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → es.length = k →
      (m :: es).mapM (fun i => (rs ++ ys)[i]?) = some o.toList → ∃ fg', Builds abi fg2 fg' (kk (m, es)) (rs ++ ys) out) :
    ∃ fg', Builds abi fg fg' (funW n ws b >>= kk) rs out := by
  unfold funW
  -- the column reader `words` named, so the proof rewrites it by `hwd`
  suffices h : ∀ wd : Cols → Bld (List Nat), (∀ es, wd (es.map (Col.atom "" .i64 ·)) = Pure.pure es) →
      (∀ cs, Grows (wd cs)) → ∃ fg', Builds abi fg fg' ((do
        let T ← funV n (ws.map (Col.atom "" .i64 ·)) [] fun n cs _ => do
          let (m, xs) ← b n (← wd cs); Pure.pure ⟨m, xs.map (Col.atom "" .i64 ·), []⟩
        Pure.pure (T.n, ← wd T.key)) >>= kk) rs out by
    refine h _ (fun es => mapM_atoms es fun _ => rfl) fun cs => Grows.mapM (fun c => ?_) cs
    split <;> first | exact Grows.pure _ | exact Grows.throw _
  intro wd hwd hwg
  have hA : tabsRegs [(⟨n, ws.map (Col.atom "" .i64 ·), []⟩ : TabB)] = Pure.pure (n :: ws) := by
    rw [tabsRegs_eq]; simp [TabB.regs, Cols.regs_atoms, Cols.regs]
  obtain ⟨A', Y, t1, -, -, t4⟩ := tab_spec (⟨n, ws.map (Col.atom "" .i64 ·), []⟩ : TabB)
  obtain rfl := pure_inj (t1.symm.trans hA)
  obtain ⟨V0, v1, v2, -, v4, v5⟩ := t4 (List.range' rs.size (n :: ws).length) [] (by simp)
  rw [List.append_nil] at v1
  obtain ⟨n0, key, val⟩ := V0
  dsimp only at v4 v5
  obtain rfl : val = [] := by cases val <;> simp_all [Cols.shape]
  obtain ⟨es0, rfl, hl0⟩ := Cols.shape_atoms v4
  rw [tabsRegs_eq] at v2
  have v2' := pure_inj v2
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TabB.regs, Cols.regs_atoms, Cols.regs,
    List.length_cons, List.range'_succ, List.cons.injEq] at v2'
  obtain ⟨rfl, rfl⟩ := v2'
  let P : TabB → Prop := fun U => U.val = [] ∧ ∃ es : List Nat, U.key = es.map (Col.atom "" .i64 ·) ∧ es.length = k
  obtain ⟨fg1, ⟨a1, ha1⟩, hb1, hB1⟩ := hB
  have hTy : Typed rs.size (fun _ => True) (do
      let (m, xs) ← b rs.size (← wd ((List.range' (rs.size + 1) ws.length).map (Col.atom "" .i64 ·)))
      Pure.pure (⟨m, xs.map (Col.atom "" .i64 ·), []⟩ : TabB)) := by
    rw [hwd, pure_bind]
    exact hT.bind fun p _ => by obtain ⟨_, _⟩ := p; exact Typed.pure trivial
  obtain ⟨ctys, hcl⟩ := Typed.cloTys (fg := fg) (fg1 := fg1) (k := (n :: ws).length) (rs := rs) hTy
  rw [bind_assoc]
  refine funV_builds (P := P) (fg1 := fg1) (Us := []) (pv := pv) (o := o) (ctys := ctys)
    (T := ⟨rs.size, (List.range' (rs.size + 1) ws.length).map (Col.atom "" .i64 ·), []⟩) hA ha v1 ?_ hfo
    (fun n X _ => (hwg X).bind fun es => (hb n es).bind fun p => by obtain ⟨_, _⟩ := p; exact Grows.pure _)
    (fun U body xs R rtys h _ hR hy is => hcl U body _ R rtys h hR hy is) ?_
  · dsimp only
    rw [hwd, pure_bind]
    exact hB1 #[]
  rintro ⟨un, ukey, uval⟩ ⟨hv, es, hes, hlk⟩ fg2 R' V ys he hf ho' hR hV
  dsimp only at hv hes
  subst hv hes
  obtain ⟨AU, YU, u1, -, -, u4⟩ := tab_spec (⟨un, es.map (Col.atom "" .i64 ·), []⟩ : TabB)
  rw [tabsRegs_eq] at u1
  obtain rfl := (pure_inj u1).symm
  have hl : R'.toList.length = ([(⟨un, es.map (Col.atom "" .i64 ·), []⟩ : TabB)].flatMap TabB.regs).length := by
    have h1 := mapM_ok_size (hR "")
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TabB.regs, Cols.regs_atoms, Cols.regs,
      List.length_cons, Array.length_toList, hlk]
    omega
  obtain ⟨V', f1, f2, -, f4, f5⟩ := u4 R'.toList [] hl
  rw [List.append_nil] at f1
  obtain rfl : V = V' := by
    have := pure_inj (hV.symm.trans f1); simp only [Prod.mk.injEq, List.cons.injEq, and_true] at this; exact this
  obtain ⟨vn, vkey, vval⟩ := V
  dsimp only at f4 f5
  obtain rfl : vval = [] := by cases vval <;> simp_all [Cols.shape]
  obtain ⟨es', rfl, hl'⟩ := Cols.shape_atoms f4
  rw [tabsRegs_eq] at f2
  have f2' := pure_inj f2
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TabB.regs, Cols.regs_atoms, Cols.regs] at f2'
  have hread := holds_of_reg (hR "")
  rw [← f2'] at hread
  simp only [hwd, pure_bind]
  obtain ⟨e1, he1⟩ := he
  exact hk fg2 vn es' ys ⟨a1 ++ e1, by rw [he1, ha1, Array.append_assoc]⟩ (by rw [hf]; exact hb1) ho'
    (hl'.trans hlk) hread

/-- **`prefixB` builds `colPrefix`'s `kscan` and its last word**: `n` holding the count `nv` and `a` the column `av`;
    `z` is `constB`'s `kscatter` (`colConst` but for the empty columns it scatters from) and `r` the `kscan` that
    `colPrefix` runs with it; `kk` continues with a register holding `r.1` and one holding the last fold word, as
    `lastB_builds` reads it (`hr`: a fold word exists where a row does). -/
theorem prefixB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {op : Kernel.Op} {n a : Nat} {nv : USize}
    {av z : Enc} {r : Enc × Option UInt64} {kk : Nat × Nat → Bld (Array Nat)} {out : Array Val}
    (hop : (Reg.get? (Reg.put op) : Option Kernel.Op) = some op)
    (hn : rs[n]? = some (.size nv)) (ha : rs[a]? = some (Reg.put av))
    (hz : colConst nv 0 = .ok z)
    (hk : kscan op false .i64 .i64 nv (some z) [(nv, z), (nv, av)] [] [] = .ok r) (hr : nv ≠ 0 → r.2.isSome)
    (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (p l : Nat) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → (rs ++ ys)[p]? = some (Reg.put r.1) →
      (rs ++ ys)[l]? = some (.size (if nv = 0 then 0 else (r.2.getD 0).toUSize + 0)) →
      ∃ fg', Builds abiOf fg2 fg' (kk (p, l)) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (prefixB op n a >>= kk) rs out := by
  unfold prefixB
  rw [bind_assoc]
  have hn' : (rs ++ #[Val.size nv, Reg.put av])[rs.size]? = some (.size nv) := by simp
  have ha' : (rs ++ #[Val.size nv, Reg.put av])[rs.size + 1]? = some (Reg.put av) := by simp
  refine funW_builds (k := 1) (pv := #[Val.size nv, Reg.put av])
    (o := #[.size (if nv = 0 then 0 else (r.2.getD 0).toUSize + 0), Reg.put r.1])
    (fun _ => reads_of (by simp [hn, ha])) rfl ⟨fg, ?_⟩ ?_ (fun n ws => ?_) hfo ?_
  · rw [show List.range' (rs.size + 1) [a].length = [rs.size + 1] from rfl]
    dsimp only
    unfold wordsB
    simp only [bind_assoc]
    refine Builds.litG fun c0 R1 h0 m1 => ?_
    refine Builds.bind1G (constB_builds (m1 hn') h0 (colConst_eq _ _ ▸ hz)) fun zr R2 hz1 m2 => ?_
    refine Builds.bindG (scanB_builds hop (by rw [m2 (m1 hn')]; rfl) (seg := some zr) (sg := some z)
      (by simp [hz1, enc_get_put]) (es := [zr, rs.size + 1]) (xs := [z, av])
      (by simp [hz1, m2 (m1 ha'), enc_get_put]) hk) fun ps R3 hps m3 => ?_
    obtain ⟨p1, hp1, hpR⟩ := holds_at hps (i := 1) rfl
    rw [nth_of (by simpa using hp1), pure_bind]
    refine Builds.bind1G (lastB_builds (m3 (m2 (m1 hn'))) hpR hr) fun lr R4 hlr m4 => ?_
    obtain ⟨p0, hp0, hp0R⟩ := holds_at hps (i := 0) rfl
    rw [nth_of (by simpa using hp0), pure_bind]
    simp only [pure_bind]
    exact Builds.answerRegs ⟨rfl, [p0], rfl, rfl⟩ (tabsRegs_eq _) fun _ => reads_of (by
      simp [TabB.regs, Cols.regs, Col.regs, hlr, m4 hp0R])
  · rw [show List.range' (rs.size + 1) [a].length = [rs.size + 1] from rfl]
    dsimp only
    exact Typed.wordsB.bind fun z hz => (Typed.scanB (Nat.le_refl _)
      (fun s hs => by cases hs; exact hz) (by intro a ha; simp at ha; omega)).bind fun r hr =>
      (Typed.nth hr 1 _).bind fun f hf => (Typed.lastB (Nat.le_refl _) hf 0).bind fun _ _ =>
      (Typed.nth hr 0 _).bind fun _ _ => Typed.pure trivial
  · dsimp only
    split
    · exact (Grows.wordsB _ _).bind fun _ => (Grows.scanB _ _ _ _ _).bind fun _ => (Grows.nth _ _ _).bind fun _ =>
        (Grows.lastB _ _ _).bind fun _ => (Grows.nth _ _ _).bind fun _ => Grows.pure _
    · exact Grows.throw _
  · intro fg2 m es ys he hf ho hl hread
    match es, hl with
    | [p], _ =>
      obtain ⟨hm, hread⟩ := mapM_get_cons hread
      obtain ⟨hp, -⟩ := mapM_get_cons hread
      simp only [pure_bind]
      exact hkk fg2 p m ys he hf ho hp hm

/-- **`groupFoldB` builds `groupFold` over `seenSeg`'s marks**: `n` holding the row count `nv`, `g` the groups `gv`,
    `f` the first rows `fv`, `m` the group count `mv`, `x` the column `xv`. `sg` is the marks `seenSeg` answers and `ov`
    what `groupFold` answers over them: `kk` continues with a register holding `ov`. -/
theorem groupFoldB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {op : Kernel.Op} {n g f m x : Nat}
    {z : UInt64} {nv mv : USize} {gv fv xv w sg zz ov : Enc} {r : Enc × Option UInt64} {kk : Nat → Bld (Array Nat)}
    {out : Array Val} (hop : (Reg.get? (Reg.put op) : Option Kernel.Op) = some op)
    (hn : rs[n]? = some (.size nv)) (hg : rs[g]? = some (Reg.put gv)) (hf : rs[f]? = some (Reg.put fv))
    (hm : rs[m]? = some (.size mv)) (hx : rs[x]? = some (Reg.put xv))
    (hseg : Tab.seenSeg nv fv mv = .ok sg) (hgf : Tab.groupFold op nv gv sg mv z xv = .ok ov) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (p : Nat) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → (rs ++ ys)[p]? = some (Reg.put ov) →
      ∃ fg', Builds abiOf fg2 fg' (kk p) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (groupFoldB op n g f m z x >>= kk) rs out := by
  obtain ⟨w, hw, hseg⟩ : ∃ w, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) mv 1 = .ok w ∧
      kscatter .last mv fv w nv 0 = .ok sg := by
    unfold Tab.seenSeg at hseg
    rcases hc : colConst mv 1 with e | w <;> rw [hc] at hseg
    · cases hseg
    · exact ⟨w, by rwa [← colConst_eq], hseg⟩
  obtain ⟨zz, r, hzz, hk, ho⟩ : ∃ (zz : Enc) (r : Enc × Option UInt64),
      kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv z = .ok zz ∧
      kscan op false .i64 .i64 nv (some sg) [(nv, zz), (nv, xv)] [] [] = .ok r ∧
      kscatter .last nv gv r.1 mv z = .ok ov := by
    unfold Tab.groupFold at hgf
    rcases hc : colConst nv z with e | zz <;> rw [hc] at hgf
    · cases hgf
    · have hgf' : (kscan op false .i64 .i64 nv (some sg) [(nv, zz), (nv, xv)] [] [] >>= fun r =>
          kscatter .last nv gv r.1 mv z) = .ok ov := hgf
      rcases hs : kscan op false .i64 .i64 nv (some sg) [(nv, zz), (nv, xv)] [] [] with e | r <;> rw [hs] at hgf'
      · cases hgf'
      · exact ⟨zz, r, by rwa [← colConst_eq], hs, hgf'⟩
  have hl : (Reg.get? (Reg.put Kernel.Op.last) : Option Kernel.Op) = some .last := by with_unfolding_all rfl
  have hlt : m < rs.size := by
    rcases Nat.lt_or_ge m rs.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hm
  unfold groupFoldB
  rw [bind_assoc]
  let pv : Array Val := #[Val.size nv, Reg.put gv, Reg.put xv]
  have hn' : (rs ++ pv)[rs.size]? = some (.size nv) := by simp [pv]
  have hx' : (rs ++ pv)[rs.size + 2]? = some (Reg.put xv) := by simp [pv]
  refine funW_builds (k := 1) (o := #[.size mv, Reg.put ov]) (pv := pv)
    (fun _ => reads_of (by simp [pv, hn, hg, hx])) rfl ⟨fg, ?_⟩ ?_ (fun n ws => ?_) hfo ?_
  · rw [show List.range' (rs.size + 1) [g, x].length = [rs.size + 1, rs.size + 2] from rfl]
    dsimp only
    unfold wordsB
    simp only [bind_assoc]
    refine Builds.litG fun c0 R1 h0 m1 => ?_
    refine Builds.bind1G (constB_builds (m1 (get_app hm)) h0 hw) fun wr R2 hw1 m2 => ?_
    refine Builds.bind1G (scatterB_builds (m2 (m1 (get_app hm))) (m2 (m1 (get_app hf))) hw1 (m2 (m1 hn')) hl hseg)
      fun sr R3 hs1 m3 => ?_
    refine Builds.litG fun c1 R4 h1 m4 => ?_
    refine Builds.bind1G (constB_builds (m4 (m3 (m2 (m1 hn')))) h1 hzz) fun zr R5 hz1 m5 => ?_
    refine Builds.bindG (scanB_builds hop (by rw [m5 (m4 (m3 (m2 (m1 hn'))))]; rfl) (seg := some sr) (sg := some sg)
      (by simp [m5 (m4 hs1), enc_get_put]) (es := [zr, rs.size + 2]) (xs := [zz, xv])
      (by simp [hz1, m5 (m4 (m3 (m2 (m1 hx')))), enc_get_put]) hk) fun ps R6 hps m6 => ?_
    obtain ⟨p0, hp0, hp0R⟩ := holds_at hps (i := 0) rfl
    rw [nth_of (by simpa using hp0), pure_bind]
    refine Builds.bind1G (scatterB_builds (m6 (m5 (m4 (m3 (m2 (m1 hn')))))) (m6 (m5 (m4 (m3 (m2 (m1
      (show (rs ++ pv)[rs.size + 1]? = some (Reg.put gv) by simp [pv]))))))) hp0R
      (m6 (m5 (m4 (m3 (m2 (m1 (get_app hm))))))) hl ho) fun orr R7 ho1 m7 => ?_
    simp only [pure_bind]
    exact Builds.answerRegs ⟨rfl, [orr], rfl, rfl⟩ (tabsRegs_eq _) fun _ => reads_of (by
      simp [TabB.regs, Cols.regs, Col.regs, ho1, m7 (m6 (m5 (m4 (m3 (m2 (m1 (get_app hm)))))))])
  · rw [show List.range' (rs.size + 1) [g, x].length = [rs.size + 1, rs.size + 2] from rfl]
    dsimp only
    exact Typed.wordsB.bind fun _ _ => Typed.scatterB.bind fun s hs => Typed.wordsB.bind
      fun zr hzr => (Typed.scanB (Nat.le_refl _) (fun s' h => by cases h; exact hs)
        (by intro a ha; simp at ha; omega)).bind fun r hr => (Typed.nth hr 0 _).bind fun _ _ =>
      Typed.scatterB.bind fun _ _ => Typed.pure trivial
  · dsimp only
    split
    · exact (Grows.wordsB _ _).bind fun _ => (Grows.scatterB _ _ _ _ _ _).bind fun _ => (Grows.wordsB _ _).bind
        fun _ => (Grows.scanB _ _ _ _ _).bind fun _ => (Grows.nth _ _ _).bind fun _ =>
        (Grows.scatterB _ _ _ _ _ _).bind fun _ => Grows.pure _
    · exact Grows.throw _
  · intro fg2 k es ys he hf' ho' hlen hread
    match es, hlen with
    | [p], _ =>
      obtain ⟨-, hread⟩ := mapM_get_cons hread
      obtain ⟨hp, -⟩ := mapM_get_cons hread
      simp only [pure_bind]
      exact hkk fg2 p ys he hf' ho' hp

/-! ### `Grows`, `Typed` -/

theorem Grows.funW {n : Nat} {ws : List Nat} {b : Nat → List Nat → Bld (Nat × List Nat)}
    (hb : ∀ n ws, Grows (b n ws)) : Grows (Plan.funW n ws b) := by
  unfold Plan.funW
  dsimp only
  refine (Grows.funV fun n X _ => (Grows.mapM (fun c => ?_) X).bind fun es => (hb n es).bind fun p => by
    obtain ⟨_, _⟩ := p; exact Grows.pure _).bind fun T => (Grows.mapM (fun c => ?_) T.key).bind fun _ => Grows.pure _
  all_goals split <;> first | exact Grows.pure _ | exact Grows.throw _

/-- The registers of atom columns, each read off its column, are the columns' registers. -/
theorem Typed.atomWords {m : Nat} {s : String} {X : Cols} (hX : AllGe m (Cols.regs X)) :
    Typed m (fun es => AllGe m es) (X.mapM fun | .atom _ _ e => Pure.pure e | _ => MonadExcept.throw s) :=
  Typed.mapM fun c hc => by
    cases c with
    | atom p t e => exact Typed.pure (hX e (Cols.regs_mem hc e (by simp [Col.regs])))
    | arr => exact Typed.throw _
    | sum => exact Typed.throw _

theorem Typed.funW {m n : Nat} {ws : List Nat} {b : Nat → List Nat → Bld (Nat × List Nat)} (hn : m ≤ n)
    (hw : AllGe m ws) (hb : ∀ n ws, m ≤ n → AllGe m ws → Typed m (fun r => m ≤ r.1 ∧ AllGe m r.2) (b n ws)) :
    Typed m (fun r => m ≤ r.1 ∧ AllGe m r.2) (Plan.funW n ws b) := by
  unfold Plan.funW
  dsimp only
  refine (Typed.funV hn (by rw [Cols.regs_atoms]; exact hw) (fun _ h => by simp at h) fun n' X _ hn' hX _ => ?_).bind
    fun T hT => ?_
  · refine (Typed.atomWords hX).bind fun es hes => (hb n' es hn' hes).bind fun p hp => ?_
    obtain ⟨k, xs⟩ := p
    refine Typed.pure fun a ha => ?_
    simp only [TabB.regs, Cols.regs_atoms, Cols.regs, List.append_nil, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hp.1
    · exact hp.2 a ha
  · exact (Typed.atomWords (X := T.key) fun a ha => hT a (by simp [TabB.regs, Cols.regs_append, ha])).bind
      fun es hes =>
      Typed.pure ⟨hT _ (by simp [TabB.regs]), hes⟩

theorem Grows.prefixB (op : Kernel.Op) (n a : Nat) : Grows (Plan.prefixB op n a) := by
  unfold Plan.prefixB
  refine (Grows.funW fun n ws => ?_).bind fun p => ?_
  · dsimp only
    split
    · exact (Grows.wordsB _ _).bind fun _ => (Grows.scanB _ _ _ _ _).bind fun _ => (Grows.nth _ _ _).bind fun _ =>
        (Grows.lastB _ _ _).bind fun _ => (Grows.nth _ _ _).bind fun _ => Grows.pure _
    · exact Grows.throw _
  · dsimp only
    split
    · exact Grows.pure _
    · exact Grows.throw _

theorem Grows.groupFoldB (op : Kernel.Op) (n g f m : Nat) (z : UInt64) (x : Nat) :
    Grows (Plan.groupFoldB op n g f m z x) := by
  unfold Plan.groupFoldB
  refine (Grows.funW fun n ws => ?_).bind fun p => ?_
  · dsimp only
    split
    · exact (Grows.wordsB _ _).bind fun _ => (Grows.scatterB _ _ _ _ _ _).bind fun _ => (Grows.wordsB _ _).bind
        fun _ => (Grows.scanB _ _ _ _ _).bind fun _ => (Grows.nth _ _ _).bind fun _ =>
        (Grows.scatterB _ _ _ _ _ _).bind fun _ => Grows.pure _
    · exact Grows.throw _
  · dsimp only
    split
    · exact Grows.pure _
    · exact Grows.throw _

theorem Typed.prefixB {lv : Nat} {op : Kernel.Op} {n a : Nat} (hn : lv ≤ n) (ha : lv ≤ a) :
    Typed lv (fun r => lv ≤ r.1 ∧ lv ≤ r.2) (Plan.prefixB op n a) := by
  unfold Plan.prefixB
  refine (Typed.funW hn (fun _ h => by simp at h; omega) fun n ws hn' hws => ?_).bind fun p hp => ?_
  · rcases ws with _ | ⟨a', _ | ⟨_, _⟩⟩
    · exact Typed.throw _
    · have ha' : lv ≤ a' := hws a' (by simp)
      exact Typed.wordsB.bind fun z hz => (Typed.scanB hn' (fun s hs => by cases hs; exact hz)
        (by intro a ha; simp at ha; omega)).bind fun r hr => (Typed.nth hr 1 _).bind fun f hf =>
        (Typed.lastB hn' hf 0).bind fun l hl => (Typed.nth hr 0 _).bind fun q hq =>
        Typed.pure ⟨hl, fun _ h => by simp at h; omega⟩
    · exact Typed.throw _
  · obtain ⟨l, _ | ⟨q, _ | ⟨_, _⟩⟩⟩ := p
    · exact Typed.throw _
    · exact Typed.pure ⟨hp.2 q (by simp), hp.1⟩
    · exact Typed.throw _

theorem Typed.groupFoldB {lv : Nat} {op : Kernel.Op} {n g f m : Nat} {z : UInt64} {x : Nat} (hn : lv ≤ n)
    (hg : lv ≤ g) (hm : lv ≤ m) (hx : lv ≤ x) : Typed lv (fun r => lv ≤ r) (Plan.groupFoldB op n g f m z x) := by
  unfold Plan.groupFoldB
  refine (Typed.funW hn (fun _ h => by simp at h; omega) fun n ws hn' hws => ?_).bind fun p hp => ?_
  · rcases ws with _ | ⟨g', _ | ⟨x', _ | ⟨_, _⟩⟩⟩
    · exact Typed.throw _
    · exact Typed.throw _
    · have hx' : lv ≤ x' := hws x' (by simp)
      exact Typed.wordsB.bind fun _ _ => Typed.scatterB.bind fun s hs => Typed.wordsB.bind
        fun zr hzr => (Typed.scanB hn' (fun s' h => by cases h; exact hs)
          (by intro a ha; simp at ha; omega)).bind fun r hr => (Typed.nth hr 0 _).bind fun _ _ =>
        Typed.scatterB.bind fun o ho => Typed.pure ⟨hm, fun _ h => by simp at h; omega⟩
    · exact Typed.throw _
  · obtain ⟨l, _ | ⟨q, _ | ⟨_, _⟩⟩⟩ := p
    · exact Typed.throw _
    · exact Typed.pure (hp.2 q (by simp))
    · exact Typed.throw _

end Rel.Lang.Plan
