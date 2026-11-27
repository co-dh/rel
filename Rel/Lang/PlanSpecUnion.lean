module

public import Rel.Lang.PlanSpecConcat

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `unionB` builds `Tab.union`

`unionB R S` is `funT [R, S]` of `catB`, two `concatB`s (the key side, the value side) and `canonT`: `Tab.union` is
`Tab.concat` then `Tab.canon`. `funT_builds` reads the two tables off the parameter registers, `catB_builds`,
`concatB_builds` and `canonT_builds` build the body in turn, and the answer's registers are read back as a table. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- The two tables `[R, S]` read from consecutive registers from `s`: tables of `R`'s and `S`'s shapes, `R`'s registers
    first. -/
theorem tabsAt_two (R S : TabB) (s : Nat) : ∃ R1 S1 : TabB,
    tabsAt [R, S] (List.range' s (R.regs ++ S.regs).length) = Pure.pure ([R1, S1], []) ∧
      Cols.shape R1.key = Cols.shape R.key ∧ Cols.shape R1.val = Cols.shape R.val ∧
      Cols.shape S1.key = Cols.shape S.key ∧ Cols.shape S1.val = Cols.shape S.val ∧
      R1.regs = List.range' s R.regs.length ∧ S1.regs = List.range' (s + R.regs.length) S.regs.length := by
  obtain ⟨A1, Y1, t1, -, hl1, t4⟩ := tab_spec R
  obtain ⟨A2, Y2, u1, -, hl2, u4⟩ := tab_spec S
  rw [tabsRegs_eq] at t1 u1
  obtain rfl := pure_inj t1
  obtain rfl := pure_inj u1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hl1 hl2 ⊢
  obtain ⟨V1, v1, v2, -, v4, v5⟩ := t4 (List.range' s R.regs.length) (List.range' (s + R.regs.length) S.regs.length) (by simp)
  obtain ⟨V2, w1, w2, -, w4, w5⟩ := u4 (List.range' (s + R.regs.length) S.regs.length) [] (by simp)
  rw [List.append_nil] at w1
  refine ⟨V1, V2, ?_, v4, v5, w4, w5, ?_, ?_⟩
  · rw [show [R, S] = [R] ++ [S] from rfl, tabsAt_append, List.length_append, ← List.range'_append_1, v1]
    simp only [pure_bind]; rw [w1]; rfl
  · rw [tabsRegs_eq] at v2; simpa using pure_inj v2
  · rw [tabsRegs_eq] at w2; simpa using pure_inj w2

/-- The kernel facts `canonT_builds` takes of the concatenation `C` of a union (`hN`, `hz`, `hsc` there; no totality lemma
    for these kernels exists), with the count strictly below `2^63` so that `catB`'s `CatOff` applies to its parts. -/
def CanOK {A B : Obj} (C : Tab A B) : Prop := C.n.toNat < 2 ^ 63 ∧
  ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) C.n 0 = .ok z ∧
    ∀ es vs p k g f, ValsB.cols (A := .prod A B) (C.key, C.val) = .ok es → kasc C.n es = .ok (vs, p) →
      kseen C.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 C.n (some z) [(C.n, z), (C.n, g)] [] [] = .ok r

/-- **`unionB` builds `Tab.union`**: the tables `R'`, `S'` (sides of `A` and `B`) hold `R`, `S` in `rs`, `R.union S = U`;
    `kk` continues with a table of `R'`'s shape whose registers hold `U`. -/
def UnionSpec (A B : Obj) : Prop := ∀ {R S U : Tab A B} {R' S' : TabB} {fg : Array Fun × Array Fun} {rs : Array Val}
    {kk : TabB → Bld (Array Nat)} {out : Array Val}, ColsOf A R'.key → ColsOf B R'.val → ColsOf A S'.key →
    ColsOf B S'.val → R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
    S'.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
    R.union S = .ok U → (∀ C, R.concat S = .ok C → CanOK C) → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape R'.key → Cols.shape W.val = Cols.shape R'.val →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size U.n :: (U.key.regVals ++ U.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (unionB R' S' >>= kk) rs out

theorem unionB_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A B : Obj) : UnionSpec A B := by
  intro R S U R' S' fg rs kk out hRk hRv hSk hSv hR hS hU hcan hfo hkk
  obtain ⟨C, hC, hcn⟩ := except_bind_ok hU
  obtain ⟨hCN, z, hz, hsc⟩ := hcan C hC
  unfold Tab.concat at hC
  obtain ⟨p, hp, hC⟩ := except_bind_ok hC
  obtain ⟨ck, hck, hC⟩ := except_bind_ok hC
  obtain ⟨cv, hcv, hC⟩ := except_bind_ok hC
  cases hC
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
  rw [e1] at gR
  rw [e2] at gS
  obtain ⟨hn1, gR⟩ := mapM_get_cons gR
  obtain ⟨hn2, gS⟩ := mapM_get_cons gS
  have hAk1 : ColsOf A R1.key := ColsOf.shape A hRk hsR1
  have hAv1 : ColsOf B R1.val := ColsOf.shape B hRv hsR2
  have hAk2 : ColsOf A S1.key := ColsOf.shape A hSk hsS1
  have hAv2 : ColsOf B S1.val := ColsOf.shape B hSv hsS2
  obtain ⟨gRk, gRv⟩ := mapM_split (ColsOf.regs_length hAk1 R.key) gR
  obtain ⟨gSk, gSv⟩ := mapM_split (ColsOf.regs_length hAk2 S.key) gS
  let P : TabB → Prop := fun W => Cols.shape W.key = Cols.shape R'.key ∧ Cols.shape W.val = Cols.shape R'.val
  let o : Array Val := (Val.size U.n :: (U.key.regVals ++ U.val.regVals)).toArray
  let body : Bld TabB := do
    let (n, off) ← catB R1.n S1.n
    canonT ⟨n, ← concatB n R1.n S1.n off R1.key S1.key, ← concatB n R1.n S1.n off R1.val S1.val⟩
  have hB : ∃ fg1, Builds abiOf fg fg1 (body >>= answerRegs P) (rs ++ pv.toArray) o := by
    simp only [body, bind_assoc]
    obtain ⟨zc, oc, f, hzc, hoc⟩ := hc R.n S.n (by rw [← catRows_ok hp]; exact hCN)
    refine Builds.bind2F (Free.catB _ _) (catB_builds hn1 hn2 hp hzc hoc) fun r1 r2 R2 hr1' hr2' hE => ?_
    dsimp only
    refine concatB_builds hc h63 A (x := R.key) (y := S.key) (z := ck) hAk1 hAk2 (mapM_extends hE gRk)
      (mapM_extends hE gSk) hr1' (hE hn1) (hE hn2) hck hfo ?_
    intro fg2 cs' ys he hf ho hs hr
    refine concatB_builds hc h63 B (x := R.val) (y := S.val) (z := cv) hAv1 hAv2 (mapM_get_app (mapM_extends hE gRv))
      (mapM_get_app (mapM_extends hE gSv)) (get_app hr1') (get_app (hE hn1)) (get_app (hE hn2)) hcv ho ?_
    intro fg3 cs'' ys2 he3 hf3 ho3 hs3 hr3
    refine canonT_builds (R := ⟨p, ck, cv⟩) (R' := U) (T := ⟨r1, cs', cs''⟩) (z := z) (ColsOf.shape A hAk1 hs)
      (ColsOf.shape B hAv1 hs3) ?_ hcn (Nat.le_of_lt hCN) hz hsc ho3 ?_
    · show (r1 :: Cols.regs (cs' ++ cs'')).mapM _ = _
      rw [Cols.regs_append]
      rw [List.mapM_cons, List.mapM_append, get_app (get_app hr1'), mapM_get_app hr, hr3]
      rfl
    · intro fg4 U' ys3 he4 hf4 ho4 hs4 hs5 hr4
      refine ⟨fg4, Builds.answerRegs (P := P) ⟨hs4.trans (hs.trans hsR1), hs5.trans (hs3.trans hsR2)⟩ (tabsRegs_eq _) fun _ => ?_⟩
      simpa [o] using reads_of hr4
  obtain ⟨fg1, ⟨a1, ha1⟩, hb1, hB1⟩ := hB
  have hm1 : AllGe rs.size R1.regs := fun a ha => by rw [hr1, List.mem_range'_1] at ha; omega
  have hm2 : AllGe rs.size S1.regs := fun a ha => by rw [hs1, List.mem_range'_1] at ha; omega
  have hnR : rs.size ≤ R1.n := hm1 _ (by rw [e1]; simp)
  have hnS : rs.size ≤ S1.n := hm2 _ (by rw [e2]; simp)
  have hkR : AllGe rs.size (Cols.regs R1.key) := fun a ha => hm1 a (by rw [e1]; simp [ha])
  have hvR : AllGe rs.size (Cols.regs R1.val) := fun a ha => hm1 a (by rw [e1]; simp [ha])
  have hkS : AllGe rs.size (Cols.regs S1.key) := fun a ha => hm2 a (by rw [e2]; simp [ha])
  have hvS : AllGe rs.size (Cols.regs S1.val) := fun a ha => hm2 a (by rw [e2]; simp [ha])
  have hTy : Typed rs.size (fun _ => True) body := by
    refine (Typed.catB hnR hnS).bind fun ⟨n, off⟩ hno => ?_
    refine (Typed.concatBOf (S := []) (Col.sizes R1.key + 1) n R1.n S1.n off R1.key S1.key (Nat.lt_succ_self _)
      (.inl hno.1) hnR hnS hkR hkS).bind fun ck' hck' => ?_
    refine (Typed.concatBOf (S := []) (Col.sizes R1.val + 1) n R1.n S1.n off R1.val S1.val (Nat.lt_succ_self _)
      (.inl hno.1) hnR hnS hvR hvS).bind fun cv' hcv' => ?_
    refine (Typed.canonT _ ?_).mono fun _ _ => trivial
    intro a ha
    simp only [TabB.regs, Cols.regs_append, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ha | ha
    · exact hno.1
    · simpa using hck' a ha
    · simpa using hcv' a ha
  obtain ⟨ctys, hcl⟩ := Typed.cloTys (fg := fg) (fg1 := fg1) (k := (R'.regs ++ S'.regs).length) hTy
  unfold unionB
  refine funT_builds (P := P) (Us := [R1, S1]) (ctys := ctys) (o := o) hA ha hUs (hB1 #[]) hfo ?_
    (fun U body xs R rtys h _ hR hy is => hcl U body _ R rtys h hR hy is) ?_
  · intro Ts
    rcases Ts with _ | ⟨T1, _ | ⟨T2, _ | ⟨T3, Ts⟩⟩⟩ <;> try exact Grows.throw _
    exact (Grows.catB _ _).bind fun ⟨n, off⟩ => (Grows.concatB (Col.sizes T1.key + 1) _ _ _ _ _ _
      (Nat.lt_succ_self _)).bind fun _ => (Grows.concatB (Col.sizes T1.val + 1) _ _ _ _ _ _
      (Nat.lt_succ_self _)).bind fun _ => Grows.canonT _
  · intro U' ⟨hsk, hsv⟩ fg2 Rr V ys he hf ho' hRr hV
    obtain ⟨AU, YU, u1, -, -, u4⟩ := tab_spec U'
    rw [tabsRegs_eq] at u1
    obtain rfl := (pure_inj u1).symm
    have hl : Rr.toList.length = ([U'].flatMap TabB.regs).length := by
      have h1 := mapM_ok_size (hRr "")
      have k1 := ColsOf.regs_length (ColsOf.shape A hRk hsk) U.key
      have k2 := ColsOf.regs_length (ColsOf.shape B hRv hsv) U.val
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
