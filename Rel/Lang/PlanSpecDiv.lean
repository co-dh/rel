module

public import Rel.Lang.PlanSpecConcat
public import Rel.Lang.PlanSpecGather
public import Rel.Lang.PlanSpecCorefl
public import Rel.Lang.PlanSpecUnion
public import Rel.Lang.PlanSpecExpand
public import Rel.Lang.PlanSpecSelect

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `ldivB`, `ldivSelB`, `rdivB` build `Tab.ldiv`, `Tab.ldivSel`, `Tab.rdiv`

`ldivB R S UB UC` is `ldivOfB` of `canonT R`, `canonT S`: two `canonT_builds` and then `ldivOfB`'s own spec `LdivOfSpec`.
`rdivB` is `convB` twice around `ldivSelB ldivOfB`. The kernel facts `Tab.ldivOf` leaves open (no totality lemma for them
exists) are one premise `Tot` on `ldivOf`'s four arguments, `ldivOfB`'s chain of `compB`, `ascSeenB`, `groupFoldB`,
`whereB`, `gatherB`, `selectB`, `crossB` and `unionB` being the owed proof of `LdivOfSpec Tot`. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- The kernel facts `canonT_builds` takes of a table `R` it canonises (`hN`, `hz`, `hsc` there). -/
def CanPre {A B : Obj} (R : Tab A B) : Prop := R.n.toNat ≤ 2 ^ 63 ∧
  ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) R.n 0 = .ok z ∧
    ∀ es vs p k g f, ValsB.cols (A := .prod A B) (R.key, R.val) = .ok es → kasc R.n es = .ok (vs, p) →
      kseen R.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 R.n (some z) [(R.n, z), (R.n, g)] [] [] = .ok r

/-- **A plan builder `d` of four tables builds `Tab.ldivOf`** (under the kernel facts `Tot`): the tables `r'`, `s'`, `ub`,
    `uc` hold `r`, `s`, `UB`, `UC`, `r.ldivOf s UB UC = U`; `kk` continues with a table of `ub.key`'s and `uc.key`'s shapes
    whose registers hold `U`. `ldivOfB` and `ldivSelB ldivOfB bits` are its two instances. -/
def DivSpec (A B C : Obj) (Tot : Tab A B → Tab A C → Tab B B → Tab C C → Prop)
    (d : TabB → TabB → TabB → TabB → Bld TabB) : Prop :=
  ∀ {r : Tab A B} {s : Tab A C} {UB : Tab B B} {UC : Tab C C} {U : Tab B C} {r' s' ub uc : TabB}
    {fg : Array Fun × Array Fun} {rs : Array Val} {kk : TabB → Bld (Array Nat)} {out : Array Val},
    ColsOf A r'.key → ColsOf B r'.val → ColsOf A s'.key → ColsOf C s'.val → ColsOf B ub.key → ColsOf B ub.val →
    ColsOf C uc.key → ColsOf C uc.val →
    r'.regs.mapM (fun i => rs[i]?) = some (.size r.n :: (r.key.regVals ++ r.val.regVals)) →
    s'.regs.mapM (fun i => rs[i]?) = some (.size s.n :: (s.key.regVals ++ s.val.regVals)) →
    ub.regs.mapM (fun i => rs[i]?) = some (.size UB.n :: (UB.key.regVals ++ UB.val.regVals)) →
    uc.regs.mapM (fun i => rs[i]?) = some (.size UC.n :: (UC.key.regVals ++ UC.val.regVals)) →
    r.ldivOf s UB UC = .ok U → Tot r s UB UC → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape ub.key → Cols.shape W.val = Cols.shape uc.key →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size U.n :: (U.key.regVals ++ U.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (d r' s' ub uc >>= kk) rs out

/-- `ldivOfB` builds `Tab.ldivOf`: the owed spec (the chain `compB`, `ascSeenB`, `groupFoldB`, `whereB`, `gatherB`,
    `selectB`, `crossB`, `unionB`). -/
abbrev LdivOfSpec (A B C : Obj) (Tot : Tab A B → Tab A C → Tab B B → Tab C C → Prop) : Prop := DivSpec A B C Tot ldivOfB

/-- `ldivSelB ldivOfB bits` builds `Tab.ldivOf` (as `rdivB`'s call): the owed spec (`ldivBitsB` where `bitsWinB` holds,
    else `ldivOfB`; `Tot` includes that the bit matrix answers as `ldivOf` does, `Tab.ldivBits_holds`). -/
abbrev LdivSelSpec (A B C : Obj) (Tot : Tab A B → Tab A C → Tab B B → Tab C C → Prop) (bits : Nat) : Prop :=
  DivSpec A B C Tot (ldivSelB ldivOfB bits)

/-- **`ldivB` builds `Tab.ldiv`**: `canonT` of each side (`canonT_builds`), then `ldivOfB` on the canonical answers
    (`LdivOfSpec Tot`, `Tot` holding of them). `CanPre` is the kernel facts of the two `canon`s. -/
theorem ldivB_builds {A B C : Obj} {Tot : Tab A B → Tab A C → Tab B B → Tab C C → Prop} (hL : LdivOfSpec A B C Tot) :
    ∀ {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {U : Tab B C} {R' S' ub uc : TabB}
      {fg : Array Fun × Array Fun} {rs : Array Val} {kk : TabB → Bld (Array Nat)} {out : Array Val},
    ColsOf A R'.key → ColsOf B R'.val → ColsOf A S'.key → ColsOf C S'.val → ColsOf B ub.key → ColsOf B ub.val →
    ColsOf C uc.key → ColsOf C uc.val →
    R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
    S'.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
    ub.regs.mapM (fun i => rs[i]?) = some (.size UB.n :: (UB.key.regVals ++ UB.val.regVals)) →
    uc.regs.mapM (fun i => rs[i]?) = some (.size UC.n :: (UC.key.regVals ++ UC.val.regVals)) →
    R.ldiv S UB UC = .ok U → CanPre R → CanPre S →
    (∀ R1 S1, R.canon = .ok R1 → S.canon = .ok S1 → Tot R1 S1 UB UC) → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape ub.key → Cols.shape W.val = Cols.shape uc.key →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size U.n :: (U.key.regVals ++ U.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (ldivB R' S' ub uc >>= kk) rs out := by
  intro R S UB UC U R' S' ub uc fg rs kk out hRk hRv hSk hSv hbk hbv hck hcv hR hS hB hC hU ⟨hNR, zR, hzR, hscR⟩
    ⟨hNS, zS, hzS, hscS⟩ hTot hfo hkk
  unfold Tab.ldiv at hU
  obtain ⟨R1, hR1, hU⟩ := except_bind_ok hU
  obtain ⟨S1, hS1, hU⟩ := except_bind_ok hU
  unfold ldivB
  simp only [bind_assoc]
  refine canonT_builds hRk hRv hR hR1 hNR hzR hscR hfo ?_
  intro fg2 R2 ys he hf ho hsk hsv hr2
  refine canonT_builds (R := S) (R' := S1) hSk hSv (mapM_get_app hS) hS1 hNS hzS hscS ho ?_
  intro fg3 S2 ys2 he2 hf2 ho2 hsk2 hsv2 hr3
  obtain ⟨e1, h1⟩ := he
  obtain ⟨e2, h2⟩ := he2
  refine hL (r := R1) (s := S1) (UB := UB) (UC := UC) (U := U) (r' := R2) (s' := S2) (ub := ub) (uc := uc)
    (ColsOf.shape A hRk hsk) (ColsOf.shape B hRv hsv) (ColsOf.shape A hSk hsk2) (ColsOf.shape C hSv hsv2) hbk hbv hck hcv
    ?_ hr3 ?_ ?_ hU (hTot R1 S1 hR1 hS1) ho2 ?_
  · exact mapM_get_app hr2
  · exact mapM_get_app (mapM_get_app hB)
  · exact mapM_get_app (mapM_get_app hC)
  · intro fg4 W ys3 he3 hf3 ho3 hsk3 hsv3 hr4
    obtain ⟨e3, h3⟩ := he3
    have := hkk fg4 W (ys ++ ys2 ++ ys3) ⟨e1 ++ (e2 ++ e3), by rw [h3, h2, h1, Array.append_assoc, Array.append_assoc]⟩
      (hf.trans (hf2.trans hf3)) ho3 hsk3 hsv3 (by simpa [Array.append_assoc] using hr4)
    simpa only [Array.append_assoc] using this

/-- The kernel facts `convT_builds` takes of a table `R` it converses (`hN`, `hz`, `hsc` there). -/
def ConvPre {A B : Obj} (R : Tab A B) : Prop := R.n.toNat ≤ 2 ^ 63 ∧
  ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) R.n 0 = .ok z ∧
    ∀ es vs p k g f, ValsB.cols (A := .prod B A) (R.val, R.key) = .ok es → kasc R.n es = .ok (vs, p) →
      kseen R.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 R.n (some z) [(R.n, z), (R.n, g)] [] [] = .ok r

/-- **`rdivB` builds `Tab.rdiv`**: `convB` of each side (`convT_builds`), `ldivSelB ldivOfB` on the converses
    (`LdivSelSpec`, `Tot` holding of them), then `convB` of the quotient (`ConvPre` of it, `hQ`). -/
theorem rdivB_builds {A B C : Obj} {Tot : Tab C B → Tab C A → Tab B B → Tab A A → Prop}
    (hL : LdivSelSpec C B A Tot Tab.bitsMax) :
    ∀ {R : Tab A C} {S : Tab B C} {UA : Tab A A} {UB : Tab B B} {U : Tab A B} {R' S' ua ub : TabB}
      {fg : Array Fun × Array Fun} {rs : Array Val} {kk : TabB → Bld (Array Nat)} {out : Array Val},
    ColsOf A R'.key → ColsOf C R'.val → ColsOf B S'.key → ColsOf C S'.val → ColsOf A ua.key → ColsOf A ua.val →
    ColsOf B ub.key → ColsOf B ub.val →
    R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
    S'.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
    ua.regs.mapM (fun i => rs[i]?) = some (.size UA.n :: (UA.key.regVals ++ UA.val.regVals)) →
    ub.regs.mapM (fun i => rs[i]?) = some (.size UB.n :: (UB.key.regVals ++ UB.val.regVals)) →
    R.rdiv S UA UB = .ok U → ConvPre S → ConvPre R →
    (∀ Sc Rc, S.conv = .ok Sc → R.conv = .ok Rc → Tot Sc Rc UB UA) →
    (∀ Sc Rc L, S.conv = .ok Sc → R.conv = .ok Rc → Sc.ldivOf Rc UB UA = .ok L → ConvPre L) → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape ua.key → Cols.shape W.val = Cols.shape ub.key →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size U.n :: (U.key.regVals ++ U.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (rdivB R' S' ua ub >>= kk) rs out := by
  intro R S UA UB U R' S' ua ub fg rs kk out hRk hRv hSk hSv hak hav hbk hbv hR hS hA hB hU ⟨hNS, zS, hzS, hscS⟩
    ⟨hNR, zR, hzR, hscR⟩ hTot hQ hfo hkk
  unfold Tab.rdiv at hU
  obtain ⟨Sc, hSc, hU⟩ := except_bind_ok hU
  obtain ⟨Rc, hRc, hU⟩ := except_bind_ok hU
  obtain ⟨L, hLd, hU⟩ := except_bind_ok hU
  unfold rdivB
  simp only [convB, bind_assoc]
  refine convT_builds hSk hSv hS hSc hNS hzS hscS hfo ?_
  intro fg2 S2 ys he hf ho hsk hsv hr2
  refine convT_builds (R := R) (R' := Rc) hRk hRv (mapM_get_app hR) hRc hNR hzR hscR ho ?_
  intro fg3 R2 ys2 he2 hf2 ho2 hrk hrv hr3
  obtain ⟨hNL, zL, hzL, hscL⟩ := hQ Sc Rc L hSc hRc hLd
  obtain ⟨e1, h1⟩ := he
  obtain ⟨e2, h2⟩ := he2
  refine hL (r := Sc) (s := Rc) (UB := UB) (UC := UA) (U := L) (r' := S2) (s' := R2) (ub := ub) (uc := ua)
    (ColsOf.shape C hSv hsk) (ColsOf.shape B hSk hsv) (ColsOf.shape C hRv hrk) (ColsOf.shape A hRk hrv) hbk hbv hak hav
    (mapM_get_app hr2) hr3 (mapM_get_app (mapM_get_app hB)) (mapM_get_app (mapM_get_app hA)) hLd (hTot Sc Rc hSc hRc)
    ho2 ?_
  intro fg4 W ys3 he3 hf3 ho3 hWk hWv hr4
  obtain ⟨e3, h3⟩ := he3
  have hLU : L.conv = .ok U := hU
  refine convT_builds (R := L) (R' := U) (ColsOf.shape B hbk hWk) (ColsOf.shape A hak hWv) hr4 hLU hNL hzL hscL ho3 ?_
  intro fg5 W' ys4 he4 hf4 ho4 hWk' hWv' hr5
  obtain ⟨e4, h4⟩ := he4
  have := hkk fg5 W' (ys ++ ys2 ++ ys3 ++ ys4)
    ⟨e1 ++ (e2 ++ (e3 ++ e4)), by rw [h4, h3, h2, h1, Array.append_assoc, Array.append_assoc, Array.append_assoc]⟩
    (hf.trans (hf2.trans (hf3.trans hf4))) ho4 (hWk'.trans hWv) (hWv'.trans hWk)
    (by simpa [Array.append_assoc] using hr5)
  simpa only [Array.append_assoc] using this

end Rel.Lang.Plan
