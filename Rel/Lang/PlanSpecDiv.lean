module

public import Rel.Lang.PlanSpecConcat
public import Rel.Lang.PlanSpecGather
public import Rel.Lang.PlanSpecCorefl
public import Rel.Lang.PlanSpecUnion
public import Rel.Lang.PlanSpecExpand
public import Rel.Lang.PlanSpecSelect
public import Rel.Lang.PlanSpecComp
public import Rel.Lang.PlanSpecPrefix
public import Rel.Lang.PlanSpecNone
public import Rel.Lang.PlanSpecCross

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

/-- **`ldivOfB`, stage A** (`compB` to the group counts): `Q = r° ≫ ⟨𝟙, s⟩` (`compB_builds`), its rows' groups over
    `(b, c)` (`ascSeenB_builds`), their row counts `cnt` (`groupFoldB_builds` over `wordsB`). `kk` continues with `Q`'s
    table `W`, the registers of `K`, `g`, `f`, `p`, `cnt`, and `W`'s columns `key ++ val.drop` (`Q.key`, the `C` side). -/
theorem ldivA_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) {A B C : Obj} {r : Tab A B} {s : Tab A C}
    {Q : Tab B (.prod A C)} {x : Vals (.prod B C) Q.n} (hx : x = (Q.key, (Q.val : Vals A Q.n × Vals C Q.n).2))
    {r' s' : TabB} {fg : Array Fun × Array Fun} {rs out : Array Val} {es : List (AscKey × Enc)} {vs : List Enc}
    {p g f z sg o1 cnt : Enc} {k : Nat} {rr : Enc × Option UInt64}
    {kk : TabB → Nat → Nat → Nat → Nat → Nat → Bld (Array Nat)}
    (hRk : ColsOf A r'.key) (hRv : ColsOf B r'.val) (hSk : ColsOf A s'.key) (hSv : ColsOf C s'.val)
    (hR : r'.regs.mapM (fun i => rs[i]?) = some (.size r.n :: (r.key.regVals ++ r.val.regVals)))
    (hS : s'.regs.mapM (fun i => rs[i]?) = some (.size s.n :: (s.key.regVals ++ s.val.regVals)))
    (hone : (⟨r.n, r.val, r.key⟩ : Tab B A).compOne (⟨s.n, s.key, (s.key, s.val)⟩ : Tab A (.prod A C)) = .ok Q)
    (hpre : CompPre B A (.prod A C) (⟨r.n, r.val, r.key⟩ : Tab B A) (⟨s.n, s.key, (s.key, s.val)⟩ : Tab A (.prod A C)))
    (hpost : CompPost B A (.prod A C) (⟨r.n, r.val, r.key⟩ : Tab B A) Q)
    (hes : ValsB.cols x = .ok es) (hka : kasc Q.n es = .ok (vs, p)) (hks : kseen Q.n ((es.map (·.1)).zip vs) = .ok (k, g, f))
    (hN : Q.n.toNat ≤ 2 ^ 63) (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) Q.n 0 = .ok z)
    (hsc : kscan .max false .i64 .i64 Q.n (some z) [(Q.n, z), (Q.n, g)] [] [] = .ok rr)
    (hseg : Tab.seenSeg Q.n f k.toUSize = .ok sg) (h1 : colConst Q.n 1 = .ok o1)
    (hgf : Tab.groupFold .add Q.n g sg k.toUSize 0 o1 = .ok cnt) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (R : Array Val) (a b c d e : Nat), (∃ y, fg2.1 = fg.1 ++ y) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R → ColsOf B W.key → ColsOf C (W.val.drop s'.key.length) →
      R[W.n]? = some (.size Q.n) →
      (Cols.regs (W.key ++ W.val.drop s'.key.length)).mapM (fun i => R[i]?) = some x.regVals →
      [a, b, c, d, e].mapM (fun i => R[i]?) = some [.size k.toUSize, Reg.put g, Reg.put f, Reg.put p, Reg.put cnt] →
      ∃ fg', Builds abiOf fg2 fg' (kk W a b c d e) R out) :
    ∃ fg', Builds abiOf fg fg' (do
      let W ← compB ⟨r'.n, r'.val, r'.key⟩ ⟨s'.n, s'.key, s'.key ++ s'.val⟩
      let (K, g, f, p) ← ascSeenB W.n (W.key ++ W.val.drop s'.key.length)
      let cnt ← groupFoldB .add W.n g f K 0 (← wordsB W.n 1)
      kk W K g f p cnt) rs out := by
  have e1 : r'.regs = r'.n :: (Cols.regs r'.key ++ Cols.regs r'.val) := by simp [TabB.regs, Cols.regs_append]
  have e2 : s'.regs = s'.n :: (Cols.regs s'.key ++ Cols.regs s'.val) := by simp [TabB.regs, Cols.regs_append]
  rw [e1] at hR
  rw [e2] at hS
  obtain ⟨hn1, gR⟩ := mapM_get_cons hR
  obtain ⟨hn2, gS⟩ := mapM_get_cons hS
  obtain ⟨gRk, gRv⟩ := mapM_split (ColsOf.regs_length hRk r.key) gR
  obtain ⟨gSk, gSv⟩ := mapM_split (ColsOf.regs_length hSk s.key) gS
  refine compB_builds hc h63 B A (.prod A C) (R := ⟨r.n, r.val, r.key⟩) (S := ⟨s.n, s.key, (s.key, s.val)⟩) (T' := Q)
    (R' := ⟨r'.n, r'.val, r'.key⟩) (S' := ⟨s'.n, s'.key, s'.key ++ s'.val⟩) hRv hRk hSk ⟨s'.key, s'.val, rfl, hSk, hSv⟩
    ?_ ?_ hone hpre hpost hfo ?_
  · simp only [TabB.regs, Cols.regs_append, List.mapM_cons, hn1, List.mapM_append, gRv, gRk]
    rfl
  · simp only [TabB.regs, Cols.regs_append, List.mapM_cons, hn2, List.mapM_append, gSk, gSv]
    rfl
  intro fg2 W ys he hf ho hWk hWv hWr
  obtain ⟨c1, c2, hW, hc1, hc2⟩ := ColsOf.shape (.prod A C) ⟨s'.key, s'.val, rfl, hSk, hSv⟩ hWv
  have hWk' : ColsOf B W.key := ColsOf.shape B hRv hWk
  have hdrop : W.val.drop s'.key.length = c2 := by
    rw [hW, show s'.key.length = c1.length from (ColsOf.length_eq hSk).trans (ColsOf.length_eq hc1).symm,
      List.drop_left' rfl]
  have e3 : W.regs = W.n :: (Cols.regs W.key ++ (Cols.regs c1 ++ Cols.regs c2)) := by
    simp [TabB.regs, Cols.regs_append, hW]
  rw [e3] at hWr
  obtain ⟨hn3, g3⟩ := mapM_get_cons hWr
  have hQv : Q.val.regVals = (Q.val : Vals A Q.n × Vals C Q.n).1.regVals ++ (Q.val : Vals A Q.n × Vals C Q.n).2.regVals := by
    simp [ValsB.regVals]
  rw [hQv] at g3
  obtain ⟨g3k, g3v⟩ := mapM_split (ColsOf.regs_length hWk' Q.key) g3
  obtain ⟨g3c1, g3c2⟩ := mapM_split (ColsOf.regs_length hc1 (Q.val : Vals A Q.n × Vals C Q.n).1) g3v
  have hxr : (Cols.regs (W.key ++ c2)).mapM (fun i => (rs ++ ys)[i]?) = some x.regVals := by
    simp only [Cols.regs_append, List.mapM_append, g3k, g3c2, hx]
    rfl
  simp only [hdrop]
  refine ascSeenB_builds (.prod B C) (x := x) (cs := W.key ++ c2) (L := Cols.regs (W.key ++ c2)) (rs := rs ++ ys) (n := W.n)
    ⟨W.key, c2, rfl, hWk', hc2⟩ (regsOf_eq _) hxr hn3 hes hN hka hks hz hsc ho ?_
  intro fg3 ys2 a b c d he3 hf3 ho3 hread3
  obtain ⟨ha, hread3⟩ := mapM_get_cons hread3
  obtain ⟨hb, hread3⟩ := mapM_get_cons hread3
  obtain ⟨hc', hread3⟩ := mapM_get_cons hread3
  obtain ⟨hd, -⟩ := mapM_get_cons hread3
  refine Builds.bind1F (Free.wordsB _ _) (wordsB_builds (n := W.n) (get_app hn3) (by rw [← Rel.colConst_eq]; exact h1))
    fun w R hw m => ?_
  refine groupFoldB_builds (n := W.n) (g := b) (f := c) (m := a) (x := w) (by with_unfolding_all rfl) (m (get_app hn3)) (m hb) (m hc')
    (m ha) hw hseg hgf ho3 ?_
  intro fg4 pp ys4 he4 hf4 ho4 hpp
  obtain ⟨e1', h1'⟩ := he
  obtain ⟨e2', h2'⟩ := he3
  obtain ⟨e3', h3'⟩ := he4
  rw [hf3] at hf4
  refine hkk fg4 W (R ++ ys4) a b c d pp ⟨e1' ++ (e2' ++ e3'), by
      rw [h3', h2', h1', Array.append_assoc, Array.append_assoc]⟩ (hf.trans hf4) ho4
    (fun h => get_app (m (get_app (get_app h)))) hWk' (by rw [hdrop]; exact hc2) (get_app (m (get_app hn3)))
    (by rw [hdrop]; exact mapM_get_app (mapM_extends m (mapM_get_app hxr))) ?_
  simp only [List.mapM_cons, List.mapM_nil, get_app (m ha), get_app (m hb), get_app (m hc'), get_app (m hd), hpp]
  rfl

/-- **`ldivOfB`, stage B** (`catB` to `scatterB`): the rows of `X` (`n1`) then `Y` (`n2`) are `Z` (`N` rows, below `2^63`:
    the guard), their groups over `Z` (`ascSeenB_builds` of `concatB_builds`), per group the count `cR` of `X`'s rows
    (`.lt` of the positions against the constant column of `n1`, `colMap_const_eq`), and `code`, each row's group
    (`scatterB_builds`). `kk` continues with the registers of `N`, the group count, `g`, `f`, `p`, `cR`, `code`. -/
theorem ldivCat_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) {B : Obj} {n1 n2 N : USize}
    {X : Vals B n1} {Y : Vals B n2} {Z : Vals B N} {cx cy : Cols} {a1 a2 : Nat} {fg : Array Fun × Array Fun}
    {rs out : Array Val} {bs : List (AscKey × Enc)} {bv : List Enc} {bp bg bf z sg cm cR code : Enc} {kc : Nat}
    {rr : Enc × Option UInt64} {kk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bld (Array Nat)}
    (hcx : ColsOf B cx) (hcy : ColsOf B cy) (hn1 : rs[a1]? = some (.size n1)) (hn2 : rs[a2]? = some (.size n2))
    (hx : (Cols.regs cx).mapM (fun i => rs[i]?) = some X.regVals)
    (hy : (Cols.regs cy).mapM (fun i => rs[i]?) = some Y.regVals)
    (hcat : catRows n1 n2 = .ok N) (hlt : N.toNat < 2 ^ 63) (hconc : ValsB.concat N X Y = .ok Z)
    (hbs : ValsB.cols Z = .ok bs) (hka : kasc N bs = .ok (bv, bp))
    (hks : kseen N ((bs.map (·.1)).zip bv) = .ok (kc, bg, bf))
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) N 0 = .ok z)
    (hsc : kscan .max false .i64 .i64 N (some z) [(N, z), (N, bg)] [] [] = .ok rr)
    (hseg : Tab.seenSeg N bf kc.toUSize = .ok sg)
    (hkn : ∃ k, colConst N n1.toUInt64 = .ok k ∧ ∃ o, colMap .lt N bp k = .ok o)
    (hcm : colMap .first N bp bp .i64 .i64 [] [(.gt, n1.toUInt64)] = .ok cm)
    (hgf : Tab.groupFold .add N bg sg kc.toUSize 0 cm = .ok cR) (hsca : kscatter .last N bp bg N 0 = .ok code)
    (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val) (a b c d e f g : Nat), (∃ y, fg2.1 = fg.1 ++ y) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R →
      [a, b, c, d, e, f, g].mapM (fun i => R[i]?) =
        some [.size N, .size kc.toUSize, Reg.put bg, Reg.put bf, Reg.put bp, Reg.put cR, Reg.put code] →
      ∃ fg', Builds abiOf fg2 fg' (kk a b c d e f g) R out) :
    ∃ fg', Builds abiOf fg fg' (do
      let (N, sh) ← catB a1 a2
      guard (← call1 (kernel% USize.decLt) #[N, ← lit (.size (2 ^ 63))]) "ldiv: rows past 2^63" #[N]
      let (bk, bg, bf, bp) ← ascSeenB N (← concatB N a1 a2 sh cx cy)
      let cR ← groupFoldB .add N bg bf bk 0 (← mapB .lt N bp (← constB N (← wordOf a1)))
      let code ← scatterB .last N bp bg N
      kk N bk bg bf bp cR code) rs out := by
  have hNs : N.toNat = n1.toNat + n2.toNat := catRows_ok hcat
  have hnm : n1.toNat + n2.toNat < 2 ^ 63 := hNs ▸ hlt
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  obtain ⟨zc, oc, f', hzc, hoc⟩ := hc n1 n2 hnm
  obtain ⟨kcc, hkc, o, ho⟩ := hkn
  obtain ⟨f1, ho'⟩ := colMap_kscan ho
  obtain rfl : o = cm := colMap_const_eq hkc ho hcm (fun w v h => by simpa [Op.eval] using h)
  simp only [bind_assoc]
  refine Builds.bind2F (Free.catB _ _) (catB_builds hn1 hn2 hcat hzc hoc) fun r1 r2 R2 hr1 hr2 hE => ?_
  dsimp only
  refine litE fun c1 R5 h1 m5 => ?_
  up m5 [hr1 hr2]
  have hE5 : Extends rs R5 := fun h => m5 (hE h)
  refine call1E (v := .bit (decide (N < 2 ^ 63))) (by abiK) rfl
    (reads_of (l := [r1, c1]) (vs := [.size N, .size (2 ^ 63)]) (by simp [hr1, h1])) (by simp [arg, hsz, Out.out]; rfl)
    rfl fun g R6 hg m6 => ?_
  up m6 [hr1 hr2]
  have hE6 : Extends rs R6 := fun h => m6 (hE5 h)
  have hlt' : N < 2 ^ 63 := by rw [USize.lt_iff_toNat_lt, h63]; exact hlt
  refine Builds.guardE (by simpa [hlt'] using hg) ?_
  refine concatB_builds hc h63 B (x := X) (y := Y) (z := Z) hcx hcy (mapM_extends hE6 hx) (mapM_extends hE6 hy) hr1
    (hE6 hn1) (hE6 hn2) hconc hfo ?_
  intro fg2 cs' ys heC hfC hoC hs hr
  refine ascSeenB_builds B (x := Z) (cs := cs') (L := Cols.regs cs') (n := r1) (ColsOf.shape B hcx hs) (regsOf_eq _) hr
    (get_app hr1) hbs (Nat.le_of_lt hlt) hka hks hz hsc hoC ?_
  intro fg3 ys2 a b c d he3 hf3 ho3 hread3
  dsimp only
  obtain ⟨ha, hread3⟩ := mapM_get_cons hread3
  obtain ⟨hb, hread3⟩ := mapM_get_cons hread3
  obtain ⟨hc', hread3⟩ := mapM_get_cons hread3
  obtain ⟨hd, -⟩ := mapM_get_cons hread3
  have hn1x : (R6 ++ ys ++ ys2)[a1]? = some (.size n1) := get_app (get_app (hE6 hn1))
  have hr1x : (R6 ++ ys ++ ys2)[r1]? = some (.size N) := get_app (get_app hr1)
  refine call1E (v := .u64 n1.toUInt64) (by abiK) rfl (reads_of (l := [a1]) (vs := [.size n1])
    (by simp only [List.mapM_cons, List.mapM_nil, hn1x]; rfl))
    (by simp [arg, hsz, Out.out]; rfl) rfl fun w R9 hw m9 => ?_
  up m9 [ha hb hc' hd hr1x hn1x]
  refine Builds.bind1F (Free.constB _ _) (constB_builds hr1x hw (by rw [← Rel.colConst_eq]; exact hkc)) fun cc R10 hcc m10 => ?_
  up m10 [ha hb hc' hd hr1x]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hr1x hd (enc_get_put _) hcc (enc_get_put _) (by rop)
    (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) ho') fun mm R11 hmm m11 => ?_
  up m11 [ha hb hc' hd hr1x]
  refine groupFoldB_builds (n := r1) (g := b) (f := c) (m := a) (x := mm) (by with_unfolding_all rfl) hr1x hb hc' ha hmm
    hseg hgf ho3 ?_
  intro fg4 pp ys4 he4 hf4 ho4 hpp
  have m4' : Extends R11 (R11 ++ ys4) := fun h => get_app h
  up m4' [ha hb hc' hd hr1x]
  refine Builds.bind1F (Free.scatterB _ _ _ _ _ _) (scatterB_builds hr1x hd hb hr1x (by rop) hsca) fun co R12 hco m12 => ?_
  up m12 [ha hb hc' hd hr1x hpp]
  obtain ⟨e1', h1'⟩ := heC
  obtain ⟨e2', h2'⟩ := he3
  obtain ⟨e3', h3'⟩ := he4
  rw [hf3] at hf4
  refine hkk fg4 R12 r1 a b c d pp co ⟨e1' ++ (e2' ++ e3'), by
      rw [h3', h2', h1', Array.append_assoc, Array.append_assoc]⟩ (hfC.trans hf4) ho4
    (fun h => m12 (get_app (m11 (m10 (m9 (get_app (get_app (hE6 h)))))))) ?_
  simp only [List.mapM_cons, List.mapM_nil, hr1x, ha, hb, hc', hd, hpp, hco]
  rfl

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
