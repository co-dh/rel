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
      Cols.shape W.key = Cols.shape r'.val → Cols.shape (W.val.drop s'.key.length) = Cols.shape s'.val →
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
  have hshC : Cols.shape (W.val.drop s'.key.length) = Cols.shape s'.val := by
    have hWv' : Cols.shape W.val = Cols.shape (s'.key ++ s'.val) := hWv
    rw [Cols.shape_eq_map, List.map_drop, ← Cols.shape_eq_map, hWv', Cols.shape_eq_map, List.map_append,
      List.drop_left' (by simp), ← Cols.shape_eq_map]
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
    (fun h => get_app (m (get_app (get_app h)))) hWk' (by rw [hdrop]; exact hc2) hWk hshC (get_app (m (get_app hn3)))
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

set_option hygiene false in
/-- `up`, and the column-register facts `hx1`, `hx2` and the extension `hext` of the first registers with it. -/
local macro "upc " m:ident " [" hs:ident* "]" : tactic => do
  let rs ← hs.mapM fun h => `(tactic| replace $h:ident := $m:ident $h:ident)
  `(tactic| ($[$rs];*; replace hx1 := mapM_extends $m hx1; replace hx2 := mapM_extends $m hx2; replace hext := ext_trans hext $m))

/-- **`ldivOfB`, stage C** (`q` gathered at the group firsts, the count `d` of `r`'s rows of each group's `b` read through
    `code`, the groups with `cnt = d` by `whereB` (`WhereAgree`: its chain answers as `whereCol`), `P`'s columns `Q.key`,
    `Q.val.2` gathered at them). `kk` continues with `P`, of the shapes of `cs1`, `cs2`, whose registers hold `yk`, `yv`. -/
theorem ldivSel_builds {B C : Obj} {Kv Qn n1 Nv bkv Mv : USize} {Qk : Vals B Qn} {Qc : Vals C Qn}
    {yk : Vals B Mv} {yv : Vals C Mv} {cs1 cs2 : Cols} {fg : Array Fun × Array Fun} {rs out : Array Val}
    {rK rF rP rcnt rN rBk rCode rCR rQn a1 : Nat} {f p cnt cR code q qa d1 d bits sel ix : Enc}
    {kk : TabB → Bld (Array Nat)}
    (hcs1 : ColsOf B cs1) (hcs2 : ColsOf C cs2)
    (hx1 : (Cols.regs cs1).mapM (fun i => rs[i]?) = some Qk.regVals)
    (hx2 : (Cols.regs cs2).mapM (fun i => rs[i]?) = some Qc.regVals)
    (hQn : rs[rQn]? = some (.size Qn)) (hn1 : rs[a1]? = some (.size n1)) (hK : rs[rK]? = some (.size Kv))
    (hf : rs[rF]? = some (Reg.put f)) (hp : rs[rP]? = some (Reg.put p)) (hcnt : rs[rcnt]? = some (Reg.put cnt))
    (hN : rs[rN]? = some (.size Nv)) (hbk : rs[rBk]? = some (.size bkv))
    (hcR : rs[rCR]? = some (Reg.put cR)) (hcode : rs[rCode]? = some (Reg.put code))
    (hq : kgather Kv f Qn p = .ok q)
    (hkn : ∃ k, colConst Kv n1.toUInt64 = .ok k ∧ ∃ o, colMap .add Kv q k = .ok o)
    (hqa : colMap .first Kv q q .i64 .i64 [] [(.add, n1.toUInt64)] = .ok qa)
    (hd1 : kgather Kv qa Nv code = .ok d1) (hd : kgather Kv d1 bkv cR = .ok d)
    (hkeep : colMap .eq Kv cnt d = .ok bits)
    (hW : WhereAgree Kv Mv bits sel) (hix : kgather Mv sel Kv q = .ok ix)
    (hgk : ValsB.gather Mv ix Qk = .ok yk) (hgv : ValsB.gather Mv ix Qc = .ok yv) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (P : TabB) (R : Array Val), (∃ y, fg2.1 = fg.1 ++ y) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R → Cols.shape P.key = Cols.shape cs1 →
      Cols.shape P.val = Cols.shape cs2 →
      P.regs.mapM (fun i => R[i]?) = some (.size Mv :: (yk.regVals ++ yv.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk P) R out) :
    ∃ fg', Builds abiOf fg fg' (do
      let q ← gatherB rK rF rQn rP
      let d ← gatherB rK (← gatherB rK (← mapB .add rK q (← constB rK (← wordOf a1))) rN rCode) rBk rCR
      let (M, sel) ← whereB rK (← mapB .eq rK rcnt d)
      let ix ← gatherB M sel rK q
      kk ⟨M, ← gatherCols M ix rQn cs1, ← gatherCols M ix rQn cs2⟩) rs out := by
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  have hext : ∀ (i : Nat) (v : Val), rs[i]? = some v → rs[i]? = some v := fun _ _ h => h
  obtain ⟨kcc, hkc, o, ho⟩ := hkn
  obtain ⟨f1, ho'⟩ := colMap_kscan ho
  obtain rfl : o = qa := colMap_const_eq hkc ho hqa (fun w v h => by simpa [Op.eval, UInt64.add_comm] using h)
  obtain ⟨f2, hk'⟩ := colMap_kscan hkeep
  obtain ⟨zc2, pc, ixc, ix1c, zrc, onec, cutc, fo, ixf, cutf, fw, hz2, hp2, hf2, hK2, hix2, hs2, hzr, hone2, hcut,
    hg2, hrt⟩ := hW
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hK hf hQn hp hq) fun qr R1 hqr m1 => ?_
  upc m1 [hQn hn1 hK hf hp hcnt hN hbk hcR hcode]
  refine call1E (v := .u64 n1.toUInt64) (by abiK) rfl (reads_of (l := [a1]) (vs := [.size n1])
    (by simp only [List.mapM_cons, List.mapM_nil, hn1]; rfl))
    (by simp [arg, hsz, Out.out]; rfl) rfl fun w R2 hw m2 => ?_
  upc m2 [hQn hn1 hK hf hp hcnt hN hbk hcR hcode hqr]
  refine Builds.bind1F (Free.constB _ _) (constB_builds hK hw (by rw [← Rel.colConst_eq]; exact hkc)) fun cc R3 hcc m3 => ?_
  upc m3 [hQn hn1 hK hf hp hcnt hN hbk hcR hcode hqr]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hK hqr (enc_get_put _) hcc (enc_get_put _) (by rop)
    (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) ho') fun mm R4 hmm m4 => ?_
  upc m4 [hQn hn1 hK hf hp hcnt hN hbk hcR hcode hqr]
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hK hmm hN hcode hd1) fun g1 R5 hg1 m5 => ?_
  upc m5 [hQn hn1 hK hf hp hcnt hN hbk hcR hcode hqr]
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hK hg1 hbk hcR hd) fun g2 R6 hg2' m6 => ?_
  upc m6 [hQn hn1 hK hf hp hcnt hN hbk hcR hcode hqr]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hK hcnt (enc_get_put _) hg2' (enc_get_put _) (by rop)
    (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hk') fun bt R7 hbt m7 => ?_
  upc m7 [hQn hn1 hK hf hp hcnt hN hbk hcR hcode hqr]
  refine Builds.bind2F (Free.whereB _ _) (whereB_builds hK (by simp [hbt, enc_get_put]) hz2 hp2 hf2 hK2 hix2 hs2 hzr
    hone2 hcut hg2 hrt) fun kr sr R8 hk8 hsr8 m8 => ?_
  dsimp only
  upc m8 [hQn hn1 hK hf hp hcnt hN hbk hcR hcode hqr]
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hk8 hsr8 hK hqr hix) fun i1 R9 hi1 m9 => ?_
  upc m9 [hQn hn1 hK hf hp hcnt hN hbk hcR hcode hqr hk8 hsr8]
  refine gatherCols_builds B (x := Qk) (y := yk) hcs1 hx1 hk8 hi1 hQn hgk hfo ?_
  intro fg7 ks'' ys7 he7 hf7 ho7 hs7 hr7
  have mg : Extends R9 (R9 ++ ys7) := fun h => get_app h
  upc mg [hQn hn1 hK hf hp hcnt hN hbk hcR hcode hqr hk8 hsr8 hi1]
  refine gatherCols_builds C (x := Qc) (y := yv) hcs2 hx2 hk8 hi1 hQn hgv ho7 ?_
  intro fg8 vs'' ys8 he8 hf8 ho8 hs8 hr8
  refine hkk fg8 ⟨kr, ks'', vs''⟩ ((R9 ++ ys7) ++ ys8) (FExt.trans he7 he8) (hf7.trans hf8) ho8
    (fun h => get_app (hext _ _ h)) hs7 hs8 ?_
  simp only [TabB.regs, Cols.regs_append]
  refine omapM_cons.mpr ⟨_, _, get_app hk8, ?_, rfl⟩
  rw [List.mapM_append, mapM_get_app hr7, hr8]
  rfl

/-- The kernel facts `coreflB_ran_builds` takes of the table `R` whose `ran` it builds (`hN`, `hz`, `hsc` there). -/
def RanPre {a b : Obj} (R : Tab a b) : Prop := R.n.toNat ≤ 2 ^ 63 ∧
  ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) R.n 0 = .ok z ∧
    ∀ es vs p k g f, ValsB.cols R.val = .ok es → kasc R.n es = .ok (vs, p) →
      kseen R.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 R.n (some z) [(R.n, z), (R.n, g)] [] [] = .ok r

/-- The kernel facts `selBody_builds` takes (all but `TagOff`) of the tables `R`, `S` that `Tab.select kp` selects. -/
def SelPre {a b : Obj} (kp : USize → Enc → Enc → Except String Enc) (R S : Tab a b) : Prop :=
  R.n.toNat + S.n.toNat < 2 ^ 63 ∧
  (∀ C tag, R.tagged S = .ok (C, tag) → ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) C.n 0 = .ok z) ∧
  (∀ C tag es vs p k g f z, R.tagged S = .ok (C, tag) →
      kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) C.n 0 = .ok z →
      ValsB.cols (A := .prod a b) (C.key, C.val) = .ok es → kasc C.n es = .ok (vs, p) →
      kseen C.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 C.n (some z) [(C.n, z), (C.n, g)] [] [] = .ok r) ∧
  (∀ m mn mx bits K sel, kp m mn mx = .ok bits → whereCol m bits = .ok (K, sel) → WhereAgree m K bits sel)

/-- The kernel answers `crossB_cross_builds` takes: the constant column of `mv`, then the `.div` and `.mod` of the `Tv`
    positions by it. -/
def CrossPre (Tv mv : USize) : Prop := ∃ (k d r : Enc) (f1 f2 : Option UInt64), colConst Tv mv.toUInt64 = .ok k ∧
  kscan .div false .i64 .i64 Tv none [(Tv, .pos), (Tv, k)] [] [] = .ok (d, f1) ∧
  kscan .mod false .i64 .i64 Tv none [(Tv, .pos), (Tv, k)] [] [] = .ok (r, f2)

/-- `Extends rs R` is `R = rs ++ ys`. -/
theorem Extends.exists_app {rs R : Array Val} (h : Extends rs R) : ∃ ys, R = rs ++ ys := by
  refine ⟨(R.toList.drop rs.size).toArray, Array.ext_getElem? fun i => ?_⟩
  by_cases hi : i < rs.size
  · have := h (Array.getElem?_eq_getElem hi)
    rw [Array.getElem?_append_left hi, this]
    exact (Array.getElem?_eq_getElem hi).symm
  · rw [Array.getElem?_append_right (by omega)]
    simp [List.getElem?_drop, show rs.size + (i - rs.size) = i by omega]

/-- **`ldivOfB`, stage D** (`(ran UB − ran r) × ran UC` unioned into `P`): `coreflB` of `UB`'s and `r`'s values
    (`coreflB_ran_builds`), `selectB` of them (`diffB_builds`), `coreflB` of `UC`'s, `crossB` of the two key sides
    (`crossB_cross_builds`), `unionB` of `P` and the product (`unionB_builds`). `hunion` states `P.union` of the raw
    product: `Tab.cross` canonises it first, and `union` canonises again. -/
theorem ldivTail_builds (hT : TagOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) {A B C : Obj} {r : Tab A B}
    {UB : Tab B B} {UC : Tab C C} {RU RR V : Tab B B} {WC : Tab C C} {Tv Mv : USize} {x' : Vals B Tv}
    {y' : Vals C Tv} {yk : Vals B Mv} {yv : Vals C Mv} {U : Tab B C} {r' ub uc P : TabB} {fg : Array Fun × Array Fun}
    {rs out : Array Val} {kk : TabB → Bld (Array Nat)}
    (hrv : ColsOf B r'.val) (hubv : ColsOf B ub.val) (hucv : ColsOf C uc.val) (hPk : ColsOf B P.key)
    (hPv : ColsOf C P.val)
    (hrx : (Cols.regs r'.val).mapM (fun i => rs[i]?) = some r.val.regVals) (hrn : rs[r'.n]? = some (.size r.n))
    (hubx : (Cols.regs ub.val).mapM (fun i => rs[i]?) = some UB.val.regVals) (hubn : rs[ub.n]? = some (.size UB.n))
    (hucx : (Cols.regs uc.val).mapM (fun i => rs[i]?) = some UC.val.regVals) (hucn : rs[uc.n]? = some (.size UC.n))
    (hP : P.regs.mapM (fun i => rs[i]?) = some (.size Mv :: (yk.regVals ++ yv.regVals)))
    (hran1 : UB.ran = .ok RU) (hran2 : r.ran = .ok RR) (hran3 : UC.ran = .ok WC) (hdiff : RU.diff RR = .ok V)
    (hcr : Vals.cross V.key WC.key = .ok ⟨Tv, x', y'⟩)
    (hunion : Tab.union (⟨Mv, yk, yv⟩ : Tab B C) ⟨Tv, x', y'⟩ = .ok U)
    (hpre1 : RanPre UB) (hpre2 : RanPre r) (hpre3 : RanPre UC)
    (hsel : SelPre (fun m _ mx => colMap .not m mx mx) RU RR) (hcpre : CrossPre Tv WC.n)
    (hcan : ∀ Cc, Tab.concat (⟨Mv, yk, yv⟩ : Tab B C) ⟨Tv, x', y'⟩ = .ok Cc → CanOK Cc) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (R : Array Val), (∃ y, fg2.1 = fg.1 ++ y) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R → Cols.shape W.key = Cols.shape P.key →
      Cols.shape W.val = Cols.shape P.val →
      W.regs.mapM (fun i => R[i]?) = some (.size U.n :: (U.key.regVals ++ U.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) R out) :
    ∃ fg', Builds abiOf fg fg' (do
      let V ← selectB (fun m _ mx => mapB .not m mx mx) (← coreflB ub.n ub.val) (← coreflB r'.n r'.val)
      let W ← coreflB uc.n uc.val
      let (T, x, y) ← crossB V.n W.n V.key W.key
      unionB P ⟨T, x, y⟩ >>= kk) rs out := by
  obtain ⟨hN1, z1, hz1, hsc1⟩ := hpre1
  obtain ⟨hN2, z2, hz2, hsc2⟩ := hpre2
  obtain ⟨hN3, z3, hz3, hsc3⟩ := hpre3
  obtain ⟨hlt, hzs, hscs, hWs⟩ := hsel
  obtain ⟨kc, dc, rc, f1, f2, hkc, hdc, hrc⟩ := hcpre
  refine coreflB_ran_builds (R := UB) (R' := RU) hubv hubx hubn hran1 hN1 hz1 hsc1 hfo ?_
  intro fg1 U1 ys1 he1 hf1 ho1 hsk1 hsv1 hr1
  refine coreflB_ran_builds (R := r) (R' := RR) hrv (mapM_get_app hrx) (get_app hrn) hran2 hN2 hz2 hsc2 ho1 ?_
  intro fg2 U2 ys2 he2 hf2 ho2 hsk2 hsv2 hr2
  refine diffB_builds hT h63 B B (R := RU) (S := RR) (T' := V) (R' := U1) (S' := U2)
    (ColsOf.shape B hubv hsk1) (ColsOf.shape B hubv hsv1) (ColsOf.shape B hrv hsk2) (ColsOf.shape B hrv hsv2)
    (mapM_get_app hr1) hr2 hdiff hlt hzs hscs hWs ho2 ?_
  intro fg3 V1 ys3 he3 hf3 ho3 hsk3 hsv3 hr3
  refine coreflB_ran_builds (R := UC) (R' := WC) hucv (mapM_get_app (mapM_get_app (mapM_get_app hucx)))
    (get_app (get_app (get_app hucn))) hran3 hN3 hz3 hsc3 ho3 ?_
  intro fg4 W1 ys4 he4 hf4 ho4 hsk4 hsv4 hr4
  have hVk : ColsOf B V1.key := ColsOf.shape B hubv (hsk3.trans hsk1)
  have hVv : ColsOf B V1.val := ColsOf.shape B hubv (hsv3.trans hsv1)
  have hWk : ColsOf C W1.key := ColsOf.shape C hucv hsk4
  have hVe : V1.regs = V1.n :: (Cols.regs V1.key ++ Cols.regs V1.val) := by simp [TabB.regs, Cols.regs_append]
  have hr3' : V1.regs.mapM (fun i => (rs ++ ys1 ++ ys2 ++ ys3 ++ ys4)[i]?) = _ := mapM_get_app hr3
  rw [hVe] at hr3'
  obtain ⟨hn3, hr3''⟩ := mapM_get_cons hr3'
  obtain ⟨hVkx, -⟩ := mapM_split (ColsOf.regs_length hVk V.key) hr3''
  have hWe : W1.regs = W1.n :: (Cols.regs W1.key ++ Cols.regs W1.val) := by simp [TabB.regs, Cols.regs_append]
  rw [hWe] at hr4
  obtain ⟨hn4, hr4'⟩ := mapM_get_cons hr4
  obtain ⟨hWkx, -⟩ := mapM_split (ColsOf.regs_length hWk WC.key) hr4'
  refine crossB_cross_builds (A := B) (B := C) (xs := V1.key) (ys := W1.key) (x := V.key) (y := WC.key) hcr h63
    hn3 hn4 hkc hdc hrc hVk hWk hVkx hWkx ho4 ?_
  intro fg5 T xs' ys' R5 he5 hf5 ho5 hs5 hs6 hE5 hr5
  have hPR : P.regs.mapM (fun i => R5[i]?) = some (.size Mv :: (yk.regVals ++ yv.regVals)) :=
    mapM_extends (fun h => hE5 (get_app (get_app (get_app (get_app h))))) hP
  have hSR : (⟨T, xs', ys'⟩ : TabB).regs.mapM (fun i => R5[i]?) =
      some (.size (⟨Tv, x', y'⟩ : Tab B C).n :: ((⟨Tv, x', y'⟩ : Tab B C).key.regVals ++
        (⟨Tv, x', y'⟩ : Tab B C).val.regVals)) := by
    simp only [TabB.regs, Cols.regs_append]; exact hr5
  refine unionB_builds hT.catOff h63 B C (R := ⟨Mv, yk, yv⟩) (S := ⟨Tv, x', y'⟩) (U := U) (R' := P) (S' := ⟨T, xs', ys'⟩)
    hPk hPv (ColsOf.shape B hVk hs5) (ColsOf.shape C hWk hs6) hPR hSR hunion hcan ho5 ?_
  intro fg6 W ys6 he6 hf6 ho6 hsk hsv hr6
  obtain ⟨e1, h1⟩ := he1
  obtain ⟨e2, h2⟩ := he2
  obtain ⟨e3, h3⟩ := he3
  obtain ⟨e4, h4⟩ := he4
  obtain ⟨e5, h5⟩ := he5
  obtain ⟨e6, h6⟩ := he6
  refine hkk fg6 W (R5 ++ ys6) ⟨e1 ++ (e2 ++ (e3 ++ (e4 ++ (e5 ++ e6)))), by
      rw [h6, h5, h4, h3, h2, h1, Array.append_assoc, Array.append_assoc, Array.append_assoc, Array.append_assoc,
        Array.append_assoc]⟩
    (hf1.trans (hf2.trans (hf3.trans (hf4.trans (hf5.trans hf6))))) ho6
    (fun h => get_app (hE5 (get_app (get_app (get_app (get_app h)))))) hsk hsv hr6

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

/-- The kernel facts `ascSeenB_builds` takes of the columns `x` it groups (`hz`, `hsc` there). -/
def AscPre {B : Obj} {n : USize} (x : Vals B n) : Prop :=
  ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) n 0 = .ok z ∧
    ∀ es vs p k g f, ValsB.cols x = .ok es → kasc n es = .ok (vs, p) → kseen n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 n (some z) [(n, z), (n, g)] [] [] = .ok r

/-- **The premises the four stages of `ldivOfB` leave open**, for the tables `r'`, `s'`, `ub`, `uc` holding `r`, `s`,
    `UB`, `UC`: kernel facts of the run of `r.ldivOf s UB UC` (each gated by the run's own earlier values) and three
    that the plan and the model do not yet agree on. -/
structure LdivTot {A B C : Obj} (r : Tab A B) (s : Tab A C) (UB : Tab B B) (UC : Tab C C) (r' s' ub uc : TabB) : Prop where
  /-- `compB`'s output has the columns of `r'.val`, which `ub.key` must share: the plan does not say it (open). -/
  shapeB : Cols.shape r'.val = Cols.shape ub.key
  /-- Likewise `s'.val` and `uc.key` (open). -/
  shapeC : Cols.shape s'.val = Cols.shape uc.key
  /-- `Tab.cross` canonises its product and `ldivOfB` unions the raw one, so the unions agree only if `canon` of the
      concatenation ignores that (open). -/
  hunion : ∀ (P : Tab B C) (V : Tab B B) (WC : Tab C C) (Tv : USize) (x' : Vals B Tv) (y' : Vals C Tv) (Cr U : Tab B C),
    Vals.cross V.key WC.key = .ok ⟨Tv, x', y'⟩ → Tab.cross V.key WC.key = .ok Cr → P.union Cr = .ok U →
    P.union ⟨Tv, x', y'⟩ = .ok U
  comp : ∀ Q, (⟨r.n, r.val, r.key⟩ : Tab B A).compOne (⟨s.n, s.key, (s.key, s.val)⟩ : Tab A (.prod A C)) = .ok Q →
    CompPre B A (.prod A C) (⟨r.n, r.val, r.key⟩ : Tab B A) (⟨s.n, s.key, (s.key, s.val)⟩ : Tab A (.prod A C)) ∧
    CompPost B A (.prod A C) (⟨r.n, r.val, r.key⟩ : Tab B A) Q ∧
    AscPre (B := .prod B C) (n := Q.n) (Q.key, (Q.val : Vals A Q.n × Vals C Q.n).2)
  cat : ∀ {N : USize} (Z : Vals B N) bs bv bp, ValsB.cols Z = .ok bs → kasc N bs = .ok (bv, bp) →
    AscPre Z ∧ ∃ k, colConst N r.n.toUInt64 = .ok k ∧ ∃ o, colMap .lt N bp k = .ok o
  addC : ∀ (K Qn : USize) f p q, kgather K f Qn p = .ok q →
    ∃ k, colConst K r.n.toUInt64 = .ok k ∧ ∃ o, colMap .add K q k = .ok o
  whereC : ∀ Kv cnt d bits M sel, colMap .eq Kv cnt d = .ok bits → whereCol Kv bits = .ok (M, sel) →
    WhereAgree Kv M bits sel
  ranUB : RanPre UB
  ranR : RanPre r
  ranUC : RanPre UC
  sel : ∀ RU RR, UB.ran = .ok RU → r.ran = .ok RR → SelPre (fun m _ mx => colMap .not m mx mx) RU RR
  cross : ∀ (V : Tab B B) (WC : Tab C C) Tv x' y', Vals.cross V.key WC.key = .ok ⟨Tv, x', y'⟩ → CrossPre Tv WC.n
  can : ∀ (P : Tab B C) (V : Tab B B) (WC : Tab C C) Tv x' y', Vals.cross V.key WC.key = .ok ⟨Tv, x', y'⟩ →
    ∀ Cc, Tab.concat P ⟨Tv, x', y'⟩ = .ok Cc → CanOK Cc

/-! `ldivOfB` then `kk`, cut into the continuations of its stages. Each stage theorem states its goal with `kk` innermost
and `bind_assoc` cannot commute `kk` into `ldivOfB`'s pair matches (`simp` turns them into projections that the
stage statements do not unify with, a timeout): so each continuation is a named definition and the unification is
first-order. -/

/-- Stage D and `kk` (`ldivTail_builds`). -/
def ldivR3 (r ub uc : TabB) (kk : TabB → Bld (Array Nat)) (P : TabB) : Bld (Array Nat) := do
  let V ← selectB (fun m _ mx => mapB .not m mx mx) (← coreflB ub.n ub.val) (← coreflB r.n r.val)
  let W2 ← coreflB uc.n uc.val
  let (T, x, y) ← crossB V.n W2.n V.key W2.key
  unionB P ⟨T, x, y⟩ >>= kk

/-- Stage C and what follows (`ldivSel_builds`). -/
def ldivR2 (r s ub uc : TabB) (kk : TabB → Bld (Array Nat)) (W : TabB) (K f p cnt N bk cR code : Nat) :
    Bld (Array Nat) := do
  let q ← gatherB K f W.n p
  let d ← gatherB K (← gatherB K (← mapB .add K q (← constB K (← wordOf r.n))) N code) bk cR
  let (M, sel) ← whereB K (← mapB .eq K cnt d)
  let ix ← gatherB M sel K q
  ldivR3 r ub uc kk ⟨M, ← gatherCols M ix W.n W.key, ← gatherCols M ix W.n (W.val.drop s.key.length)⟩

/-- Stage B and what follows (`ldivCat_builds`). -/
def ldivR1 (r s ub uc : TabB) (kk : TabB → Bld (Array Nat)) (W : TabB) (K f p cnt : Nat) : Bld (Array Nat) := do
  let (N, sh) ← catB r.n W.n
  guard (← call1 (kernel% USize.decLt) #[N, ← lit (.size (2 ^ 63))]) "ldiv: rows past 2^63" #[N]
  let (bk, bg, bf, bp) ← ascSeenB N (← concatB N r.n W.n sh r.val W.key)
  let cR ← groupFoldB .add N bg bf bk 0 (← mapB .lt N bp (← constB N (← wordOf r.n)))
  let code ← scatterB .last N bp bg N
  ldivR2 r s ub uc kk W K f p cnt N bk cR code

theorem ldivOfB_cps (r s ub uc : TabB) (kk : TabB → Bld (Array Nat)) : (ldivOfB r s ub uc >>= kk) = (do
    let W ← compB ⟨r.n, r.val, r.key⟩ ⟨s.n, s.key, s.key ++ s.val⟩
    let (K, g, f, p) ← ascSeenB W.n (W.key ++ W.val.drop s.key.length)
    let cnt ← groupFoldB .add W.n g f K 0 (← wordsB W.n 1)
    ldivR1 r s ub uc kk W K f p cnt) := by
  simp only [ldivOfB, ldivR1, ldivR2, ldivR3, bind_assoc]

/-- **`ldivOfB` builds `Tab.ldivOf`**: the four stages in order (`ldivA_builds`, `ldivCat_builds`, `ldivSel_builds`,
    `ldivTail_builds`), the values of each read off the run `hU` of the model, the kernel facts in `LdivTot`. -/
theorem ldivOfB_builds (hT : TagOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) {A B C : Obj} {r : Tab A B} {s : Tab A C}
    {UB : Tab B B} {UC : Tab C C} {U : Tab B C} {r' s' ub uc : TabB} {fg : Array Fun × Array Fun}
    {rs out : Array Val} {kk : TabB → Bld (Array Nat)}
    (hRk : ColsOf A r'.key) (hRv : ColsOf B r'.val) (hSk : ColsOf A s'.key) (hSv : ColsOf C s'.val)
    (hbv : ColsOf B ub.val) (hcv : ColsOf C uc.val)
    (hR : r'.regs.mapM (fun i => rs[i]?) = some (.size r.n :: (r.key.regVals ++ r.val.regVals)))
    (hS : s'.regs.mapM (fun i => rs[i]?) = some (.size s.n :: (s.key.regVals ++ s.val.regVals)))
    (hB : ub.regs.mapM (fun i => rs[i]?) = some (.size UB.n :: (UB.key.regVals ++ UB.val.regVals)))
    (hC : uc.regs.mapM (fun i => rs[i]?) = some (.size UC.n :: (UC.key.regVals ++ UC.val.regVals)))
    (hU : r.ldivOf s UB UC = .ok U) (hTot : LdivTot r s UB UC r' s' ub uc) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape ub.key → Cols.shape W.val = Cols.shape uc.key →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size U.n :: (U.key.regVals ++ U.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (ldivOfB r' s' ub uc >>= kk) rs out := by
  unfold Tab.ldivOf at hU
  obtain ⟨Q, hone, hU⟩ := except_bind_ok hU
  obtain ⟨es, hes, hU⟩ := except_bind_ok hU
  obtain ⟨⟨vs, p⟩, hka, hU⟩ := except_bind_ok hU
  obtain ⟨⟨k, g, f⟩, hks, hU⟩ := except_bind_ok hU
  obtain ⟨sg, hseg, hU⟩ := except_bind_ok hU
  obtain ⟨o1, h1, hU⟩ := except_bind_ok hU
  obtain ⟨cnt, hgf, hU⟩ := except_bind_ok hU
  obtain ⟨N, hcat, hU⟩ := except_bind_ok hU
  obtain ⟨hlt, hU⟩ : N.toNat < 2 ^ 63 ∧ _ := by
    split at hU
    · cases hU
    · exact ⟨by omega, by simpa using hU⟩
  obtain ⟨Z, hconc, hU⟩ := except_bind_ok hU
  obtain ⟨bs, hbs, hU⟩ := except_bind_ok hU
  obtain ⟨⟨bv, bp⟩, hka2, hU⟩ := except_bind_ok hU
  obtain ⟨⟨bk, bg, bf⟩, hks2, hU⟩ := except_bind_ok hU
  obtain ⟨sg2, hseg2, hU⟩ := except_bind_ok hU
  obtain ⟨cm, hcm, hU⟩ := except_bind_ok hU
  obtain ⟨cR, hgf2, hU⟩ := except_bind_ok hU
  obtain ⟨code, hsca, hU⟩ := except_bind_ok hU
  obtain ⟨q, hq, hU⟩ := except_bind_ok hU
  obtain ⟨qa, hqa, hU⟩ := except_bind_ok hU
  obtain ⟨d1, hd1, hU⟩ := except_bind_ok hU
  obtain ⟨d, hd, hU⟩ := except_bind_ok hU
  obtain ⟨bits, hkeep, hU⟩ := except_bind_ok hU
  obtain ⟨⟨M, sel⟩, hwh, hU⟩ := except_bind_ok hU
  obtain ⟨ix, hix, hU⟩ := except_bind_ok hU
  obtain ⟨yk, hgk, hU⟩ := except_bind_ok hU
  obtain ⟨yv, hgv, hU⟩ := except_bind_ok hU
  obtain ⟨RU, hran1, hU⟩ := except_bind_ok hU
  obtain ⟨RR, hran2, hU⟩ := except_bind_ok hU
  obtain ⟨V, hdiff, hU⟩ := except_bind_ok hU
  obtain ⟨WC, hran3, hU⟩ := except_bind_ok hU
  obtain ⟨Cr, hCr, hU⟩ := except_bind_ok hU
  have hcr' : Tab.cross V.key WC.key = .ok Cr := hCr
  unfold Tab.cross at hCr
  obtain ⟨⟨Tv, x', y'⟩, hcr, -⟩ := except_bind_ok hCr
  have hQN : Q.n.toNat ≤ 2 ^ 63 := by have := catRows_ok hcat; omega
  obtain ⟨hpre, hpost, zA, hzA, hscA⟩ := hTot.comp Q hone
  obtain ⟨rrA, hsA⟩ := hscA es vs p k g f hes hka hks
  obtain ⟨⟨zB, hzB, hscB⟩, hknB⟩ := hTot.cat Z bs bv bp hbs hka2
  obtain ⟨rrB, hsB⟩ := hscB bs bv bp bk bg bf hbs hka2 hks2
  have hcO := hT.catOff
  have eR : r'.regs = r'.n :: (Cols.regs r'.key ++ Cols.regs r'.val) := by simp [TabB.regs, Cols.regs_append]
  have eB : ub.regs = ub.n :: (Cols.regs ub.key ++ Cols.regs ub.val) := by simp [TabB.regs, Cols.regs_append]
  have eC : uc.regs = uc.n :: (Cols.regs uc.key ++ Cols.regs uc.val) := by simp [TabB.regs, Cols.regs_append]
  obtain ⟨hrn, gR⟩ := mapM_get_cons (eR ▸ hR)
  obtain ⟨-, gRv⟩ := mapM_split (ColsOf.regs_length hRk r.key) gR
  obtain ⟨hubn, gB⟩ := mapM_get_cons (eB ▸ hB)
  obtain ⟨-, gBv⟩ := mapM_split (ColsOf.regs_length (A := B) (ColsOf.shape B hRv hTot.shapeB.symm) UB.key) gB
  obtain ⟨hucn, gC⟩ := mapM_get_cons (eC ▸ hC)
  obtain ⟨-, gCv⟩ := mapM_split (ColsOf.regs_length (A := C) (ColsOf.shape C hSv hTot.shapeC.symm) UC.key) gC
  rw [ldivOfB_cps]
  refine ldivA_builds (r := r) (s := s) (r' := r') (s' := s') (fg := fg) (rs := rs) (out := out) hcO h63 (Q := Q) rfl hRk hRv hSk hSv hR hS hone hpre hpost hes hka hks hQN hzA hsA hseg h1 hgf hfo
    (kk := fun W K _ f p cnt => ldivR1 r' s' ub uc kk W K f p cnt) ?_
  intro fg2 W R a b c d e he hf ho hex hWk hWc hshK hshC hWn hWx hr5
  unfold ldivR1
  have hxr : ValsB.regVals (show Vals (.prod B C) Q.n from (Q.key, (Q.val : Vals A Q.n × Vals C Q.n).2)) =
      Q.key.regVals ++ (Q.val : Vals A Q.n × Vals C Q.n).2.regVals := by simp [ValsB.regVals]
  rw [Cols.regs_append, hxr] at hWx
  obtain ⟨hy, hz2⟩ := mapM_split (ColsOf.regs_length hWk Q.key) hWx
  refine ldivCat_builds hcO h63 (B := B) (n1 := r.n) (n2 := Q.n) (N := N) (X := r.val) (Y := Q.key) (Z := Z)
    (cx := r'.val) (cy := W.key) (a1 := r'.n) (a2 := W.n) (fg := fg2) (rs := R) hRv hWk (hex hrn) hWn
    (mapM_extends hex gRv) hy hcat hlt hconc hbs hka2 hks2 hzB hsB hseg2 hknB hcm hgf2 hsca ho
    (kk := fun N bk _ _ _ cR code => ldivR2 r' s' ub uc kk W a c d e N bk cR code) ?_
  intro fg3 R2 a' b' c' d' e' f' g' he3 hf3 ho3 hex3 hr3
  unfold ldivR2
  obtain ⟨hKa, hr5⟩ := mapM_get_cons hr5
  obtain ⟨-, hr5⟩ := mapM_get_cons hr5
  obtain ⟨hFc, hr5⟩ := mapM_get_cons hr5
  obtain ⟨hPd, hr5⟩ := mapM_get_cons hr5
  obtain ⟨hCe, -⟩ := mapM_get_cons hr5
  obtain ⟨hNa, hr3⟩ := mapM_get_cons hr3
  obtain ⟨hBb, hr3⟩ := mapM_get_cons hr3
  obtain ⟨-, hr3⟩ := mapM_get_cons hr3
  obtain ⟨-, hr3⟩ := mapM_get_cons hr3
  obtain ⟨-, hr3⟩ := mapM_get_cons hr3
  obtain ⟨hCRf, hr3⟩ := mapM_get_cons hr3
  obtain ⟨hCodeg, -⟩ := mapM_get_cons hr3
  obtain ⟨kc, hkc, o, ho'⟩ := hTot.addC _ _ _ _ _ hq
  refine ldivSel_builds (B := B) (C := C) (Kv := k.toUSize) (Qn := Q.n) (n1 := r.n) (Nv := N) (bkv := bk.toUSize)
    (Mv := M) (Qk := Q.key) (Qc := (Q.val : Vals A Q.n × Vals C Q.n).2) (yk := yk) (yv := yv) (cs1 := W.key)
    (cs2 := W.val.drop s'.key.length) (fg := fg3) (rs := R2) (rK := a) (rF := c) (rP := d) (rcnt := e) (rN := a')
    (rBk := b') (rCode := g') (rCR := f') (rQn := W.n) (a1 := r'.n) hWk hWc (mapM_extends hex3 hy)
    (mapM_extends hex3 hz2) (hex3 hWn) (hex3 (hex hrn)) (hex3 hKa) (hex3 hFc) (hex3 hPd) (hex3 hCe) hNa hBb hCRf
    hCodeg hq ⟨kc, hkc, o, ho'⟩ hqa hd1 hd hkeep (hTot.whereC _ _ _ _ _ _ hkeep hwh) hix hgk hgv ho3
    (kk := ldivR3 r' ub uc kk) ?_
  intro fg4 P R3 he4 hf4 ho4 hex4 hPk hPv hPr
  unfold ldivR3
  have hE3 : Extends rs R3 := fun h => hex4 (hex3 (hex h))
  refine ldivTail_builds hT h63 (r := r) (UB := UB) (UC := UC) (RU := RU) (RR := RR) (V := V) (WC := WC) (Tv := Tv)
    (Mv := M) (x' := x') (y' := y') (yk := yk) (yv := yv) (U := U) (r' := r') (ub := ub) (uc := uc) (P := P)
    (fg := fg4) (rs := R3) hRv hbv hcv (ColsOf.shape B hWk hPk) (ColsOf.shape C hWc hPv) (mapM_extends hE3 gRv)
    (hE3 hrn) (mapM_extends hE3 gBv) (hE3 hubn) (mapM_extends hE3 gCv) (hE3 hucn) hPr hran1 hran2 hran3 hdiff hcr
    (hTot.hunion _ V WC Tv x' y' Cr U hcr hcr' hU) hTot.ranUB hTot.ranR hTot.ranUC (hTot.sel RU RR hran1 hran2)
    (hTot.cross V WC Tv x' y' hcr) (hTot.can _ V WC Tv x' y' hcr) ho4 ?_
  intro fg5 W' R5 he5 hf5 ho5 hex5 hsk hsv hr5'
  obtain ⟨ys, rfl⟩ := Extends.exists_app fun h => hex5 (hE3 h)
  exact hkk fg5 W' ys (FExt.trans (FExt.trans (FExt.trans he he3) he4) he5) (hf.trans (hf3.trans (hf4.trans hf5))) ho5
    (hsk.trans (hPk.trans (hshK.trans hTot.shapeB))) (hsv.trans (hPv.trans (hshC.trans hTot.shapeC))) hr5'

end Rel.Lang.Plan
