module

public import Rel.Lang.PlanSpecPrefix
public import Rel.Lang.PlanSpecConcat
public import Rel.Lang.PlanSpecGather
public import Rel.Lang.PlanSpecUnion
public import Rel.Lang.PlanSpecExpand

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `selectB` builds `Tab.select`; `interB`, `diffB` are its instances (PLAN-THM-E6)

`Tab.select keep R S` tags the concatenation of `R` and `S` by source, groups equal rows (`kasc ≫ kseen`), folds each
group's tags with `and` and `or` (`groupFold`), and keeps the groups `keep` passes (`whereCol`). `selectB kb R S` is
the same chain of plan builders. `keep` is abstract: `KeepSpec kp kb` says the builder `kb` builds what the table
function `kp` answers, and `inter`, `diff` are its instances at `colMap op` / `mapB op`. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- `whereB` grows (its `ite` branches grow, the rest are primitives). -/
theorem Grows.whereB (n keep : Nat) : Grows (Plan.whereB n keep) := by
  unfold Plan.whereB
  refine (Grows.lit _).bind fun _ => (Grows.constB _ _).bind fun _ => (Grows.scanB _ _ _ _ _).bind fun _ =>
    (Grows.nth _ _ _).bind fun _ => (Grows.nth _ _ _).bind fun _ => (Grows.lit _).bind fun _ =>
    (Grows.call1 _ _).bind fun _ => (Grows.ite ((Grows.lit _).bind fun _ => Grows.pure _)
      ((Grows.projB _ _ _ _).bind fun _ => Grows.pure _)).bind fun _ => (Grows.nth _ _ _).bind fun _ =>
    (Grows.call1 _ _).bind fun _ => (Grows.scanB _ _ _ _ _).bind fun _ => (Grows.nth _ _ _).bind fun _ =>
    (Grows.lit _).bind fun _ => (Grows.call1 _ _).bind fun _ => (Grows.lit _).bind fun _ => (Grows.lit _).bind fun _ =>
    (Grows.lit _).bind fun _ => (Grows.call1 _ _).bind fun _ => (Grows.lit _).bind fun _ => (Grows.constB _ _).bind
    fun _ => (Grows.lit _).bind fun _ => (Grows.constB _ _).bind fun _ => (Grows.scanB _ _ _ _ _).bind fun _ =>
    (Grows.nth _ _ _).bind fun _ => (Grows.call1 _ _).bind fun _ => Grows.pure _

/-- `whereB` types: the count and the positions it answers are registers above `m` when `n` and `keep` are. -/
theorem Typed.whereB {m n keep : Nat} (hn : m ≤ n) (hk : m ≤ keep) :
    Typed m (fun r : Nat × Nat => m ≤ r.1 ∧ m ≤ r.2) (Plan.whereB n keep) := by
  unfold Plan.whereB
  refine (Typed.lit _).bind fun u hu => Typed.constB.bind fun z hz =>
    (Typed.scanB hn (fun s hs => by cases hs; exact hz) (by intro a ha; simp at ha; omega)).bind fun ps hps =>
    (Typed.nth hps 0 "kscan").bind fun p hp => (Typed.nth hps 1 "kscan").bind fun fo hfo =>
    (Typed.lit _).bind fun s0 hs0 => (Typed.call1 (by simp; omega)).bind fun em hem =>
    (Typed.ite hem ((Typed.lit _).bind fun x hx => Typed.pure (by simp; omega))
      ((Typed.projB hfo 1 0 .u64).bind fun x hx => Typed.pure (by simp; omega))).bind fun ib hib =>
    (Typed.nth hib 0 "if").bind fun ib0 hib0 => (Typed.call1 (by simp; omega)).bind fun r hr =>
    (Typed.scanB hn (fun s hs => by cases hs) (by intro a ha; simp at ha; omega)).bind fun is hi =>
    (Typed.nth hi 0 "kscan").bind fun ix hix => (Typed.lit _).bind fun s1 hs1 =>
    (Typed.call1 (by simp; omega)).bind fun r1 hr1 => (Typed.lit _).bind fun l0 hl0 =>
    (Typed.lit _).bind fun l1 hl1 => (Typed.lit _).bind fun l2 hl2 =>
    (Typed.call1 (by simp; omega)).bind fun ix1 hix1 => (Typed.lit _).bind fun u2 hu2 =>
    Typed.constB.bind fun zr hzr => (Typed.lit _).bind fun u3 hu3 => Typed.constB.bind fun on hon =>
    (Typed.scanB hr (fun s hs => by cases hs; exact hzr) (by intro a ha; simp at ha; omega)).bind fun cs hcs =>
    (Typed.nth hcs 0 "kscan").bind fun cut hcut => (Typed.call1 (by simp; omega)).bind fun w hw =>
    Typed.pure ⟨hr, hw⟩


/-- `ite` reads nothing of the block it is built after: its branches are blocks of their own, started empty. -/
theorem Free.ite (c : Nat) (t e : Bld (Array Nat)) : Free (Plan.ite c t e) := by
  intro is n fg r is' n' fg' h
  unfold Plan.ite Plan.block at h ⊢
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, bind_assoc] at h ⊢
  cases ht : StateT.run t (#[], n, fg) with
  | error x => simp [ht, liftM, monadLift, MonadLift.monadLift, Bind.bind, Except.bind] at h
  | ok pt =>
    obtain ⟨rt, it, nt, fgt⟩ := pt
    cases he : StateT.run e (#[], n, fgt) with
    | error x => simp [ht, he, liftM, monadLift, MonadLift.monadLift, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    | ok pe =>
      obtain ⟨re, ie, ne, fge⟩ := pe
      simp [ht, he, liftM, monadLift, MonadLift.monadLift, Pure.pure, Except.pure, Bind.bind, Except.bind] at h ⊢
      by_cases hs : rt.size = re.size
      · rw [if_pos hs] at h ⊢
        exact (Free.emit _ _) _ _ _ _ _ _ _ h
      · rw [if_neg hs] at h ⊢
        exact (Free.bind (Free.throw _) fun _ => Free.emit _ _) _ _ _ _ _ _ _ h

/-- `free` with `ite`; `with_reducible` so that a primitive is not tried against a builder by unfolding both. -/
macro "free'" : tactic => `(tactic| repeat (first
    | with_reducible apply Free.ite
    | with_reducible apply Free.bind
    | with_reducible apply Free.pure
    | with_reducible apply Free.lit
    | with_reducible apply Free.ctorB
    | with_reducible apply Free.nth
    | with_reducible apply Free.callK
    | with_reducible apply Free.call1
    | with_reducible apply Free.listB
    | with_reducible apply Free.emit1
    | with_reducible apply Free.emit
    | intro _))

set_option maxRecDepth 8000 in
theorem Free.whereB (n keep : Nat) : Free (Plan.whereB n keep) := by
  unfold Plan.whereB Plan.constB Plan.scanB Plan.projB Plan.srcB
  simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind]
  free'

theorem Free.wordsB (n : Nat) (w : UInt64) : Free (Plan.wordsB n w) := by
  unfold Plan.wordsB Plan.constB; free'

/-- The body of `selectB`'s plan function (`funT [R, S]`): the registers of the two tables are its parameters. -/
def selBody (kb : Nat → Nat → Nat → Bld Nat) (R S : TabB) : Bld TabB := do
  let (n, off) ← catB R.n S.n
  let tag ← scatterB .last S.n off (← wordsB S.n 1) n
  let ks ← concatB n R.n S.n off R.key S.key
  let vs ← concatB n R.n S.n off R.val S.val
  let (m, g, f, p) ← ascSeenB n (ks ++ vs)
  let ts ← gatherB n p n tag
  let mn ← groupFoldB .and n g f m 1 ts
  let mx ← groupFoldB .or n g f m 0 ts
  let (k, sel) ← whereB m (← kb m mn mx)
  let ix ← gatherB k (← gatherB k sel m f) n p
  pure ⟨k, ← gatherCols k ix n ks, ← gatherCols k ix n vs⟩

/-- `selectB` is `funT` of its body. -/
theorem selectB_eq (kb : Nat → Nat → Nat → Bld Nat) (R S : TabB) :
    selectB kb R S = funT [R, S] (fun | [R, S] => selBody kb R S | _ => throw "select: not two tables") := rfl

theorem Grows.selBody {kb : Nat → Nat → Nat → Bld Nat} (hk : ∀ m mn mx, Grows (kb m mn mx)) (R S : TabB) :
    Grows (Plan.selBody kb R S) := by
  unfold Plan.selBody
  refine (Grows.catB _ _).bind fun p => ?_
  obtain ⟨n, off⟩ := p
  refine (Grows.wordsB _ _).bind fun _ => (Grows.scatterB _ _ _ _ _ _).bind fun _ =>
    (Grows.concatB (Col.sizes R.key + 1) _ _ _ _ _ _ (Nat.lt_succ_self _)).bind fun _ =>
    (Grows.concatB (Col.sizes R.val + 1) _ _ _ _ _ _ (Nat.lt_succ_self _)).bind fun _ =>
    (Grows.ascSeenB _ _).bind fun q => ?_
  obtain ⟨m, g, f, p⟩ := q
  refine (Grows.gatherB _ _ _ _).bind fun _ => (Grows.groupFoldB _ _ _ _ _ _ _).bind fun _ =>
    (Grows.groupFoldB _ _ _ _ _ _ _).bind fun _ => (hk _ _ _).bind fun _ => (Grows.whereB _ _).bind fun q => ?_
  obtain ⟨k, sel⟩ := q
  exact (Grows.gatherB _ _ _ _).bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ =>
    (Grows.gatherCols _ _ _ _).bind fun _ => (Grows.gatherCols _ _ _ _).bind fun _ => Grows.pure _

theorem Typed.selBody {m : Nat} {kb : Nat → Nat → Nat → Bld Nat}
    (hkb : ∀ a b c, m ≤ a → m ≤ b → m ≤ c → Typed m (fun r => m ≤ r) (kb a b c)) {R S : TabB}
    (hR : AllGe m R.regs) (hS : AllGe m S.regs) : Typed m (fun U => AllGe m U.regs) (Plan.selBody kb R S) := by
  have hRn : m ≤ R.n := hR _ (by simp [TabB.regs])
  have hSn : m ≤ S.n := hS _ (by simp [TabB.regs])
  have hRk : AllGe m (Cols.regs R.key) := fun a ha => hR a (by simp [TabB.regs, Cols.regs_append, ha])
  have hRv : AllGe m (Cols.regs R.val) := fun a ha => hR a (by simp [TabB.regs, Cols.regs_append, ha])
  have hSk : AllGe m (Cols.regs S.key) := fun a ha => hS a (by simp [TabB.regs, Cols.regs_append, ha])
  have hSv : AllGe m (Cols.regs S.val) := fun a ha => hS a (by simp [TabB.regs, Cols.regs_append, ha])
  unfold Plan.selBody
  refine (Typed.catB hRn hSn).bind fun p hp => ?_
  obtain ⟨n, off⟩ := p
  obtain ⟨hn, hoff⟩ := hp
  dsimp only at hn hoff ⊢
  refine Typed.wordsB.bind fun w hw => Typed.scatterB.bind fun tag htag => ?_
  refine ((Typed.concatBOf (S := []) (Col.sizes R.key + 1) n R.n S.n off R.key S.key (Nat.lt_succ_self _) (.inl hn) hRn
    hSn hRk hSk).mono fun r h a ha => (h a ha).resolve_right (by simp)).bind fun ks hks => ?_
  refine ((Typed.concatBOf (S := []) (Col.sizes R.val + 1) n R.n S.n off R.val S.val (Nat.lt_succ_self _) (.inl hn) hRn
    hSn hRv hSv).mono fun r h a ha => (h a ha).resolve_right (by simp)).bind fun vs hvs => ?_
  have hkv : AllGe m (Cols.regs (ks ++ vs)) := by
    intro a ha; rw [Cols.regs_append] at ha; rcases List.mem_append.1 ha with ha | ha
    · exact hks a ha
    · exact hvs a ha
  refine (Typed.ascSeenB (ks ++ vs) hn hkv).bind fun q hq => ?_
  obtain ⟨mm, g, f, p⟩ := q
  obtain ⟨hm, hg, hf, hp⟩ := hq
  dsimp only at hm hg hf hp ⊢
  refine Typed.gatherB.bind fun ts hts => (Typed.groupFoldB hn hg hm hts).bind fun mn hmn =>
    (Typed.groupFoldB hn hg hm hts).bind fun mx hmx => (hkb _ _ _ hm hmn hmx).bind fun bits hbits =>
    (Typed.whereB hm hbits).bind fun q hq => ?_
  obtain ⟨k, sel⟩ := q
  obtain ⟨hk, hsel⟩ := hq
  dsimp only at hk hsel ⊢
  refine Typed.gatherB.bind fun i0 hi0 => Typed.gatherB.bind fun ix hix =>
    (Typed.gatherCols hk n ks hn hks).bind fun ks' hks' => (Typed.gatherCols hk n vs hn hvs).bind fun vs' hvs' =>
    Typed.pure ?_
  intro a ha
  simp only [TabB.regs, Cols.regs_append, List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | ha | ha
  · exact hk
  · exact hks' a ha
  · exact hvs' a ha


/-- The kernel answers `selectB`'s tag column rests on: `catB`'s offsets (`CatOff`'s) and that they are `shiftCol`'s
    column, the one `Tab.tagged` scatters through (two kernel calls of one word per row, `colMap_const_eq`). -/
def TagOff : Prop := ∀ a b : USize, a.toNat + b.toNat < 2 ^ 63 → ∃ zc oc f,
  kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) b a.toUInt64 = .ok zc ∧
    kscan .add false .i64 .i64 b none [(b, .pos), (b, zc)] [] [] = .ok (oc, f) ∧ shiftCol b a.toUInt64 = .ok oc

theorem TagOff.catOff (h : TagOff) : CatOff := fun a b hab => by
  obtain ⟨zc, oc, f, h1, h2, -⟩ := h a b hab
  exact ⟨zc, oc, f, h1, h2⟩

/-- `kb` builds what the table function `kp` answers: its builder grows, reads nothing of its block (`Free`, so that
    the registers it answers are fixed before the block is), is typed at every `m`, and where `kp` answers `bits` for
    the columns `mn`, `mx` its register holds `bits`. -/
def KeepSpec (kp : USize → Enc → Enc → Except String Enc) (kb : Nat → Nat → Nat → Bld Nat) : Prop :=
  (∀ m mn mx, Grows (kb m mn mx)) ∧ (∀ m mn mx, Free (kb m mn mx)) ∧
  (∀ lv m mn mx, lv ≤ m → lv ≤ mn → lv ≤ mx → Typed lv (fun r => lv ≤ r) (kb m mn mx)) ∧
  ∀ {fg : Array Fun × Array Fun} {rs : Array Val} {m mn mx : Nat} {mv : USize} {mnc mxc bits : Enc},
    rs[m]? = some (.size mv) → rs[mn]? = some (Reg.put mnc) → rs[mx]? = some (Reg.put mxc) → kp mv mnc mxc = .ok bits →
    Builds abiOf fg fg (do let r ← kb m mn mx; Pure.pure #[r]) rs #[Reg.put bits]

/-- `mapB op` over registers chosen from `mn`, `mx` by `ra`, `rb` builds `colMap op` over the columns `ea`, `eb` chosen
    the same way: the keep-builder of every `Tab.select` whose `keep` is one `kscan` map of the two folded masks. -/
theorem keepSpec_map (op : Kernel.Op) (hop : (Reg.get? (Reg.put op) : Option Kernel.Op) = some op) (ra rb : Nat → Nat → Nat) (ea eb : Enc → Enc → Enc)
    (hga : ∀ lv mn mx, lv ≤ mn → lv ≤ mx → lv ≤ ra mn mx) (hgb : ∀ lv mn mx, lv ≤ mn → lv ≤ mx → lv ≤ rb mn mx)
    (hra : ∀ {rs : Array Val} {mn mx : Nat} {mnc mxc : Enc}, rs[mn]? = some (Reg.put mnc) → rs[mx]? = some (Reg.put mxc) →
      rs[ra mn mx]? = some (Reg.put (ea mnc mxc)))
    (hrb : ∀ {rs : Array Val} {mn mx : Nat} {mnc mxc : Enc}, rs[mn]? = some (Reg.put mnc) → rs[mx]? = some (Reg.put mxc) →
      rs[rb mn mx]? = some (Reg.put (eb mnc mxc))) :
    KeepSpec (fun m mn mx => colMap op m (ea mn mx) (eb mn mx)) (fun m mn mx => mapB op m (ra mn mx) (rb mn mx)) :=
  ⟨fun _ _ _ => Grows.mapB _ _ _ _ _ _ _ _, fun _ _ _ => Free.mapB _ _ _ _ _ _ _ _,
    fun lv m mn mx h1 h2 h3 => Typed.mapB h1 (hga lv mn mx h2 h3) (hgb lv mn mx h2 h3),
    fun {fg rs m mn mx mv mnc mxc bits} hm hmn hmx hk => by
      obtain ⟨r, hr, hr1⟩ := except_bind_ok hk
      obtain rfl : r.1 = bits := by cases hr1; rfl
      exact mapB_builds hm (hra hmn hmx) (enc_get_put _) (hrb hmn hmx) (enc_get_put _) hop (reg_ty _) (reg_ty _)
        reg_nil reg_nil hr⟩

/-- `interB`'s keep-builder builds `Tab.inter`'s `keep` (`colMap .lt` of the `and` and `or` masks). -/
theorem keepSpec_inter : KeepSpec (fun m mn mx => colMap .lt m mn mx) (fun m mn mx => mapB .lt m mn mx) :=
  keepSpec_map .lt (by with_unfolding_all rfl) (fun a _ => a) (fun _ b => b) (fun a _ => a) (fun _ b => b)
    (fun _ _ _ h _ => h) (fun _ _ _ _ h => h) (fun h _ => h) (fun _ h => h)

/-- `diffB`'s keep-builder builds `Tab.diff`'s `keep` (`colMap .not` of the `or` mask). -/
theorem keepSpec_diff : KeepSpec (fun m _ mx => colMap .not m mx mx) (fun m _ mx => mapB .not m mx mx) :=
  keepSpec_map .not (by with_unfolding_all rfl) (fun _ b => b) (fun _ b => b) (fun _ b => b) (fun _ b => b)
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ h => h) (fun _ h => h)

/-- `whereB`'s kernel calls over the mask `kc` of `nv` rows answer the count `K` and the positions `w`, which `whereCol`
    answers by other calls (`.sub` and `kscatter` at `pos`, not `.mul` and a cut): the one place `Tab.select`'s model and
    its plan part ways. Asked of the masks `keep` answers only (`selectB_builds`' `hW`). -/
def WhereAgree (nv K : USize) (kc w : Enc) : Prop := ∃ (zc pc ixc ix1c zrc onec cutc : Enc) (fo ixf cutf : Option UInt64)
    (f : UInt64), kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok zc ∧
    kscan .add false .i64 .i64 nv (some zc) [(nv, zc), (nv, kc)] [] [] = .ok (pc, fo) ∧ (nv ≠ 0 → fo = some f) ∧
    (if nv = 0 then (0 : UInt64) else f).toUSize = K ∧
    kscan .mul false .i64 .i64 nv none [(nv, kc), (nv, pc)] [] [] = .ok (ixc, ixf) ∧
    kscatter .last nv ixc .pos (K + 1) 0 = .ok ix1c ∧ kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) K 0 = .ok zrc ∧
    kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) K 1 = .ok onec ∧
    kscan .add false .i64 .i64 K (some zrc) [(K, zrc), (K, onec)] [] [] = .ok (cutc, cutf) ∧
    kgather K cutc (K + 1) ix1c = .ok w ∧
    ∀ e ∈ [zc, pc, ixc, ix1c, zrc, onec, cutc, .pos], (Reg.get? (Reg.put e) : Option Enc) = some e

theorem FExt.trans {x y z : Array Fun} (h1 : ∃ e, y = x ++ e) (h2 : ∃ e, z = y ++ e) : ∃ e, z = x ++ e := by
  obtain ⟨e1, rfl⟩ := h1; obtain ⟨e2, rfl⟩ := h2; exact ⟨e1 ++ e2, by rw [Array.append_assoc]⟩

/-- **`selBody` builds `Tab.select`** (`kk` continues with a table of `R`'s shape whose registers hold the answer). -/
theorem selBody_builds {a b : Obj} {Rv Sv T' : Tab a b} {kp : USize → Enc → Enc → Except String Enc}
    {kb : Nat → Nat → Nat → Bld Nat} {R S : TabB} {fg : Array Fun × Array Fun} {rs : Array Val}
    {kk : TabB → Bld (Array Nat)} {out : Array Val} (hT : TagOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63)
    (hK : KeepSpec kp kb) (hRk : ColsOf a R.key) (hRv : ColsOf b R.val) (hSk : ColsOf a S.key) (hSv : ColsOf b S.val)
    (hR : R.regs.mapM (fun i => rs[i]?) = some (.size Rv.n :: (Rv.key.regVals ++ Rv.val.regVals)))
    (hS : S.regs.mapM (fun i => rs[i]?) = some (.size Sv.n :: (Sv.key.regVals ++ Sv.val.regVals)))
    (hsel : Tab.select kp Rv Sv = .ok T') (hlt : Rv.n.toNat + Sv.n.toNat < 2 ^ 63)
    (hz : ∀ C tag, Rv.tagged Sv = .ok (C, tag) → ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) C.n 0 = .ok z)
    (hsc : ∀ C tag es vs p k g f z, Rv.tagged Sv = .ok (C, tag) →
      kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) C.n 0 = .ok z →
      ValsB.cols (A := .prod a b) (C.key, C.val) = .ok es → kasc C.n es = .ok (vs, p) →
      kseen C.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 C.n (some z) [(C.n, z), (C.n, g)] [] [] = .ok r)
    (hW : ∀ m mn mx bits K sel, kp m mn mx = .ok bits → whereCol m bits = .ok (K, sel) → WhereAgree m K bits sel)
    (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (U : TabB) (Rn : Array Val), Extends rs Rn → (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Cols.shape U.key = Cols.shape R.key → Cols.shape U.val = Cols.shape R.val →
      U.regs.mapM (fun i => Rn[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk U) Rn out) :
    ∃ fg', Builds abiOf fg fg' (Plan.selBody kb R S >>= kk) rs out := by
  have hsel' := hsel
  unfold Tab.select at hsel'
  obtain ⟨⟨C, tag⟩, hct, h⟩ := except_bind_ok hsel'
  dsimp only at h
  obtain ⟨es, hes, h⟩ := except_bind_ok h
  obtain ⟨⟨vs, p⟩, hka, h⟩ := except_bind_ok h
  obtain ⟨⟨m, g, f⟩, hks, h⟩ := except_bind_ok h
  obtain ⟨ts, hts, h⟩ := except_bind_ok h
  obtain ⟨seg, hseg, h⟩ := except_bind_ok h
  obtain ⟨mn, hmn, h⟩ := except_bind_ok h
  obtain ⟨mx, hmx, h⟩ := except_bind_ok h
  obtain ⟨bits, hbits, h⟩ := except_bind_ok h
  obtain ⟨⟨K, sel⟩, hwh, h⟩ := except_bind_ok h
  dsimp only at h
  obtain ⟨ix1, hix1, h⟩ := except_bind_ok h
  obtain ⟨ix, hix, hfin⟩ := except_bind_ok h
  have hct' := hct
  unfold Tab.tagged at hct'
  obtain ⟨nn, hnn, hct'⟩ := except_bind_ok hct'
  obtain ⟨ck, hck, hct'⟩ := except_bind_ok hct'
  obtain ⟨cv, hcv, hct'⟩ := except_bind_ok hct'
  obtain ⟨sh, hsh, hct'⟩ := except_bind_ok hct'
  obtain ⟨one, hone, hct'⟩ := except_bind_ok hct'
  obtain ⟨tg, htg, hct'⟩ := except_bind_ok hct'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hct')
  have hRe : R.regs = R.n :: (Cols.regs R.key ++ Cols.regs R.val) := by simp [TabB.regs, Cols.regs_append]
  have hSe : S.regs = S.n :: (Cols.regs S.key ++ Cols.regs S.val) := by simp [TabB.regs, Cols.regs_append]
  rw [hRe] at hR
  rw [hSe] at hS
  obtain ⟨hRn, hR⟩ := mapM_get_cons hR
  obtain ⟨hSn, hS⟩ := mapM_get_cons hS
  obtain ⟨hRk', hRv'⟩ := mapM_split (ColsOf.regs_length hRk Rv.key) hR
  obtain ⟨hSk', hSv'⟩ := mapM_split (ColsOf.regs_length hSk Sv.key) hS
  obtain ⟨zc, oc, f0, hzc, hoc, hshift⟩ := hT Rv.n Sv.n hlt
  obtain rfl : sh = oc := Except.ok.inj (hsh.symm.trans hshift)
  obtain ⟨zz, hzz⟩ := hz _ _ hct
  obtain ⟨hKA, hKF, hKT, hKB⟩ := hK
  have hone' : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) Sv.n 1 = .ok one := by rwa [← colConst_eq]
  have hN : nn.toNat < 2 ^ 63 := by rw [catRows_ok hnn]; exact hlt
  simp only [Plan.selBody, bind_assoc, pure_bind]
  refine Builds.bind2F (Free.catB _ _) (catB_builds hRn hSn hnn hzc hoc) fun r1 r2 R1 hr1 hr2 hE1 => ?_
  dsimp only
  refine Builds.bind1F (Free.wordsB _ _) (wordsB_builds (hE1 hSn) hone') fun w R2 hw hE2 => ?_
  refine Builds.bind1F (Free.scatterB _ _ _ _ _ _) (scatterB_builds (hE2 (hE1 hSn)) (hE2 hr2) hw (hE2 hr1) rfl htg)
    fun tgr R3 htr hE3 => ?_
  have hE3' : Extends rs R3 := fun h => hE3 (hE2 (hE1 h))
  have hn3 : R3[r1]? = some (.size nn) := hE3 (hE2 hr1)
  refine concatB_builds hT.catOff h63 a (x := Rv.key) (y := Sv.key) (z := ck) hRk hSk (mapM_extends hE3' hRk')
    (mapM_extends hE3' hSk') hn3 (hE3' hRn) (hE3' hSn) hck hfo ?_
  intro fg2 ks' ys he hf ho hs hr
  have hA0 : Extends rs (R3 ++ ys) := fun h => get_app (hE3' h)
  refine concatB_builds hT.catOff h63 b (x := Rv.val) (y := Sv.val) (z := cv) hRv hSv (mapM_extends hA0 hRv')
    (mapM_extends hA0 hSv') (get_app hn3) (hA0 hRn) (hA0 hSn) hcv ho ?_
  intro fg3 vs' ys2 he3 hf3 ho3 hs3 hr3
  have hcs : ColsOf (.prod a b) (ks' ++ vs') := ⟨ks', vs', rfl, ColsOf.shape a hRk hs, ColsOf.shape b hRv hs3⟩
  let X : ValsB false (.prod a b) nn := (ck, cv)
  have hx : (Cols.regs (ks' ++ vs')).mapM (fun i => ((R3 ++ ys) ++ ys2)[i]?) =
      some X.regVals := by
    rw [Cols.regs_append, List.mapM_append, mapM_get_app hr, hr3]; rfl
  obtain ⟨rr, hrr⟩ := hsc _ _ es vs p m g f zz hct hzz hes hka hks
  refine ascSeenB_builds (A := .prod a b) (x := X) (cs := ks' ++ vs') (L := Cols.regs (ks' ++ vs')) (n := r1) hcs
    (regsOf_eq _) hx (get_app (get_app hn3)) hes (Nat.le_of_lt hN) hka hks hzz hrr ho3 ?_
  intro fg4 ys3 ra rb rc rd he4 hg4 ho4 hq
  obtain ⟨hm4, hq⟩ := mapM_get_cons hq
  obtain ⟨hg4', hq⟩ := mapM_get_cons hq
  obtain ⟨hf4, hq⟩ := mapM_get_cons hq
  obtain ⟨hp4, -⟩ := mapM_get_cons hq
  have hn4 : (((R3 ++ ys) ++ ys2) ++ ys3)[r1]? = some (.size nn) := get_app (get_app (get_app hn3))
  have ht4 : (((R3 ++ ys) ++ ys2) ++ ys3)[tgr]? = some (Reg.put tg) := get_app (get_app (get_app htr))
  have hE4 : Extends rs (((R3 ++ ys) ++ ys2) ++ ys3) := fun h => get_app (get_app (get_app (hE3' h)))
  have hk4 : (Cols.regs ks').mapM (fun i => (((R3 ++ ys) ++ ys2) ++ ys3)[i]?) = some ck.regVals :=
    mapM_get_app (mapM_get_app hr)
  have hv4 : (Cols.regs vs').mapM (fun i => (((R3 ++ ys) ++ ys2) ++ ys3)[i]?) = some cv.regVals := mapM_get_app hr3
  generalize ((R3 ++ ys) ++ ys2) ++ ys3 = R4 at hm4 hg4' hf4 hp4 hn4 ht4 hE4 hk4 hv4
  have hfe4 : ∃ e, fg4.1 = fg.1 ++ e := FExt.trans (FExt.trans he he3) he4
  have hfg4 : GExt fg.2 fg4.2 := (hf.trans hf3).trans (by rw [hg4]; exact GExt.refl _)
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hn4 hp4 hn4 ht4 hts) fun tsr R5 hts5 hE5 => ?_
  refine groupFoldB_builds (n := r1) (g := rb) (f := rc) (m := ra) (x := tsr) rfl (hE5 hn4) (hE5 hg4') (hE5 hf4)
    (hE5 hm4) hts5 hseg hmn ho4 ?_
  intro fg5 mnr ys5 he5 hf5 ho5 hmn5
  refine groupFoldB_builds (n := r1) (g := rb) (f := rc) (m := ra) (x := tsr) rfl (get_app (hE5 hn4))
    (get_app (hE5 hg4')) (get_app (hE5 hf4)) (get_app (hE5 hm4)) (get_app hts5) hseg hmx ho5 ?_
  intro fg6 mxr ys6 he6 hf6 ho6 hmx6
  have hfe6 : ∃ e, fg6.1 = fg.1 ++ e := FExt.trans (FExt.trans hfe4 he5) he6
  have hfg6 : GExt fg.2 fg6.2 := (hfg4.trans hf5).trans hf6
  have hn7 : ((R5 ++ ys5) ++ ys6)[r1]? = some (.size nn) := get_app (get_app (hE5 hn4))
  have hm7 : ((R5 ++ ys5) ++ ys6)[ra]? = some (.size m.toUSize) := get_app (get_app (hE5 hm4))
  have hf7 : ((R5 ++ ys5) ++ ys6)[rc]? = some (Reg.put f) := get_app (get_app (hE5 hf4))
  have hp7 : ((R5 ++ ys5) ++ ys6)[rd]? = some (Reg.put p) := get_app (get_app (hE5 hp4))
  have hmn7 : ((R5 ++ ys5) ++ ys6)[mnr]? = some (Reg.put mn) := get_app hmn5
  have hmx7 : ((R5 ++ ys5) ++ ys6)[mxr]? = some (Reg.put mx) := hmx6
  have hE7 : Extends rs ((R5 ++ ys5) ++ ys6) := fun h => get_app (get_app (hE5 (hE4 h)))
  have hk7 : (Cols.regs ks').mapM (fun i => ((R5 ++ ys5) ++ ys6)[i]?) = some ck.regVals :=
    mapM_get_app (mapM_get_app (mapM_extends hE5 hk4))
  have hv7 : (Cols.regs vs').mapM (fun i => ((R5 ++ ys5) ++ ys6)[i]?) = some cv.regVals :=
    mapM_get_app (mapM_get_app (mapM_extends hE5 hv4))
  generalize (R5 ++ ys5) ++ ys6 = R7 at hn7 hm7 hf7 hp7 hmn7 hmx7 hE7 hk7 hv7
  obtain ⟨y1, y2, hy1, hy2, hT'⟩ : ∃ y1 y2, ValsB.gather K ix ck = .ok y1 ∧ ValsB.gather K ix cv = .ok y2 ∧
      (⟨K, y1, y2⟩ : Tab a b) = T' := by
    dsimp only at hfin
    simp only [ValsB.gather] at hfin
    cases h1 : ValsB.gather K ix ck with
    | error e => rw [h1] at hfin; cases hfin
    | ok y1 =>
      cases h2 : ValsB.gather K ix cv with
      | error e => rw [h1, h2] at hfin; cases hfin
      | ok y2 =>
        rw [h1, h2] at hfin
        exact ⟨y1, y2, rfl, rfl, Except.ok.inj hfin⟩
  subst hT'
  refine Builds.bind1F (hKF _ _ _) (hKB hm7 hmn7 hmx7 hbits) fun bt R8 hbt hE8 => ?_
  obtain ⟨zc2, pc, ixc, ix1c, zrc, onec, cutc, fo, ixf, cutf, f1, hz2, hp2, hf2, hK2, hix2, hs2, hzr, hone2, hcut, hg2,
    hrt⟩ := hW _ mn mx bits K sel hbits hwh
  refine Builds.bind2F (Free.whereB _ _) (whereB_builds (hE8 hm7) (by simp [hbt, enc_get_put]) hz2 hp2 hf2 hK2 hix2
    hs2 hzr hone2 hcut hg2 hrt) fun kr sr R9 hk9 hsr9 hE9 => ?_
  dsimp only
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 hk9 hsr9 (hE9 (hE8 hm7)) (hE9 (hE8 hf7)) hix1)
    fun i1 R10 hi1 hE10 => ?_
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 (hE10 hk9) hi1 (hE10 (hE9 (hE8 hn7)))
    (hE10 (hE9 (hE8 hp7))) hix) fun i2 R11 hi2 hE11 => ?_
  have hE11' : Extends R7 R11 := fun h => hE11 (hE10 (hE9 (hE8 h)))
  refine gatherCols_builds a (x := ck) (y := y1) (ColsOf.shape a hRk hs) (mapM_extends hE11' hk7) (hE11 (hE10 hk9))
    hi2 (hE11' hn7) hy1 ho6 ?_
  intro fg7 ks'' ys7 he7 hf7' ho7 hs7 hr7
  refine gatherCols_builds b (x := cv) (y := y2) (ColsOf.shape b hRv hs3) (mapM_get_app (mapM_extends hE11' hv7))
    (get_app (hE11 (hE10 hk9))) (get_app hi2) (get_app (hE11' hn7)) hy2 ho7 ?_
  intro fg8 vs'' ys8 he8 hf8 ho8 hs8 hr8
  refine hkk fg8 ⟨kr, ks'', vs''⟩ ((R11 ++ ys7) ++ ys8) (fun h => get_app (get_app (hE11' (hE7 h))))
    (FExt.trans (FExt.trans hfe6 he7) he8) ((hfg6.trans hf7').trans hf8) ho8 (hs7.trans hs) (hs8.trans hs3) ?_
  simp only [TabB.regs, Cols.regs_append]
  refine omapM_cons.mpr ⟨_, _, get_app (get_app (hE11 (hE10 hk9))), ?_, rfl⟩
  rw [List.mapM_append, mapM_get_app hr7, hr8]
  rfl


/-- **`selectB` builds `Tab.select`**: the tables `R'`, `S'` hold `R`, `S` in `rs`, `Tab.select kp R S = T'`; `kk`
    continues with a table of `R'`'s shape whose registers hold `T'`. The kernel facts are `selBody_builds`'. -/
def SelectSpec (A B : Obj) (kp : USize → Enc → Enc → Except String Enc) (kb : Nat → Nat → Nat → Bld Nat) : Prop :=
  ∀ {R S T' : Tab A B} {R' S' : TabB} {fg : Array Fun × Array Fun} {rs : Array Val}
    {kk : TabB → Bld (Array Nat)} {out : Array Val}, ColsOf A R'.key → ColsOf B R'.val → ColsOf A S'.key →
    ColsOf B S'.val → R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
    S'.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
    Tab.select kp R S = .ok T' → R.n.toNat + S.n.toNat < 2 ^ 63 →
    (∀ C tag, R.tagged S = .ok (C, tag) → ∃ z, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) C.n 0 = .ok z) →
    (∀ C tag es vs p k g f z, R.tagged S = .ok (C, tag) →
      kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) C.n 0 = .ok z →
      ValsB.cols (A := .prod A B) (C.key, C.val) = .ok es → kasc C.n es = .ok (vs, p) →
      kseen C.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 C.n (some z) [(C.n, z), (C.n, g)] [] [] = .ok r) →
    (∀ m mn mx bits K sel, kp m mn mx = .ok bits → whereCol m bits = .ok (K, sel) → WhereAgree m K bits sel) →
    Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape R'.key → Cols.shape W.val = Cols.shape R'.val →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (selectB kb R' S' >>= kk) rs out

theorem selectB_builds {kp : USize → Enc → Enc → Except String Enc} {kb : Nat → Nat → Nat → Bld Nat} (hT : TagOff)
    (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (hK : KeepSpec kp kb) (A B : Obj) : SelectSpec A B kp kb := by
  intro R S T' R' S' fg rs kk out hRk hRv hSk hSv hR hS hsel hlt hz hsc hW hfo hkk
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
  let P : TabB → Prop := fun W => Cols.shape W.key = Cols.shape R'.key ∧ Cols.shape W.val = Cols.shape R'.val
  let o : Array Val := (Val.size T'.n :: (T'.key.regVals ++ T'.val.regVals)).toArray
  have hB : ∃ fg1, Builds abiOf fg fg1 (selBody kb R1 S1 >>= answerRegs P) (rs ++ pv.toArray) o := by
    refine selBody_builds (Rv := R) (Sv := S) (T' := T') hT h63 hK (ColsOf.shape A hRk hsR1) (ColsOf.shape B hRv hsR2)
      (ColsOf.shape A hSk hsS1) (ColsOf.shape B hSv hsS2) gR gS hsel hlt hz hsc hW hfo ?_
    intro fg4 U' ys3 he4 hf4 ho4 hs4 hs5 hs6 hr4
    refine ⟨fg4, Builds.answerRegs (P := P) ⟨hs5.trans hsR1, hs6.trans hsR2⟩ (tabsRegs_eq _) fun _ => ?_⟩
    simpa [o] using reads_of hr4
  obtain ⟨fg1, ⟨a1, ha1⟩, hb1, hB1⟩ := hB
  have hm1 : AllGe rs.size R1.regs := fun a ha => by rw [hr1, List.mem_range'_1] at ha; omega
  have hm2 : AllGe rs.size S1.regs := fun a ha => by rw [hs1, List.mem_range'_1] at ha; omega
  have hTy : Typed rs.size (fun _ => True) (selBody kb R1 S1) :=
    (Typed.selBody (fun a b c h1 h2 h3 => hK.2.2.1 _ a b c h1 h2 h3) hm1 hm2).mono fun _ _ => trivial
  obtain ⟨ctys, hcl⟩ := Typed.cloTys (fg := fg) (fg1 := fg1) (k := (R'.regs ++ S'.regs).length) hTy
  rw [selectB_eq]
  refine funT_builds (P := P) (Us := [R1, S1]) (ctys := ctys) (o := o) hA ha hUs (hB1 #[]) hfo ?_
    (fun U body xs R rtys h _ hR hy is => hcl U body _ R rtys h hR hy is) ?_
  · intro Ts
    rcases Ts with _ | ⟨T1, _ | ⟨T2, _ | ⟨T3, Ts⟩⟩⟩ <;> try exact Grows.throw _
    exact Grows.selBody hK.1 T1 T2
  · intro U' ⟨hsk, hsv⟩ fg2 Rr V ys he hf ho' hRr hV
    obtain ⟨AU, YU, u1, -, -, u4⟩ := tab_spec U'
    rw [tabsRegs_eq] at u1
    obtain rfl := (pure_inj u1).symm
    have hl : Rr.toList.length = ([U'].flatMap TabB.regs).length := by
      have h1 := mapM_ok_size (hRr "")
      have k1 := ColsOf.regs_length (ColsOf.shape A hRk hsk) T'.key
      have k2 := ColsOf.regs_length (ColsOf.shape B hRv hsv) T'.val
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

/-- **`interB` builds `Tab.inter`**: `SelectSpec` at `inter`'s `keep`; `interB R S` is `selectB` at that builder, and
    `Tab.inter R S` is `Tab.select` at that `keep`, by unfolding. -/
theorem interB_builds (hT : TagOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A B : Obj) :
    SelectSpec A B (fun m mn mx => colMap .lt m mn mx) (fun m mn mx => mapB .lt m mn mx) :=
  selectB_builds hT h63 keepSpec_inter A B

/-- **`diffB` builds `Tab.diff`**: `SelectSpec` at `diff`'s `keep`, as `interB_builds`. -/
theorem diffB_builds (hT : TagOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A B : Obj) :
    SelectSpec A B (fun m _ mx => colMap .not m mx mx) (fun m _ mx => mapB .not m mx mx) :=
  selectB_builds hT h63 keepSpec_diff A B

end Rel.Lang.Plan
