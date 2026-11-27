module

public import Rel.Lang.PlanSpecPrefix
public import Rel.Lang.PlanSpecConcat
public import Rel.Lang.PlanSpecGather

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

/-- `kb` builds what the table function `kp` answers: its builder grows, is typed at every `m`, and where `kp` answers
    `bits` for the columns `mn`, `mx` its register holds `bits`. -/
def KeepSpec (kp : USize → Enc → Enc → Except String Enc) (kb : Nat → Nat → Nat → Bld Nat) : Prop :=
  (∀ m mn mx, Grows (kb m mn mx)) ∧
  (∀ lv m mn mx, lv ≤ m → lv ≤ mn → lv ≤ mx → Typed lv (fun r => lv ≤ r) (kb m mn mx)) ∧
  ∀ {fg : Array Fun × Array Fun} {rs : Array Val} {m mn mx : Nat} {mv : USize} {mnc mxc bits : Enc},
    rs[m]? = some (.size mv) → rs[mn]? = some (Reg.put mnc) → rs[mx]? = some (Reg.put mxc) → kp mv mnc mxc = .ok bits →
    Builds abiOf fg fg (do let r ← kb m mn mx; Pure.pure #[r]) rs #[Reg.put bits]

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

end Rel.Lang.Plan
