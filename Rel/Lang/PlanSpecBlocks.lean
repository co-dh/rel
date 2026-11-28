module

public import Rel.Lang.PlanSpecPack
public import Rel.Lang.PlanSpecCuts
public import Rel.Lang.PlanSpecFix

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `compBlocksB` builds `Tab.compBlocks` (PLAN-THM-E9c)

The block loop of `compBlocksB` is `fixB`'s loop with a block number in the state: a round reads the accumulator `A` and
the number `j` (`tabsAt`), `packT`s `A`, builds block `j + 1`, `∪`s them and compares `j + 2` with the block count.
`compRound_builds` is `fixRound_builds` for it, `compLoop_builds` `fixLoop_builds`; the pack enters as `TabSpec` and the
block as `BlockSpec`, in the style of `UnionSpec`. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- A round of `compBlocksB`'s block loop on the state `st`: the accumulator (of `A0`'s shape) and the block number `j`;
    `blk` builds block `j + 1`, `Cn` holds the block count and `one` the size `1`. `compBlocksB`'s round is
    `compRoundB A0 C.n one (blk C R S)`. -/
def compRoundB (A0 : TabB) (Cn one : Nat) (blk : Nat → Bld TabB) (st : Array Nat) : Bld (Array Nat × Nat) := do
  let ([A], js) ← tabsAt [A0] st.toList | throw "comp: the loop state is not one table"
  let [j] := js | throw "comp: the loop state holds no block number"
  let j1 ← call1 (kernel% USize.add) #[j, one]
  let U ← unionB (← packT A) (← blk j1)
  pure ((← tabsRegs [U]).toArray.push j1, ← call1 (kernel% USize.decEq) #[← call1 (kernel% USize.add) #[j1, one], Cn])

/-- **A block builder builds the block function `bm`**: from registers `Rn` extending `rs0` whose register `j` holds the
    block number `jv`, where `bm jv` answers `Bk`, `blk j` builds a table of the sides `A`, `C` holding `Bk`. -/
def BlockSpec (A C : Obj) (rs0 : Array Val) (bm : Nat → Except String (Tab A C)) (blk : Nat → Bld TabB) : Prop :=
  ∀ {j : Nat} {jv : USize} {Bk : Tab A C} {fg : Array Fun × Array Fun} {Rn : Array Val} {kk : TabB → Bld (Array Nat)}
    {out : Array Val}, Extends rs0 Rn → Rn[j]? = some (.size jv) → bm jv.toNat = .ok Bk → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (Rn' : Array Val), Extends Rn Rn' → (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → ColsOf A W.key → ColsOf C W.val → TabHolds W Bk Rn' →
      ∃ fg', Builds abiOf fg2 fg' (kk W) Rn' out) →
    ∃ fg', Builds abiOf fg fg' (blk j >>= kk) Rn out

/-- `USize.add` of two registers holding the sizes `x`, `y` answers `x + y`. -/
theorem addB_buildsE {fg : Array Fun × Array Fun} {rs : Array Val} {a b : Nat} {x y : USize}
    (ha : rs[a]? = some (.size x)) (hb : rs[b]? = some (.size y)) {c : Nat → Bld (Array Nat)} {out : Array Val}
    (hc : ∀ (r : Nat) (R : Array Val), R[r]? = some (.size (x + y)) → Extends rs R →
      ∃ fg', Builds abiOf fg fg' (c r) R out) :
    ∃ fg', Builds abiOf fg fg' (call1 (kernel% USize.add) #[a, b] >>= c) rs out := by
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  refine call1E (vs := #[.size x, .size y]) (v := .size (x + y)) (by abiK) (by rop)
    (reads_of (l := [a, b]) (vs := [.size x, .size y]) (by simp [ha, hb])) ?_ rfl hc
  simp [arg, hsz]; rfl

/-- **One round of the block loop** from the state holding the accumulator `X` and the block number `i`
    (`X.pack = Y`, block `i + 1` is `Bk`, `Y ∪ Bk = X'`): it builds the registers of `X'`, of `i + 1` and the bit of
    `i + 2 = nb`. -/
theorem compRound_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) {A C : Obj} {A0 : TabB}
    {blk : Nat → Bld TabB} {bm : Nat → Except String (Tab A C)} {rs0 : Array Val} {Cn one : Nat} {nb i : USize}
    {X Y Bk X' : Tab A C} {fg : Array Fun × Array Fun}
    (hP : TabSpec A C Tab.pack (fun T => packT T)) (hB : BlockSpec A C rs0 bm blk)
    (hAk : ColsOf A A0.key) (hAv : ColsOf C A0.val) (hCn : rs0[Cn]? = some (.size nb))
    (hone : rs0[one]? = some (.size 1)) (hfo : Ordered fg.1)
    (hpack : X.pack = .ok Y) (hb : bm (i + 1).toNat = .ok Bk) (hu : Y.union Bk = .ok X') (hU : UnionPre Y Bk) :
    ∃ fg', Builds abiOf fg fg'
      ((fun p => p.1.push p.2) <$> compRoundB A0 Cn one blk (List.range' rs0.size (A0.regs.length + 1)).toArray)
      (rs0 ++ (tabVals X ++ [Val.size i]).toArray) ((tabVals X' ++ [Val.size (i + 1), Val.bit (decide (i + 1 + 1 = nb))]).toArray) := by
  have hl : A0.regs.length = (tabVals X).length := TabB.regs_length hAk hAv X
  obtain ⟨L, Y0, h1, -, -, h4⟩ := tab_spec A0
  rw [tabsRegs_eq] at h1
  obtain rfl : A0.regs = L := by simpa using pure_inj h1
  obtain ⟨V, hV, hVr, -, hsk, hsv⟩ := h4 (List.range' rs0.size A0.regs.length) [rs0.size + A0.regs.length]
    (by simp)
  rw [tabsRegs_eq] at hVr
  have hVr' : V.regs = List.range' rs0.size A0.regs.length := by simpa using pure_inj hVr
  have hrd := mapM_range_append rs0 (tabVals X ++ [Val.size i])
  rw [List.length_append, List.length_singleton, ← hl, List.range'_concat, Nat.one_mul] at hrd
  obtain ⟨hXr, hir⟩ := mapM_split (by simp [hl]) hrd
  have hVX : TabHolds V X (rs0 ++ (tabVals X ++ [Val.size i]).toArray) := by unfold TabHolds; rw [hVr']; exact hXr
  have hj : (rs0 ++ (tabVals X ++ [Val.size i]).toArray)[rs0.size + A0.regs.length]? = some (.size i) := by
    exact (mapM_get_cons hir).1
  have hE0 : Extends rs0 (rs0 ++ (tabVals X ++ [Val.size i]).toArray) := fun h => get_app h
  have e : (List.range' rs0.size (A0.regs.length + 1)).toArray.toList =
      List.range' rs0.size A0.regs.length ++ [rs0.size + A0.regs.length] := by
    rw [List.toList_toArray, List.range'_concat, Nat.one_mul]
  unfold compRoundB
  rw [e, hV]
  simp only [pure_bind, map_bind, map_pure]
  refine addB_buildsE hj (hE0 hone) fun j1 R1 hj1 m1 => ?_
  refine hP (ColsOf.shape A hAk hsk) (ColsOf.shape C hAv hsv) (mapM_extends m1 hVX) hpack hfo
    fun fg2 W ys he2 hf2 ho2 hW1 hW2 hW => ?_
  have hWk : ColsOf A W.key := ColsOf.shape A (ColsOf.shape A hAk hsk) hW1
  have hWv : ColsOf C W.val := ColsOf.shape C (ColsOf.shape C hAv hsv) hW2
  refine hB (fun h => get_app (m1 (hE0 h))) (get_app hj1) hb ho2 fun fg3 Bt Rn ext3 he3 hf3 ho3 hBk hBv hBt => ?_
  refine unionB_builds hc h63 A C hWk hWv hBk hBv (mapM_extends ext3 hW) hBt hu hU ho3
    fun fg4 U zs he4 hf4 ho4 hU1 hU2 hUr => ?_
  rw [tabsRegs_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, pure_bind]
  have hE4 : Extends (rs0 ++ (tabVals X ++ [Val.size i]).toArray) (Rn ++ zs) :=
    fun h => get_app (ext3 (get_app (m1 h)))
  have hj1' : (Rn ++ zs)[j1]? = some (.size (i + 1)) := get_app (ext3 (get_app hj1))
  refine addB_buildsE hj1' (hE4 (hE0 hone)) fun d1 R2 hd1 m2 => ⟨fg4, ?_⟩
  refine decEq_builds hd1 (m2 (hE4 (hE0 hCn))) fun d R3 hd m3 => Builds.pure fun who => ?_
  have hl : (U.regs ++ [j1, d]).mapM (fun x => R3[x]?) =
      some (tabVals X' ++ [Val.size (i + 1), Val.bit (decide (i + 1 + 1 = nb))]) := by
    rw [List.mapM_append, mapM_extends (fun h => m3 (m2 h)) hUr]
    simp [m3 (m2 hj1'), hd, tabVals]
  simpa using reads_of (who := who) hl

theorem usize_succ_toNat (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) {i : USize} (h : i.toNat < 2 ^ 63) :
    (i + 1).toNat = i.toNat + 1 := by
  have := USize.toNat_lt_size (2 ^ 63 : USize)
  rw [h63] at this
  have hs : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]

/-- **The block loop of `compBlocksB`** from the state `init` holding the block `X0` and the number `0`, the register `Cn`
    the block count `nb ≥ 2`: where `compBlocks`' fold over the blocks `1 … nb - 1` answers `Yf` from `X0`, the loop
    builds the registers of `Yf` and a last block number. `hU` is `∪`'s kernel premise at each round. -/
theorem compLoop_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) {A C : Obj} {A0 : TabB}
    {blk : Nat → Bld TabB} {bm : Nat → Except String (Tab A C)} {rs0 : Array Val} {Cn one : Nat} {nb : USize}
    {X0 Yf : Tab A C} {fg : Array Fun × Array Fun} {init : Array Nat} {msg : String}
    (hP : TabSpec A C Tab.pack (fun T => packT T)) (hB : BlockSpec A C rs0 bm blk)
    (hAk : ColsOf A A0.key) (hAv : ColsOf C A0.val) (hCn : rs0[Cn]? = some (.size nb))
    (hone : rs0[one]? = some (.size 1)) (hfo : Ordered fg.1) (hsz : init.size = A0.regs.length + 1)
    (hi : init.mapM (reg rs0 "loop") = .ok (tabVals X0 ++ [Val.size 0]).toArray) (h2 : 2 ≤ nb.toNat)
    (hnb : nb.toNat < 2 ^ 63)
    (hY : (List.range (nb.toNat - 1)).foldlM (fun acc j => do (← acc.pack).union (← bm (j + 1))) X0 = .ok Yf)
    (hU : ∀ i acc Y Bk, i + 1 < nb.toNat →
      (List.range i).foldlM (fun acc j => do (← acc.pack).union (← bm (j + 1))) X0 = .ok acc →
      acc.pack = .ok Y → bm (i + 1) = .ok Bk → UnionPre Y Bk) :
    ∃ fg1 i, Builds abiOf fg fg1 (loop Cn init msg (compRoundB A0 Cn one blk)) rs0 (tabVals Yf ++ [Val.size i]).toArray := by
  let step : Tab A C → Nat → Except String (Tab A C) := fun acc j => do (← acc.pack).union (← bm (j + 1))
  let I : Nat → Array Val → Prop := fun left s => ∃ (i : USize) (acc : Tab A C), s = (tabVals acc ++ [Val.size i]).toArray ∧
    i.toNat + left = nb.toNat ∧ i.toNat + 2 ≤ nb.toNat ∧ (List.range i.toNat).foldlM step X0 = .ok acc ∧
    (List.range' i.toNat (nb.toNat - 1 - i.toNat)).foldlM step acc = .ok Yf
  let J : Array Val → Prop := fun o => ∃ i, o = (tabVals Yf ++ [Val.size i]).toArray
  have hsl : ∀ acc : Tab A C, ∀ i : USize, (tabVals acc ++ [Val.size i]).toArray.size = init.size := fun acc i => by
    simp [hsz, ← TabB.regs_length hAk hAv acc]
  have hround : ∀ j (s : Array Val), I (j + 1) s → ∃ (s' : Array Val) (bt : Bool) (fg' : Array Fun × Array Fun),
      s'.size = init.size ∧ (if bt then J s' else I j s') ∧ Builds abiOf fg fg'
        ((fun p => p.1.push p.2) <$> compRoundB A0 Cn one blk (List.range' rs0.size init.size).toArray)
        (rs0 ++ s) (s'.push (.bit bt)) := by
    rintro j s ⟨i, acc, rfl, hj, hi2, hpre, hrest⟩
    obtain ⟨k, hk⟩ : ∃ k, nb.toNat - 1 - i.toNat = k + 1 := ⟨nb.toNat - 2 - i.toNat, by omega⟩
    rw [hk, List.range'_succ, List.foldlM_cons] at hrest
    obtain ⟨acc', hst, hrest'⟩ := except_bind_ok hrest
    obtain ⟨Y, hpk, h⟩ := except_bind_ok hst
    obtain ⟨Bk, hbk, hun⟩ := except_bind_ok h
    have hi1 := usize_succ_toNat h63 (i := i) (by omega)
    obtain ⟨fg', hB'⟩ := compRound_builds hc h63 (i := i) (nb := nb) hP hB hAk hAv hCn hone hfo hpk (by rw [hi1]; exact hbk)
      hun (hU _ _ _ _ (by omega) hpre hpk hbk)
    refine ⟨(tabVals acc' ++ [Val.size (i + 1)]).toArray, decide (i + 1 + 1 = nb), fg', hsl acc' (i + 1), ?_,
      by rw [hsz]; simpa using hB'⟩
    have hd : (i + 1 + 1 = nb) ↔ i.toNat + 2 = nb.toNat := by
      rw [← USize.toNat_inj, usize_succ_toNat h63 (by omega), hi1]
    by_cases hq : i.toNat + 2 = nb.toNat
    · have hb : decide (i + 1 + 1 = nb) = true := decide_eq_true (hd.2 hq)
      rw [hb, if_pos rfl]
      obtain rfl : k = 0 := by omega
      simp only [List.range'_zero, List.foldlM_nil] at hrest'
      exact ⟨i + 1, by rw [Except.ok.inj hrest']⟩
    · have hb : decide (i + 1 + 1 = nb) = false := decide_eq_false fun h => hq (hd.1 h)
      rw [hb]
      simp only [Bool.false_eq_true, if_false]
      refine ⟨i + 1, acc', rfl, by omega, by omega, ?_, ?_⟩
      · rw [hi1, List.range_succ, List.foldlM_append, hpre]
        simp only [List.foldlM_cons, List.foldlM_nil]
        show (step acc i.toNat >>= fun a => pure a) = _
        rw [hst]; rfl
      · rw [hi1, show nb.toNat - 1 - (i.toNat + 1) = k by omega]
        exact hrest'
  have hI0 : I nb.toNat (tabVals X0 ++ [Val.size 0]).toArray :=
    ⟨0, X0, rfl, by simp, by simpa using h2, by simp; rfl, by simpa [List.range_eq_range'] using hY⟩
  obtain ⟨j0, hj0⟩ : ∃ j, nb.toNat = j + 1 := ⟨nb.toNat - 1, by omega⟩
  obtain ⟨s1, bt1, fg1, -, -, hB1⟩ := hround j0 _ (hj0 ▸ hI0)
  refine ⟨fg1, ?_⟩
  obtain ⟨o, ⟨io, rfl⟩, hB⟩ := Builds.loop (abi := abiOf) (I := I) (J := J) (init := init) (msg := msg) (fg := fg)
    (fg1 := fg1) (b := compRoundB A0 Cn one blk) (c := nb) (rs := rs0) (s₀ := (tabVals X0 ++ [Val.size 0]).toArray) hCn
    hi hI0 (fun s ⟨i, _, _, h1, h2', _⟩ => by omega) fun j s hs hI => by
      obtain ⟨s', bt, fg', hs', hc', hB'⟩ := hround j s hI
      obtain rfl : fg' = fg1 := Builds.fg_unique hB' hB1 (by simp [hs, hsl])
      exact ⟨s', bt, hs', hc', hB'⟩
  exact ⟨io, hB⟩

/-! ### `Grows`, `Typed` of `compBlocksB`'s parts (`funT_builds`' `hb`, `hty`) -/

/-- A builder that `Grows` keeps the functions `Ordered`: what a continuation asks of the functions a build leaves. -/
theorem Builds.ordered {abi : String → Option Kernel} {fg fg' : Array Fun × Array Fun} {b : Bld (Array Nat)}
    {rs out : Array Val} (hB : Builds abi fg fg' b rs out) (hg : Grows b) (ho : Ordered fg.1) : Ordered fg'.1 := by
  obtain ⟨-, -, h⟩ := hB
  obtain ⟨js, xs, r, hr, -, -⟩ := h #[]
  exact ((hg _ _ _ hr) ho (fun j hj => by simp [Instr.callsB] at hj)).1

/-- The builders `compBlocksB` is made of, closing on their own `Grows` lemmas. -/
local macro "growsB" : tactic => `(tactic| repeat' first
  | exact Grows.pure _ | exact Grows.throw _ | (with_reducible refine Grows.bind ?_ (fun _ => ?_))
  | (with_reducible refine Grows.ite ?_ ?_) | (with_reducible refine Grows.mapM (fun _ => ?_) _)
  | exact Grows.lit _ | exact Grows.call1 _ _ | exact Grows.callK _ _ | exact Grows.nth _ _ _
  | exact Grows.ctorB _ _ _ | exact Grows.listB _ | exact Grows.srcB _ _ | exact Grows.mapB _ _ _ _ _ _ _ _
  | exact Grows.u64B _ | exact Grows.gatherB _ _ _ _ | exact Grows.prefixB _ _ _ | exact Grows.expandB _ _
  | exact Grows.withRegs _ _ | exact Grows.cellsBoundB _ _ _ | exact Grows.scanB _ _ _ _ _ | exact Grows.wordsB _ _
  | exact Grows.gatherCols _ _ _ _ | exact Grows.whereB _ _ | exact Grows.guard _ _ _
  | exact Grows.of_pure (regsOf_eq _) | dsimp only | split)

theorem Grows.mapWB (op : Kernel.Op) (n a b : Nat) (ps : List (Kernel.Op × Nat)) : Grows (Plan.mapWB op n a b ps) := by
  unfold Plan.mapWB; growsB

theorem Grows.clampB (n x c : Nat) : Grows (Plan.clampB n x c) := by
  unfold Plan.clampB
  exact (Grows.lit _).bind fun _ => (Grows.u64B _).bind fun _ => Grows.mapWB _ _ _ _ _

theorem Grows.keepB (T : TabB) (b : Nat) : Grows (Plan.keepB T b) := by
  unfold Plan.keepB
  exact (Grows.whereB _ _).bind fun ⟨_, _⟩ => (Grows.gatherCols _ _ _ _).bind fun _ =>
    (Grows.gatherCols _ _ _ _).bind fun _ => Grows.pure _

theorem Grows.compOneB (R S : TabB) : Grows (Plan.compOneB R S) := by
  unfold Plan.compOneB
  refine Grows.funT fun Us => ?_
  rcases Us with _ | ⟨T1, _ | ⟨T2, _ | ⟨T3, Us⟩⟩⟩ <;> try exact Grows.throw _
  exact (Grows.groupsB _ _).bind fun x => Grows.compFromB _ _ x

theorem Grows.iteT {c : Nat} {ks vs : Cols} {t e : Bld TabB} (ht : Grows t) (he : Grows e) :
    Grows (Plan.iteT c ks vs t e) := by
  have hf : ∀ {b : Bld TabB}, Grows b → ∀ w, Grows (Plan.iteFlat c ks vs w (Plan.funT [] fun _ => b)) := fun hb w => by
    unfold Plan.iteFlat
    refine (Grows.funT fun _ => hb).bind fun T => ?_
    rw [regsOf_eq, pure_bind]
    split
    · exact Grows.pure _
    · exact (Grows.throw _).bind fun _ => Grows.pure _
  unfold Plan.iteT
  rw [regsOf_eq, pure_bind]
  exact (Grows.ite (hf ht _) (hf he _)).bind fun _ => (Grows.withRegs _ _).bind fun ⟨_, _⟩ =>
    (Grows.nth _ _ _).bind fun _ => Grows.pure _

theorem Grows.col1 (cs : Cols) : Grows (Plan.col1 cs) := by
  unfold Plan.col1; split
  · exact Grows.pure _
  · exact Grows.throw _

-- The registers `withRegs` hands back are among those it was given.
mutual
theorem Typed.withRegs {m : Nat} : ∀ (cs : Cols) (rs : List Nat), AllGe m rs →
    Typed m (fun r => AllGe m (Cols.regs r.1) ∧ AllGe m r.2) (withRegs cs rs)
  | [], rs, h => by unfold Rel.Lang.Plan.withRegs; exact Typed.pure ⟨fun a ha => by simp [Cols.regs] at ha, h⟩
  | c :: cs, rs, h => by
    unfold Rel.Lang.Plan.withRegs
    exact (Typed.withReg c rs h).bind fun ⟨c', rs1⟩ h1 => (Typed.withRegs cs rs1 h1.2).bind fun ⟨cs', rs2⟩ h2 =>
      Typed.pure ⟨fun a ha => by
        simp only [Cols.regs, List.mem_append] at ha; exact ha.elim (h1.1 a) (h2.1 a), h2.2⟩
theorem Typed.withReg {m : Nat} : ∀ (c : Col) (rs : List Nat), AllGe m rs →
    Typed m (fun r => AllGe m (Col.regs r.1) ∧ AllGe m r.2) (withReg c rs)
  | .atom p t e, r :: rs, h => by
    unfold Rel.Lang.Plan.withReg
    exact Typed.pure ⟨fun a ha => by simp [Col.regs] at ha; subst ha; exact h _ (by simp),
      fun a ha => h a (by simp [ha])⟩
  | .atom p t e, [], h => by unfold Rel.Lang.Plan.withReg; exact Typed.throw _
  | .arr p m' lo hi f, a :: b :: d :: rs, h => by
    unfold Rel.Lang.Plan.withReg
    exact (Typed.withRegs f rs fun x hx => h x (by simp [hx])).bind fun ⟨f', rs1⟩ h1 =>
      Typed.pure ⟨fun x hx => by
        simp only [Col.regs, List.cons_append, List.nil_append, List.mem_cons] at hx
        rcases hx with rfl | rfl | rfl | hx
        · exact h _ (by simp)
        · exact h _ (by simp)
        · exact h _ (by simp)
        · exact h1.1 x hx, h1.2⟩
  | .arr p m' lo hi f, [], h => by unfold Rel.Lang.Plan.withReg; exact Typed.throw _
  | .arr p m' lo hi f, [_], h => by unfold Rel.Lang.Plan.withReg; exact Typed.throw _
  | .arr p m' lo hi f, [_, _], h => by unfold Rel.Lang.Plan.withReg; exact Typed.throw _
  | .sum p tag x y, a :: rs, h => by
    unfold Rel.Lang.Plan.withReg
    exact (Typed.withRegs x rs fun z hz => h z (by simp [hz])).bind fun ⟨x', rs1⟩ h1 =>
      (Typed.withRegs y rs1 h1.2).bind fun ⟨y', rs2⟩ h2 => Typed.pure ⟨fun z hz => by
        simp only [Col.regs, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hz
        rcases hz with rfl | hz | hz
        · exact h _ (by simp)
        · exact h1.1 z hz
        · exact h2.1 z hz, h2.2⟩
  | .sum p tag x y, [], h => by unfold Rel.Lang.Plan.withReg; exact Typed.throw _
end

theorem Typed.mapWB {m : Nat} {op : Kernel.Op} {n a b : Nat} {ps : List (Kernel.Op × Nat)} (hn : m ≤ n) (ha : m ≤ a)
    (hb : m ≤ b) (hps : ∀ p ∈ ps, m ≤ p.2) : Typed m (fun r => m ≤ r) (Plan.mapWB op n a b ps) := by
  unfold Plan.mapWB
  refine (Typed.lit _).bind fun r1 h1 => (Typed.lit _).bind fun r2 h2 => (Typed.lit _).bind fun r3 h3 =>
    (Typed.lit _).bind fun r4 h4 => (Typed.ctorB (by simp) (by simp) 0).bind fun r5 h5 =>
    (Typed.srcB hn ha).bind fun r6 h6 => (Typed.srcB hn hb).bind fun r7 h7 =>
    (Typed.listB (by simp [AllGe, h6, h7])).bind fun r8 h8 => (Typed.listB (by simp [AllGe])).bind fun r9 h9 =>
    (Typed.mapM (Q := fun r => m ≤ r) fun ⟨o, w⟩ hw => (Typed.lit _).bind fun r h =>
      Typed.ctorB (by simp [h, hps _ hw]) (by simp) 0).bind fun l hl =>
    (Typed.listB hl).bind fun r10 h10 => (Typed.callK ?_).bind fun rs hrs => Typed.nth hrs 0 _
  simp [h1, h2, h3, h4, h5, h8, h9, h10]; omega

theorem Typed.clampB {m n x c : Nat} (hn : m ≤ n) (hx : m ≤ x) :
    Typed m (fun r => m ≤ r) (Plan.clampB n x c) := by
  unfold Plan.clampB
  exact (Typed.lit _).bind fun z hz => Typed.u64B.bind fun u hu =>
    Typed.mapWB hn hx hx (by simp [hz, hu])

theorem Typed.keepB {m : Nat} {T : TabB} {b : Nat} (hT : AllGe m T.regs) (hb : m ≤ b) :
    Typed m (fun U => AllGe m U.regs) (Plan.keepB T b) := by
  have hn : m ≤ T.n := hT _ (by rw [TabB.regs_eq]; simp)
  have hk : AllGe m (Cols.regs T.key) := fun a ha => hT a (by rw [TabB.regs_eq]; simp [ha])
  have hv : AllGe m (Cols.regs T.val) := fun a ha => hT a (by rw [TabB.regs_eq]; simp [ha])
  unfold Plan.keepB
  refine (Typed.whereB hn hb).bind fun ⟨k, sel⟩ hks => ?_
  refine (Typed.gatherCols hks.1 _ _ hn hk).bind fun ck hck => (Typed.gatherCols hks.1 _ _ hn hv).bind
    fun cv hcv => Typed.pure ?_
  intro a ha
  simp only [TabB.regs, Cols.regs_append, List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | ha | ha
  · exact hks.1
  · exact hck a ha
  · exact hcv a ha

theorem Typed.compOneB {m : Nat} {R S : TabB} (hR : AllGe m R.regs) (hS : AllGe m S.regs) :
    Typed m (fun U => AllGe m U.regs) (Plan.compOneB R S) := by
  unfold Plan.compOneB
  refine Typed.funT (fun a ha => ?_) fun Us hU => ?_
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at ha
    exact ha.elim (hR a) (hS a)
  rcases Us with _ | ⟨R1, _ | ⟨S1, _ | ⟨T3, Us⟩⟩⟩ <;> try exact Typed.throw _
  have hm1 : AllGe m R1.regs := fun a ha => hU a (by simp [ha])
  have hm2 : AllGe m S1.regs := fun a ha => hU a (by simp [ha])
  exact (Typed.groupsB hm1 hm2).bind fun x hx => Typed.compFromB hm1 hm2 hx

theorem Typed.iteFlat {m c w : Nat} {ks vs : Cols} {b : Bld TabB} (hb : Typed m (fun U => AllGe m U.regs) b) :
    Typed m (fun r => ∀ a ∈ r, m ≤ a) (Plan.iteFlat c ks vs w b) := by
  unfold Plan.iteFlat
  refine hb.bind fun T hT => ?_
  rw [regsOf_eq, pure_bind]
  have hn : m ≤ T.n := hT _ (by rw [TabB.regs_eq]; simp)
  have hr : AllGe m (Cols.regs (T.key ++ T.val)) := fun a ha => hT a (by simp [TabB.regs, ha])
  split
  · exact Typed.pure fun a ha => by
      simp only [Array.mem_append, List.mem_toArray] at ha
      rcases ha with ha | ha
      · simp at ha; omega
      · exact hr a ha
  · exact (Typed.throw (Q := fun _ => True) _).bind fun _ _ => Typed.pure fun a ha => by
      simp only [Array.mem_append, List.mem_toArray] at ha
      rcases ha with ha | ha
      · simp at ha; omega
      · exact hr a ha

theorem Typed.iteT {m c : Nat} {ks vs : Cols} {t e : Bld TabB} (hc : m ≤ c)
    (ht : Typed m (fun U => AllGe m U.regs) t) (he : Typed m (fun U => AllGe m U.regs) e) :
    Typed m (fun U => AllGe m U.regs) (Plan.iteT c ks vs t e) := by
  unfold Plan.iteT
  rw [regsOf_eq, pure_bind]
  refine (Typed.ite hc (Typed.iteFlat (Typed.funT (by simp [AllGe]) fun _ _ => ht))
    (Typed.iteFlat (Typed.funT (by simp [AllGe]) fun _ _ => he))).bind fun rs hrs => ?_
  refine (Typed.withRegs _ _ fun a ha => hrs a (by simpa using List.mem_of_mem_drop ha)).bind
    fun ⟨cs, rest⟩ hcs => (Typed.nth hrs 0 _).bind fun n0 hn0 => Typed.pure ?_
  intro a ha
  simp only [TabB.regs, List.take_append_drop, List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact hn0
  · exact hcs.1 a ha

/-! ### `Grows`, `Typed` of `packB`, `packT` -/

theorem Grows.packWidthsB (o : Bool) (n lo hi : Nat) : Grows (Plan.packWidthsB o n lo hi) := by
  unfold Plan.packWidthsB
  split
  · exact (Grows.wordsB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
      (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => Grows.pure _
  · exact (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => Grows.pure _

theorem Grows.packWideB (k m T : Nat) : Grows (Plan.packWideB k m T) := by
  unfold Plan.packWideB
  split
  · exact Grows.lit _
  · exact (Grows.lit _).bind fun _ => (Grows.call1 _ _).bind fun _ => Grows.call1 _ _

theorem Grows.cellsLayB (n w P : Nat) : Grows (Plan.cellsLayB n w P) := by
  unfold Plan.cellsLayB
  exact (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.scanB _ _ _ _ _).bind fun _ =>
    (Grows.nth _ _ _).bind fun _ => Grows.pure _

/-- Induction on `Col.sizes`, the measure `packB` terminates by. -/
theorem Grows.packB (k : Nat) : ∀ (o : Bool) (n : Nat) (cs : Cols), Grows (Plan.packB o k n cs) := by
  intro o n cs
  induction hs : Col.sizes cs using Nat.strongRecOn generalizing o n cs with
  | _ s ih =>
    unfold Plan.packB
    refine Grows.mapM (fun x => ?_) _
    obtain ⟨c, hc⟩ := x
    have hle := Col.size_le_of_mem hc
    rcases c with ⟨p, t, e⟩ | ⟨p, m, lo, hi, f⟩ | ⟨p, tag, x, y⟩
    · exact Grows.pure _
    · have hf : Col.sizes f < s := by simp [Col.size] at hle; omega
      refine (Grows.cellsBoundB _ _ _).bind fun _ => (Grows.packWidthsB _ _ _ _).bind fun ⟨sw, w⟩ =>
        (Grows.prefixB _ _ _).bind fun ⟨P, T⟩ => ?_
      dsimp only
      have hkeep : Grows (Plan.packB false k m f >>= fun f' => regsOf [Col.arr p m lo hi f'] >>= fun L =>
          (Pure.pure L.toArray : Bld (Array Nat))) :=
        (ih _ hf false m f rfl).bind fun _ => (Grows.of_pure (regsOf_eq _)).bind fun _ => Grows.pure _
      refine (Grows.packWideB _ _ _).bind fun wide => (Grows.lit _).bind fun _ => (Grows.call1 _ _).bind fun _ =>
        (Grows.ite hkeep (Grows.ite hkeep ?_)).bind fun rs => (Grows.withRegs _ _).bind fun x => ?_
      · refine (Grows.expandB _ _).bind fun ⟨T', G, u⟩ => (Grows.gatherB _ _ _ _).bind fun _ =>
          (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.gatherCols _ _ _ _).bind fun g =>
          (Grows.cellsLayB _ _ _).bind fun ⟨lo', hi'⟩ => ?_
        dsimp only
        split
        · refine (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
            (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.pure _).bind fun _ => ?_
          split
          · exact (ih _ (by omega) false T' g rfl).bind fun _ => (Grows.of_pure (regsOf_eq _)).bind fun _ =>
              Grows.pure _
          · exact Grows.throw _
        · refine (Grows.pure _).bind fun _ => ?_
          split
          · exact (ih _ (by omega) false T' g rfl).bind fun _ => (Grows.of_pure (regsOf_eq _)).bind fun _ =>
              Grows.pure _
          · exact Grows.throw _
      · rcases x with ⟨_ | ⟨c, _ | _⟩, _⟩
        all_goals first | exact Grows.pure _ | exact Grows.throw _
    · have hx : Col.sizes x < s := by simp [Col.size] at hle; omega
      have hy : Col.sizes y < s := by simp [Col.size] at hle; omega
      exact (ih _ hx true n x rfl).bind fun _ => (ih _ hy true n y rfl).bind fun _ => Grows.pure _

theorem Grows.packT (T : TabB) (k : Nat) : Grows (Plan.packT T k) := by
  unfold Plan.packT
  refine Grows.funT fun Us => ?_
  rcases Us with _ | ⟨T1, _ | ⟨T2, Us⟩⟩ <;> try exact Grows.throw _
  exact (Grows.packB _ _ _ _).bind fun _ => (Grows.packB _ _ _ _).bind fun _ => Grows.pure _

theorem Typed.packWidthsB {m : Nat} {o : Bool} {n lo hi : Nat} (hn : m ≤ n) (hlo : m ≤ lo) (hhi : m ≤ hi) :
    Typed m (fun r : Nat × Nat => m ≤ r.1 ∧ m ≤ r.2) (Plan.packWidthsB o n lo hi) := by
  unfold Plan.packWidthsB
  split
  · exact Typed.wordsB.bind fun z hz => (Typed.mapB hn hlo hz).bind fun s hs => (Typed.mapB hn hhi hz).bind
      fun e he => (Typed.mapB hn he hs).bind fun w hw => Typed.pure ⟨hs, hw⟩
  · exact (Typed.mapB hn hhi hlo).bind fun w hw => Typed.pure ⟨hlo, hw⟩

theorem Typed.packWideB {m k mm T : Nat} (hm : m ≤ mm) (hT : m ≤ T) :
    Typed m (fun r => m ≤ r) (Plan.packWideB k mm T) := by
  unfold Plan.packWideB
  split
  · exact Typed.lit _
  · exact (Typed.lit _).bind fun l hl => (Typed.call1 (by simp [hm, hl])).bind fun q hq =>
      Typed.call1 (by simp [hq, hT])

theorem Typed.cellsLayB {m n w P : Nat} (hn : m ≤ n) (hw : m ≤ w) (hP : m ≤ P) :
    Typed m (fun r : Nat × Nat => m ≤ r.1 ∧ m ≤ r.2) (Plan.cellsLayB n w P) := by
  unfold Plan.cellsLayB
  exact (Typed.mapB hn hP hw).bind fun a ha => (Typed.scanB hn (by simp) (by simp [AllGe, hP])).bind fun r hr =>
    (Typed.nth hr 0 _).bind fun b hb => Typed.pure ⟨ha, hb⟩

/-- `packB` reads only registers it was given, and answers registers above `m`: induction on `Col.sizes`. -/
theorem Typed.packB {m : Nat} (k : Nat) : ∀ (o : Bool) (n : Nat) (cs : Cols), m ≤ n → AllGe m (Cols.regs cs) →
    Typed m (fun r => AllGe m (Cols.regs r)) (Plan.packB o k n cs) := by
  intro o n cs hn hcs
  induction hs : Col.sizes cs using Nat.strongRecOn generalizing o n cs with
  | _ s ih =>
    unfold Plan.packB
    refine (Typed.mapM (Q := fun c => AllGe m (Col.regs c)) fun x hx => ?_).mono
      fun r hr => (Cols.regs_all (P := fun a => m ≤ a) r).2 hr
    obtain ⟨c, hc⟩ := x
    have hcr : AllGe m (Col.regs c) := (Cols.regs_all (P := fun a => m ≤ a) cs).1 hcs c hc
    have hle := Col.size_le_of_mem hc
    rcases c with ⟨p, t, e⟩ | ⟨p, mm, lo, hi, f⟩ | ⟨p, tag, x, y⟩
    · exact Typed.pure hcr
    · have hf : Col.sizes f < s := by simp [Col.size] at hle; omega
      have h1 : m ≤ mm := hcr _ (by simp [Col.regs])
      have hlo : m ≤ lo := hcr _ (by simp [Col.regs])
      have hhi : m ≤ hi := hcr _ (by simp [Col.regs])
      have hfr : AllGe m (Cols.regs f) := fun a ha => hcr a (by simp [Col.regs, ha])
      refine (Typed.cellsBoundB hn h1).bind fun _ _ => (Typed.packWidthsB hn hlo hhi).bind fun ⟨sw, w⟩ hsw =>
        (Typed.prefixB hn hsw.2).bind fun ⟨P, T⟩ hPT => ?_
      dsimp only
      have hrec : ∀ (n' l h : Nat) (g : Cols), Col.sizes g < s → m ≤ n' → m ≤ l → m ≤ h → AllGe m (Cols.regs g) →
          Typed m (fun r => ∀ a ∈ r, m ≤ a) (Plan.packB false k n' g >>= fun f' =>
            regsOf [Col.arr p n' l h f'] >>= fun L => (Pure.pure L.toArray : Bld (Array Nat))) :=
        fun n' l h g hg h1 h2 h3 hgr => (ih _ hg false n' g h1 hgr rfl).bind fun f' hf' => by
          rw [regsOf_eq, pure_bind]
          exact Typed.pure fun a ha => by
            simp only [List.mem_toArray, Cols.regs, Col.regs, List.append_nil, List.cons_append, List.nil_append,
              List.mem_cons] at ha
            rcases ha with rfl | rfl | rfl | ha
            · exact h1
            · exact h2
            · exact h3
            · exact hf' a ha
      refine (Typed.packWideB h1 hPT.2).bind fun wide hwd => (Typed.lit _).bind fun z hz =>
        (Typed.call1 (by simp [h1, hz])).bind fun d hd =>
        (Typed.ite hd (hrec _ _ _ _ hf h1 hlo hhi hfr) (Typed.ite hwd (hrec _ _ _ _ hf h1 hlo hhi hfr) ?_)).bind
        fun rs hrs => (Typed.withRegs _ _ fun a ha => hrs a (by simpa using ha)).bind fun x hx => ?_
      · refine (Typed.expandB hn hsw.2).bind fun ⟨T', G, u⟩ he => Typed.gatherB.bind fun g0 hg0 =>
          (Typed.mapB he.1 hg0 he.2.2).bind fun ix hix => (Typed.gatherCols he.1 mm f h1 hfr).bind fun g hg =>
          (Typed.cellsLayB hn hsw.2 hPT.1).bind fun ⟨lo', hi'⟩ hl => ?_
        dsimp only
        split
        · refine (Typed.mapB hn hlo hlo).bind fun big hb => (Typed.mapB hn hb hl.1).bind fun a ha =>
            (Typed.mapB hn hb hl.2).bind fun b hb' =>
            (Typed.pure (Q := fun r : Nat × Nat => m ≤ r.1 ∧ m ≤ r.2) ⟨ha, hb'⟩).bind fun y hy => ?_
          split
          · exact hrec _ _ _ _ (by omega) he.1 hy.1 hy.2 hg
          · exact Typed.throw _
        · refine (Typed.pure (Q := fun r : Nat × Nat => m ≤ r.1 ∧ m ≤ r.2) hl).bind fun y hy => ?_
          split
          · exact hrec _ _ _ _ (by omega) he.1 hy.1 hy.2 hg
          · exact Typed.throw _
      · rcases x with ⟨_ | ⟨c, _ | _⟩, rest⟩
        all_goals first
          | exact Typed.throw _
          | exact Typed.pure fun a ha => hx.1 a (by simp [Cols.regs, ha])
    · have hx : Col.sizes x < s := by simp [Col.size] at hle; omega
      have hy : Col.sizes y < s := by simp [Col.size] at hle; omega
      have ht : m ≤ tag := hcr _ (by simp [Col.regs])
      have hxr : AllGe m (Cols.regs x) := fun a ha => hcr a (by simp [Col.regs, ha])
      have hyr : AllGe m (Cols.regs y) := fun a ha => hcr a (by simp [Col.regs, ha])
      refine (ih _ hx true n x hn hxr rfl).bind fun x' hx' => (ih _ hy true n y hn hyr rfl).bind fun y' hy' =>
        Typed.pure fun a ha => ?_
      simp only [Col.regs, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at ha
      rcases ha with rfl | ha | ha
      · exact ht
      · exact hx' a ha
      · exact hy' a ha

theorem Typed.packT {m : Nat} {T : TabB} {k : Nat} (hT : AllGe m T.regs) :
    Typed m (fun U => AllGe m U.regs) (Plan.packT T k) := by
  unfold Plan.packT
  refine Typed.funT (by simpa using hT) fun Us hU => ?_
  rcases Us with _ | ⟨T1, _ | ⟨T2, Us⟩⟩ <;> try exact Typed.throw _
  have hm : AllGe m T1.regs := fun a ha => hU a (by simp [ha])
  have hn : m ≤ T1.n := hm _ (by rw [TabB.regs_eq]; simp)
  have hk : AllGe m (Cols.regs T1.key) := fun a ha => hm a (by rw [TabB.regs_eq]; simp [ha])
  have hv : AllGe m (Cols.regs T1.val) := fun a ha => hm a (by rw [TabB.regs_eq]; simp [ha])
  refine (Typed.packB k false _ _ hn hk).bind fun ck hck => (Typed.packB k false _ _ hn hv).bind fun cv hcv =>
    Typed.pure fun a ha => ?_
  simp only [TabB.regs, Cols.regs_append, List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | ha | ha
  · exact hn
  · exact hck a ha
  · exact hcv a ha

/-- **`compBlockB` is a block builder** (`BlockSpec`) of `Tab.compBlock R S ce`: `R'`, `S'` hold `R`, `S` and `c` the
    block words `ce` in `rs0`; `hk` is `compBlockB_builds`' premise at every block number. -/
theorem compBlockB_spec (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A B C : Obj) {R : Tab A B}
    {S : Tab B C} {R' S' : TabB} {c : Nat} {ce : Enc} {rs0 : Array Val}
    (hRk : ColsOf A R'.key) (hRv : ColsOf B R'.val) (hSk : ColsOf B S'.key) (hSv : ColsOf C S'.val)
    (hR : TabHolds R' R rs0) (hS : TabHolds S' S rs0) (hce : rs0[c]? = some (Reg.put ce))
    (hk : ∀ (jv : USize) (X : Tab A C), Tab.compBlock R S ce jv.toNat = .ok X → ∀ m Rk,
      colMap .first R.n ce ce .i64 .i64 [] [(.eq, jv.toUInt64)] = .ok m → R.keep m = .ok Rk →
      (∀ K sel, whereCol R.n m = .ok (K, sel) → WhereAgree R.n K m sel) ∧ CompPre A B C Rk S ∧ CompPost A B C Rk X) :
    BlockSpec A C rs0 (fun j => Tab.compBlock R S ce j) (fun j => compBlockB R' S' c j) := by
  intro j jv Bk fg Rn kk out hE hj hb hfo hkk
  exact compBlockB_builds hc h63 A B C hRk hRv hSk hSv (mapM_extends hE hR) (mapM_extends hE hS) (hE hce) hj hb
    (hk jv Bk hb) hfo fun fg2 W Rn' ext he hf ho hsk hsv hreg =>
      hkk fg2 W Rn' ext he hf ho (ColsOf.shape A hRk hsk) (ColsOf.shape C hSv hsv) hreg

end Rel.Lang.Plan
