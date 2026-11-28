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

theorem Grows.iteFlat {c : Nat} {ks vs : Cols} {w : Nat} {b : Bld TabB} (hb : Grows b) :
    Grows (Plan.iteFlat c ks vs w b) := by
  unfold Plan.iteFlat
  refine hb.bind fun T => ?_
  rw [regsOf_eq, pure_bind]
  split
  · exact Grows.pure _
  · exact (Grows.throw _).bind fun _ => Grows.pure _

theorem Grows.iteT {c : Nat} {ks vs : Cols} {t e : Bld TabB} (ht : Grows t) (he : Grows e) :
    Grows (Plan.iteT c ks vs t e) := by
  unfold Plan.iteT
  rw [regsOf_eq, pure_bind]
  exact (Grows.ite (Grows.iteFlat (Grows.funT fun _ => ht)) (Grows.iteFlat (Grows.funT fun _ => he))).bind fun _ =>
    (Grows.withRegs _ _).bind fun ⟨_, _⟩ => (Grows.nth _ _ _).bind fun _ => Grows.pure _

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

/-! ### `compBlocksB`'s two plan functions, named -/

/-- `compBlocksB`'s `blk`: block `j`, the block words read off the pseudo-table `C` (`col1`). -/
def compBlkB (C R S : TabB) (j : Nat) : Bld TabB := do
  compOneB (← keepB R (← mapWB .first R.n (← col1 C.key) (← col1 C.key) [(.eq, ← u64B j)])) S

/-- `compBlocksB`'s loop function on the block `A0`, the pseudo-table `C` and the sides `R`, `S`. -/
def compLoopBody : List TabB → Bld TabB
  | [A0, C, R, S] => do
    let one ← lit (.size 1)
    let init := (← tabsRegs [A0]).toArray.push (← lit (.size 0))
    let rs ← loop C.n init "comp: a block loop ran past its blocks" (compRoundB A0 C.n one (compBlkB C R S))
    match (← tabsAt [A0] rs.toList).1 with
    | [U] => pure U
    | _ => throw "comp: the block loop's answer is not one table"
  | _ => throw "comp: not four tables"

/-- `compBlocksB`'s function on the pseudo-table `C` and the sides `R`, `S`. -/
def compBlocksBody : List TabB → Bld TabB
  | [C, R, S] => do
    let one ← lit (.size 1)
    let A0 ← compBlkB C R S (← lit (.size 0))
    iteT (← call1 (kernel% USize.decEq) #[C.n, one]) R.key S.val (pure A0) (funT [A0, C, R, S] compLoopBody)
  | _ => throw "comp: not three tables"

theorem compBlocksB_eq (R S : TabB) (nb bid : Nat) : compBlocksB R S nb bid = (do
    guard (← call1 (kernel% USize.decLt) #[nb, ← lit (.size (2 ^ 63))]) "comp: blocks past 2^63" #[nb]
    let c ← clampB R.n bid (← call1 (kernel% USize.sub) #[nb, ← lit (.size 1)])
    funT [⟨nb, [.atom "" .i64 c], []⟩, R, S] compBlocksBody) := rfl

theorem Grows.compBlkB (C R S : TabB) (j : Nat) : Grows (Plan.compBlkB C R S j) := by
  unfold Plan.compBlkB
  exact (Grows.col1 _).bind fun _ => (Grows.col1 _).bind fun _ => (Grows.u64B _).bind fun _ =>
    (Grows.mapWB _ _ _ _ _).bind fun _ => (Grows.keepB _ _).bind fun _ => Grows.compOneB _ _

theorem Grows.compRoundB (A0 : TabB) (Cn one : Nat) {blk : Nat → Bld TabB} (hb : ∀ j, Grows (blk j))
    (st : Array Nat) : Grows (Plan.compRoundB A0 Cn one blk st) := by
  unfold Plan.compRoundB
  refine (Grows.tabsAt _ _).bind fun x => ?_
  obtain ⟨Ts, js⟩ := x
  rcases Ts with _ | ⟨A, _ | ⟨A', Ts⟩⟩ <;> try exact Grows.throw _
  rcases js with _ | ⟨j, _ | ⟨j', js⟩⟩ <;> try exact Grows.throw _
  exact (Grows.call1 _ _).bind fun _ => (Grows.packT _ _).bind fun _ => (hb _).bind fun _ =>
    (Grows.unionB _ _).bind fun _ => (Grows.tabsRegs _).bind fun _ => (Grows.call1 _ _).bind fun _ =>
    (Grows.call1 _ _).bind fun _ => Grows.pure _

theorem Grows.compLoopBody (Us : List TabB) : Grows (Plan.compLoopBody Us) := by
  rcases Us with _ | ⟨A0, _ | ⟨C, _ | ⟨R, _ | ⟨S, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> try exact Grows.throw _
  unfold Plan.compLoopBody
  refine (Grows.lit _).bind fun _ => (Grows.tabsRegs _).bind fun _ => (Grows.lit _).bind fun _ =>
    (Grows.loop fun _ => Grows.compRoundB _ _ _ (fun _ => Grows.compBlkB _ _ _ _) _).bind fun _ =>
    (Grows.tabsAt _ _).bind fun x => ?_
  rcases x with ⟨_ | ⟨U, _ | _⟩, _⟩ <;> first | exact Grows.pure _ | exact Grows.throw _

theorem Grows.compBlocksBody (Us : List TabB) : Grows (Plan.compBlocksBody Us) := by
  rcases Us with _ | ⟨C, _ | ⟨R, _ | ⟨S, _ | ⟨_, _⟩⟩⟩⟩ <;> try exact Grows.throw _
  unfold Plan.compBlocksBody
  exact (Grows.lit _).bind fun _ => (Grows.lit _).bind fun _ => (Grows.compBlkB _ _ _ _).bind fun _ =>
    (Grows.call1 _ _).bind fun _ => Grows.iteT (Grows.pure _) (Grows.funT fun Us => Grows.compLoopBody Us)

theorem Typed.col1 {m : Nat} {cs : Cols} (h : AllGe m (Cols.regs cs)) : Typed m (fun r => m ≤ r) (Plan.col1 cs) := by
  unfold Plan.col1; split
  · exact Typed.pure (h _ (by simp [Cols.regs, Col.regs]))
  · exact Typed.throw _

theorem Typed.compBlkB {m j : Nat} {C R S : TabB} (hC : AllGe m (Cols.regs C.key)) (hR : AllGe m R.regs)
    (hS : AllGe m S.regs) : Typed m (fun U => AllGe m U.regs) (Plan.compBlkB C R S j) := by
  have hn : m ≤ R.n := hR _ (by rw [TabB.regs_eq]; simp)
  unfold Plan.compBlkB
  exact (Typed.col1 hC).bind fun a ha => (Typed.col1 hC).bind fun b hb => (Typed.u64B (s := j)).bind fun u hu =>
    (Typed.mapWB hn ha hb (by simp [hu])).bind fun w hw => (Typed.keepB hR hw).bind fun K hK => Typed.compOneB hK hS

theorem Typed.compRoundB {m n' : Nat} {A0 : TabB} {Cn one : Nat} {blk : Nat → Bld TabB} (hn' : m ≤ n') (hCn : m ≤ Cn)
    (hone : m ≤ one) (hb : ∀ j, m ≤ j → Typed m (fun U => AllGe m U.regs) (blk j)) :
    Typed m (fun r => (∀ a ∈ r.1, m ≤ a) ∧ m ≤ r.2)
      (Plan.compRoundB A0 Cn one blk (List.range' n' (A0.regs.length + 1)).toArray) := by
  obtain ⟨L, Y0, h1, -, -, h4⟩ := tab_spec A0
  rw [tabsRegs_eq] at h1
  obtain rfl : A0.regs = L := by simpa using pure_inj h1
  obtain ⟨V, hV, hVr, -, -, -⟩ := h4 (List.range' n' A0.regs.length) [n' + A0.regs.length] (by simp)
  rw [tabsRegs_eq] at hVr
  have hVr' : V.regs = List.range' n' A0.regs.length := by simpa using pure_inj hVr
  have hVg : AllGe m V.regs := fun a ha => by rw [hVr', List.mem_range'_1] at ha; omega
  have e : (List.range' n' (A0.regs.length + 1)).toArray.toList =
      List.range' n' A0.regs.length ++ [n' + A0.regs.length] := by
    rw [List.toList_toArray, List.range'_concat, Nat.one_mul]
  unfold Plan.compRoundB
  rw [e, hV]
  simp only [pure_bind, tabsRegs_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine (Typed.call1 ?_).bind fun j1 hj1 => (Typed.packT hVg).bind fun P hP => (hb j1 hj1).bind fun B hB =>
    (Typed.unionB hP hB).bind fun U hU => (Typed.call1 ?_).bind fun d1 hd1 => (Typed.call1 ?_).bind fun d hd =>
    Typed.pure ⟨fun a ha => ?_, hd⟩
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]; omega
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]; omega
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]; omega
  · simp only [Array.mem_push, List.mem_toArray] at ha
    rcases ha with ha | rfl
    · exact hU a ha
    · exact hj1

/-- `compLoopBody` after its two `lit`s (the round's `1` in `one`, the first block number in `z`). -/
def compLoopRest (A0 C R S : TabB) (one z : Nat) : Bld TabB := do
  let rs ← loop C.n (A0.regs.toArray.push z) "comp: a block loop ran past its blocks" (compRoundB A0 C.n one (compBlkB C R S))
  match (← tabsAt [A0] rs.toList).1 with
  | [U] => pure U
  | _ => throw "comp: the block loop's answer is not one table"

theorem compLoopBody_eq (A0 C R S : TabB) : compLoopBody [A0, C, R, S] =
    (do let one ← lit (.size 1); let z ← lit (.size 0); compLoopRest A0 C R S one z) := by
  simp only [compLoopBody, compLoopRest, tabsRegs_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil, pure_bind]

theorem Typed.compLoopRest {m one z : Nat} {A0 C R S : TabB} (hA0 : AllGe m A0.regs) (hC : AllGe m C.regs)
    (hR : AllGe m R.regs) (hS : AllGe m S.regs) (hone : m ≤ one) (hz : m ≤ z) :
    Typed m (fun U => AllGe m U.regs) (Plan.compLoopRest A0 C R S one z) := by
  have hCn : m ≤ C.n := hC _ (by rw [TabB.regs_eq]; simp)
  have hCk : AllGe m (Cols.regs C.key) := fun a ha => hC a (by rw [TabB.regs_eq]; simp [ha])
  obtain ⟨L, Y0, h1, -, -, h4⟩ := tab_spec A0
  rw [tabsRegs_eq] at h1
  obtain rfl : A0.regs = L := by simpa using pure_inj h1
  unfold Plan.compLoopRest
  refine (Typed.loop (k := C.n) (fun a ha => ?_) fun n' hn' => ?_).bind fun r hr => ?_
  · simp only [Array.mem_push, List.mem_toArray] at ha
    rcases ha with ha | rfl
    · exact hA0 a ha
    · exact hz
  · simp only [Array.size_push, List.size_toArray]
    exact Typed.compRoundB hn' hCn hone fun _ _ => Typed.compBlkB hCk hR hS
  · have hl : (r.toList.take A0.regs.length).length = A0.regs.length := by
      simp only [List.length_take, Array.length_toList, hr.1, Array.size_push, List.size_toArray]; omega
    obtain ⟨V, hV, hVr, -⟩ := h4 _ (r.toList.drop A0.regs.length) hl
    rw [List.take_append_drop] at hV
    rw [hV]
    simp only [pure_bind]
    rw [tabsRegs_eq] at hVr
    refine Typed.pure fun a ha => hr.2 a ?_
    have : a ∈ r.toList.take A0.regs.length := by simpa [← pure_inj hVr] using ha
    exact Array.mem_toList_iff.1 (List.mem_of_mem_take this)

theorem Typed.compLoopBody {m : Nat} {Us : List TabB} (hU : AllGe m (Us.flatMap TabB.regs)) :
    Typed m (fun U => AllGe m U.regs) (Plan.compLoopBody Us) := by
  rcases Us with _ | ⟨A0, _ | ⟨C, _ | ⟨R, _ | ⟨S, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> try exact Typed.throw _
  have g : ∀ T ∈ [A0, C, R, S], AllGe m T.regs := fun T hT a ha => hU a (List.mem_flatMap.2 ⟨T, hT, ha⟩)
  rw [compLoopBody_eq]
  exact (Typed.lit _).bind fun one hone => (Typed.lit _).bind fun z hz =>
    Typed.compLoopRest (g A0 (by simp)) (g C (by simp)) (g R (by simp)) (g S (by simp)) hone hz

theorem lit_bind_run {β : Type} (v : Val) (k : Nat → Bld β) (is : Array Instr) (n : Nat) (fg : Array Fun × Array Fun) :
    (Plan.lit v >>= k).run (is, n, fg) = (k n).run (is.push (.lit v), n + 1, fg) := rfl

/-- **`compLoopBody` is never spliced**: its block holds the two `lit`s and more, so its `funT` is an `apply`
    (`Typed.funTNS`' `hns`). -/
theorem compLoopBody_ns (Us : List TabB) (n : Nat) (fg : Array Fun × Array Fun) (U : TabB)
    (s' : Array Instr × Nat × Array Fun × Array Fun) (h : (compLoopBody Us).run (#[], n, fg) = .ok (U, s')) :
    spliceable s'.1 = false := by
  rcases Us with _ | ⟨A0, _ | ⟨C, _ | ⟨R, _ | ⟨S, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> try cases h
  rw [compLoopBody_eq] at h
  simp only [lit_bind_run] at h
  obtain ⟨js, fa, e, -⟩ := Typed.compLoopRest (m := 0) (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _)
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) _ _ _ _ _ _ (Nat.zero_le _) h
  have hs : ¬ (s'.1.size ≤ 1) := by rw [e]; simp; omega
  simp [spliceable, hs]

theorem Typed.compBlocksBody {m : Nat} {Us : List TabB} (hU : AllGe m (Us.flatMap TabB.regs)) :
    Typed m (fun U => AllGe m U.regs) (Plan.compBlocksBody Us) := by
  rcases Us with _ | ⟨C, _ | ⟨R, _ | ⟨S, _ | ⟨_, _⟩⟩⟩⟩ <;> try exact Typed.throw _
  have g : ∀ T ∈ [C, R, S], AllGe m T.regs := fun T hT a ha => hU a (List.mem_flatMap.2 ⟨T, hT, ha⟩)
  have hC := g C (by simp)
  have hCn : m ≤ C.n := hC _ (by rw [TabB.regs_eq]; simp)
  have hCk : AllGe m (Cols.regs C.key) := fun a ha => hC a (by rw [TabB.regs_eq]; simp [ha])
  unfold Plan.compBlocksBody
  refine (Typed.lit _).bind fun one hone => (Typed.lit _).bind fun z hz =>
    (Typed.compBlkB hCk (g R (by simp)) (g S (by simp))).bind fun A0 hA0 => (Typed.call1 ?_).bind fun d hd =>
    Typed.iteT hd (Typed.pure hA0) (Typed.funT ?_ fun Us hUs => Typed.compLoopBody hUs)
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]; omega
  · intro a ha
    obtain ⟨T, hT, hTa⟩ := List.mem_flatMap.1 ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact hA0 a hTa
    · exact hC a hTa
    · exact g _ (by simp) a hTa
    · exact g _ (by simp) a hTa

/-- **`funT_builds` for a body that builds a table**: the parameters `Ts` read `pv` in `rs`, the body on the parameter
    tables `Us` builds (in continuation form) a table of the shapes `K`, `V` holding `Y`, and `Typed` types what it
    closes over; `kk` continues on a table of those shapes holding `Y`. -/
theorem funTab_builds {A C : Obj} {Ts Us : List TabB} {b : List TabB → Bld TabB} {K V : Cols} {Y : Tab A C}
    {fg : Array Fun × Array Fun} {rs pv out : Array Val} {kk : TabB → Bld (Array Nat)}
    (hK : ColsOf A K) (hV : ColsOf C V)
    (ha : ∀ who, (Ts.flatMap TabB.regs).toArray.mapM (reg rs who) = .ok pv)
    (hUs : tabsAt Ts (List.range' rs.size (Ts.flatMap TabB.regs).length) = Pure.pure (Us, []))
    (hfo : Ordered fg.1) (hb : ∀ Ts', Grows (b Ts')) (hT : Typed rs.size (fun _ => True) (b Us))
    (hB : ∀ (kt : TabB → Bld (Array Nat)) (ot : Array Val), (∀ (fg2 : Array Fun × Array Fun) (W : TabB)
      (Rn : Array Val), Extends (rs ++ pv) Rn → Cols.shape W.key = Cols.shape K → Cols.shape W.val = Cols.shape V →
      TabHolds W Y Rn → Builds abiOf fg2 fg2 (kt W) Rn ot) → ∃ fg', Builds abiOf fg fg' (b Us >>= kt) (rs ++ pv) ot)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape K → Cols.shape W.val = Cols.shape V →
      TabHolds W Y (rs ++ ys) → ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (funT Ts b >>= kk) rs out := by
  let P : TabB → Prop := fun W => Cols.shape W.key = Cols.shape K ∧ Cols.shape W.val = Cols.shape V
  let o : Array Val := (tabVals Y).toArray
  obtain ⟨fg1, hB'⟩ := hB (answerRegs P) o fun fg2 W Rn _ hsk hsv hW =>
    Builds.answerRegs (P := P) ⟨hsk, hsv⟩ (tabsRegs_eq _) fun _ => by simpa [o] using reads_of hW
  obtain ⟨⟨a1, ha1⟩, hb1, hB1⟩ := hB'
  obtain ⟨ctys, hcl⟩ := Typed.cloTys (fg := fg) (fg1 := fg1) (k := (Ts.flatMap TabB.regs).length) (rs := rs) hT
  refine funT_builds (P := P) (Us := Us) (ctys := ctys) (o := o) (tabsRegs_eq Ts) ha hUs (hB1 #[]) hfo hb
    (fun U body xs R rtys h _ hR hy is => hcl U body _ R rtys h hR hy is) ?_
  intro U' ⟨hsk', hsv'⟩ fg2 Rr V' ys he hf ho' hRr hV'
  obtain ⟨AU, YU, u1, -, -, u4⟩ := tab_spec U'
  rw [tabsRegs_eq] at u1
  obtain rfl := (pure_inj u1).symm
  have hl : Rr.toList.length = ([U'].flatMap TabB.regs).length := by
    have h1 := mapM_ok_size (hRr "")
    simp only [o, List.size_toArray] at h1
    simp [h1, TabB.regs_length (ColsOf.shape A hK hsk') (ColsOf.shape C hV hsv') Y]
  obtain ⟨V'', f1, f2, -, f4, f5⟩ := u4 Rr.toList [] hl
  rw [List.append_nil] at f1
  obtain rfl : V' = V'' := by
    have := pure_inj (hV'.symm.trans f1); simp only [Prod.mk.injEq, List.cons.injEq, and_true] at this; exact this
  rw [tabsRegs_eq] at f2
  have f2' := pure_inj f2
  have hread := holds_of_reg (hRr "")
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at f2'
  rw [← f2'] at hread
  obtain ⟨e1', he1⟩ := he
  exact hkk fg2 V' ys ⟨a1 ++ e1', by rw [he1, ha1, Array.append_assoc]⟩ (by rw [hf]; exact hb1) ho'
    (f4.trans hsk') (f5.trans hsv') (by simpa [o] using hread)

/-- `Typed.funBOf` for a body that is never spliced: the `apply` reads `args` (any registers, also below `m`) and the
    closure, each typed by the function's parameter, so `args` need not be above `m`. -/
theorem Typed.funBNS {α : Type} {m : Nat} {Q : Array Nat × List Ty × α → Prop} {tys : List Ty}
    {args : List Nat} {b : List Nat → Bld (Array Nat × List Ty × α)}
    (hb : ∀ ps, (∀ p ∈ ps, m ≤ p) → ps.length = tys.length → Typed m Q (b ps))
    (hns : ∀ n fg x s', (b (List.range' n tys.length)).run (#[], n + tys.length, fg) = .ok (x, s') →
      spliceable s'.1 = false) :
    Typed m (fun x : Array Nat × α => (∀ a ∈ x.1, m ≤ a) ∧ ∃ r rtys, Q (r, rtys, x.2) ∧ r.size = x.1.size)
      (Plan.funB tys args b) := by
  intro is n fs gs x s' hm h
  by_cases hk : args.length = tys.length
  · cases hr : (b (List.range' n tys.length)).run (#[], n + tys.length, fs, gs) with
    | error _ => simp [Plan.funB, StateT.run_bind, StateT.run_get, StateT.run_monadLift, liftM, monadLift_self, hk, hr,
        err_bind_eq, Functor.map, Except.map] at h
    | ok p =>
      obtain ⟨⟨r, rtys, x0⟩, body, n1, fs1, gs1⟩ := p
      have hC : spliceable body = false := hns n (fs, gs) _ _ hr
      obtain ⟨js, fa, e1, f1, l1, q2, t1⟩ :=
        hb _ (fun p hp => by simp [List.mem_range'] at hp; omega) (by simp) _ _ _ _ _ _ (by omega) hr
      simp only [Array.empty_append] at e1 f1 l1
      subst e1 f1
      simp [Plan.funB, StateT.run_bind, StateT.run_get, StateT.run_monadLift, liftM, monadLift_self, hk, hr, hC,
        ok_bind, -List.filter_append] at h
      obtain ⟨ctys, hty, h⟩ := bind_ok h
      simp only [Functor.map, Except.map] at h
      split at h
      · cases h
      · rename_i v hv
        obtain ⟨r', s1⟩ := v
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        have hcl : ctys.length = (((readsB n body.toList ++ r.toList).filter (· < n)).eraseDups).length := by
          revert hty
          cases hc : Plan.cloTys (fs ++ fa) gs1 is body n r rtys
              ((readsB n body.toList ++ r.toList).filter (· < n)).eraseDups with
          | error e => intro h; cases h
          | ok ts => intro h; cases h; exact cloTys_length hc
        rcases addFun_spec (fs ++ fa) _ with ⟨e2, hlt, hget⟩ | ⟨e2, e1⟩
        · rw [e2] at hv
          rw [apply_run hlt, emit_ok] at hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hv)
          refine ⟨#[.apply _ _], fa, rfl, rfl, Nat.le_add_right _ _, ⟨fun a ha => ?_, r, rtys, q2, by simp⟩,
            fun y a ha hlt' => ?_⟩
          · simp at ha; omega
          · simp only [readsB, reads, List.append_nil] at ha
            obtain ⟨j, hj, hjl⟩ := idxOf?_of_mem ha
            have hjt : j < (tys ++ ctys).toArray.size := by
              simp only [List.length_append] at hjl; simp only [List.size_toArray, List.length_append]; omega
            refine ⟨((tys ++ ctys).toArray)[j], ?_⟩
            show (useTy _ a (.apply _ _) <|> none) = _
            simp only [useTy, hj, Option.bind_some, Array.getElem?_append_left hlt,
              Array.getElem?_eq_getElem hlt, hget, Option.bind_some]
            try rw [Array.getElem?_eq_getElem hjt]
            try rfl
        · rw [e2] at hv
          rw [apply_run (by rw [e1]; simp), emit_ok] at hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hv)
          refine ⟨#[.apply _ _], fa.push _, rfl, Array.push_append, Nat.le_add_right _ _,
            ⟨fun a ha => ?_, r, rtys, q2, by simp⟩, fun y a ha hlt' => ?_⟩
          · simp at ha; omega
          · simp only [readsB, reads, List.append_nil] at ha
            obtain ⟨j, hj, hjl⟩ := idxOf?_of_mem ha
            have hjt : j < (tys ++ ctys).toArray.size := by
              simp only [List.length_append] at hjl; simp only [List.size_toArray, List.length_append]; omega
            refine ⟨((tys ++ ctys).toArray)[j], ?_⟩
            show (useTy _ a (.apply _ _) <|> none) = _
            simp only [useTy, hj, Option.bind_some, e1]
            rw [Array.getElem?_append_left (by simp), Array.getElem?_push_size, Option.bind_some]
            try rw [Array.getElem?_eq_getElem hjt]
            try rfl
  · simp [Plan.funB, StateT.run_bind, StateT.run_get, hk, throwThe, MonadExceptOf.throw, MonadExcept.throw,
      err_bind_eq, Functor.map, Except.map] at h

/-- `Typed.funT` for a body that is never spliced (`Typed.funBNS`): the tables `Ts` may lie below `m`, as an `iteT`
    branch's `funT []` closes over the tables of the enclosing function. -/
theorem Typed.funTNS {m : Nat} {Ts : List TabB} {b : List TabB → Bld TabB}
    (hb : ∀ Us, AllGe m (Us.flatMap TabB.regs) → Typed m (fun _ => True) (b Us))
    (hns : ∀ Us n fg U s', (b Us).run (#[], n, fg) = .ok (U, s') → spliceable s'.1 = false) :
    Typed m (fun V => AllGe m V.regs) (Plan.funT Ts b) := by
  obtain ⟨A, Y, h1, h2, h3, -⟩ := tabs_spec Ts
  obtain rfl : A = Ts.flatMap TabB.regs := pure_inj (h1.symm.trans (tabsRegs_eq Ts))
  unfold Plan.funT
  rw [h2, h1]
  simp only [pure_bind]
  refine (Typed.funBNS (Q := fun x => x.2.2.regs = x.1.toList) (fun ps hps hlen => ?_) ?_).bind fun x hx => ?_
  · obtain ⟨Us, hat, hUs⟩ := tabsAt_regs (Ts := Ts) (ps := ps) (hlen.trans h3.symm)
    rw [hat]
    simp only [pure_bind]
    refine (hb Us (by rw [hUs]; exact hps)).bind fun U _ => ?_
    obtain ⟨A1, Y1, g1, g2, -⟩ := tab_spec U
    obtain rfl : A1 = U.regs := by simpa using pure_inj (g1.symm.trans (tabsRegs_eq [U]))
    rw [g1, g2]
    simp only [pure_bind]
    exact Typed.pure (by simp)
  · intro n fg x s' h
    obtain ⟨Us, hat, -⟩ := tabsAt_regs (Ts := Ts) (ps := List.range' n Y.flatten.length) (by simp [h3])
    simp only [hat, pure_bind, StateT.run_bind] at h
    rcases hU : (b Us).run (#[], n + Y.flatten.length, fg) with e | ⟨U, s1⟩
    · rw [hU] at h; cases h
    · rw [hU, ok_bind] at h
      obtain ⟨A1, Y1, g1, g2, -⟩ := tab_spec U
      simp only [g1, g2, pure_bind, StateT.run_pure] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact hns Us _ fg U s1 hU
  · rcases x with ⟨rs, U⟩
    obtain ⟨hrs, r, rtys, hr, hsz⟩ := hx
    simp only at hrs hr hsz
    obtain ⟨Us, hat, hUs⟩ := tabsAt_regs (Ts := [U]) (ps := rs.toList) (by simp [hr, hsz])
    dsimp only
    rw [hat]
    simp only [pure_bind]
    rcases Us with _ | ⟨V, _ | ⟨W, Vs⟩⟩
    · exact Typed.throw _
    · refine Typed.pure fun a ha => hrs a ?_
      have : V.regs = rs.toList := by simpa using hUs
      rw [this] at ha; simpa using ha
    · exact Typed.throw _

/-! ### The loop function builds `compBlocks`' fold -/

/-- On a pseudo-table of one atom column `cr`, `compBlkB` is `compBlockB` of the words in `cr`. -/
theorem compBlkB_atom (cn cr : Nat) (p : String) (t : QAtomicType) (cvs : Cols) (R S : TabB) :
    compBlkB ⟨cn, [.atom p t cr], cvs⟩ R S = compBlockB R S cr := by
  funext j; simp only [compBlkB, compBlockB, col1, pure_bind]

/-- **The loop function's body builds `compBlocks`' fold** for `nb ≥ 2` blocks: `A1` holds the block `X0`, the
    pseudo-table's count register `cn` the block count `nb` and its column `cr` the clamped words `ce`, `R1`, `S1` hold
    `R`, `S`; where the fold over the blocks `1 … nb - 1` answers `Yf` from `X0`, `kk` continues on a table of `A1`'s
    shape holding `Yf` (in the continuation form `iteFlat_builds` and `funT_builds` read). -/
theorem compLoopBody_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A B C : Obj) {R : Tab A B}
    {S : Tab B C} {X0 Yf : Tab A C} {A1 R1 S1 : TabB} {cn cr : Nat} {p : String} {t : QAtomicType} {cvs : Cols}
    {ce : Enc} {nb : USize} {fg : Array Fun × Array Fun} {rs out : Array Val} {kk : TabB → Bld (Array Nat)}
    (hP : TabSpec A C Tab.pack (fun T => packT T))
    (hAk : ColsOf A A1.key) (hAv : ColsOf C A1.val) (hRk : ColsOf A R1.key) (hRv : ColsOf B R1.val)
    (hSk : ColsOf B S1.key) (hSv : ColsOf C S1.val) (hA : TabHolds A1 X0 rs) (hR : TabHolds R1 R rs)
    (hS : TabHolds S1 S rs) (hcn : rs[cn]? = some (.size nb)) (hce : rs[cr]? = some (Reg.put ce))
    (h2 : 2 ≤ nb.toNat) (hnb : nb.toNat < 2 ^ 63)
    (hk : ∀ (jv : USize) (X : Tab A C), Tab.compBlock R S ce jv.toNat = .ok X → ∀ m Rk,
      colMap .first R.n ce ce .i64 .i64 [] [(.eq, jv.toUInt64)] = .ok m → R.keep m = .ok Rk →
      (∀ K sel, whereCol R.n m = .ok (K, sel) → WhereAgree R.n K m sel) ∧ CompPre A B C Rk S ∧ CompPost A B C Rk X)
    (hY : (List.range (nb.toNat - 1)).foldlM (fun acc j => do (← acc.pack).union (← Tab.compBlock R S ce (j + 1))) X0 =
      .ok Yf)
    (hU : ∀ i acc Y Bk, i + 1 < nb.toNat →
      (List.range i).foldlM (fun acc j => do (← acc.pack).union (← Tab.compBlock R S ce (j + 1))) X0 = .ok acc →
      acc.pack = .ok Y → Tab.compBlock R S ce (i + 1) = .ok Bk → UnionPre Y Bk) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (Rn : Array Val), Extends rs Rn →
      Cols.shape W.key = Cols.shape A1.key → Cols.shape W.val = Cols.shape A1.val → TabHolds W Yf Rn →
      Builds abiOf fg2 fg2 (kk W) Rn out) :
    ∃ fg', Builds abiOf fg fg' (compLoopBody [A1, ⟨cn, [.atom p t cr], cvs⟩, R1, S1] >>= kk) rs out := by
  obtain ⟨L, Y0, h1, -, -, h4⟩ := tab_spec A1
  have hL : L = A1.regs := by rw [tabsRegs_eq] at h1; simpa using (pure_inj h1).symm
  subst hL
  have hl : A1.regs.length = (tabVals X0).length := mapM_get_length hA
  simp only [compLoopBody, compBlkB_atom, tabsRegs_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil, bind_assoc,
    pure_bind]
  refine litE fun one R0 hone m0 => litE fun z R2 hz m1 => ?_
  have hE : Extends rs R2 := fun h => m1 (m0 h)
  have hi : (A1.regs.toArray.push z).mapM (reg R2 "loop") = .ok (tabVals X0 ++ [Val.size 0]).toArray := by
    rw [show A1.regs.toArray.push z = (A1.regs ++ [z]).toArray by simp]
    exact reads_of (by rw [List.mapM_append, mapM_extends hE hA]; simp [hz])
  have hB := @compBlockB_spec hc h63 A B C _ _ _ _ _ _ _ hRk hRv hSk hSv (mapM_extends hE hR) (mapM_extends hE hS) (hE hce) hk
  obtain ⟨fg1, i, hL⟩ := compLoop_builds (msg := "comp: a block loop ran past its blocks") hc h63 hP hB hAk hAv
    (hE hcn) (m1 hone) hfo (by simp) hi h2 hnb hY hU
  refine ⟨fg1, Builds.bind hL fun r xs hr => ?_⟩
  have hrr := holds_of_reg (hr "")
  have hlr : (r.toList.take A1.regs.length).length = A1.regs.length := by
    have := mapM_ok_size (hr ""); simp only [List.size_toArray, List.length_append, List.length_singleton] at this
    have := TabB.regs_length hAk hAv Yf; simp only [List.length_take, Array.length_toList]; omega
  obtain ⟨V, hV, hVr, -, hVk, hVv⟩ := h4 _ (r.toList.drop A1.regs.length) hlr
  rw [List.take_append_drop] at hV
  rw [hV]
  simp only [pure_bind]
  rw [tabsRegs_eq] at hVr
  have hVr' : V.regs = r.toList.take A1.regs.length := by simpa using pure_inj hVr
  rw [← List.take_append_drop A1.regs.length r.toList] at hrr
  obtain ⟨hY1, -⟩ := mapM_split (by rw [hlr, TabB.regs_length hAk hAv Yf]) hrr
  exact hkk fg1 V (R2 ++ xs) (fun h => get_app (hE h)) hVk hVv (by unfold TabHolds; rw [hVr']; exact hY1)

/-! ### `compBlocksB` builds `Tab.compBlocks` -/

/-- `USize.decEq` of two registers holding the sizes `x`, `y` answers the bit `x = y`, the functions free to grow
    after it (`decEq_builds` fixes them). -/
theorem decEq_buildsE {fg : Array Fun × Array Fun} {rs : Array Val} {a b : Nat} {x y : USize}
    (ha : rs[a]? = some (.size x)) (hb : rs[b]? = some (.size y)) {c : Nat → Bld (Array Nat)} {out : Array Val}
    (hc : ∀ (r : Nat) (R : Array Val), R[r]? = some (.bit (decide (x = y))) → Extends rs R →
      ∃ fg', Builds abiOf fg fg' (c r) R out) :
    ∃ fg', Builds abiOf fg fg' (call1 (kernel% USize.decEq) #[a, b] >>= c) rs out := by
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  exact call1E (vs := #[.size x, .size y]) (v := .bit (decide (x = y))) (by abiK) rfl
    (reads_of (l := [a, b]) (vs := [.size x, .size y]) (by simp [ha, hb])) (by simp [arg, hsz, Out.out]; rfl) rfl hc

/-- The tables `Ts` read from consecutive registers from `s`, the registers `rest` after them left: tables of `Ts`'
    shapes whose registers are those, in order (`tabsAt_two` at any number of tables). -/
theorem tabsAt_range (Ts : List TabB) (s : Nat) (rest : List Nat) : ∃ Us,
    tabsAt Ts (List.range' s (Ts.flatMap TabB.regs).length ++ rest) = Pure.pure (Us, rest) ∧
    Us.map (fun U => (Cols.shape U.key, Cols.shape U.val)) = Ts.map (fun T => (Cols.shape T.key, Cols.shape T.val)) ∧
    Us.flatMap TabB.regs = List.range' s (Ts.flatMap TabB.regs).length := by
  induction hn : Ts.length generalizing Ts rest with
  | zero =>
    obtain rfl : Ts = [] := List.length_eq_zero_iff.1 hn
    exact ⟨[], by simp [tabsAt], rfl, rfl⟩
  | succ k ih =>
    obtain rfl | ⟨Ts, T, rfl⟩ := List.eq_nil_or_concat Ts
    · simp at hn
    rw [List.concat_eq_append] at hn ⊢
    obtain ⟨A1, Y1, t1, -, -, t4⟩ := tab_spec T
    rw [tabsRegs_eq] at t1
    obtain rfl := pure_inj t1
    obtain ⟨V, v1, v2, -, v4, v5⟩ := t4 (List.range' (s + (Ts.flatMap TabB.regs).length) T.regs.length) rest (by simp)
    obtain ⟨Us, e1, e2, e3⟩ := ih Ts (List.range' (s + (Ts.flatMap TabB.regs).length) T.regs.length ++ rest)
      (by simpa using hn)
    have hV : V.regs = List.range' (s + (Ts.flatMap TabB.regs).length) T.regs.length := by
      rw [tabsRegs_eq] at v2; simpa using pure_inj v2
    have hl : ((Ts ++ [T]).flatMap TabB.regs).length = (Ts.flatMap TabB.regs).length + T.regs.length := by simp
    refine ⟨Us ++ [V], ?_, by simp [e2, v4, v5], ?_⟩
    · rw [tabsAt_append, hl, ← List.range'_append_1, List.append_assoc, e1]
      simp only [pure_bind]; rw [v1]; rfl
    · rw [List.flatMap_append, e3, hl, ← List.range'_append_1]; simp [hV]

/-- `funTab_builds` at no parameter tables: an `iteT` branch's `funT []`. -/
theorem funTab0_builds {A C : Obj} {b : List TabB → Bld TabB} {K V : Cols} {Y : Tab A C}
    {fg : Array Fun × Array Fun} {rs out : Array Val} {kk : TabB → Bld (Array Nat)}
    (hK : ColsOf A K) (hV : ColsOf C V) (hfo : Ordered fg.1) (hb : ∀ Ts', Grows (b Ts'))
    (hT : Typed rs.size (fun _ => True) (b []))
    (hB : ∀ (kt : TabB → Bld (Array Nat)) (ot : Array Val), (∀ (fg2 : Array Fun × Array Fun) (W : TabB)
      (Rn : Array Val), Extends rs Rn → Cols.shape W.key = Cols.shape K → Cols.shape W.val = Cols.shape V →
      TabHolds W Y Rn → Builds abiOf fg2 fg2 (kt W) Rn ot) → ∃ fg', Builds abiOf fg fg' (b [] >>= kt) rs ot)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape K → Cols.shape W.val = Cols.shape V →
      TabHolds W Y (rs ++ ys) → ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (funT [] b >>= kk) rs out := by
  have e : rs ++ (#[] : Array Val) = rs := Array.append_empty
  exact funTab_builds (Us := []) (pv := #[]) hK hV (fun _ => by simp; rfl) rfl hfo hb hT (by simp only [e]; exact hB) hkk

/-- **G2**: the loop branch of `compBlocksBody`'s `iteT` (on the pseudo-table `C`, the sides `R`, `S` and a block `A0` of
    their shapes) runs. At one block it is the untaken branch, which `ite` builds all the same, and no lemma proves that
    a builder's run succeeds (as E12), so the block lemmas take it as a premise. -/
def CompLoopRuns (C R S : TabB) : Prop := ∀ (A0 : TabB) (c n : Nat) (fg1 : Array Fun × Array Fun),
  Cols.shape A0.key = Cols.shape R.key → Cols.shape A0.val = Cols.shape S.val → ∃ re je n' fg2,
    (iteFlat c R.key S.val (Cols.regs (R.key ++ S.val)).length (funT [] fun _ => funT [A0, C, R, S] compLoopBody)).run
      (#[], n, fg1) = .ok (re, je, n', fg2) ∧ (∃ a, fg2.1 = fg1.1 ++ a) ∧ GExt fg1.2 fg2.2

/-- **`compBlocksBody` builds `compBlocks`' answer** on the pseudo-table `⟨cn, [.atom p t cr], []⟩` (the count `nb`,
    the clamped block words `ce`) and the sides `R1`, `S1` holding `R`, `S`: block 0 is `X0`, and the fold over the
    blocks `1 … nb - 1` answers `Yf` from it. At `nb = 1` the untaken loop branch runs (`he`, G2). -/
theorem compBlocksBody_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A B C : Obj) {R : Tab A B}
    {S : Tab B C} {X0 Yf : Tab A C} {R1 S1 : TabB} {cn cr : Nat} {p : String} {t : QAtomicType} {ce : Enc}
    {nb : USize} {fg : Array Fun × Array Fun} {rs out : Array Val} {kk : TabB → Bld (Array Nat)}
    (hP : TabSpec A C Tab.pack (fun T => packT T))
    (hRk : ColsOf A R1.key) (hRv : ColsOf B R1.val) (hSk : ColsOf B S1.key) (hSv : ColsOf C S1.val)
    (hR : TabHolds R1 R rs) (hS : TabHolds S1 S rs) (hcn : rs[cn]? = some (.size nb))
    (hce : rs[cr]? = some (Reg.put ce)) (h1 : 1 ≤ nb.toNat) (hnb : nb.toNat < 2 ^ 63)
    (hk : ∀ (jv : USize) (X : Tab A C), Tab.compBlock R S ce jv.toNat = .ok X → ∀ m Rk,
      colMap .first R.n ce ce .i64 .i64 [] [(.eq, jv.toUInt64)] = .ok m → R.keep m = .ok Rk →
      (∀ K sel, whereCol R.n m = .ok (K, sel) → WhereAgree R.n K m sel) ∧ CompPre A B C Rk S ∧ CompPost A B C Rk X)
    (h0 : Tab.compBlock R S ce 0 = .ok X0)
    (hY : (List.range (nb.toNat - 1)).foldlM (fun acc j => do (← acc.pack).union (← Tab.compBlock R S ce (j + 1))) X0 =
      .ok Yf)
    (hU : ∀ i acc Y Bk, i + 1 < nb.toNat →
      (List.range i).foldlM (fun acc j => do (← acc.pack).union (← Tab.compBlock R S ce (j + 1))) X0 = .ok acc →
      acc.pack = .ok Y → Tab.compBlock R S ce (i + 1) = .ok Bk → UnionPre Y Bk)
    (he : nb.toNat = 1 → CompLoopRuns ⟨cn, [.atom p t cr], []⟩ R1 S1) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (Rn : Array Val), Extends rs Rn →
      Cols.shape W.key = Cols.shape R1.key → Cols.shape W.val = Cols.shape S1.val → TabHolds W Yf Rn →
      Builds abiOf fg2 fg2 (kk W) Rn out) :
    ∃ fg', Builds abiOf fg fg' (compBlocksBody [⟨cn, [.atom p t cr], []⟩, R1, S1] >>= kk) rs out := by
  simp only [compBlocksBody, compBlkB_atom, bind_assoc]
  refine litE fun one R0 hone m0 => litE fun z R2 hz m1 => ?_
  have hE : Extends rs R2 := fun h => m1 (m0 h)
  have h0' : Tab.compBlock R S ce (0 : USize).toNat = .ok X0 := by simpa using h0
  refine compBlockB_builds hc h63 A B C hRk hRv hSk hSv (mapM_extends hE hR) (mapM_extends hE hS) (hE hce) hz h0'
    (hk 0 X0 h0') hfo fun fg2 W R3 ext3 _ _ ho3 hWk hWv hW => ?_
  refine decEq_buildsE (ext3 (hE hcn)) (ext3 (m1 hone)) fun d R4 hd m4 => ?_
  have hE4 : Extends rs R4 := fun h => m4 (ext3 (hE h))
  have hW4 : TabHolds W X0 R4 := mapM_extends m4 hW
  have hkk' : ∀ {T : Tab A C}, T = Yf → ∀ (fg5 : Array Fun × Array Fun) (U : TabB) (ys : Array Val),
      (∃ a, fg5.1 = fg2.1 ++ a) → GExt fg2.2 fg5.2 → Cols.shape U.key = Cols.shape R1.key →
      Cols.shape U.val = Cols.shape S1.val →
      U.regs.mapM (fun i => (R4 ++ ys)[i]?) = some (.size T.n :: (T.key.regVals ++ T.val.regVals)) →
      ∃ fg', Builds abiOf fg5 fg' (kk U) (R4 ++ ys) out := by
    rintro T rfl fg5 U ys _ _ hUk hUv hU
    exact ⟨fg5, hkk fg5 U (R4 ++ ys) (fun h => get_app (hE4 h)) hUk hUv hU⟩
  -- the `then` branch `pure A0`, block 0 (`funT []` of it)
  have ht : ∀ (kt : TabB → Bld (Array Nat)) (ot : Array Val), (∀ (fg5 : Array Fun × Array Fun) (U : TabB)
      (Rn : Array Val), Extends R4 Rn → Cols.shape U.key = Cols.shape R1.key → Cols.shape U.val = Cols.shape S1.val →
      U.regs.mapM (fun i => Rn[i]?) = some (.size X0.n :: (X0.key.regVals ++ X0.val.regVals)) →
      Builds abiOf fg5 fg5 (kt U) Rn ot) →
      ∃ fg', Builds abiOf fg2 fg' (funT [] (fun _ => Pure.pure W) >>= kt) R4 ot := fun kt ot hc' =>
    funTab0_builds (Y := X0) hRk hSv ho3 (fun _ => Grows.pure _) (Typed.pure trivial)
      (fun kt' ot' h' => ⟨fg2, by rw [pure_bind]; exact h' fg2 W R4 (fun h => h) hWk hWv hW4⟩)
      fun fg5 U ys _ _ _ s1 s2 h => ⟨fg5, hc' fg5 U (R4 ++ ys) (fun h => get_app h) s1 s2 h⟩
  by_cases h1' : nb.toNat = 1
  · have hn1 : nb = 1 := USize.toNat_inj.1 (by simpa using h1')
    have hY0 : X0 = Yf := by
      rw [h1'] at hY; exact Except.ok.inj hY
    refine iteT_true_builds (T := X0) hRk hSv (by simpa [hn1] using hd) ht (fun fg1 _ _ => he h1' W d R4.size fg1 hWk hWv)
      (hkk' hY0)
  · have h2 : 2 ≤ nb.toNat := by omega
    have hd' : R4[d]? = some (.bit false) := by
      have : nb ≠ 1 := fun h => h1' (by simp [h])
      simpa [this] using hd
    obtain ⟨fgt, hBt⟩ := iteFlat_builds (c := d) hRk hSv ht
    have hot : Ordered fgt.1 := Builds.ordered hBt (Grows.iteFlat (Grows.funT fun _ => Grows.pure _)) ho3
    obtain ⟨hf1, hg1, hat⟩ := hBt
    obtain ⟨js, xs, r, hr, -, -⟩ := hat #[]
    refine iteT_false_builds (T := Yf) hRk hSv hd' hr ⟨hf1, hg1⟩ (fun kt ot hc' => ?_) (hkk' rfl)
    -- the `else` branch: `funT []` of the loop function's `funT` over `[A0, C, R, S]`
    refine funTab0_builds (Y := Yf) hRk hSv hot (fun _ => Grows.funT fun Us => Grows.compLoopBody Us)
      ((Typed.funTNS (fun Us hU => (Typed.compLoopBody hU).mono fun _ _ => trivial) compLoopBody_ns).mono
        fun _ _ => trivial) (fun kt' ot' h' => ?_)
      fun fg5 U ys _ _ _ s1 s2 h => ⟨fg5, hc' fg5 U (R4 ++ ys) (fun h => get_app h) s1 s2 h⟩
    obtain ⟨Us, hUs, hsh, hreg⟩ := tabsAt_range [W, ⟨cn, [.atom p t cr], []⟩, R1, S1] R4.size []
    rw [List.append_nil] at hUs
    have hpv : ([W, ⟨cn, [.atom p t cr], []⟩, R1, S1].flatMap TabB.regs).mapM (fun i => R4[i]?) =
        some (tabVals X0 ++ ([.size nb, Reg.put ce] ++ (tabVals R ++ tabVals S))) := by
      unfold TabHolds at hW4
      rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mapM_append, List.mapM_append, List.mapM_append, hW4, mapM_extends hE4 hR,
        mapM_extends hE4 hS]
      simp [TabB.regs, Cols.regs, Col.regs, hE4 hcn, hE4 hce]
    have hall := mapM_range_append R4 (tabVals X0 ++ ([.size nb, Reg.put ce] ++ (tabVals R ++ tabVals S)))
    rw [← mapM_get_length hpv, ← hreg] at hall
    have hge : AllGe R4.size (Us.flatMap TabB.regs) := fun a ha => by
      rw [hreg] at ha; exact (List.mem_range'_1.1 ha).1
    obtain ⟨U1, U2, U3, U4, rfl⟩ : ∃ U1 U2 U3 U4, Us = [U1, U2, U3, U4] := by
      have hl : Us.length = 4 := by simpa using congrArg List.length hsh
      rcases Us with _ | ⟨U1, _ | ⟨U2, _ | ⟨U3, _ | ⟨U4, _ | ⟨U5, Us⟩⟩⟩⟩⟩ <;> simp at hl
      exact ⟨U1, U2, U3, U4, rfl⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hsh
    obtain ⟨⟨s1k, s1v⟩, ⟨s2k, s2v⟩, ⟨s3k, s3v⟩, ⟨s4k, s4v⟩⟩ := hsh
    obtain ⟨n2, k2, v2⟩ := U2
    obtain ⟨c2, rfl, hc2⟩ := Cols.shape_singleton s2k
    obtain rfl : v2 = [] := by cases v2 with | nil => rfl | cons _ _ => simp [Cols.shape] at s2v
    obtain ⟨p2, t2, e2, rfl⟩ : ∃ p2 t2 e2, c2 = .atom p2 t2 e2 := by
      cases c2 with
      | atom p2 t2 e2 => exact ⟨p2, t2, e2, rfl⟩
      | arr => simp [Col.shape] at hc2
      | sum => simp [Col.shape] at hc2
    have hA1k : ColsOf A U1.key := ColsOf.shape A hRk (s1k.trans hWk)
    have hA1v : ColsOf C U1.val := ColsOf.shape C hSv (s1v.trans hWv)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hall
    obtain ⟨hU1, hall⟩ := mapM_split (by rw [TabB.regs_length hA1k hA1v X0]) hall
    obtain ⟨hU2, hall⟩ := mapM_split (by simp [TabB.regs, Cols.regs, Col.regs]) hall
    obtain ⟨hU3, hU4⟩ := mapM_split (by rw [TabB.regs_length (ColsOf.shape A hRk s3k) (ColsOf.shape B hRv s3v) R]) hall
    have hU2' : [n2, e2].mapM (fun i => (R4 ++ (tabVals X0 ++ ([.size nb, Reg.put ce] ++
        (tabVals R ++ tabVals S))).toArray)[i]?) = some [.size nb, Reg.put ce] := hU2
    obtain ⟨hcn', hU2''⟩ := mapM_get_cons hU2'
    refine funTab_builds (K := R1.key) (V := S1.val) hRk hSv (fun _ => reads_of hpv) hUs hot
      (fun Ts => Grows.compLoopBody Ts) ((Typed.compLoopBody hge).mono fun _ _ => trivial) (fun kt2 ot2 h2' => ?_)
      fun fg6 U ys _ _ _ s1 s2 h => ⟨fg6, h' fg6 U (R4 ++ ys) (fun h => get_app h) s1 s2 h⟩
    exact compLoopBody_builds hc h63 A B C hP hA1k hA1v (ColsOf.shape A hRk s3k) (ColsOf.shape B hRv s3v)
      (ColsOf.shape B hSk s4k) (ColsOf.shape C hSv s4v) hU1 hU3 hU4 hcn' (mapM_get_cons hU2'').1 h2 hnb hk hY hU
      hot fun fg6 U Rn ext s1 s2 h => h2' fg6 U Rn ext (s1.trans (s1k.trans hWk)) (s2.trans (s1v.trans hWv)) h

theorem Free.clampB (n x c : Nat) : Free (Plan.clampB n x c) := by
  unfold Plan.clampB u64B
  exact (Free.lit _).bind fun _ => (Free.call1 _ _).bind fun _ => Free.mapWB _ _ _ _ _

/-- **`compBlocksB` builds `Tab.compBlocks`**: `R'`, `S'` hold `R`, `S` in `rs`, the register `nb` the block count
    `nv ≥ 1` and `bid` the block words `X`. `hk`, `hU` are `compBlocksBody_builds`' premises at the clamped words `Y`, `he`
    its G2 at the parameter tables; `kk` continues on a table of `R'`'s key and `S'`'s value shape holding `T`. -/
theorem compBlocksB_builds (hc : CatOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A B C : Obj) {R : Tab A B}
    {S : Tab B C} {T : Tab A C} {R' S' : TabB} {nb bid : Nat} {nv : USize} {X : Arr .i64 R.n}
    {fg : Array Fun × Array Fun} {rs out : Array Val} {kk : TabB → Bld (Array Nat)}
    (hP : TabSpec A C Tab.pack (fun T => packT T))
    (hRk : ColsOf A R'.key) (hRv : ColsOf B R'.val) (hSk : ColsOf B S'.key) (hSv : ColsOf C S'.val)
    (hR : TabHolds R' R rs) (hS : TabHolds S' S rs) (hnb : rs[nb]? = some (.size nv))
    (hbid : rs[bid]? = some (Reg.put X.enc)) (hpos : 0 < nv.toNat) (hT : Tab.compBlocks R S nv.toNat X = .ok T)
    (hk : ∀ Y : Arr .i64 R.n, X.clampShift (nv.toNat - 1).toUInt64 0 = .ok Y → ∀ (jv : USize) (Xb : Tab A C),
      Tab.compBlock R S Y.enc jv.toNat = .ok Xb → ∀ m Rk,
      colMap .first R.n Y.enc Y.enc .i64 .i64 [] [(.eq, jv.toUInt64)] = .ok m → R.keep m = .ok Rk →
      (∀ K sel, whereCol R.n m = .ok (K, sel) → WhereAgree R.n K m sel) ∧ CompPre A B C Rk S ∧ CompPost A B C Rk Xb)
    (hU : ∀ Y : Arr .i64 R.n, X.clampShift (nv.toNat - 1).toUInt64 0 = .ok Y → ∀ X0,
      Tab.compBlock R S Y.enc 0 = .ok X0 → ∀ i acc Yb Bk, i + 1 < nv.toNat →
      (List.range i).foldlM (fun acc j => do (← acc.pack).union (← Tab.compBlock R S Y.enc (j + 1))) X0 = .ok acc →
      acc.pack = .ok Yb → Tab.compBlock R S Y.enc (i + 1) = .ok Bk → UnionPre Yb Bk)
    (he : nv.toNat = 1 → ∀ (cn cr : Nat) (R1 S1 : TabB), Cols.shape R1.key = Cols.shape R'.key →
      Cols.shape R1.val = Cols.shape R'.val → Cols.shape S1.key = Cols.shape S'.key →
      Cols.shape S1.val = Cols.shape S'.val → CompLoopRuns ⟨cn, [.atom "" .i64 cr], []⟩ R1 S1)
    (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (Rn : Array Val), Extends rs Rn → (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Cols.shape W.key = Cols.shape R'.key → Cols.shape W.val = Cols.shape S'.val →
      TabHolds W T Rn → ∃ fg', Builds abiOf fg2 fg' (kk W) Rn out) :
    ∃ fg', Builds abiOf fg fg' (compBlocksB R' S' nb bid >>= kk) rs out := by
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  have hRn : rs[R'.n]? = some (.size R.n) := (mapM_get_cons (l := Cols.regs (R'.key ++ R'.val)) hR).1
  unfold Tab.compBlocks at hT
  have hlt : nv.toNat < 2 ^ 63 := Nat.lt_of_not_le fun h => by
    simp only [if_pos h] at hT
    first | cases hT | exact Except.noConfusion hT | simp at hT
  simp only [if_neg (show ¬ 2 ^ 63 ≤ nv.toNat by omega), pure_bind] at hT
  obtain ⟨Y, hY, hT⟩ := except_bind_ok hT
  obtain ⟨X0, h0, hT⟩ := except_bind_ok hT
  rw [← Array.foldlM_toList, Array.toList_range] at hT
  have hlt' : nv < 2 ^ 63 := by rw [USize.lt_iff_toNat_lt, h63]; exact hlt
  have hle1 : (1 : USize) ≤ nv := USize.le_iff_toNat_le.2 (by simp; omega)
  have hcl : Arr.clampShift (nv - 1).toUInt64 0 X = .ok Y := by
    have e : (nv - 1).toNat = nv.toNat - 1 := by rw [USize.toNat_sub_of_le _ _ hle1]; simp
    rw [show (nv - 1).toUInt64 = (nv.toNat - 1).toUInt64 from
      UInt64.toNat.inj (by rw [USize.toNat_toUInt64, e, UInt64.toNat_ofNat']; omega)]
    exact hY
  rw [compBlocksB_eq]
  simp only [bind_assoc]
  refine litE fun l R0 hl m0 => ?_
  refine call1E (v := .bit (decide (nv < 2 ^ 63))) (by abiK) rfl (reads_of (l := [nb, l])
    (vs := [.size nv, .size (2 ^ 63)]) (by simp [m0 hnb, hl])) (by simp [arg, hsz, Out.out]; rfl) rfl
    fun g R1 hg m1 => ?_
  refine Builds.guardE (by simpa [hlt'] using hg) ?_
  refine litE fun o R2 ho m2 => ?_
  refine call1E (v := .size (nv - 1)) (by abiK) rfl (reads_of (l := [nb, o]) (vs := [.size nv, .size 1])
    (by simp [m2 (m1 (m0 hnb)), ho])) (by simp [arg, hsz, Out.out]; rfl) rfl fun s R3 hs m3 => ?_
  have hE3 : Extends rs R3 := fun h => m3 (m2 (m1 (m0 h)))
  refine Builds.bind1F (Free.clampB _ _ _) (clampB_builds (hE3 hRn) (hE3 hbid) hs hcl) fun c R4 hc4 m4 => ?_
  have hE4 : Extends rs R4 := fun h => m4 (hE3 h)
  have hpv : ([⟨nb, [.atom "" .i64 c], []⟩, R', S'].flatMap TabB.regs).mapM (fun i => R4[i]?) =
      some ([.size nv, Reg.put Y.enc] ++ (tabVals R ++ tabVals S)) := by
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mapM_append,
      List.mapM_append, mapM_extends hE4 hR, mapM_extends hE4 hS]
    simp [TabB.regs, Cols.regs, Col.regs, hE4 hnb, hc4]
  obtain ⟨Us, hUs, hsh, hreg⟩ := tabsAt_range [⟨nb, [.atom "" .i64 c], []⟩, R', S'] R4.size []
  rw [List.append_nil] at hUs
  have hall := mapM_range_append R4 ([.size nv, Reg.put Y.enc] ++ (tabVals R ++ tabVals S))
  rw [← mapM_get_length hpv, ← hreg] at hall
  have hge : AllGe R4.size (Us.flatMap TabB.regs) := fun a ha => by
    rw [hreg] at ha; exact (List.mem_range'_1.1 ha).1
  obtain ⟨U1, U2, U3, rfl⟩ : ∃ U1 U2 U3, Us = [U1, U2, U3] := by
    have hl : Us.length = 3 := by simpa using congrArg List.length hsh
    rcases Us with _ | ⟨U1, _ | ⟨U2, _ | ⟨U3, _ | ⟨U4, Us⟩⟩⟩⟩ <;> simp at hl
    exact ⟨U1, U2, U3, rfl⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hsh
  obtain ⟨⟨s1k, s1v⟩, ⟨s2k, s2v⟩, ⟨s3k, s3v⟩⟩ := hsh
  obtain ⟨n1, k1, v1⟩ := U1
  obtain ⟨c1, rfl, hc1⟩ := Cols.shape_singleton s1k
  obtain rfl : v1 = [] := by cases v1 with | nil => rfl | cons _ _ => simp [Cols.shape] at s1v
  obtain ⟨e1, rfl⟩ : ∃ e1, c1 = .atom "" .i64 e1 := by
    cases c1 with
    | atom p1 t1 e1 => simp only [Col.shape, Col.atom.injEq, and_true] at hc1; obtain ⟨rfl, rfl⟩ := hc1; exact ⟨e1, rfl⟩
    | arr => simp [Col.shape] at hc1
    | sum => simp [Col.shape] at hc1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hall
  obtain ⟨hU1, hall⟩ := mapM_split (by simp [TabB.regs, Cols.regs, Col.regs]) hall
  obtain ⟨hU2, hU3⟩ := mapM_split (by rw [TabB.regs_length (ColsOf.shape A hRk s2k) (ColsOf.shape B hRv s2v) R]) hall
  have hU1' : [n1, e1].mapM (fun i => (R4 ++ ([.size nv, Reg.put Y.enc] ++
      (tabVals R ++ tabVals S)).toArray)[i]?) = some [.size nv, Reg.put Y.enc] := hU1
  obtain ⟨hcn', hU1''⟩ := mapM_get_cons hU1'
  refine funTab_builds (K := R'.key) (V := S'.val) hRk hSv (fun _ => reads_of hpv) hUs hfo
    (fun Ts => Grows.compBlocksBody Ts) ((Typed.compBlocksBody hge).mono fun _ _ => trivial) (fun kt ot h' => ?_)
    fun fg2 W ys he' hf ho s1 s2 h => hkk fg2 W (R4 ++ ys) (fun h => get_app (hE4 h)) he' hf ho s1 s2 h
  exact compBlocksBody_builds hc h63 A B C hP (ColsOf.shape A hRk s2k) (ColsOf.shape B hRv s2v)
    (ColsOf.shape B hSk s3k) (ColsOf.shape C hSv s3v) hU2 hU3 hcn' (mapM_get_cons hU1'').1 (by omega) hlt (hk Y hY)
    h0 hT (hU Y hY X0 h0) (fun h => he h n1 e1 _ _ s2k s2v s3k s3v) hfo
    fun fg2 W Rn ext s1 s2 h => h' fg2 W Rn ext (s1.trans s2k) (s2.trans s3v) h

end Rel.Lang.Plan
