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

end Rel.Lang.Plan
