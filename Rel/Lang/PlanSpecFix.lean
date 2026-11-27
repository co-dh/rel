module

public import Rel.Lang.PlanSpecLoop
public import Rel.Lang.PlanSpecUnion

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `fixB` builds `Tab.fixOn`

`fixB msg step k [X]` is `funT [X]` of one `Plan.loop`: the state is the table's registers, a round reads them as a
table (`tabsAt`), `step`s it, `packT`s the answer and compares the row counts. `Builds.loop` runs the rounds by the
invariant "`j` rounds left, the state holds `X`, `fixOn j X` answers `Y`", `funT_builds` closes the body into a plan
function. The step and the pack enter as specs in the style of `UnionSpec`: a `Spec` says a builder builds the Lean
function whenever that function answers, its continuation getting the answer's registers. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- The values of the registers of a table `X`: its count, its key columns, its value columns. -/
def tabVals {A B : Obj} (X : Tab A B) : List Val := .size X.n :: (X.key.regVals ++ X.val.regVals)

/-- The table `T` holds `X` in the registers `rs`. -/
def TabHolds {A B : Obj} (T : TabB) (X : Tab A B) (rs : Array Val) : Prop :=
  T.regs.mapM (fun i => rs[i]?) = some (tabVals X)

/-- **A table builder builds a Lean function `f` of one table** (`UnionSpec`'s shape): `W` of `X'`'s shape holding the
    answer, the continuation `kk` builds. -/
def TabSpec (A B : Obj) (f : Tab A B → Except String (Tab A B)) (bld : TabB → Bld TabB) : Prop :=
  ∀ {X S : Tab A B} {X' : TabB} {fg : Array Fun × Array Fun} {rs : Array Val} {kk : TabB → Bld (Array Nat)}
    {out : Array Val}, ColsOf A X'.key → ColsOf B X'.val → TabHolds X' X rs → f X = .ok S → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape X'.key → Cols.shape W.val = Cols.shape X'.val →
      TabHolds W S (rs ++ ys) → ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (bld X' >>= kk) rs out


/-- `Plan.loop` is typed as `Plan.ite` is: its state registers `init` at or above `m`, its round answering registers at
    or above `m`; the cap register `k` is read as a `size` (`useTy`), whether it is captured or not. -/
theorem Typed.loop {m k : Nat} {init : Array Nat} {msg : String} {b : Array Nat → Bld (Array Nat × Nat)}
    (hi : ∀ a ∈ init, m ≤ a)
    (hb : ∀ n', m ≤ n' → Typed m (fun r => (∀ a ∈ r.1, m ≤ a) ∧ m ≤ r.2) (b (List.range' n' init.size).toArray)) :
    Typed m (fun r => r.size = init.size ∧ ∀ a ∈ r, m ≤ a) (Plan.loop k init msg b) := fun is n fs gs x s' hm h => by
  cases hr : (b (Array.range' n init.size)).run (#[], n + init.size, fs, gs) with
  | error _ => simp [Plan.loop, StateT.run_bind, StateT.run_get, StateT.run_monadLift, liftM, monadLift_self, hr,
      err_bind_eq, Functor.map, Except.map] at h
  | ok p =>
    obtain ⟨⟨out, d⟩, is', n', fs', gs'⟩ := p
    have hb' : Typed m (fun r => (∀ a ∈ r.1, m ≤ a) ∧ m ≤ r.2) (b (Array.range' n init.size)) := by
      simpa using hb n hm
    obtain ⟨js, fa, e1, f1, l1, ⟨qo, qd⟩, t1⟩ := hb' #[] (n + init.size) fs gs
      (out, d) (is', n', fs', gs') (by omega) hr
    simp only [Array.empty_append] at e1 f1 l1
    subst e1
    by_cases hs : out.size = init.size
    · simp [Plan.loop, StateT.run_bind, StateT.run_get, StateT.run_monadLift, liftM, monadLift_self, hr, hs, ok_bind,
        emit_ok, Functor.map, Except.map] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨#[.loop k init is'.toList out d msg], fa, by simp, f1, by simp, ⟨by simp, fun a ha => ?_⟩, fun y a ha hlt => ?_⟩
      · simp at ha; omega
      · simp only [readsB, reads, List.append_nil, Array.mem_toList_iff, List.mem_cons, List.mem_filter,
          List.mem_append, decide_eq_true_eq] at ha
        by_cases hka : k = a
        · exact ⟨.size, by simp [useTyB, useTy, hka]⟩
        · rcases ha with (ha | ha) | ⟨(ha | ha) | ha, -⟩
          · exact absurd ha.symm hka
          · exact absurd (hi _ ha) (by omega)
          · obtain ⟨u, hu⟩ := t1 y a (by simpa using ha) hlt
            refine ⟨u, ?_⟩
            have : (k == a) = false := by simpa using hka
            simpa [useTyB, useTy, this, f1] using hu
          · exact absurd (qo a (by simpa using ha)) (by omega)
          · simp at ha; omega
    · simp [Plan.loop, StateT.run_bind, StateT.run_get, StateT.run_monadLift, liftM, monadLift_self, hr, hs, ok_bind,
        throwThe, MonadExceptOf.throw, MonadExcept.throw, err_bind_eq, Functor.map, Except.map] at h

/-- The first table of a state. -/
def firstT : List TabB → Bld TabB | T :: _ => pure T | [] => throw "a fixed point of no table"

/-- The tables `Xs` read from the registers `rs`. -/
def shapeT (Xs : List TabB) (rs : Array Nat) : Bld (List TabB) := return (← tabsAt Xs rs.toList).1

/-- `fixB`'s round on the state registers `rs`: the tables they hold, `step`, `packT` of each, and whether the first one's
    count is as it was. -/
def fixRound (step : List TabB → Bld (List TabB)) (Xs : List TabB) (rs : Array Nat) : Bld (Array Nat × Nat) := do
  let Ts ← shapeT Xs rs
  let Ys ← (← step Ts).mapM (packT ·)
  pure ((← tabsRegs Ys).toArray, ← call1 (kernel% USize.decEq) #[(← firstT Ys).n, (← firstT Ts).n])

/-- `fixB`'s body on the tables `Xs` its function reads. -/
def fixBody (msg : String) (step : List TabB → Bld (List TabB)) (k : Nat) (Xs : List TabB) : Bld TabB := do
  firstT (← shapeT Xs (← loop k (← tabsRegs Xs).toArray msg (fixRound step Xs)))

/-- `fixB` is `funT` of `fixBody`. -/
theorem fixB_eq (msg step k Xs) : fixB msg step k Xs = funT Xs (fixBody msg step k) := by
  unfold fixB fixBody fixRound shapeT firstT; rfl

/-- Any registers `ps` as many as the table `T` has are read as a table of `T`'s shape, holding them. -/
theorem tabsAt_one (T : TabB) (ps : List Nat) (hl : ps.length = T.regs.length) : ∃ V : TabB,
    tabsAt [T] ps = Pure.pure ([V], []) ∧ Cols.shape V.key = Cols.shape T.key ∧ Cols.shape V.val = Cols.shape T.val ∧
      V.regs = ps := by
  obtain ⟨A1, Y1, t1, -, hl1, t4⟩ := tab_spec T
  rw [tabsRegs_eq] at t1
  obtain rfl := pure_inj t1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hl1 ⊢
  obtain ⟨V, v1, v2, -, v4, v5⟩ := t4 ps [] (by simpa using hl)
  rw [List.append_nil] at v1
  refine ⟨V, v1, v4, v5, ?_⟩
  rw [tabsRegs_eq] at v2; simpa using pure_inj v2

/-- The `USize.decEq` of two registers holding counts `x`, `y` answers the bit `x = y`. -/
theorem decEq_builds {fg : Array Fun × Array Fun} {rs : Array Val} {a b : Nat} {x y : USize}
    (ha : rs[a]? = some (.size x)) (hb : rs[b]? = some (.size y)) {c : Nat → Bld (Array Nat)} {out : Array Val}
    (hc : ∀ (r : Nat) (R : Array Val), R[r]? = some (.bit (decide (x = y))) → Extends rs R →
      Builds abiOf fg fg (c r) R out) :
    Builds abiOf fg fg (call1 (kernel% USize.decEq) #[a, b] >>= c) rs out := by
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  refine Builds.call1G (v := .bit (decide (x = y))) (by abiK) rfl (reads_of (l := [a, b]) (vs := [.size x, .size y]) (by simp [ha, hb])) ?_ rfl hc
  simp [arg, hsz, Out.out]; rfl

theorem TabB.regs_eq (T : TabB) : T.regs = T.n :: (Cols.regs T.key ++ Cols.regs T.val) := by
  simp [TabB.regs, Cols.regs_append]

/-- The table `V` holds `Y` in `rs`: its count register holds `Y`'s count, and all its registers `Y`'s values. -/
theorem TabHolds.count {A B : Obj} {V : TabB} {Y : Tab A B} {rs : Array Val} (h : TabHolds V Y rs) :
    rs[V.n]? = some (.size Y.n) := by
  unfold TabHolds tabVals at h
  rw [TabB.regs_eq] at h
  exact (mapM_get_cons h).1

/-- **One round of `fixB`** from the state holding `X` (`stepT X = S`, `S.pack = Y`): it builds the registers of `Y`
    and the bit of `Y.n = X.n`. -/
theorem fixRound_builds {A B : Obj} {stepT : Tab A B → Except String (Tab A B)} {bldS : TabB → Bld TabB}
    {step : List TabB → Bld (List TabB)} (hs : ∀ T, step [T] = (fun W => [W]) <$> bldS T)
    (hP : TabSpec A B Tab.pack (fun T => packT T)) (hS : TabSpec A B stepT bldS)
    {R1 : TabB} {X S Y : Tab A B} {fg : Array Fun × Array Fun} {rs0 : Array Val}
    (hRk : ColsOf A R1.key) (hRv : ColsOf B R1.val) (hfo : Ordered fg.1)
    (hX : R1.regs.length = (tabVals X).length) (hstep : stepT X = .ok S) (hpack : S.pack = .ok Y) :
    ∃ fg', Builds abiOf fg fg'
      ((fun p => p.1.push p.2) <$> fixRound step [R1] (List.range' rs0.size R1.regs.length).toArray)
      (rs0 ++ (tabVals X).toArray) ((tabVals Y).toArray.push (.bit (decide (Y.n = X.n)))) := by
  obtain ⟨T1, hT1, hsk, hsv, hr1⟩ := tabsAt_one R1 (List.range' rs0.size R1.regs.length) (by simp)
  have hhold : TabHolds T1 X (rs0 ++ (tabVals X).toArray) := by
    unfold TabHolds; rw [hr1, hX]; exact mapM_range_append rs0 (tabVals X)
  have e : (fun p => p.1.push p.2) <$> fixRound step [R1] (List.range' rs0.size R1.regs.length).toArray =
      bldS T1 >>= fun W => packT W >>= fun V => call1 (kernel% USize.decEq) #[V.n, T1.n] >>= fun d =>
        Pure.pure (V.regs.toArray.push d) := by
    simp [fixRound, shapeT, hT1, hs, firstT, tabsRegs_eq]
  rw [e]
  refine hS (ColsOf.shape A hRk hsk) (ColsOf.shape B hRv hsv) hhold hstep hfo ?_
  intro fg2 W ys he hf ho hsW1 hsW2 hW
  refine hP (ColsOf.shape A (ColsOf.shape A hRk hsk) hsW1) (ColsOf.shape B (ColsOf.shape B hRv hsv) hsW2) hW hpack ho ?_
  intro fg3 V zs he3 hf3 ho3 hsV1 hsV2 hV
  have hext : Extends (rs0 ++ (tabVals X).toArray) (rs0 ++ (tabVals X).toArray ++ ys ++ zs) :=
    fun h => get_app (get_app h)
  have hT1n : (rs0 ++ (tabVals X).toArray ++ ys ++ zs)[T1.n]? = some (.size X.n) :=
    TabHolds.count (show TabHolds T1 X (rs0 ++ (tabVals X).toArray ++ ys ++ zs) from mapM_extends hext hhold)
  refine ⟨fg3, decEq_builds hV.count hT1n fun r R hr hR => Builds.pure fun who => ?_⟩
  have hl : (V.regs ++ [r]).mapM (fun i => R[i]?) = some (tabVals Y ++ [.bit (decide (Y.n = X.n))]) := by
    rw [List.mapM_append, mapM_extends hR hV]; simp [hr]
  simpa using reads_of (who := who) hl

/-- Two builds of one builder from one `fg` and registers of one length leave the same `fg'`: the run is deterministic and
    reads `rs` by its size only. -/
theorem Builds.fg_unique {fg fg1 fg2 : Array Fun × Array Fun} {b : Bld (Array Nat)} {rs rs' out out' : Array Val}
    (h1 : Builds abiOf fg fg1 b rs out) (h2 : Builds abiOf fg fg2 b rs' out') (hs : rs.size = rs'.size) : fg1 = fg2 := by
  obtain ⟨js, xs, r, hr, -⟩ := h1.2.2 #[]
  obtain ⟨js', xs', r', hr', -⟩ := h2.2.2 #[]
  rw [← hs, hr] at hr'
  exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hr')).2).2).2

/-- **The loop of `fixB`** from the table `R1` holding `X` in `rs0`, the register `k` holding the round count `c`:
    `fixOn` answering `Y` in `c` rounds, the loop builds the registers of `Y`. -/
theorem fixLoop_builds {A B : Obj} {stepT : Tab A B → Except String (Tab A B)} {bldS : TabB → Bld TabB}
    {step : List TabB → Bld (List TabB)} (hs : ∀ T, step [T] = (fun W => [W]) <$> bldS T)
    (hP : TabSpec A B Tab.pack (fun T => packT T)) (hS : TabSpec A B stepT bldS)
    {R1 : TabB} {X Y : Tab A B} {fg : Array Fun × Array Fun} {rs0 : Array Val} {k : Nat} {c : USize} {msg out' : String}
    (hRk : ColsOf A R1.key) (hRv : ColsOf B R1.val) (hfo : Ordered fg.1) (hk : rs0[k]? = some (.size c))
    (hR1 : TabHolds R1 X rs0) (hY : Tab.fixOn Tab.n Tab.pack out' stepT c.toNat X = .ok Y) :
    ∃ fg1, Builds abiOf fg fg1 (loop k R1.regs.toArray msg (fixRound step [R1])) rs0 (tabVals Y).toArray := by
  have hX : ∀ X' : Tab A B, R1.regs.length = (tabVals X').length := fun X' => by
    rw [TabB.regs_eq]
    simp [tabVals, ColsOf.regs_length hRk X'.key, ColsOf.regs_length hRv X'.val]
  let I : Nat → Array Val → Prop := fun j s =>
    ∃ X', s = (tabVals X').toArray ∧ Tab.fixOn Tab.n Tab.pack out' stepT j X' = .ok Y
  have hround : ∀ j (s : Array Val), I (j + 1) s → ∃ (s' : Array Val) (bt : Bool) (fg' : Array Fun × Array Fun),
      s'.size = R1.regs.length ∧ (if bt then s' = (tabVals Y).toArray else I j s') ∧ Builds abiOf fg fg'
        ((fun p => p.1.push p.2) <$> fixRound step [R1] (List.range' rs0.size R1.regs.length).toArray)
        (rs0 ++ s) (s'.push (.bit bt)) := by
    rintro j s ⟨X', rfl, hf⟩
    simp only [Tab.fixOn] at hf
    obtain ⟨Y1, hY1, hite⟩ := except_bind_ok hf
    obtain ⟨S, hst, hpk⟩ := except_bind_ok hY1
    obtain ⟨fg', hB⟩ := fixRound_builds hs hP hS hRk hRv hfo (rs0 := rs0) (hX X') hst hpk
    refine ⟨(tabVals Y1).toArray, decide (Y1.n = X'.n), fg', by simp [← hX Y1], ?_, hB⟩
    by_cases hq : Y1.n = X'.n
    · have hb : (Tab.n Y1 == Tab.n X') = true := by simpa using hq
      rw [hb] at hite
      simp only [if_true] at hite
      have hd : decide (Y1.n = X'.n) = true := by simpa using hq
      rw [hd]
      simp only [if_true]
      rw [Except.ok.inj hite]
    · have hb : (Tab.n Y1 == Tab.n X') = false := by simpa using hq
      rw [hb] at hite
      simp only [Bool.false_eq_true, if_false] at hite
      simp [hq]
      exact ⟨Y1, rfl, hite⟩
  obtain ⟨j0, hj0⟩ : ∃ j, c.toNat = j + 1 := by
    rcases hc : c.toNat with _ | j
    · rw [hc] at hY; simp [Tab.fixOn] at hY
    · exact ⟨j, rfl⟩
  obtain ⟨s1, bt1, fg1, hs1, -, hB1⟩ := hround j0 _ (show I (j0 + 1) (tabVals X).toArray from ⟨X, rfl, hj0 ▸ hY⟩)
  refine ⟨fg1, ?_⟩
  obtain ⟨o, rfl, hB⟩ := Builds.loop (abi := abiOf) (I := I) (J := fun o => o = (tabVals Y).toArray) (init := R1.regs.toArray)
    (msg := msg) (fg := fg) (fg1 := fg1) (b := fixRound step [R1]) (c := c) (rs := rs0) (s₀ := (tabVals X).toArray) hk
    (reads_of hR1) ⟨X, rfl, hY⟩ (fun s ⟨X', _, h⟩ => by simp [Tab.fixOn] at h) fun j s hsz hI => by
      obtain ⟨s', bt, fg', hs', hc', hB'⟩ := hround j s hI
      obtain rfl : fg' = fg1 := Builds.fg_unique hB' hB1 (by simp at hsz ⊢; rw [hsz]; exact hX X)
      exact ⟨s', bt, by simpa using hs', hc', by simpa using hB'⟩
  exact hB

theorem fixBody_eq (msg step k) (R1 : TabB) : fixBody msg step k [R1] =
    loop k R1.regs.toArray msg (fixRound step [R1]) >>= fun r => shapeT [R1] r >>= firstT := by
  simp [fixBody, tabsRegs_eq]

theorem Typed.fixBody {m : Nat} {msg : String} {step : List TabB → Bld (List TabB)} {k : Nat} {R1 : TabB}
    {bldS : TabB → Bld TabB} (hs : ∀ T, step [T] = (fun W => [W]) <$> bldS T)
    (hTS : ∀ m T, AllGe m T.regs → Typed m (fun U => AllGe m U.regs) (bldS T))
    (hTP : ∀ m T, AllGe m T.regs → Typed m (fun U => AllGe m U.regs) (packT T)) (hR1 : AllGe m R1.regs) :
    Typed m (fun _ => True) (Plan.fixBody msg step k [R1]) := by
  rw [fixBody_eq]
  refine (Typed.loop (k := k) (fun a ha => hR1 a (by simpa using ha)) fun n' hn' => ?_).bind fun r hr => ?_
  · simp only [List.size_toArray]
    obtain ⟨T1, hT1, -, -, hr1⟩ := tabsAt_one R1 (List.range' n' R1.regs.length) (by simp)
    have e : fixRound step [R1] (List.range' n' R1.regs.length).toArray =
        bldS T1 >>= fun W => packT W >>= fun V => Plan.call1 (kernel% USize.decEq) #[V.n, T1.n] >>= fun d =>
          Pure.pure (V.regs.toArray, d) := by
      simp [fixRound, shapeT, hT1, hs, firstT, tabsRegs_eq]
    rw [e]
    have hT1g : AllGe m T1.regs := fun a ha => by rw [hr1, List.mem_range'_1] at ha; omega
    refine (hTS m T1 hT1g).bind fun W hW => (hTP m W hW).bind fun V hV => (Typed.call1 ?_).bind fun d hd =>
      Typed.pure ⟨fun a ha => hV a (by simpa using ha), hd⟩
    intro a ha
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hV _ (by simp [TabB.regs])
    · exact hT1g _ (by simp [TabB.regs])
  · obtain ⟨V, hV, -⟩ := tabsAt_one R1 r.toList (by simpa using hr.1)
    simp only [shapeT, hV, firstT, pure_bind]
    exact Typed.pure trivial

theorem Grows.firstT (Ts : List TabB) : Grows (Plan.firstT Ts) := by
  unfold Plan.firstT; cases Ts <;> first | exact Grows.pure _ | exact Grows.throw _

theorem Grows.fixBody {msg : String} {step : List TabB → Bld (List TabB)} {k : Nat} (hGs : ∀ Ts, Grows (step Ts))
    (hGP : ∀ T, Grows (packT T)) (Xs : List TabB) : Grows (Plan.fixBody msg step k Xs) := by
  unfold Plan.fixBody
  refine (Grows.tabsRegs Xs).bind fun R => (Grows.loop fun ps => ?_).bind fun r => ?_
  · unfold fixRound shapeT
    refine ((Grows.tabsAt _ _).bind fun _ => Grows.pure _).bind fun Ts => (hGs Ts).bind fun Zs =>
      ((Grows.mapM (fun T => hGP T) Zs).bind fun Ys => (Grows.tabsRegs Ys).bind fun R' => ?_)
    exact (Grows.firstT Ys).bind fun _ => (Grows.firstT Ts).bind fun _ => (Grows.call1 _ _).bind fun _ => Grows.pure _
  · unfold shapeT
    refine ((Grows.tabsAt _ _).bind fun _ => Grows.pure _).bind fun Ts => ?_
    exact Grows.firstT Ts

/-- Every table of the shapes `A`, `B` has as many registers as the values of a table `Z`. -/
theorem TabB.regs_length {A B : Obj} {T : TabB} (hk : ColsOf A T.key) (hv : ColsOf B T.val) (Z : Tab A B) :
    T.regs.length = (tabVals Z).length := by
  rw [TabB.regs_eq]; simp [tabVals, ColsOf.regs_length hk Z.key, ColsOf.regs_length hv Z.val]

/-- **`fixB` builds `Tab.fixOn`** of the one-table state: `X'` holds `X` in `rs`, the register `k` the round count `c`,
    `fixOn` answers `Y` in `c` rounds; `kk` continues with a table of `X'`'s shape holding `Y`. `step` builds `stepT`
    and `packT` builds `Tab.pack` (`TabSpec`); both grow the functions only by calls of earlier ones and type their
    registers as the plan requires (`Grows`, `Typed`: what closure conversion of the round's function reads). -/
theorem fixB_builds {A B : Obj} {stepT : Tab A B → Except String (Tab A B)} {bldS : TabB → Bld TabB}
    {step : List TabB → Bld (List TabB)} (hs : ∀ T, step [T] = (fun W => [W]) <$> bldS T)
    (hP : TabSpec A B Tab.pack (fun T => packT T)) (hS : TabSpec A B stepT bldS)
    (hGs : ∀ Ts, Grows (step Ts)) (hGP : ∀ T, Grows (packT T))
    (hTS : ∀ m T, AllGe m T.regs → Typed m (fun U => AllGe m U.regs) (bldS T))
    (hTP : ∀ m T, AllGe m T.regs → Typed m (fun U => AllGe m U.regs) (packT T))
    {X' : TabB} {X Y : Tab A B} {fg : Array Fun × Array Fun} {rs : Array Val} {kk : TabB → Bld (Array Nat)}
    {out : Array Val} {k : Nat} {c : USize} {msg out' : String}
    (hRk : ColsOf A X'.key) (hRv : ColsOf B X'.val) (hX : TabHolds X' X rs) (hk : rs[k]? = some (.size c))
    (hY : Tab.fixOn Tab.n Tab.pack out' stepT c.toNat X = .ok Y) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape X'.key → Cols.shape W.val = Cols.shape X'.val →
      TabHolds W Y (rs ++ ys) → ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (fixB msg step k [X'] >>= kk) rs out := by
  rw [fixB_eq]
  obtain ⟨R1, hUs, hsk, hsv, hr1⟩ := tabsAt_one X' (List.range' rs.size X'.regs.length) (by simp)
  have hpl : X'.regs.length = (tabVals X).length := mapM_get_length hX
  have hA : tabsRegs [X'] = Pure.pure X'.regs := by rw [tabsRegs_eq]; simp
  have ha : ∀ who, X'.regs.toArray.mapM (reg rs who) = .ok (tabVals X).toArray := fun _ => reads_of hX
  have hRk1 : ColsOf A R1.key := ColsOf.shape A hRk hsk
  have hRv1 : ColsOf B R1.val := ColsOf.shape B hRv hsv
  have hR1 : TabHolds R1 X (rs ++ (tabVals X).toArray) := by
    unfold TabHolds; rw [hr1, hpl]; exact mapM_range_append rs (tabVals X)
  let P : TabB → Prop := fun W => Cols.shape W.key = Cols.shape X'.key ∧ Cols.shape W.val = Cols.shape X'.val
  let o : Array Val := (tabVals Y).toArray
  have hB : ∃ fg1, Builds abiOf fg fg1 (fixBody msg step k [R1] >>= answerRegs P) (rs ++ (tabVals X).toArray) o := by
    obtain ⟨fg1, hL⟩ := fixLoop_builds (msg := msg) hs hP hS hRk1 hRv1 hfo (get_app hk) hR1 hY
    refine ⟨fg1, ?_⟩
    rw [fixBody_eq]; simp only [bind_assoc]
    refine Builds.bind hL fun r xs hr => ?_
    have hlen : r.toList.length = R1.regs.length := by
      have := mapM_ok_size (hr ""); simp only [o, List.size_toArray] at this
      simp [← this, TabB.regs_length hRk1 hRv1 Y]
    obtain ⟨V, hV, hV1, hV2, hVr⟩ := tabsAt_one R1 r.toList hlen
    simp only [shapeT, hV, firstT, pure_bind]
    refine Builds.answerRegs (P := P) ⟨hV1.trans hsk, hV2.trans hsv⟩ (tabsRegs_eq _) fun who => ?_
    simpa [hVr] using hr who
  obtain ⟨fg1, ⟨a1, ha1⟩, hb1, hB1⟩ := hB
  have hR1g : AllGe rs.size R1.regs := fun a ha => by rw [hr1, List.mem_range'_1] at ha; omega
  obtain ⟨ctys, hcl⟩ := Typed.cloTys (fg := fg) (fg1 := fg1) (k := X'.regs.length) (rs := rs)
    (Typed.fixBody (msg := msg) (k := k) hs hTS hTP hR1g)
  refine funT_builds (P := P) (Us := [R1]) (ctys := ctys) (o := o) hA ha hUs (hB1 #[]) hfo
    (fun Ts => Grows.fixBody hGs hGP Ts) (fun U body xs R rtys h _ hR hy is => hcl U body _ R rtys h hR hy is) ?_
  intro U' ⟨hsk', hsv'⟩ fg2 Rr V ys he hf ho' hRr hV
  obtain ⟨AU, YU, u1, -, -, u4⟩ := tab_spec U'
  rw [tabsRegs_eq] at u1
  obtain rfl := (pure_inj u1).symm
  have hl : Rr.toList.length = ([U'].flatMap TabB.regs).length := by
    have h1 := mapM_ok_size (hRr "")
    simp only [o, List.size_toArray] at h1
    simp [h1, TabB.regs_length (ColsOf.shape A hRk hsk') (ColsOf.shape B hRv hsv') Y]
  obtain ⟨V', f1, f2, -, f4, f5⟩ := u4 Rr.toList [] hl
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
    (f4.trans hsk') (f5.trans hsv') (by simpa [o] using hread)

end Rel.Lang.Plan
