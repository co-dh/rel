module

public import Rel.Lang.PlanSpec

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # The control builders: `loop`, `tryCatchThe BErr`, a global's slot

`Builds.loop` runs a round's `Builds` through the rounds `runI` performs, by an invariant on the state;
`Builds.tryCatch_ok`/`tryCatch_err` are the two outcomes of `tryCatchThe BErr` (an error drops the state, so the
handler builds from the start state); `Builds.global` is the step `shareB` builds a closed table as global `k` by. -/

namespace Rel.Lang.Plan

open Tab Rel.Kernel

variable {abi : String → Option Kernel}

/-- `tryCatchThe BErr x h`, then `kk`, where `x` then `kk` builds: `x` succeeds, so the handler is never run. -/
theorem Builds.tryCatch_ok {fg fg' : Array Fun × Array Fun} {α : Type} {x : Bld α} {h : BErr → Bld α}
    {kk : α → Bld (Array Nat)} {rs out : Array Val} (hx : Builds abi fg fg' (x >>= kk) rs out) :
    Builds abi fg fg' (tryCatchThe BErr x h >>= kk) rs out := by
  refine Builds.congr (fun is => ?_) hx
  obtain ⟨-, -, hb⟩ := hx
  obtain ⟨_, _, _, hr, -⟩ := hb is
  simp only [StateT.run_bind] at hr ⊢
  obtain ⟨p, hp, -⟩ := bind_ok hr
  have e : (tryCatchThe BErr x h).run (is, rs.size, fg) =
      tryCatchThe BErr (x.run (is, rs.size, fg)) fun e => (h e).run (is, rs.size, fg) := rfl
  rw [e, hp]; rfl

/-- `tryCatchThe BErr x h`, then `kk`, where `x` fails with `e` from the states `Builds` runs it from: the handler
    `h e` runs from the start state, and it then `kk` builds. -/
theorem Builds.tryCatch_err {fg fg' : Array Fun × Array Fun} {α : Type} {x : Bld α} {h : BErr → Bld α}
    {kk : α → Bld (Array Nat)} {rs out : Array Val} {e : BErr} (hx : ∀ is, x.run (is, rs.size, fg) = .error e)
    (hh : Builds abi fg fg' (h e >>= kk) rs out) : Builds abi fg fg' (tryCatchThe BErr x h >>= kk) rs out := by
  refine Builds.congr (fun is => ?_) hh
  have e' : (tryCatchThe BErr x h).run (is, rs.size, fg) =
      tryCatchThe BErr (x.run (is, rs.size, fg)) fun e => (h e).run (is, rs.size, fg) := rfl
  rw [StateT.run_bind, StateT.run_bind, e', hx]; rfl

/-- `out.push d` reads as `s'.push v`: `out` reads as `s'`, `d` as `v`. -/
theorem mapM_push_ok {out : Array Nat} {d : Nat} {X s' : Array Val} {v : Val} {who : String}
    (h : (out.push d).mapM (reg X who) = .ok (s'.push v)) : out.mapM (reg X who) = .ok s' ∧ reg X who d = .ok v := by
  rw [Array.push_eq_append, Array.mapM_append] at h
  obtain ⟨bs, hbs, h⟩ := bind_ok h
  cases hd : reg X who d with
  | error e =>
    have e1 : (#[d] : Array Nat).mapM (reg X who) = .error e := by
      simp [Array.mapM_eq_mapM_toList, hd, Functor.map, Except.map] <;> rfl
    rw [e1, err_bind_eq] at h; cases h
  | ok c =>
    have e1 : (#[d] : Array Nat).mapM (reg X who) = .ok #[c] := by simp [Array.mapM_eq_mapM_toList, hd]; rfl
    rw [e1, ok_bind] at h
    have h' := Except.ok.inj (show Except.ok (bs ++ #[c]) = _ from h)
    rw [← Array.push_eq_append] at h'
    obtain ⟨h1, h2⟩ := Array.push_eq_push.1 h'.symm
    exact ⟨h2 ▸ hbs, h1 ▸ rfl⟩

/-- **`loop k(init)` of the round `b`**: `I j s` says the state `s` is reached with `j` rounds left of the cap the
    size in register `k` gives, and none is reached with none left. A round from such an `s` (its body built after the
    loop's registers `rs` and `s`) answers the next state `s'` and the bit `bt`: `J s'` where `bt`, else `I j s'`. The
    loop answers a last state `o`, `J o`. -/
theorem Builds.loop {fg fg1 : Array Fun × Array Fun} {k : Nat} {init : Array Nat} {msg : String}
    {b : Array Nat → Bld (Array Nat × Nat)} {c : USize} {rs s₀ : Array Val} {I : Nat → Array Val → Prop}
    {J : Array Val → Prop} (hk : rs[k]? = some (.size c)) (hi : init.mapM (reg rs "loop") = .ok s₀)
    (h₀ : I c.toNat s₀) (hn : ∀ s, ¬ I 0 s)
    (hb : ∀ j (s : Array Val), s.size = init.size → I (j + 1) s → ∃ (s' : Array Val) (bt : Bool), s'.size = init.size ∧ (if bt then J s' else I j s') ∧
      Builds abi fg fg1 ((fun p => p.1.push p.2) <$> b (List.range' rs.size init.size).toArray) (rs ++ s)
        (s'.push (.bit bt))) :
    ∃ o, J o ∧ Builds abi fg fg1 (Plan.loop k init msg b) rs o := by
  have hs₀ : s₀.size = init.size := mapM_ok_size hi
  obtain ⟨j₀, hj₀⟩ : ∃ j, c.toNat = j + 1 := by
    rcases hc : c.toNat with _ | j
    · exact absurd (hc ▸ h₀) (hn s₀)
    · exact ⟨j, rfl⟩
  obtain ⟨s1, bt1, hs1, -, ⟨a1, ha1⟩, hb1, hB⟩ := hb j₀ s₀ hs₀ (by rw [← hj₀]; exact h₀)
  obtain ⟨js, xs1, r, hr, -, hm1⟩ := hB #[]
  -- the round's build, the same from every state: `b` answering `(out, d)`, `r = out.push d`
  obtain ⟨out, d, m, hbr, rfl⟩ : ∃ (out : Array Nat) (d m : Nat), (b (List.range' rs.size init.size).toArray).run
      (#[], rs.size + init.size, fg) = .ok ((out, d), js, m, fg1) ∧ r = out.push d := by
    rw [StateT.run_map, Array.size_append, hs₀] at hr
    cases hbr : (b (List.range' rs.size init.size).toArray).run (#[], rs.size + init.size, fg) with
    | error e => rw [hbr] at hr; cases hr
    | ok p =>
      rw [hbr] at hr
      obtain ⟨⟨o, d⟩, is', m, fg2⟩ := p
      simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq, Array.empty_append] at hr
      obtain ⟨rfl, rfl, -, rfl⟩ := hr
      exact ⟨o, d, m, rfl, rfl⟩
  have key : ∀ j s, s.size = init.size → I j s → ∃ o, J o ∧ o.size = init.size ∧ ∀ fs gs, Env abi fs gs fg1 →
      ∀ ws, rounds (fun s ws => runB abi fs gs js.toList (rs ++ s) ws) out d msg j s ws = .ok (o, ws) := by
    intro j
    induction j with
    | zero => intro s _ h; exact absurd h (hn s)
    | succ j ih =>
      intro s hs hI
      obtain ⟨s', bt, hs', hJ, -, -, hB⟩ := hb j s hs hI
      obtain ⟨js2, xs2, r2, hr2, hrun, hm⟩ := hB #[]
      rw [StateT.run_map, Array.size_append, hs, hbr] at hr2
      simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq, Array.empty_append] at hr2
      obtain ⟨rfl, rfl, -⟩ := hr2
      obtain ⟨ho, hd⟩ := mapM_push_ok (hm "loop")
      cases bt with
      | true => exact ⟨s', hJ, hs', fun fs gs hE ws => by
          simp only [rounds] at hrun ⊢
          rw [hrun fs gs hE ws, ok_bind]; dsimp only; rw [ho, ok_bind, hd, ok_bind]; rfl⟩
      | false =>
        obtain ⟨o, hJo, hso, hro⟩ := ih s' hs' hJ
        exact ⟨o, hJo, hso, fun fs gs hE ws => by
          simp only [rounds] at hrun ⊢
          rw [hrun fs gs hE ws, ok_bind]; dsimp only; rw [ho, ok_bind, hd, ok_bind]; exact hro fs gs hE ws⟩
  obtain ⟨o, hJ, ho, hro⟩ := key c.toNat s₀ hs₀ h₀
  have hsz : out.size = init.size := hs1 ▸ (mapM_ok_size (mapM_push_ok (hm1 "")).1).symm
  refine ⟨o, hJ, ⟨a1, ha1⟩, hb1, fun is => ⟨#[.loop k init js.toList out d msg], o,
    (List.range' rs.size init.size).toArray, ?_, fun fs gs hE ws => ?_, fun who => ho ▸ mapM_reg_range rs o who⟩⟩
  · rw [show (List.range' rs.size init.size).toArray = Array.range' rs.size init.size by simp] at hbr
    simp [Plan.loop, StateT.run_bind, StateT.run_get, StateT.run_monadLift, liftM, monadLift_self, hbr, hsz,
      ok_bind, emit_run, Functor.map, Except.map, ho]
  · rw [show (#[Instr.loop k init js.toList out d msg] : Array Instr).toList = [.loop k init js.toList out d msg]
      from rfl, runB.eq_2]
    simp [runI, reg_of hk, hi, hro fs gs hE ws, runB.eq_1, ok_bind, Functor.map, Except.map]

/-- Setting slot `k` of `G` (past its end, the slots between filled with `d`): the slots of `G` below `k` are kept, and
    those at or above `k` are all unbuilt, so `GExt` holds. -/
theorem GExt.fill {G : Array Fun} {k : Nat} (F : Fun) (hk : ∀ i (h : i < G.size), k ≤ i → G[i].res = #[]) :
    GExt G ((G ++ Array.replicate (k + 1 - G.size) default).modify k fun _ => F) := by
  refine ⟨by simp, fun i hi => ?_⟩
  by_cases h : k = i
  · exact Or.inl (hk i hi (by omega))
  · exact Or.inr (by rw [Array.getElem?_modify, if_neg h, Array.getElem?_append_left hi]; simp [hi])

/-- **A global's slot** (`shareB`'s step): `x`, built closed (after no register, in a block of its own) answering
    a nonempty `v`, becomes global `k`'s body, then `use`. `use` may read global `k` as `v` under every meaning of plan
    functions and globals extending the ones the step leaves, as `defFun`'s continuation applies its function. Slot `k`
    may lie below globals `x` left (`shareB` fills it after a higher one), as every slot of `fg1.2` at or above `k` is
    unbuilt (empty `res`): the step then overwrites no built slot, which `GExt` in `Builds` needs. -/
theorem Builds.global {fg fg1 fg' : Array Fun × Array Fun} {k : Nat} {x : Bld (List Nat)} {use : Bld (Array Nat)}
    {v rs out : Array Val} (hx : Builds abi fg fg1 (List.toArray <$> x) #[] v) (hv : v ≠ #[])
    (hk : ∀ i (h : i < fg1.2.size), k ≤ i → fg1.2[i].res = #[])
    (hu : ∀ F : Fun, (∀ fs gs F' G', (∃ a, F' = fg1.1 ++ a) →
        GExt ((fg1.2 ++ Array.replicate (k + 1 - fg1.2.size) default).modify k (fun _ => F)) G' →
        Env abi fs gs (F', G') → gs[k]? = some v) →
      Builds abi (fg1.1, (fg1.2 ++ Array.replicate (k + 1 - fg1.2.size) default).modify k fun _ => F) fg' use rs
        out) :
    Builds abi fg fg' (do
      let (is, n, fs, gs) ← get
      let (rs, body, _, fs, gs) ← x.run (#[], 0, fs, gs)
      set (is, n, fs, (gs ++ Array.replicate (k + 1 - gs.size) default).modify k fun _ =>
        (⟨#[], body.toList, rs.toArray⟩ : Fun))
      use) rs out := by
  obtain ⟨F0, G0⟩ := fg; obtain ⟨F1, G1⟩ := fg1
  simp only at hk hu
  obtain ⟨⟨a1, ha1⟩, hb1, hx⟩ := hx
  obtain ⟨js, xs, r, hr, hrun, hm⟩ := hx #[]
  obtain ⟨l, hxr, rfl⟩ : ∃ l, x.run (#[], 0, F0, G0) = .ok (l, js, xs.size, F1, G1) ∧ l.toArray = r := by
    rw [StateT.run_map] at hr
    cases hxr : x.run (#[], 0, F0, G0) with
    | error e => simp [hxr, Functor.map, Except.map] at hr
    | ok p =>
      simp only [hxr, Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq, Array.empty_append,
        List.size_toArray, List.length_nil] at hr
      obtain ⟨l, is', m, F, G⟩ := p
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hr
      exact ⟨l, rfl, rfl⟩
  have hfill := GExt.fill (G := G1) (k := k) (⟨#[], js.toList, l.toArray⟩ : Fun) hk
  have hne : (⟨#[], js.toList, l.toArray⟩ : Fun).res ≠ #[] := fun h =>
    hv (Array.eq_empty_of_size_eq_zero ((mapM_ok_size (hm "")).trans (by simpa using congrArg Array.size h)))
  have hF : ∀ fs gs F' G', (∃ a, F' = F1 ++ a) →
      GExt ((G1 ++ Array.replicate (k + 1 - G1.size) default).modify k
        (fun _ => (⟨#[], js.toList, l.toArray⟩ : Fun))) G' → Env abi fs gs (F', G') → gs[k]? = some v := by
    rintro fs gs F' G' ⟨a, rfl⟩ hG hE
    have hkG : k < ((G1 ++ Array.replicate (k + 1 - G1.size) default).modify k
        (fun _ => (⟨#[], js.toList, l.toArray⟩ : Fun))).size := by simp; omega
    have hGk : G'[k]? = some ⟨#[], js.toList, l.toArray⟩ := by
      rcases hG.2 k hkG with e | e
      · rw [Array.getElem_modify_self] at e; exact absurd e hne
      · rw [Array.getElem_modify_self] at e; exact e
    have hk' : k < G'.size := Nat.lt_of_lt_of_le hkG hG.1
    have hGk' : G'[k] = ⟨#[], js.toList, l.toArray⟩ :=
      Option.some.inj ((Array.getElem?_eq_getElem hk').symm.trans hGk)
    obtain ⟨v', hv', fs', hf', hsem⟩ := hE.2 k hk' (by rw [hGk']; exact hne)
    have hE' : Env abi fs' (gs.extract 0 k) (F1, G1) := (hE.restrict (hfill.trans hG) (FEnv.mono hf') k hk
      (by simp [Array.extract_extract]))
    have hm' := hm "result"
    rw [Array.empty_append] at hm'
    have := hsem #[]
    simp only [hGk', Fun.sem, hrun fs' _ hE' #[], Array.empty_append, ok_bind, hm'] at this
    rw [hv', (Prod.mk.inj (Except.ok.inj (show Except.ok (v, (#[] : Writes)) = _ from this))).1]
  obtain ⟨⟨a2, ha2⟩, hb2, hu'⟩ := hu _ hF
  simp only at ha1 ha2
  refine ⟨⟨a1 ++ a2, by rw [ha2, ha1, Array.append_assoc]⟩, hb1.trans (hfill.trans hb2), fun is => ?_⟩
  obtain ⟨js2, xs2, r2, hr2, hs2, hm2⟩ := hu' is
  refine ⟨js2, xs2, r2, ?_, hs2, hm2⟩
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, liftM, monadLift_self, hxr,
    ok_bind, pure_bind, bind_assoc]
  exact hr2

end Rel.Lang.Plan
