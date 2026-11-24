module

public import Rel.Lang.EmitC

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # A builder's plan means its def (`doc/rel-native-design.md` §13, stage 1b)

`Builds abi fg fg' b rs out`: `b`, built while the plan's functions and globals grow from `fg` to `fg'`, appends
instructions which, run after the registers `rs` under any meaning of `fg'` (`Env`), answer `out`. One lemma per
builder primitive — `emit1` (so `lit`), `emit` (so `call`, `apply`), `ite`, `defFun`, `global` — and one per
instruction run (`runI_call`, `runI_apply`) say what each does; a builder's theorem is a rewrite through them, never
an unfolding of `runB`. -/

namespace Rel.Lang.Plan

open Tab Rel.Kernel

/-! ### Reading registers -/

/-- `Except`'s bind on a success, which `simp` does not reduce by itself. -/
theorem ok_bind {α β : Type} (a : α) (f : α → Except String β) : (Except.ok a >>= f) = f a := rfl

/-- What `emit` appends: `i`, defining the next `nres` registers. -/
theorem emit_run (i : Instr) (nres : Nat) (is : Array Instr) (n : Nat) (fg : Array Fun × Array Fun) :
    (emit i nres).run (is, n, fg) = .ok ((List.range' n nres).toArray, is.push i, n + nres, fg) := rfl

theorem reg_of {rs : Array Val} {a : Nat} {v : Val} (h : rs[a]? = some v) (who : String) :
    reg rs who a = .ok v := by unfold reg; rw [h]; rfl

theorem mapM_ok_length {α β : Type} {f : α → Except String β} :
    ∀ (l : List α) {bs : List β}, l.mapM f = .ok bs → bs.length = l.length
  | [], bs, h => by rw [List.mapM_nil] at h; injection h with h; subst h; rfl
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok b =>
      cases hl : l.mapM f with
      | error e => rw [ha, hl] at h; cases h
      | ok cs => rw [ha, hl] at h; injection h with h; subst h; simp [mapM_ok_length l hl]

theorem mapM_ok_size {α β : Type} {f : α → Except String β} {as : Array α} {bs : Array β}
    (h : as.mapM f = .ok bs) : bs.size = as.size := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : as.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok cs => rw [hl] at h; injection h with h; subst h; simp [mapM_ok_length _ hl]

/-- The registers `xs` defined after `rs`, read back by their numbers. -/
theorem mapM_reg_range (rs xs : Array Val) (who : String) :
    (List.range' rs.size xs.size).toArray.mapM (reg (rs ++ xs) who) = .ok xs := by
  have key : ∀ (l : List Val) k, (∀ i (h : i < l.length), (rs ++ xs)[k + i]? = some l[i]) →
      (List.range' k l.length).mapM (reg (rs ++ xs) who) = .ok l := by
    intro l; induction l with
    | nil => intro k _; rfl
    | cons a l ih =>
      intro k h
      have h0 : (rs ++ xs)[k]? = some a := by simpa using h 0 (by simp)
      have h1 : ∀ i (hi : i < l.length), (rs ++ xs)[k + 1 + i]? = some l[i] := fun i hi => by
        rw [show k + 1 + i = k + (i + 1) by omega]; simpa using h (i + 1) (by simp; omega)
      rw [List.length_cons, List.range'_succ, List.mapM_cons, reg_of h0, ih (k + 1) h1]; rfl
  rw [List.mapM_toArray, ← Array.length_toList (xs := xs), key xs.toList rs.size ?_]
  · rfl
  · intro i h; rw [Array.getElem?_append_right (by omega)]; simp

/-! ### What the plan's functions and globals mean -/

/-- `fs` means the functions `F`: each entry is its function's meaning over the entries before it, as `sems` makes. -/
def FEnv (abi : String → Option Kernel) (fs : Array Sem) (F : Array Fun) : Prop :=
  ∀ i (h : i < F.size), fs[i]? = some (F[i].sem abi (fs.extract 0 i))

/-- `fs`, `gs` mean the functions and globals `fg`: a global holds what its body answers, writing nothing, under
    some meaning of the functions — any, as a built body answers the same under each. -/
def Env (abi : String → Option Kernel) (fs : Array Sem) (gs : Array (Array Val)) (fg : Array Fun × Array Fun) :
    Prop :=
  FEnv abi fs fg.1 ∧ ∀ i (h : i < fg.2.size), ∃ v, gs[i]? = some v ∧
    ∃ fs', FEnv abi fs' fg.1 ∧ ∀ ws, fg.2[i].sem abi fs' (gs.extract 0 i) #[] ws = .ok (v, ws)

variable {abi : String → Option Kernel}

theorem FEnv.mono {fs : Array Sem} {F a : Array Fun} (h : FEnv abi fs (F ++ a)) : FEnv abi fs F := fun i hi => by
  have := h i (by simp; omega); rwa [Array.getElem_append_left hi] at this

/-- A function's meaning reads only the entries before it, so a prefix of `fs` means a prefix of the functions. -/
theorem FEnv.extract {fs : Array Sem} {F a : Array Fun} (h : FEnv abi fs (F ++ a)) :
    FEnv abi (fs.extract 0 F.size) F := fun i hi => by
  have h1 := h i (by simp; omega)
  have hs : i < fs.size := by
    rcases Nat.lt_or_ge i fs.size with hs | hs
    · exact hs
    · rw [Array.getElem?_eq_none hs] at h1; cases h1
  rw [Array.getElem_append_left hi] at h1
  rw [Array.getElem?_extract, if_pos (by simp; omega), Array.extract_extract]
  simpa [Nat.min_eq_left (Nat.le_of_lt hi)] using h1

/-- A prefix of the functions and globals, under any meaning `fs'` of those functions and globals `gs'` agreeing
    with `gs` on that prefix. -/
theorem Env.restrict {fs fs' : Array Sem} {gs gs' : Array (Array Val)} {F a G b : Array Fun}
    (h : Env abi fs gs (F ++ a, G ++ b)) (hf : FEnv abi fs' F) (hg : gs'.extract 0 G.size = gs.extract 0 G.size) :
    Env abi fs' gs' (F, G) := by
  refine ⟨hf, fun i hi => ?_⟩
  simp only at hi
  obtain ⟨v, hv, fs'', h1, h2⟩ := h.2 i (by simp; omega)
  have ex : ∀ x : Array (Array Val), (x.extract 0 G.size)[i]? = x[i]? := fun x => by
    rw [Array.getElem?_extract]; split
    · simp
    · rw [Array.getElem?_eq_none (by omega)]
  have e1 : gs'[i]? = gs[i]? := by rw [← ex gs', hg, ex gs]
  have e2 : gs'.extract 0 i = gs.extract 0 i := by
    have := congrArg (·.extract 0 i) hg; simpa [Array.extract_extract, Nat.min_eq_left (Nat.le_of_lt hi)] using this
  refine ⟨v, e1.trans hv, fs'', FEnv.mono h1, fun ws => ?_⟩
  rw [e2]; simpa [Array.getElem_append_left hi] using h2 ws

theorem Env.mono {fs : Array Sem} {gs : Array (Array Val)} {fg fg' : Array Fun × Array Fun}
    (h1 : ∃ a, fg'.1 = fg.1 ++ a) (h2 : ∃ a, fg'.2 = fg.2 ++ a) (h : Env abi fs gs fg') : Env abi fs gs fg := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  obtain rfl : fg' = (fg.1 ++ a, fg.2 ++ b) := Prod.ext ha hb
  exact h.restrict (FEnv.mono h.1) rfl

/-! ### The primitives -/

/-- `b`, built after the registers `rs` while the functions and globals grow from `fg` to `fg'`, appends
    instructions which, run after `rs` and any writes under any meaning of `fg'`, define the registers `xs` and write
    nothing, and answers registers holding `out`. -/
def Builds (abi : String → Option Kernel) (fg fg' : Array Fun × Array Fun) (b : Bld (Array Nat))
    (rs out : Array Val) : Prop :=
  (∃ a, fg'.1 = fg.1 ++ a) ∧ (∃ a, fg'.2 = fg.2 ++ a) ∧ ∀ is, ∃ js xs r,
    b.run (is, rs.size, fg) = .ok (r, is ++ js, (rs ++ xs).size, fg') ∧
    (∀ fs gs, Env abi fs gs fg' → ∀ ws, runB abi fs gs js.toList rs ws = .ok (rs ++ xs, ws)) ∧
    ∀ who, r.mapM (reg (rs ++ xs) who) = .ok out

variable {fs : Array Sem} {gs : Array (Array Val)}

/-- A kernel call: its arguments read, its pure answer appended. -/
theorem runI_call {sym : String} {as : Array Nat} {k : Kernel} {f : Array Val → Except String (Array Val)}
    {vs out rs : Array Val} {ws : Writes} (hk : abi sym = some k) (hf : k.run = .inl f)
    (ha : as.mapM (reg rs sym) = .ok vs) (ho : f vs = .ok out) (hs : out.size = k.res.size) :
    runI abi fs gs (.call sym as) rs ws = .ok (rs ++ out, ws) := by
  simp [runI, hk, hf, ha, ho, hs, ok_bind, pure, Except.pure]

/-- A function application: its arguments read, its answer appended. -/
theorem runI_apply {f : Nat} {as : Array Nat} {g : Sem} {vs out rs : Array Val} {ws : Writes}
    (hf : fs[f]? = some g) (ha : as.mapM (reg rs s!"apply f{f}") = .ok vs) (ho : g gs vs ws = .ok (out, ws)) :
    runI abi fs gs (.apply f as) rs ws = .ok (rs ++ out, ws) := by
  simp [runI, hf, ha, ho, ok_bind, pure, Except.pure]

/-- Nothing built: `r` read. -/
theorem Builds.pure {fg : Array Fun × Array Fun} {r : Array Nat} {rs out : Array Val}
    (hm : ∀ who, r.mapM (reg rs who) = .ok out) : Builds abi fg fg (Pure.pure r) rs out :=
  ⟨⟨#[], by simp⟩, ⟨#[], by simp⟩, fun is => ⟨#[], #[], r, by simp only [Array.append_empty]; rfl,
    fun _ _ _ ws => by rw [Array.append_empty]; rfl, by simpa using hm⟩⟩

/-- One register defined by `i`, then `k` on it. `lit v` is `emit1 (.lit v)`. -/
theorem Builds.emit1 {fg fg' : Array Fun × Array Fun} {i : Instr} {v : Val} {k : Nat → Bld (Array Nat)}
    {rs out : Array Val} (hi : ∀ fs gs, Env abi fs gs fg' → ∀ ws, runI abi fs gs i rs ws = .ok (rs.push v, ws))
    (hk : Builds abi fg fg' (k rs.size) (rs.push v) out) : Builds abi fg fg' (Plan.emit1 i >>= k) rs out := by
  obtain ⟨h1, h2, hk⟩ := hk
  refine ⟨h1, h2, fun is => ?_⟩
  obtain ⟨js, xs, r, hr, hb, hm⟩ := hk (is.push i)
  refine ⟨#[i] ++ js, #[v] ++ xs, r, ?_, fun fs gs hE ws => ?_, fun who => ?_⟩
  · show (k rs.size).run (is.push i, rs.size + 1, fg) = _
    rw [← Array.size_push (xs := rs) v, hr]; simp [← Array.append_assoc]
  · rw [Array.toList_append, show (#[i] : Array Instr).toList = [i] from rfl, List.singleton_append,
      runB.eq_2, hi fs gs hE]
    exact (hb fs gs hE ws).trans (by simp [← Array.append_assoc])
  · simpa [← Array.append_assoc] using hm who

/-- An instruction defining `o`, then `k` on its registers. `call`, `apply` are `emit`s. -/
theorem Builds.emit_bind {fg fg' : Array Fun × Array Fun} {i : Instr} {o : Array Val} {k : Array Nat → Bld (Array Nat)}
    {rs out : Array Val} (hi : ∀ fs gs, Env abi fs gs fg' → ∀ ws, runI abi fs gs i rs ws = .ok (rs ++ o, ws))
    (hk : Builds abi fg fg' (k (List.range' rs.size o.size).toArray) (rs ++ o) out) :
    Builds abi fg fg' (Plan.emit i o.size >>= k) rs out := by
  obtain ⟨h1, h2, hk⟩ := hk
  refine ⟨h1, h2, fun is => ?_⟩
  obtain ⟨js, xs, r, hr, hb, hm⟩ := hk (is.push i)
  refine ⟨#[i] ++ js, o ++ xs, r, ?_, fun fs gs hE ws => ?_, fun who => ?_⟩
  · show (k _).run (is.push i, rs.size + o.size, fg) = _
    rw [show rs.size + o.size = (rs ++ o).size by simp, hr]; simp [← Array.append_assoc]
  · rw [Array.toList_append, show (#[i] : Array Instr).toList = [i] from rfl, List.singleton_append,
      runB.eq_2, hi fs gs hE]
    exact (hb fs gs hE ws).trans (by simp [← Array.append_assoc])
  · simpa [← Array.append_assoc] using hm who

/-- An instruction defining `out`, last. -/
theorem Builds.emit {fg : Array Fun × Array Fun} {i : Instr} {nres : Nat} {rs out : Array Val}
    (hi : ∀ fs gs, Env abi fs gs fg → ∀ ws, runI abi fs gs i rs ws = .ok (rs ++ out, ws)) (hn : out.size = nres) :
    Builds abi fg fg (Plan.emit i nres) rs out := by
  subst hn
  have := Builds.emit_bind (k := Pure.pure) hi (Builds.pure (mapM_reg_range rs out))
  rwa [bind_pure] at this

/-- `apply f(as)` of a function answering `o` on the arguments `vs`, then `k` on its registers. -/
theorem Builds.apply {fg fg' : Array Fun × Array Fun} {f : Nat} {as : Array Nat} {vs o : Array Val}
    {k : Array Nat → Bld (Array Nat)} {rs out : Array Val}
    (hf : ∀ fs gs, Env abi fs gs fg' → ∀ ws, ∃ g, fs[f]? = some g ∧ g gs vs ws = .ok (o, ws))
    (ha : as.mapM (reg rs s!"apply f{f}") = .ok vs)
    (hk : Builds abi fg fg' (k (List.range' rs.size o.size).toArray) (rs ++ o) out) :
    Builds abi fg fg' (Plan.apply f as o.size >>= k) rs out :=
  Builds.emit_bind (fun fs gs hE ws => let ⟨_, hg, ho⟩ := hf fs gs hE ws; runI_apply hg ha ho) hk

/-- `if c then t else e`: the branch the bit in `c` names; the other must build, as many registers wide. -/
theorem Builds.ite {fg fg1 fg2 : Array Fun × Array Fun} {c : Nat} {bt : Bool} {t e : Bld (Array Nat)}
    {rs ot oe : Array Val} (hc : rs[c]? = some (.bit bt)) (ht : Builds abi fg fg1 t rs ot)
    (he : Builds abi fg1 fg2 e rs oe) (hs : ot.size = oe.size) :
    Builds abi fg fg2 (Plan.ite c t e) rs (if bt then ot else oe) := by
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, ht⟩ := ht
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩, he⟩ := he
  obtain ⟨jt, xt, rt, hrt, hbt, hmt⟩ := ht #[]
  obtain ⟨je, xe, re, hre, hbe, hme⟩ := he #[]
  have st : ot.size = rt.size := mapM_ok_size (hmt "")
  have se : oe.size = re.size := mapM_ok_size (hme "")
  have ho : (if bt then ot else oe).size = rt.size := by cases bt <;> simp <;> omega
  refine ⟨⟨a1 ++ a2, by rw [ha2, ha1, Array.append_assoc]⟩, ⟨b1 ++ b2, by rw [hb2, hb1, Array.append_assoc]⟩,
    fun is => ⟨#[.ite c jt.toList rt je.toList re], if bt then ot else oe, (List.range' rs.size rt.size).toArray,
    ?_, fun fs gs hE ws => ?_, fun who => ho ▸ mapM_reg_range rs _ who⟩⟩
  · have hrs : rt.size = re.size := by omega
    simp only [Plan.ite, block, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, monadLift_self, hrt, hre,
      ok_bind, pure_bind, bind_assoc]
    simp [hrs, emit_run, ho]
  · have hE1 : Env abi fs gs fg1 := Env.mono ⟨a2, ha2⟩ ⟨b2, hb2⟩ hE
    rw [show (#[Instr.ite c jt.toList rt je.toList re] : Array Instr).toList = [.ite c jt.toList rt je.toList re]
      from rfl, runB.eq_2]
    cases bt <;> simp [runI, reg_of hc, hbt fs gs hE1, hbe fs gs hE, hmt, hme, runB.eq_1, ok_bind,
      Functor.map, Except.map]

/-- `defFun ps b`, then `k` on its number. `Q pv o` says what the function answers: `o` on the parameters `pv`;
    `pv₀` is one such, from which the body is built. `k` may apply the function at any later table. -/
theorem Builds.defFun {fg fg1 fg' : Array Fun × Array Fun} {ps : Array Ty} {b : Array Nat → Bld (Array Nat)}
    {k : Nat → Bld (Array Nat)} {Q : Array Val → Array Val → Prop} {pv₀ o₀ rs out : Array Val}
    (hq : ∀ pv o, Q pv o → pv.size = ps.size) (h₀ : Q pv₀ o₀)
    (hb : ∀ pv o, Q pv o → Builds abi fg fg1 (b (List.range ps.size).toArray) pv o)
    (hk : ∀ F : Fun, (∀ fs gs F' G', (∃ a, F' = fg1.1.push F ++ a) → (∃ a, G' = fg1.2 ++ a) →
        Env abi fs gs (F', G') → ∀ pv o ws, Q pv o → ∃ g, fs[fg1.1.size]? = some g ∧ g gs pv ws = .ok (o, ws)) →
      Builds abi (fg1.1.push F, fg1.2) fg' (k fg1.1.size) rs out) :
    Builds abi fg fg' (Plan.defFun ps b >>= k) rs out := by
  obtain ⟨F0, G0⟩ := fg; obtain ⟨F1, G1⟩ := fg1
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, hb₀⟩ := hb pv₀ o₀ h₀
  obtain ⟨body, xs₀, r, hrun, -, -⟩ := hb₀ #[]
  rw [hq _ _ h₀, Array.empty_append] at hrun
  have hF : ∀ fs gs F' G', (∃ a, F' = F1.push ⟨ps, body.toList, r⟩ ++ a) → (∃ a, G' = G1 ++ a) →
      Env abi fs gs (F', G') → ∀ pv o ws, Q pv o → ∃ g, fs[F1.size]? = some g ∧ g gs pv ws = .ok (o, ws) := by
    rintro fs gs F' G' ⟨a, rfl⟩ ⟨c, rfl⟩ hE pv o ws hpo
    rw [Array.push_eq_append, Array.append_assoc] at hE
    refine ⟨Fun.sem abi (fs.extract 0 F1.size) ⟨ps, body.toList, r⟩, by simpa using hE.1 F1.size (by simp; omega), ?_⟩
    obtain ⟨-, -, h⟩ := hb pv o hpo
    obtain ⟨js, xs, r', hr', hrun', hm'⟩ := h #[]
    rw [hq _ _ hpo, Array.empty_append, hrun] at hr'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl, -⟩ := hr'
    have hE' : Env abi (fs.extract 0 F1.size) gs (F1, G1) := hE.restrict (FEnv.extract hE.1) rfl
    simp [Fun.sem, hrun' _ gs hE' ws, hm' "result", ok_bind, Functor.map, Except.map]
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩, hk₀⟩ := hk _ hF
  refine ⟨⟨a1 ++ #[⟨ps, body.toList, r⟩] ++ a2, ?_⟩, ⟨b1 ++ b2, ?_⟩, fun is => ?_⟩
  · rw [ha2]; simp only at ha1 ⊢; subst ha1; simp only [Array.push_eq_append, Array.append_assoc]
  · rw [hb2]; simp only at hb1 ⊢; subst hb1; simp only [Array.append_assoc]
  obtain ⟨js, xs, r2, hr2, hbk, hm2⟩ := hk₀ is
  refine ⟨js, xs, r2, ?_, hbk, hm2⟩
  simp only [Plan.defFun, StateT.run_bind, StateT.run_get, StateT.run_set, liftM, StateT.run_monadLift,
    monadLift_self, pure_bind, bind_assoc, hrun, ok_bind]
  exact hr2


/-- A block of two parts runs as the first, then the second on what it left. -/
theorem runB_append (l1 l2 : List Instr) (rs : Array Val) (ws : Writes) :
    runB abi fs gs (l1 ++ l2) rs ws = (runB abi fs gs l1 rs ws >>= fun p => runB abi fs gs l2 p.1 p.2) := by
  induction l1 generalizing rs ws with
  | nil => rfl
  | cons i l ih =>
    rw [List.cons_append, runB.eq_2, runB.eq_2]
    cases runI abi fs gs i rs ws with
    | error e => rfl
    | ok p => exact ih p.1 p.2

/-- `b`, then `k` on its registers: `k` built after whatever `b` defined, holding `b`'s answer at `b`'s
    registers. -/
theorem Builds.bind {fg fg1 fg' : Array Fun × Array Fun} {b : Bld (Array Nat)} {k : Array Nat → Bld (Array Nat)}
    {rs o out : Array Val} (hb : Builds abi fg fg1 b rs o)
    (hk : ∀ r xs, (∀ who, r.mapM (reg (rs ++ xs) who) = .ok o) → Builds abi fg1 fg' (k r) (rs ++ xs) out) :
    Builds abi fg fg' (b >>= k) rs out := by
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, hb⟩ := hb
  obtain ⟨_, xs0, r0, -, -, hm0⟩ := hb #[]
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩, -⟩ := hk r0 xs0 hm0
  refine ⟨⟨a1 ++ a2, by rw [ha2, ha1, Array.append_assoc]⟩, ⟨b1 ++ b2, by rw [hb2, hb1, Array.append_assoc]⟩,
    fun is => ?_⟩
  obtain ⟨js, xs, r, hr, hs, hm⟩ := hb is
  obtain ⟨-, -, hk'⟩ := hk r xs hm
  obtain ⟨js2, xs2, r2, hr2, hs2, hm2⟩ := hk' (is ++ js)
  refine ⟨js ++ js2, xs ++ xs2, r2, ?_, fun fs gs hE ws => ?_, fun who => by simpa [Array.append_assoc] using hm2 who⟩
  · simp only [StateT.run_bind, hr, ok_bind]; simpa [Array.append_assoc] using hr2
  · rw [Array.toList_append, runB_append, hs fs gs (Env.mono ⟨a2, ha2⟩ ⟨b2, hb2⟩ hE) ws, ok_bind]
    simpa [Array.append_assoc] using hs2 fs gs hE ws


/-- `guard c` with the bit in `c` set defines no register: `k` runs after the registers so far. -/
theorem Builds.guard {fg fg' : Array Fun × Array Fun} {c : Nat} {msg : String} {as : Array Nat} {k : Bld (Array Nat)}
    {rs out : Array Val} (hc : rs[c]? = some (.bit true)) (hk : Builds abi fg fg' k rs out) :
    Builds abi fg fg' (Plan.guard c msg as >>= fun _ => k) rs out := by
  have e : (Plan.guard c msg as >>= fun _ => k) =
      (Plan.emit (.ite c [] #[] [.fail msg as] #[]) (#[] : Array Val).size >>= fun _ => k) := by
    funext st; rfl
  rw [e]
  refine Builds.emit_bind (fun _ _ _ ws => ?_) (by simpa using hk)
  simp only [runI, reg_of hc, ok_bind, runB.eq_1]
  simp; rfl

/-! ### Straight-line builders -/

/-- A one-register kernel call: its arguments read, its one answer pushed. -/
theorem runI_call1 {k : Kernel} {f : Array Val → Except String (Array Val)} {as : Array Nat} {vs rs : Array Val}
    {v : Val} {ws : Writes} (hk : abi k.sym = some k) (hf : k.run = .inl f) (ha : as.mapM (reg rs k.sym) = .ok vs)
    (ho : f vs = .ok #[v]) (hs : k.res.size = 1) : runI abi fs gs (.call k.sym as) rs ws = .ok (rs.push v, ws) := by
  rw [Array.push_eq_append]; exact runI_call hk hf ha ho (by simp [hs])

/-- `call1 k as`, then the rest: the kernel `k` of the ABI answers one register from the registers `as` read. -/
theorem Builds.call1 {fg fg' : Array Fun × Array Fun} {k : Kernel} {f : Array Val → Except String (Array Val)}
    {as : Array Nat} {vs rs out : Array Val} {v : Val} {c : Nat → Bld (Array Nat)} (hk : abiOf k.sym = some k)
    (hf : k.run = .inl f) (ha : as.mapM (reg rs k.sym) = .ok vs) (ho : f vs = .ok #[v]) (hs : k.res.size = 1)
    (hc : Builds abiOf fg fg' (c rs.size) (rs.push v) out) : Builds abiOf fg fg' (Plan.call1 k as >>= c) rs out := by
  rw [show Plan.call1 k as = Plan.emit1 (.call k.sym as) by simp [Plan.call1, hs]]
  exact Builds.emit1 (fun _ _ _ _ => runI_call1 hk hf ha ho hs) hc

/-- `lit x`, then the rest: the literal is pushed. -/
theorem Builds.lit {fg fg' : Array Fun × Array Fun} {x : Val} {rs out : Array Val} {c : Nat → Bld (Array Nat)}
    (hc : Builds abi fg fg' (c rs.size) (rs.push x) out) : Builds abi fg fg' (Plan.lit x >>= c) rs out :=
  Builds.emit1 (fun _ _ _ _ => rfl) hc

/-- The registers `as` read from concrete registers: each a literal index into a known array. -/
macro "reads" : tactic => `(tactic| (rw [List.mapM_toArray]; simp only [List.mapM_cons, List.mapM_nil]; rfl))

/-- One step of a straight-line builder: an `if` of the builder, a literal, a kernel call of one result, or the
answer. Each lemma is matched by its head only (reducible), so a step that is not its case fails at once. -/
macro "build_step" : tactic => `(tactic| ((try simp only [bind_assoc, pure_bind]); (first
  | split
  | with_reducible refine Builds.lit ?_
  | with_reducible refine Builds.call1 (by with_unfolding_all simp [abiOf, Rel.Lang.Plan.abi, List.find?])
                          (by with_unfolding_all rfl) (by with_unfolding_all reads) (by with_unfolding_all rfl) rfl ?_
  | (with_reducible refine Builds.pure ?_); intro; reads)))

/-! ### `whereB`: primitives its recipe uses beyond `lit`/`call1` -/

/-- `ctorB`, then the rest: the constructor of `os`, `ss` (the registers `objs`, `scal` read) is pushed. -/
theorem Builds.ctorB {fg fg' : Array Fun × Array Fun} {tag : Nat} {objs scal : Array Nat} {os ss rs out : Array Val}
    {c : Nat → Bld (Array Nat)} (ho : objs.mapM (reg rs "ctor") = .ok os) (hs : scal.mapM (reg rs "ctor") = .ok ss)
    (hc : Builds abi fg fg' (c rs.size) (rs.push (.ctor tag os ss)) out) :
    Builds abi fg fg' (Plan.ctorB tag objs scal >>= c) rs out :=
  Builds.emit1 (fun _ _ _ ws => by simp [runI, ho, hs, ok_bind]; rfl) hc

/-- `projB`, then the rest: field `i` of the constructor `tag` in register `x`, a `v` of type `t`, is pushed. -/
theorem Builds.projB {fg fg' : Array Fun × Array Fun} {x tag i : Nat} {t : Ty} {os ss rs out : Array Val} {v : Val}
    {c : Nat → Bld (Array Nat)} (hx : rs[x]? = some (.ctor tag os ss)) (hv : os[i]? = some v) (ht : v.ty = t)
    (hc : Builds abi fg fg' (c rs.size) (rs.push v) out) : Builds abi fg fg' (Plan.projB x tag i t >>= c) rs out :=
  Builds.emit1 (fun _ _ _ ws => by
    have e : (t == t) = true := by cases t <;> rfl
    simp [runI, reg_of hx, hv, ht, e, ok_bind]; rfl) hc

/-- `callK k as`, then the rest: the kernel `k` answers all its registers `o` from the registers `as` read. -/
theorem Builds.callK {fg fg' : Array Fun × Array Fun} {k : Kernel} {f : Array Val → Except String (Array Val)}
    {as : Array Nat} {vs o rs out : Array Val} {c : Array Nat → Bld (Array Nat)} (hk : abiOf k.sym = some k)
    (hf : k.run = .inl f) (ha : as.mapM (reg rs k.sym) = .ok vs) (ho : f vs = .ok o) (hs : o.size = k.res.size)
    (hc : Builds abiOf fg fg' (c (List.range' rs.size o.size).toArray) (rs ++ o) out) :
    Builds abiOf fg fg' (Plan.callK k as >>= c) rs out := by
  rw [show Plan.callK k as = Plan.emit (.call k.sym as) o.size by simp [Plan.callK, Plan.call, hs]]
  exact Builds.emit_bind (fun _ _ _ _ => runI_call hk hf ha ho hs) hc

/-- `nth rs i` of a register list that holds `r` at `i` is `r`, building nothing. -/
theorem nth_of {rs : Array Nat} {i r : Nat} {who : String} (h : rs[i]? = some r) : nth rs i who = Pure.pure r := by
  simp [nth, h]

/-- `if c then t else e` with the bit in `c` set: `t` builds and runs, and `e` is only built — its instructions never
    run, so it need not succeed (`whereB`'s `else` reads a fold that is `none` exactly where `then` is taken). -/
theorem Builds.ite_true {fg fg1 fg2 : Array Fun × Array Fun} {c : Nat} {t e : Bld (Array Nat)} {rs ot : Array Val}
    {je : Array Instr} {n' : Nat} {re' : Array Nat} (hc : rs[c]? = some (.bit true)) (ht : Builds abi fg fg1 t rs ot)
    (he : e.run (#[], rs.size, fg1) = .ok (re', je, n', fg2)) (hs : ot.size = re'.size)
    (h2 : (∃ a, fg2.1 = fg1.1 ++ a) ∧ (∃ a, fg2.2 = fg1.2 ++ a)) :
    Builds abi fg fg2 (Plan.ite c t e) rs ot := by
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, ht⟩ := ht
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩⟩ := h2
  obtain ⟨jt, xt, rt, hrt, hbt, hmt⟩ := ht #[]
  have st : ot.size = rt.size := mapM_ok_size (hmt "")
  refine ⟨⟨a1 ++ a2, by rw [ha2, ha1, Array.append_assoc]⟩, ⟨b1 ++ b2, by rw [hb2, hb1, Array.append_assoc]⟩,
    fun is => ⟨#[.ite c jt.toList rt je.toList re'], ot, (List.range' rs.size rt.size).toArray, ?_, fun fs gs hE ws => ?_,
    fun who => st ▸ mapM_reg_range rs _ who⟩⟩
  · have hrs : rt.size = re'.size := by omega
    simp only [Plan.ite, block, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, monadLift_self, hrt,
      he, ok_bind, pure_bind, bind_assoc]
    simp [hrs, emit_run, st]
  · have hE1 : Env abi fs gs fg1 := Env.mono ⟨a2, ha2⟩ ⟨b2, hb2⟩ hE
    rw [show (#[Instr.ite c jt.toList rt je.toList re'] : Array Instr).toList = [.ite c jt.toList rt je.toList re']
      from rfl, runB.eq_2]
    simp [runI, reg_of hc, hbt fs gs hE1, hmt, runB.eq_1, ok_bind, Functor.map, Except.map]
/-! ### Recipes on the kernels: `constB`, `scanB` -/

/-- A `foR` column is a register that reads back as itself (`Reg Enc` writes its parts and reads them back). -/
theorem foR_get_put (m p : ByteArray) : (Reg.get? (Reg.put (Ext.Enc.foR m p : Enc)) : Option Enc) = some (.foR m p) := by
  have hp : (Reg.put (Ext.Enc.foR m p : Enc) : Val) = .ctor 0 (#[m, p].map .bytes) #[] := by with_unfolding_all rfl
  rw [hp]
  dsimp only [Reg.get?]
  conv => lhs; whnf
  rw [Array.mapM_eq_mapM_toList]
  have c4 : ((0 : Nat) == (Ext.Enc.pos : Enc).ctorIdx) = false := by with_unfolding_all rfl
  simp [c4]
  with_unfolding_all rfl

/-- A `wordsFoR` is a register that reads back as itself. -/
theorem wordsFoR_get_put (ws : Array UInt64) :
    (Reg.get? (Reg.put (wordsFoR ws)) : Option Enc) = some (wordsFoR ws) := foR_get_put _ _

/-- `constB n fill`, `n` holding the row count `nv` and `fill` the word `fv`: its register holds the column
    `kscatter .last 0 e e nv fv` answers (`e` the empty column: no row is scattered). -/
theorem constB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n fill : Nat} {nv : USize} {fv : UInt64} {c : Enc}
    (hn : rs[n]? = some (.size nv)) (hf : rs[fill]? = some (.u64 fv))
    (hk : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv fv = .ok c) :
    Builds abiOf fg fg (do let r ← constB n fill; Pure.pure #[r]) rs #[Reg.put c] := by
  have hn1 : n < rs.size := by
    rcases Nat.lt_or_ge n rs.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hn; cases hn
  have hf1 : fill < rs.size := by
    rcases Nat.lt_or_ge fill rs.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hf; cases hf
  unfold constB; simp only [bind_assoc]
  with_reducible refine Builds.lit ?_
  with_reducible refine Builds.lit ?_
  with_reducible refine Builds.lit ?_
  refine Builds.call1 (vs := #[Reg.put Kernel.Op.last, .size 0, Reg.put (wordsFoR #[]), Reg.put (wordsFoR #[]),
      .size nv, .u64 fv]) (v := Reg.put c) (by with_unfolding_all simp [abiOf, Rel.Lang.Plan.abi, List.find?])
    (by with_unfolding_all rfl) ?_ ?_ rfl ?_
  · rw [List.mapM_toArray]
    simp [reg, Array.getElem?_push, Array.getElem_push, hn, hf, show n ≠ rs.size by omega, show n ≠ rs.size + 1 by omega, show n ≠ rs.size + 1 + 1 by omega, show fill ≠ rs.size by omega, show fill ≠ rs.size + 1 by omega, show fill ≠ rs.size + 1 + 1 by omega, show rs.size ≠ rs.size + 1 + 1 by omega]
    rfl
  · have hop : (Reg.get? (Reg.put Kernel.Op.last) : Option Kernel.Op) = some .last := by with_unfolding_all rfl
    have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
    have hu : ∀ x : UInt64, (Reg.get? (Val.u64 x) : Option UInt64) = some x := fun _ => rfl
    simp [arg, hop, hsz, hu, wordsFoR_get_put, hk, Out.out]
    rfl
  · with_reducible refine Builds.pure ?_
    intro who
    simp [reg, Array.size_push, Array.getElem_push]
    rfl


/-! ### `scanB`: its arguments as lists and pairs -/

/-- A register stays where it was after more are appended. -/
theorem get_app {rs xs : Array Val} {i : Nat} {v : Val} (h : rs[i]? = some v) : (rs ++ xs)[i]? = some v := by
  rcases Nat.lt_or_ge i rs.size with h1 | h1
  · rw [Array.getElem?_append_left h1, h]
  · rw [Array.getElem?_eq_none h1] at h; cases h

theorem get_push {rs : Array Val} {x : Val} {i : Nat} {v : Val} (h : rs[i]? = some v) : (rs.push x)[i]? = some v := by
  rw [Array.push_eq_append]; exact get_app h

/-- `Option`'s `mapM` over a cons answers a cons exactly when the head and the tail answer. -/
theorem omapM_cons {α β : Type} {f : α → Option β} {x : α} {l : List α} {ws : List β} :
    (x :: l).mapM f = some ws ↔ ∃ v vs, f x = some v ∧ l.mapM f = some vs ∧ ws = v :: vs := by
  rw [List.mapM_cons]
  cases hx : f x <;> cases hl : l.mapM f <;> simp [eq_comm]

/-- The registers `l`, holding `vs`, still hold them after more are appended. -/
theorem mapM_get_app {rs xs : Array Val} : ∀ {l : List Nat} {vs : List Val},
    l.mapM (fun x => rs[x]?) = some vs → l.mapM (fun x => (rs ++ xs)[x]?) = some vs
  | [], _, h => h
  | _ :: _, _, h => by
    obtain ⟨v, vs, hx, hl, rfl⟩ := omapM_cons.mp h
    exact omapM_cons.mpr ⟨v, vs, get_app hx, mapM_get_app hl, rfl⟩

/-- The registers `l`, holding `vs`, read. -/
theorem reads_of {rs : Array Val} {who : String} {l : List Nat} {vs : List Val}
    (h : l.mapM (fun x => rs[x]?) = some vs) : l.toArray.mapM (reg rs who) = .ok vs.toArray := by
  rw [List.mapM_toArray]
  suffices e : l.mapM (reg rs who) = .ok vs by rw [e]; rfl
  induction l generalizing vs with
  | nil => simp at h; subst h; rfl
  | cons x l ih =>
    obtain ⟨v, vs, hx, hl, rfl⟩ := omapM_cons.mp h
    rw [List.mapM_cons, reg_of hx, ih hl]; rfl

/-- Registers each reading as an `α`: the values they hold. -/
theorem mapM_bind_split {α : Type} [Reg α] {rs : Array Val} : ∀ {es : List Nat} {xs : List α},
    es.mapM (fun x => rs[x]?.bind Reg.get?) = some xs →
    ∃ bs, es.mapM (fun x => rs[x]?) = some bs ∧ bs.mapM Reg.get? = some xs
  | [], xs, h => ⟨[], rfl, h⟩
  | _ :: _, _, h => by
    obtain ⟨a, as, ha, hl, rfl⟩ := omapM_cons.mp h
    obtain ⟨v, hv, hg⟩ := Option.bind_eq_some_iff.mp ha
    obtain ⟨bs, hbs, hgs⟩ := mapM_bind_split hl
    exact ⟨v :: bs, omapM_cons.mpr ⟨v, bs, hv, hbs, rfl⟩, omapM_cons.mpr ⟨a, as, hg, hgs, rfl⟩⟩

/-- The list `Reg (List α)` lays out of the cells `vs` reads back as the cells read. -/
theorem listGet?_foldr {α : Type} [Reg α] (vs : List Val) :
    (Reg.get? (vs.foldr (fun v c => .ctor 1 #[v, c] #[]) (.ctor 0 #[] #[])) : Option (List α)) = vs.mapM Reg.get? := by
  show listGet? _ = _
  induction vs with
  | nil => rw [listGet?.eq_def]; rfl
  | cons v vs ih =>
    rw [listGet?.eq_def]
    change (do pure ((← Reg.get? v) :: (← listGet? (vs.foldr (fun v c => Val.ctor 1 #[v, c] #[]) (.ctor 0 #[] #[])))))
      = _
    rw [ih, List.mapM_cons]

/-- Pairs of `v` (reading `a`) and each of `bs` (reading `xs`) read as the pairs of `a` and each of `xs`. -/
theorem mapM_pair {α β : Type} [Reg α] [Reg β] {v : Val} {a : α} (hv : Reg.get? v = some a) :
    ∀ (bs : List Val) {xs : List β}, bs.mapM Reg.get? = some xs →
      (bs.map fun b => Val.ctor 0 #[v, b] #[]).mapM (Reg.get? (α := α × β)) = some (xs.map (a, ·))
  | [], xs, h => by simp at h; subst h; rfl
  | b :: bs, _, h => by
    obtain ⟨x, ys, hb, hl, rfl⟩ := omapM_cons.mp h
    have hp : (Reg.get? (Val.ctor 0 #[v, b] #[]) : Option (α × β)) = some (a, x) := by
      show (do pure (← Reg.get? v, ← Reg.get? b)) = _; rw [hv, hb]; rfl
    exact omapM_cons.mpr ⟨_, _, hp, mapM_pair hv bs hl, rfl⟩

/-- `es.mapM (srcB n)`, then `k` on its registers: each the pair of `a` (register `n`) and its column. -/
theorem Builds.srcs {fg fg' : Array Fun × Array Fun} {n : Nat} {a : Val} {out : Array Val} :
    ∀ (es : List Nat) {bs : List Val} {rs : Array Val} {k : List Nat → Bld (Array Nat)}, rs[n]? = some a →
    es.mapM (fun x => rs[x]?) = some bs →
    (∀ xs rl, rl.mapM (fun r => (rs ++ xs)[r]?) = some (bs.map fun b => Val.ctor 0 #[a, b] #[]) →
      Builds abi fg fg' (k rl) (rs ++ xs) out) →
    Builds abi fg fg' (es.mapM (srcB n) >>= k) rs out
  | [], _, rs, k, _, h, hk => by
    simp at h; subst h; simpa using hk #[] [] rfl
  | x :: es, _, rs, k, hn, h, hk => by
    obtain ⟨b, bs, hx, h1, rfl⟩ := omapM_cons.mp h
    rw [List.mapM_cons]; simp only [bind_assoc, pure_bind]; unfold srcB
    refine Builds.ctorB (reads_of (l := [n, x]) (vs := [a, b]) (by simp [hn, hx])) (reads_of (l := []) (vs := []) rfl) ?_
    have e : ∀ xs, rs.push (Val.ctor 0 #[a, b] #[]) ++ xs = rs ++ (#[Val.ctor 0 #[a, b] #[]] ++ xs) := fun xs => by
      simp only [Array.push_eq_append, Array.append_assoc]
    refine Builds.srcs es (get_push hn) (by rw [Array.push_eq_append]; exact mapM_get_app h1) fun xs rl hrl => ?_
    rw [e] at hrl ⊢
    exact hk _ _ (omapM_cons.mpr ⟨_, _, by rw [← Array.append_assoc]; exact get_app (by simp), hrl, rfl⟩)

/-- The cells `l` (holding `vs`) consed onto the list in `acc`, then `k` on the list's register. -/
theorem Builds.cells {fg fg' : Array Fun × Array Fun} {out rs : Array Val} {acc : Nat} {av : Val}
    (ha : rs[acc]? = some av) : ∀ (l : List Nat) {vs : List Val} {k : Nat → Bld (Array Nat)},
    l.mapM (fun x => rs[x]?) = some vs →
    (∀ xs r, (rs ++ xs)[r]? = some (vs.foldr (fun v c => .ctor 1 #[v, c] #[]) av) →
      Builds abi fg fg' (k r) (rs ++ xs) out) →
    Builds abi fg fg' (l.foldrM (fun x c => Plan.ctorB 1 #[x, c] #[]) acc >>= k) rs out
  | [], _, k, h, hk => by simp at h; subst h; simpa using hk #[] acc (by simpa using ha)
  | x :: l, _, k, h, hk => by
    obtain ⟨v, vs, hx, h1, rfl⟩ := omapM_cons.mp h
    rw [List.foldrM_cons, bind_assoc]
    refine Builds.cells ha l h1 fun xs r hr => Builds.ctorB
      (reads_of (l := [x, r]) (vs := [v, vs.foldr (fun v c => .ctor 1 #[v, c] #[]) av]) (by simp [get_app hx, hr]))
      (reads_of (l := []) (vs := []) rfl) ?_
    have e : (rs ++ xs).push (Val.ctor 1 #[v, vs.foldr (fun v c => .ctor 1 #[v, c] #[]) av] #[]) =
        rs ++ xs.push (Val.ctor 1 #[v, vs.foldr (fun v c => .ctor 1 #[v, c] #[]) av] #[]) := by
      simp only [Array.push_eq_append, Array.append_assoc]
    rw [e]; exact hk _ _ (by rw [← e]; simp)

/-- `listB l` of the registers `l` holding `vs`, then `k` on its register: the list `Reg (List α)` lays out. -/
theorem Builds.listB {fg fg' : Array Fun × Array Fun} {out rs : Array Val} {l : List Nat} {vs : List Val}
    {k : Nat → Bld (Array Nat)} (h : l.mapM (fun x => rs[x]?) = some vs)
    (hk : ∀ xs r, (rs ++ xs)[r]? = some (vs.foldr (fun v c => .ctor 1 #[v, c] #[]) (.ctor 0 #[] #[])) →
      Builds abi fg fg' (k r) (rs ++ xs) out) : Builds abi fg fg' (Plan.listB l >>= k) rs out := by
  unfold Plan.listB; rw [bind_assoc]
  refine Builds.ctorB (reads_of (l := []) (vs := []) rfl) (reads_of (l := []) (vs := []) rfl) ?_
  have e : ∀ xs, rs.push (Val.ctor 0 #[] #[]) ++ xs = rs ++ (#[Val.ctor 0 #[] #[]] ++ xs) := fun xs => by
    simp only [Array.push_eq_append, Array.append_assoc]
  refine Builds.cells (av := .ctor 0 #[] #[]) (by simp) l (by rw [Array.push_eq_append]; exact mapM_get_app h) fun xs r hr => ?_
  rw [e] at hr ⊢; exact hk _ _ hr

/-- `scanB op t n seg es`, the registers holding: the row count `nv` (`n`), the segment-start column `sg` (`seg`,
    `none`: every row, a map) and the columns `xs` (`es`), each read as `Reg.get?` reads it: its two registers are
    the pair `kscan op false t t nv sg (xs.map (nv, ·)) [] []` answers. -/
theorem scanB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {op : Kernel.Op} {t : QAtomicType} {n : Nat}
    {nv : USize} {seg : Option Nat} {sg : Option Enc} {es : List Nat} {xs : List Enc} {r : Enc × Option UInt64}
    (hop : (Reg.get? (Reg.put op) : Option Kernel.Op) = some op) (hn : rs[n]?.bind Reg.get? = some nv)
    (hseg : seg.mapM (fun s => rs[s]?.bind Reg.get?) = some sg)
    (hes : es.mapM (fun x => rs[x]?.bind Reg.get?) = some xs)
    (hk : kscan op false t t nv sg (xs.map (nv, ·)) [] [] = .ok r) :
    Builds abiOf fg fg (scanB op t n seg es) rs #[Reg.put r.1, Reg.put r.2] := by
  obtain ⟨vn, hvn, hgn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨bs, hbs, hgb⟩ := mapM_bind_split hes
  have ht : (Reg.get? (Reg.put t) : Option QAtomicType) = some t := by cases t <;> rfl
  have hl : (Reg.get? ((bs.map fun b => Val.ctor 0 #[vn, b] #[]).foldr (fun v c => .ctor 1 #[v, c] #[])
      (.ctor 0 #[] #[])) : Option (List (USize × Enc))) = some (xs.map (nv, ·)) := by
    rw [listGet?_foldr, mapM_pair hgn bs hgb]
  have hnil : (Reg.get? (Val.ctor 0 #[] #[]) : Option (List (Kernel.Op × UInt64))) = some [] := by
    show listGet? _ = _; rw [listGet?.eq_def]; rfl
  unfold scanB
  -- the segment register `gv`; then the same steps for either `seg`
  cases seg
  case' none =>
    simp at hseg; subst hseg; dsimp only
    refine Builds.ctorB (reads_of (l := []) (vs := []) rfl) (reads_of (l := []) (vs := []) rfl) ?_
    have hgv : (Reg.get? (Val.ctor 0 #[] #[]) : Option (Option Enc)) = some none := rfl
    generalize Val.ctor 0 #[] #[] = gv at hgv ⊢
  case' some s =>
    obtain ⟨e, he, rfl⟩ : ∃ e : Enc, rs[s]?.bind Reg.get? = some e ∧ sg = some e := by
      cases h : rs[s]?.bind (Reg.get? (α := Enc)) <;> simp [h] at hseg; exact ⟨_, rfl, hseg.symm⟩
    obtain ⟨v, hv, hge⟩ := Option.bind_eq_some_iff.mp he
    dsimp only
    refine Builds.ctorB (reads_of (l := [s]) (vs := [v]) (by simp [hv])) (reads_of (l := []) (vs := []) rfl) ?_
    have hgv : (Reg.get? (Val.ctor 1 #[v] #[]) : Option (Option Enc)) = some (some e) := by
      show some <$> Reg.get? v = _; rw [hge]; rfl
    generalize Val.ctor 1 #[v] #[] = gv at hgv ⊢
  all_goals
    refine Builds.lit (Builds.lit (Builds.lit (Builds.lit ?_)))
    refine Builds.srcs es (get_push (get_push (get_push (get_push (get_push hvn)))))
      (by simp only [Array.push_eq_append]; exact mapM_get_app (mapM_get_app (mapM_get_app (mapM_get_app
        (mapM_get_app hbs))))) fun xs1 rl hrl => ?_
    refine Builds.listB hrl fun xs2 r1 hr1 => ?_
    refine Builds.listB (l := []) rfl fun xs3 r2 hr2 => ?_
    refine Builds.listB (l := []) rfl fun xs4 r3 hr3 => ?_
    rw [← bind_pure (Plan.callK (kernel% kscan) _)]
    refine Builds.callK (o := #[Reg.put r.1, Reg.put r.2])
      (by with_unfolding_all simp [abiOf, Rel.Lang.Plan.abi]) rfl
      (reads_of (vs := [Reg.put op, .bit false, Reg.put t, Reg.put t, vn, gv,
        (bs.map fun b => Val.ctor 0 #[vn, b] #[]).foldr (fun v c => .ctor 1 #[v, c] #[]) (.ctor 0 #[] #[]),
        .ctor 0 #[] #[], .ctor 0 #[] #[]]) ?_) ?_ rfl (Builds.pure (mapM_reg_range _ _))
    · refine omapM_cons.mpr ⟨_, _, ?_, omapM_cons.mpr ⟨_, _, ?_, omapM_cons.mpr ⟨_, _, ?_, omapM_cons.mpr ⟨_, _, ?_,
        omapM_cons.mpr ⟨_, _, ?_, omapM_cons.mpr ⟨_, _, ?_, omapM_cons.mpr ⟨_, _, ?_, omapM_cons.mpr ⟨_, _, ?_,
        omapM_cons.mpr ⟨_, _, ?_, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      · exact get_app (get_app (get_app (get_app (by simp [Array.getElem_push]))))
      · exact get_app (get_app (get_app (get_app (by simp [Array.getElem_push]))))
      · exact get_app (get_app (get_app (get_app (by simp [Array.getElem_push]))))
      · exact get_app (get_app (get_app (get_app (by simp [Array.getElem_push]))))
      · exact get_app (get_app (get_app (get_app (get_push (get_push (get_push (get_push (get_push hvn))))))))
      · exact get_app (get_app (get_app (get_app (get_push (get_push (get_push (get_push (by simp))))))))
      · exact get_app (get_app hr1)
      · exact get_app hr2
      · exact hr3
    · (simp [arg, hop, ht, hgn, hgv, hl, hnil, hk, Out.out]) <;> rfl

end Rel.Lang.Plan
