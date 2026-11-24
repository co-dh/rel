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

/-! ### `whereB`: its kernel chain, registers named by what they hold -/

/-- Registers `a` that `reg` reads as `o` hold `o`. -/
theorem holds_of_reg {R : Array Val} {who : String} {a : Array Nat} {o : Array Val} (h : a.mapM (reg R who) = .ok o) :
    a.toList.mapM (fun x => R[x]?) = some o.toList := by
  have key : ∀ (l : List Nat) {os : List Val}, l.mapM (reg R who) = .ok os → l.mapM (fun x => R[x]?) = some os := by
    intro l; induction l with
    | nil => intro os h; rw [List.mapM_nil] at h; injection h with h; subst h; rfl
    | cons x l ih =>
      intro os h
      rw [List.mapM_cons] at h
      cases hx : reg R who x with
      | error e => rw [hx] at h; cases h
      | ok v =>
        cases hl : l.mapM (reg R who) with
        | error e => rw [hx, hl] at h; cases h
        | ok vs =>
          rw [hx, hl] at h; injection h with h; subst h
          have hv : R[x]? = some v := by unfold reg at hx; split at hx <;> cases hx <;> simp_all
          exact omapM_cons.mpr ⟨v, vs, hv, ih hl, rfl⟩
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : a.toList.mapM (reg R who) with
  | error e => rw [hl] at h; cases h
  | ok os => rw [hl] at h; injection h with h; subst h; simpa using key _ hl

/-- Register `i` of registers holding `vs`: it holds `vs[i]`. -/
theorem holds_at {R : Array Val} : ∀ {l : List Nat} {vs : List Val}, l.mapM (fun x => R[x]?) = some vs →
    ∀ {i : Nat} {v : Val}, vs[i]? = some v → ∃ p, l[i]? = some p ∧ R[p]? = some v
  | [], vs, h, i, v, hv => by simp at h; subst h; simp at hv
  | x :: l, _, h, i, v, hv => by
    obtain ⟨w, ws, hx, hl, rfl⟩ := omapM_cons.mp h
    cases i with
    | zero => simp at hv; subst hv; exact ⟨x, rfl, hx⟩
    | succ i => simpa using holds_at hl (by simpa using hv)

/-- `R1` holds every register `R` holds. -/
abbrev Extends (R R1 : Array Val) : Prop := ∀ {i : Nat} {v : Val}, R[i]? = some v → R1[i]? = some v

/-- `lit x`, then `c` on a register holding `x`, in registers extending `rs`. -/
theorem Builds.litG {fg fg' : Array Fun × Array Fun} {x : Val} {rs out : Array Val} {c : Nat → Bld (Array Nat)}
    (hc : ∀ r R, R[r]? = some x → Extends rs R → Builds abi fg fg' (c r) R out) : Builds abi fg fg' (Plan.lit x >>= c) rs out :=
  Builds.lit (hc _ _ (by simp) fun h => get_push h)

/-- `call1 k as`, then `c` on a register holding its one value `v`, in registers extending `rs`. -/
theorem Builds.call1G {fg fg' : Array Fun × Array Fun} {k : Kernel} {f : Array Val → Except String (Array Val)}
    {as : Array Nat} {vs rs out : Array Val} {v : Val} {c : Nat → Bld (Array Nat)} (hk : abiOf k.sym = some k)
    (hf : k.run = .inl f) (ha : as.mapM (reg rs k.sym) = .ok vs) (ho : f vs = .ok #[v]) (hs : k.res.size = 1)
    (hc : ∀ r R, R[r]? = some v → Extends rs R → Builds abiOf fg fg' (c r) R out) :
    Builds abiOf fg fg' (Plan.call1 k as >>= c) rs out :=
  Builds.call1 hk hf ha ho hs (hc _ _ (by simp) fun h => get_push h)

/-- `b`, then `k` on its registers, holding `o`, in registers extending `rs`. -/
theorem Builds.bindG {fg fg1 fg' : Array Fun × Array Fun} {b : Bld (Array Nat)} {k : Array Nat → Bld (Array Nat)}
    {rs o out : Array Val} (hb : Builds abi fg fg1 b rs o)
    (hk : ∀ a R, a.toList.mapM (fun x => R[x]?) = some o.toList → Extends rs R → Builds abi fg1 fg' (k a) R out) :
    Builds abi fg fg' (b >>= k) rs out :=
  Builds.bind hb fun a _ h => hk a _ (holds_of_reg (h "")) fun h => get_app h

/-- A one-register builder `b` (its theorem stated of `do let r ← b; pure #[r]`), then `k` on its register. -/
theorem Builds.bind1G {fg fg1 fg' : Array Fun × Array Fun} {b : Bld Nat} {k : Nat → Bld (Array Nat)}
    {rs out : Array Val} {o : Val} (hb : Builds abi fg fg1 (do let r ← b; Pure.pure #[r]) rs #[o])
    (hk : ∀ r R, R[r]? = some o → Extends rs R → Builds abi fg1 fg' (k r) R out) :
    Builds abi fg fg' (b >>= k) rs out := by
  have e : b >>= k = (do let r ← b; Pure.pure #[r]) >>= fun a => k (a[0]?.getD 0) := by simp
  rw [e]
  refine Builds.bindG hb fun a R h m => ?_
  obtain ⟨r, hr, hR⟩ := holds_at h (i := 0) (v := o) rfl
  rw [show a[0]?.getD 0 = r by simp at hr; simp [hr]]
  exact hk r R hR m

/-- The `kernel%` value `k` is the ABI's entry under its own symbol. -/
macro "abiK" : tactic => `(tactic| with_unfolding_all simp [abiOf, Rel.Lang.Plan.abi])

/-- `whereB n keep` builds, and its two registers hold the count `K` of kept rows and their positions `w`: the
    results of its own kernel chain (`kscatter` zeros, `kscan` running sum of `keep`, its fold, `kscan` product,
    `kscatter` to `pos`, `kgather` of the cut points), each named by a hypothesis. -/
theorem whereB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n keep : Nat} {nv K : USize}
    {kc zc pc ixc ix1c zrc onec cutc w : Enc} {fo ixf cutf : Option UInt64} {f : UInt64}
    (hn : rs[n]? = some (.size nv)) (hkeep : rs[keep]?.bind Reg.get? = some kc)
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok zc)
    (hp : kscan .add false .i64 .i64 nv (some zc) [(nv, zc), (nv, kc)] [] [] = .ok (pc, fo))
    (hf : nv ≠ 0 → fo = some f) (hK : (if nv = 0 then (0 : UInt64) else f).toUSize = K)
    (hix : kscan .mul false .i64 .i64 nv none [(nv, kc), (nv, pc)] [] [] = .ok (ixc, ixf))
    (hs : kscatter .last nv ixc .pos (K + 1) 0 = .ok ix1c)
    (hzr : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) K 0 = .ok zrc)
    (hone : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) K 1 = .ok onec)
    (hcut : kscan .add false .i64 .i64 K (some zrc) [(K, zrc), (K, onec)] [] [] = .ok (cutc, cutf))
    (hg : kgather K cutc (K + 1) ix1c = .ok w)
    (hrt : ∀ e ∈ [zc, pc, ixc, ix1c, zrc, onec, cutc, .pos], (Reg.get? (Reg.put e) : Option Enc) = some e) :
    Builds abiOf fg fg (whereB n keep >>= fun (r, p) => Pure.pure #[r, p]) rs #[.size K, Reg.put w] := by
  obtain ⟨kv, hkv, hgk⟩ := Option.bind_eq_some_iff.mp hkeep
  have hadd : (Reg.get? (Reg.put Kernel.Op.add) : Option Kernel.Op) = some .add := by with_unfolding_all rfl
  have hmul : (Reg.get? (Reg.put Kernel.Op.mul) : Option Kernel.Op) = some .mul := by with_unfolding_all rfl
  have hlast : (Reg.get? (Reg.put Kernel.Op.last) : Option Kernel.Op) = some .last := by with_unfolding_all rfl
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  have hu : ∀ x : UInt64, (Reg.get? (Val.u64 x) : Option UInt64) = some x := fun _ => rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hrt
  obtain ⟨rz, rp, rix, rix1, rzr, rone, rcut, hpos⟩ := hrt
  unfold whereB
  simp only [bind_assoc, pure_bind]
  refine Builds.litG fun c0 R0 h0 m0 => ?_
  refine Builds.bind1G (constB_builds (m0 hn) h0 hz) fun z R1 hz1 m1 => ?_
  refine Builds.bindG (scanB_builds hadd (by rw [m1 (m0 hn)]; rfl) (seg := some z) (sg := some zc)
    (by simp [hz1, rz]) (es := [z, keep]) (xs := [zc, kc])
    (by simp [hz1, rz, m1 (m0 hkv), hgk]) hp) fun ps R2 hps m2 => ?_
  obtain ⟨p, hp0, hpR⟩ := holds_at hps (i := 0) rfl
  obtain ⟨fl, hf0, hfR⟩ := holds_at hps (i := 1) rfl
  rw [nth_of (by simpa using hp0), pure_bind, nth_of (by simpa using hf0), pure_bind]
  refine Builds.litG fun c1 R3 h1 m3 => ?_
  refine Builds.call1G (v := .bit (decide (nv = 0))) (by abiK) rfl
    (reads_of (l := [n, c1]) (vs := [.size nv, .size 0]) (by simp [h1, m3 (m2 (m1 (m0 hn)))])) ?_ rfl
    fun e R4 he m4 => ?_
  · simp [arg, hsz, Out.out]; rfl
  -- the `if`: one register holding the fold's word, `0` when there are no rows
  have hite : Builds abiOf fg fg (Plan.ite e (do pure #[← Plan.lit (.u64 0)]) (do pure #[← Plan.projB fl 1 0 .u64]))
      R4 #[.u64 (if nv = 0 then 0 else f)] := by
    have ht : Builds abiOf fg fg (do pure #[← Plan.lit (.u64 0)]) R4 #[.u64 0] :=
      Builds.litG fun r R hr _ => Builds.pure fun _ => reads_of (l := [r]) (vs := [.u64 0]) (by simp [hr])
    by_cases h0 : nv = 0
    · rw [if_pos h0]
      exact Builds.ite_true (by simpa [h0] using he) ht rfl rfl ⟨⟨#[], by simp⟩, ⟨#[], by simp⟩⟩
    · rw [if_neg h0]
      have hfl : R4[fl]? = some (.ctor 1 #[.u64 f] #[]) := by
        rw [m4 (m3 hfR), hf h0]; rfl
      exact Builds.ite (bt := false) (by simpa [h0] using he) ht
        (Builds.projB hfl rfl rfl (Builds.pure fun _ =>
          reads_of (l := [_]) (vs := [.u64 f]) (by simp))) rfl
  refine Builds.bindG hite fun a R5 ha m5 => ?_
  obtain ⟨x0, hx0, hX⟩ := holds_at ha (i := 0) rfl
  rw [nth_of (by simpa using hx0), pure_bind]
  refine Builds.call1G (v := .size K) (by abiK) rfl
    (reads_of (l := [x0]) (vs := [.u64 (if nv = 0 then 0 else f)]) (by simp [hX])) ?_ rfl fun r R6 hr m6 => ?_
  · simp [arg, hu, Out.out, hK]; rfl
  have M6 : Extends rs R6 := fun h => m6 (m5 (m4 (m3 (m2 (m1 (m0 h))))))
  refine Builds.bindG (scanB_builds hmul (by rw [M6 hn]; rfl) (seg := none) (sg := none) rfl
    (es := [keep, p]) (xs := [kc, pc]) (by simp [M6 hkv, hgk, m6 (m5 (m4 (m3 hpR))), rp]) hix)
    fun ixs R7 hixs m7 => ?_
  obtain ⟨ix, hix0, hixR⟩ := holds_at hixs (i := 0) rfl
  rw [nth_of (by simpa using hix0), pure_bind]
  refine Builds.litG fun c2 R8 h2 m8 => ?_
  refine Builds.call1G (v := .size (K + 1)) (by abiK) rfl
    (reads_of (l := [r, c2]) (vs := [.size K, .size 1]) (by simp [h2, m8 (m7 hr)])) ?_ rfl fun r1 R9 hr1 m9 => ?_
  · simp [arg, hsz, Out.out]; rfl
  refine Builds.litG fun cl R10 hcl m10 => ?_
  refine Builds.litG fun cp R11 hcp m11 => ?_
  refine Builds.litG fun c3 R12 h3 m12 => ?_
  have N12 : Extends R6 R12 := fun h => m12 (m11 (m10 (m9 (m8 (m7 h)))))
  refine Builds.call1G (v := Reg.put ix1c) (by abiK) rfl
    (reads_of (l := [cl, n, ix, cp, r1, c3])
      (vs := [Reg.put Kernel.Op.last, .size nv, Reg.put ixc, Reg.put (Ext.Enc.pos : Enc), .size (K + 1), .u64 0])
      (by simp [h3, m12 hcp, m12 (m11 hcl), m12 (m11 (m10 hr1)), N12 (M6 hn), m12 (m11 (m10 (m9 (m8 hixR))))]))
    ?_ rfl fun ix1 R13 hix1 m13 => ?_
  · simp [arg, hlast, hsz, rix, hpos, hu, hs, Out.out]; rfl
  refine Builds.litG fun c4 R14 h4 m14 => ?_
  refine Builds.bind1G (constB_builds (m14 (m13 (N12 hr))) h4 hzr) fun zr R15 hzr1 m15 => ?_
  refine Builds.litG fun c5 R16 h5 m16 => ?_
  have N16 : Extends R6 R16 := fun h => m16 (m15 (m14 (m13 (N12 h))))
  refine Builds.bind1G (constB_builds (N16 hr) h5 hone) fun one R17 hone1 m17 => ?_
  refine Builds.bindG (scanB_builds hadd (by rw [m17 (N16 hr)]; rfl) (seg := some zr) (sg := some zrc)
    (by simp [m17 (m16 hzr1), rzr]) (es := [zr, one]) (xs := [zrc, onec])
    (by simp [m17 (m16 hzr1), rzr, hone1, rone]) hcut) fun cs R18 hcs m18 => ?_
  obtain ⟨cut, hc0, hcR⟩ := holds_at hcs (i := 0) rfl
  rw [nth_of (by simpa using hc0), pure_bind]
  refine Builds.call1G (v := Reg.put w) (by abiK) rfl
    (reads_of (l := [r, cut, r1, ix1]) (vs := [.size K, Reg.put cutc, .size (K + 1), Reg.put ix1c])
      (by simp [m18 (m17 (N16 hr)), hcR, m18 (m17 (m16 (m15 (m14 (m13 (m12 (m11 (m10 hr1)))))))),
        m18 (m17 (m16 (m15 (m14 hix1))))]))
    ?_ rfl fun wr R19 hw m19 => ?_
  · simp [arg, hsz, rcut, rix1, hg, Out.out]; rfl
  exact Builds.pure fun _ => reads_of (l := [r, wr]) (vs := [.size K, Reg.put w])
    (by simp [hw, m19 (m18 (m17 (N16 hr)))])

/-! ### `groupIdsB`: its kernel chain, registers named by what they hold -/

/-- `ctorB`, then `c` on a register holding the constructor, in registers extending `rs`. -/
theorem Builds.ctorBG {fg fg' : Array Fun × Array Fun} {tag : Nat} {objs scal : Array Nat} {os ss rs out : Array Val}
    {c : Nat → Bld (Array Nat)} (ho : objs.mapM (reg rs "ctor") = .ok os) (hs : scal.mapM (reg rs "ctor") = .ok ss)
    (hc : ∀ r R, R[r]? = some (.ctor tag os ss) → Extends rs R → Builds abi fg fg' (c r) R out) :
    Builds abi fg fg' (Plan.ctorB tag objs scal >>= c) rs out :=
  Builds.ctorB ho hs (hc _ _ (by simp) fun h => get_push h)

/-- `projB`, then `c` on a register holding the field, in registers extending `rs`. -/
theorem Builds.projBG {fg fg' : Array Fun × Array Fun} {x tag i : Nat} {t : Ty} {os ss rs out : Array Val} {v : Val}
    {c : Nat → Bld (Array Nat)} (hx : rs[x]? = some (.ctor tag os ss)) (hv : os[i]? = some v) (ht : v.ty = t)
    (hc : ∀ r R, R[r]? = some v → Extends rs R → Builds abi fg fg' (c r) R out) :
    Builds abi fg fg' (Plan.projB x tag i t >>= c) rs out :=
  Builds.projB hx hv ht (hc _ _ (by simp) fun h => get_push h)

/-- `callK k as`, then `c` on registers holding the answers `o`, in registers extending `rs`. -/
theorem Builds.callKG {fg fg' : Array Fun × Array Fun} {k : Kernel} {f : Array Val → Except String (Array Val)}
    {as : Array Nat} {vs o rs out : Array Val} {c : Array Nat → Bld (Array Nat)} (hk : abiOf k.sym = some k)
    (hf : k.run = .inl f) (ha : as.mapM (reg rs k.sym) = .ok vs) (ho : f vs = .ok o) (hs : o.size = k.res.size)
    (hc : ∀ a R, a.toList.mapM (fun x => R[x]?) = some o.toList → Extends rs R → Builds abiOf fg fg' (c a) R out) :
    Builds abiOf fg fg' (Plan.callK k as >>= c) rs out :=
  Builds.callK hk hf ha ho hs (hc _ _ (holds_of_reg (mapM_reg_range rs o "")) fun h => get_app h)

/-- `listB l`, then `k` on a register holding the list, in registers extending `rs`. -/
theorem Builds.listBG {fg fg' : Array Fun × Array Fun} {out rs : Array Val} {l : List Nat} {vs : List Val}
    {k : Nat → Bld (Array Nat)} (h : l.mapM (fun x => rs[x]?) = some vs)
    (hk : ∀ r R, R[r]? = some (vs.foldr (fun v c => .ctor 1 #[v, c] #[]) (.ctor 0 #[] #[])) → Extends rs R →
      Builds abi fg fg' (k r) R out) : Builds abi fg fg' (Plan.listB l >>= k) rs out :=
  Builds.listB h fun _ _ hr => hk _ _ hr fun h => get_app h

theorem groupIdsB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {t n c : Nat} {nv : USize} {ty : QAtomicType}
    {cc s0 pe g1 g2 out : Enc} {sl : List Enc} {cnt : Nat}
    (hn : rs[n]? = some (.size nv)) (ht : rs[t]? = some (Reg.put ty)) (hc : rs[c]?.bind Reg.get? = some cc)
    (hak : (Reg.get? (Val.ctor 0 #[] #[Reg.put ty]) : Option AscKey) = some (.atom ty))
    (hs : kasc nv [(.atom ty, cc)] = .ok (s0 :: sl, pe))
    (hg : kseen nv [(.atom ty, s0)] = .ok (cnt, g1, g2))
    (hk : kscatter .last nv pe g1 nv 0 = .ok out)
    (hrt : ∀ e ∈ [s0, pe, g1], (Reg.get? (Reg.put e) : Option Enc) = some e) :
    Builds abiOf fg fg (do let r ← groupIdsB t n c; Pure.pure #[r]) rs #[Reg.put out] := by
  obtain ⟨cv, hcv, hgc⟩ := Option.bind_eq_some_iff.mp hc
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hrt
  obtain ⟨rs0, rpe, rg1⟩ := hrt
  have hpair : ∀ (a : Enc) (v : Val), Reg.get? v = some a →
      (Reg.get? (Val.ctor 0 #[Val.ctor 0 #[] #[Reg.put ty], v] #[]) : Option (AscKey × Enc)) = some (.atom ty, a) := by
    intro a v hv
    show (do pure (← Reg.get? (Val.ctor 0 #[] #[Reg.put ty]), ← Reg.get? v)) = _
    rw [hak, hv]; rfl
  have hlist : ∀ (pv : Val) (x : AscKey × Enc), Reg.get? pv = some x →
      (Reg.get? (Val.ctor 1 #[pv, Val.ctor 0 #[] #[]] #[]) : Option (List (AscKey × Enc))) = some [x] := by
    intro pv x h; exact (listGet?_foldr [pv]).trans (by simp [h])
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  have hu : ∀ x : UInt64, (Reg.get? (Val.u64 x) : Option UInt64) = some x := fun _ => rfl
  have hlast : (Reg.get? (Reg.put Kernel.Op.last) : Option Kernel.Op) = some .last := by with_unfolding_all rfl
  unfold groupIdsB
  simp only [bind_assoc]
  refine Builds.ctorBG (reads_of (l := []) (vs := []) rfl) (reads_of (l := [t]) (vs := [Reg.put ty]) (by simp [ht]))
    fun a R1 ha m1 => ?_
  refine Builds.ctorBG (reads_of (l := [a, c]) (vs := [Val.ctor 0 #[] #[Reg.put ty], cv]) (by simp [ha, m1 hcv]))
    (reads_of (l := []) (vs := []) rfl) fun p R2 hp m2 => ?_
  refine Builds.listBG (l := [p]) (vs := [Val.ctor 0 #[Val.ctor 0 #[] #[Reg.put ty], cv] #[]]) (by simp [hp])
    fun l1 R3 hl1 m3 => ?_
  have M3 : Extends rs R3 := fun h => m3 (m2 (m1 h))
  refine Builds.callKG (o := #[Reg.put (s0 :: sl), Reg.put pe]) (by abiK) rfl
    (reads_of (l := [n, l1]) (vs := [.size nv, [Val.ctor 0 #[Val.ctor 0 #[] #[Reg.put ty], cv] #[]].foldr
      (fun v c => Val.ctor 1 #[v, c] #[]) (Val.ctor 0 #[] #[])]) (by simp [hl1, M3 hn])) ?_ rfl fun sp R4 hsp m4 => ?_
  · simp [arg, hsz, hlist _ _ (hpair _ _ hgc), hs, Out.out]; rfl
  obtain ⟨p0, hp0, hpR⟩ := holds_at hsp (i := 0) rfl
  obtain ⟨p1, hp1, hpR1⟩ := holds_at hsp (i := 1) rfl
  have e : (Reg.put (s0 :: sl) : Val) = .ctor 1 #[Reg.put s0, Reg.put sl] #[] := by with_unfolding_all rfl
  rw [e] at hpR
  rw [nth_of (by simpa using hp0), pure_bind]
  have M4 : Extends rs R4 := fun h => m4 (M3 h)
  refine Builds.projBG (os := #[Reg.put s0, Reg.put sl]) (ss := #[]) (v := Reg.put s0) hpR rfl
    (by with_unfolding_all rfl) fun so R5 hso m5 => ?_
  refine Builds.ctorBG (reads_of (l := []) (vs := []) rfl)
    (reads_of (l := [t]) (vs := [Reg.put ty]) (by simp [m5 (M4 ht)])) fun a2 R6 ha2 m6 => ?_
  refine Builds.ctorBG (reads_of (l := [a2, so]) (vs := [Val.ctor 0 #[] #[Reg.put ty], Reg.put s0])
    (by simp [ha2, m6 hso])) (reads_of (l := []) (vs := []) rfl) fun p2 R7 hp2 m7 => ?_
  refine Builds.listBG (l := [p2]) (vs := [Val.ctor 0 #[Val.ctor 0 #[] #[Reg.put ty], Reg.put s0] #[]])
    (by simp [hp2]) fun l2 R8 hl2 m8 => ?_
  have M8 : Extends rs R8 := fun h => m8 (m7 (m6 (m5 (M4 h))))
  refine Builds.callKG (o := #[.nat cnt, Reg.put g1, Reg.put g2]) (by abiK) rfl
    (reads_of (l := [n, l2]) (vs := [.size nv, [Val.ctor 0 #[Val.ctor 0 #[] #[Reg.put ty], Reg.put s0] #[]].foldr
      (fun v c => Val.ctor 1 #[v, c] #[]) (Val.ctor 0 #[] #[])]) (by simp [hl2, M8 hn])) ?_ rfl fun kg R9 hkg m9 => ?_
  · simp [arg, hsz, hlist _ _ (hpair _ _ rs0), hg, Out.out]; rfl
  obtain ⟨q1, hq1, hqR⟩ := holds_at hkg (i := 1) rfl
  refine Builds.litG fun cl R10 hcl m10 => ?_
  rw [nth_of (by simpa using hp1), pure_bind, nth_of (by simpa using hq1), pure_bind]
  refine Builds.litG fun c0 R11 hc0 m11 => ?_
  refine Builds.call1G (v := Reg.put out) (by abiK) rfl
    (reads_of (l := [cl, n, p1, q1, n, c0]) (vs := [Reg.put Kernel.Op.last, .size nv, Reg.put pe, Reg.put g1, .size nv, .u64 0])
      (by simp [hc0, m11 hcl, m11 (m10 (m9 (M8 hn))), m11 (m10 (m9 (m8 (m7 (m6 (m5 hpR1)))))), m11 (m10 hqR)])) ?_ rfl
    fun r R12 hr m12 => ?_
  · simp [arg, hlast, hsz, rpe, rg1, hu, hk, Out.out]; rfl
  exact Builds.pure fun _ => reads_of (l := [r]) (vs := [Reg.put out]) (by simp [hr])

/-! ### `arithB`: its kernel chain, registers named by what they hold -/

/-- The column `o a b` answers: the map `kscan o` (every row a segment) over the `i64` columns `a`, `b` of `nv` rows. -/
def MapCol (o : Kernel.Op) (nv : USize) (a b r : Enc) : Prop :=
  ∃ f, kscan o false .i64 .i64 nv none [(nv, a), (nv, b)] [] [] = .ok (r, f)

/-- The column "`s = u op v` did not wrap" that `arithB` computes, each map of its chain named by its column: for
    `add` and `sub` the sign of `v` against the side of `u` that `s` lies on, for `mul` `u = 0` or `s / u = v`. -/
def ArithExact (op : Kernel.Op) (nv : USize) (zc uc vc sc ec : Enc) : Prop := match op with
  | .add => ∃ g1 g2, MapCol .ge nv vc zc g1 ∧ MapCol .ge nv sc uc g2 ∧ MapCol .eq nv g1 g2 ec ∧
      (Reg.get? (Reg.put g1) : Option Enc) = some g1 ∧ (Reg.get? (Reg.put g2) : Option Enc) = some g2
  | .sub => ∃ g1 g2, MapCol .ge nv vc zc g1 ∧ MapCol .le nv sc uc g2 ∧ MapCol .eq nv g1 g2 ec ∧
      (Reg.get? (Reg.put g1) : Option Enc) = some g1 ∧ (Reg.get? (Reg.put g2) : Option Enc) = some g2
  | .mul => ∃ g0 g1 g2 g3, MapCol .eq nv uc zc g0 ∧ MapCol .add nv uc g0 g1 ∧ MapCol .div nv sc g1 g2 ∧
      MapCol .eq nv g2 vc g3 ∧ MapCol .or nv g0 g3 ec ∧ (Reg.get? (Reg.put g0) : Option Enc) = some g0 ∧
      (Reg.get? (Reg.put g1) : Option Enc) = some g1 ∧ (Reg.get? (Reg.put g2) : Option Enc) = some g2 ∧
      (Reg.get? (Reg.put g3) : Option Enc) = some g3
  | _ => False



/-- `m o a b` (one `kscan` map, its first answer taken), then `c` on a register holding the column `rc`. -/
theorem Builds.mB {fg fg' : Array Fun × Array Fun} {rs out : Array Val} {o : Kernel.Op} {n a b : Nat} {nv : USize}
    {ua ub : Val} {ca cb rc : Enc} {c : Nat → Bld (Array Nat)}
    (hop : (Reg.get? (Reg.put o) : Option Kernel.Op) = some o) (hn : rs[n]? = some (.size nv))
    (ha : rs[a]? = some ua) (hga : Reg.get? ua = some ca) (hb : rs[b]? = some ub) (hgb : Reg.get? ub = some cb)
    (hk : MapCol o nv ca cb rc)
    (hc : ∀ r R, R[r]? = some (Reg.put rc) → Extends rs R → Builds abiOf fg fg' (c r) R out) :
    Builds abiOf fg fg' (scanB o .i64 n none [a, b] >>= fun x => nth x 0 "kscan" >>= c) rs out := by
  obtain ⟨f, hk⟩ := hk
  refine Builds.bindG (scanB_builds hop (by rw [hn]; rfl) (seg := none) (sg := none) rfl (es := [a, b])
    (xs := [ca, cb]) (by simp [ha, hga, hb, hgb]) hk) fun ps R hps m => ?_
  obtain ⟨p, hp0, hpR⟩ := holds_at hps (i := 0) rfl
  rw [nth_of (by simpa using hp0), pure_bind]
  exact hc p R hpR m

/-- `whereB n keep`, then `k` on its two registers holding `o0`, `o1`, in registers extending `rs`. -/
theorem Builds.whereG {fg : Array Fun × Array Fun} {rs out : Array Val} {n keep : Nat} {o0 o1 : Val}
    (hb : Builds abiOf fg fg (whereB n keep >>= fun (r, p) => Pure.pure #[r, p]) rs #[o0, o1])
    {k : Nat × Nat → Bld (Array Nat)}
    (hk : ∀ r p R, R[r]? = some o0 → R[p]? = some o1 → Extends rs R → Builds abiOf fg fg (k (r, p)) R out) :
    Builds abiOf fg fg (whereB n keep >>= k) rs out := by
  have e : whereB n keep >>= k = (whereB n keep >>= fun (r, p) => Pure.pure #[r, p]) >>= fun a =>
      k (a[0]?.getD 0, a[1]?.getD 0) := by simp
  rw [e]
  refine Builds.bindG hb fun a R h m => ?_
  obtain ⟨r, hr, hR⟩ := holds_at h (i := 0) (v := o0) rfl
  obtain ⟨p, hp, hP⟩ := holds_at h (i := 1) (v := o1) rfl
  rw [show a[0]?.getD 0 = r by simp at hr; simp [hr], show a[1]?.getD 0 = p by simp at hp; simp [hp]]
  exact hk r p R hR hP m


set_option hygiene false in
/-- After a step whose registers extend the old ones through `m`, the listed facts about registers hold in the new. -/
macro "up " m:ident " [" hs:ident* "]" : tactic => do
  let rs ← hs.mapM fun h => `(tactic| replace $h:ident := $m:ident $h:ident)
  `(tactic| ($[$rs];*))

/-- The `Op` a `kscan` map takes reads back from its register. -/
macro "rop" : tactic => `(tactic| with_unfolding_all rfl)

/-- What `arithB` builds once its `exact` column (register `ex`) is known: the rows kept where no operand and not `s` is
    null and `s` did not wrap, `whereB` of them, and the columns gathered there. Kept a `def` of its own so that its
    theorem is a lemma of its own (a declaration's proof is limited in heartbeats); `arithB_builds` checks that it is
    what `arithB` continues with. -/
def arithTail (n u v s nul ex : Nat) : Bld (Array Nat) := do
  let m (o : Kernel.Op) (a b : Nat) : Bld Nat := do nth (← scanB o .i64 n none [a, b]) 0 "kscan"
  let keep ← m .and (← m .and (← m .ne u nul) (← m .ne v nul)) (← m .and (← m .ne s nul) ex)
  let (r, w) ← whereB n keep
  let g (x : Nat) := call1 (kernel% kgather) #[r, w, n, x]
  return #[r, ← g u, ← g v, ← g s]

theorem arithTail_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n u v s nul ex : Nat} {nv K : USize}
    {uv vv : Val} {uc vc zc nc sc ec k1 k2 k3 k4 k5 kc pc ixc ix1c zrc onec cutc w gu gv gs : Enc}
    {fo ixf cutf : Option UInt64} {f : UInt64}
    (hn : rs[n]? = some (.size nv)) (hu : rs[u]? = some uv) (hgu : Reg.get? uv = some uc)
    (hv : rs[v]? = some vv) (hgv : Reg.get? vv = some vc)
    (hsr : rs[s]? = some (Reg.put sc)) (hnr : rs[nul]? = some (Reg.put nc)) (her : rs[ex]? = some (Reg.put ec))
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok zc)
    (hk1 : MapCol .ne nv uc nc k1) (hk2 : MapCol .ne nv vc nc k2) (hk3 : MapCol .and nv k1 k2 k3)
    (hk4 : MapCol .ne nv sc nc k4) (hk5 : MapCol .and nv k4 ec k5) (hk6 : MapCol .and nv k3 k5 kc)
    (hwp : kscan .add false .i64 .i64 nv (some zc) [(nv, zc), (nv, kc)] [] [] = .ok (pc, fo))
    (hwf : nv ≠ 0 → fo = some f) (hwK : (if nv = 0 then (0 : UInt64) else f).toUSize = K)
    (hwix : kscan .mul false .i64 .i64 nv none [(nv, kc), (nv, pc)] [] [] = .ok (ixc, ixf))
    (hws : kscatter .last nv ixc .pos (K + 1) 0 = .ok ix1c)
    (hwzr : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) K 0 = .ok zrc)
    (hwone : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) K 1 = .ok onec)
    (hwcut : kscan .add false .i64 .i64 K (some zrc) [(K, zrc), (K, onec)] [] [] = .ok (cutc, cutf))
    (hwg : kgather K cutc (K + 1) ix1c = .ok w)
    (hgu' : kgather K w nv uc = .ok gu) (hgv' : kgather K w nv vc = .ok gv) (hgs' : kgather K w nv sc = .ok gs)
    (hrt : ∀ e ∈ [zc, nc, sc, ec, k1, k2, k3, k4, k5, kc, w, pc, ixc, ix1c, zrc, onec, cutc, .pos],
      (Reg.get? (Reg.put e) : Option Enc) = some e) :
    Builds abiOf fg fg (arithTail n u v s nul ex) rs #[.size K, Reg.put gu, Reg.put gv, Reg.put gs] := by
  have hrtw : ∀ e ∈ [zc, pc, ixc, ix1c, zrc, onec, cutc, (.pos : Enc)], (Reg.get? (Reg.put e) : Option Enc) = some e :=
    fun e he => hrt e (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
      rcases he with h | h | h | h | h | h | h | h <;> simp [h])
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hrt
  obtain ⟨rz, rnl, rsc, rex, rk1, rk2, rk3, rk4, rk5, rkc, rw, rp, rix, rix1, rzr, rone, rcut, rpos⟩ := hrt
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  unfold arithTail
  simp only [bind_assoc]
  refine Builds.mB (by rop) hn hu hgu hnr rnl hk1 fun a1 R h1 m => ?_
  up m [hn hu hv hsr hnr her]
  refine Builds.mB (by rop) hn hv hgv hnr rnl hk2 fun a2 R h2 m => ?_
  up m [hn hu hv hsr hnr her h1]
  refine Builds.mB (by rop) hn h1 rk1 h2 rk2 hk3 fun a3 R h3 m => ?_
  up m [hn hu hv hsr hnr her]
  refine Builds.mB (by rop) hn hsr rsc hnr rnl hk4 fun a4 R h4 m => ?_
  up m [hn hu hv hsr hnr her h3]
  refine Builds.mB (by rop) hn h4 rk4 her rex hk5 fun a5 R h5 m => ?_
  up m [hn hu hv hsr hnr h3]
  refine Builds.mB (by rop) hn h3 rk3 h5 rk5 hk6 fun keep R hkp m => ?_
  up m [hn hu hv hsr]
  refine Builds.whereG (whereB_builds hn (by simp [hkp, rkc]) hz hwp hwf hwK hwix hws hwzr hwone hwcut hwg hrtw)
    fun r p R hr hp m => ?_
  dsimp only
  up m [hn hu hv hsr]
  refine Builds.call1G (v := Reg.put gu) (by abiK) rfl
    (reads_of (l := [r, p, n, u]) (vs := [.size K, Reg.put w, .size nv, uv]) (by simp [hr, hp, hn, hu])) ?_ rfl
    fun x1 R h1 m => ?_
  · simp [arg, hsz, rw, hgu, hgu', Out.out]; rfl
  up m [hn hu hv hsr hr hp]
  refine Builds.call1G (v := Reg.put gv) (by abiK) rfl
    (reads_of (l := [r, p, n, v]) (vs := [.size K, Reg.put w, .size nv, vv]) (by simp [hr, hp, hn, hv])) ?_ rfl
    fun x2 R h2 m => ?_
  · simp [arg, hsz, rw, hgv, hgv', Out.out]; rfl
  up m [hn hu hv hsr hr hp h1]
  refine Builds.call1G (v := Reg.put gs) (by abiK) rfl
    (reads_of (l := [r, p, n, s]) (vs := [.size K, Reg.put w, .size nv, Reg.put sc])
      (by simp [hr, hp, hn, hsr])) ?_ rfl
    fun x3 R h3 m => ?_
  · simp [arg, hsz, rw, rsc, hgs', Out.out]; rfl
  up m [hr h1 h2]
  exact Builds.pure fun _ => reads_of (l := [r, x1, x2, x3])
    (vs := [.size K, Reg.put gu, Reg.put gv, Reg.put gs]) (by simp [hr, h1, h2, h3])

theorem arithB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {op : Kernel.Op} {n u v : Nat} {nv K : USize}
    {uv vv : Val} {uc vc zc nc sc ec k1 k2 k3 k4 k5 kc pc ixc ix1c zrc onec cutc w gu gv gs : Enc}
    {fo ixf cutf : Option UInt64} {f : UInt64}
    (hn : rs[n]? = some (.size nv)) (hu : rs[u]? = some uv) (hgu : Reg.get? uv = some uc)
    (hv : rs[v]? = some vv) (hgv : Reg.get? vv = some vc)
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok zc)
    (hnl : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv Alg.nul.toUInt64 = .ok nc)
    (hs : MapCol op nv uc vc sc) (hex : ArithExact op nv zc uc vc sc ec)
    (hk1 : MapCol .ne nv uc nc k1) (hk2 : MapCol .ne nv vc nc k2) (hk3 : MapCol .and nv k1 k2 k3)
    (hk4 : MapCol .ne nv sc nc k4) (hk5 : MapCol .and nv k4 ec k5) (hk6 : MapCol .and nv k3 k5 kc)
    (hwp : kscan .add false .i64 .i64 nv (some zc) [(nv, zc), (nv, kc)] [] [] = .ok (pc, fo))
    (hwf : nv ≠ 0 → fo = some f) (hwK : (if nv = 0 then (0 : UInt64) else f).toUSize = K)
    (hwix : kscan .mul false .i64 .i64 nv none [(nv, kc), (nv, pc)] [] [] = .ok (ixc, ixf))
    (hws : kscatter .last nv ixc .pos (K + 1) 0 = .ok ix1c)
    (hwzr : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) K 0 = .ok zrc)
    (hwone : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) K 1 = .ok onec)
    (hwcut : kscan .add false .i64 .i64 K (some zrc) [(K, zrc), (K, onec)] [] [] = .ok (cutc, cutf))
    (hwg : kgather K cutc (K + 1) ix1c = .ok w)
    (hgu' : kgather K w nv uc = .ok gu) (hgv' : kgather K w nv vc = .ok gv) (hgs' : kgather K w nv sc = .ok gs)
    (hrt : ∀ e ∈ [zc, nc, sc, ec, k1, k2, k3, k4, k5, kc, w, pc, ixc, ix1c, zrc, onec, cutc, .pos],
      (Reg.get? (Reg.put e) : Option Enc) = some e) :
    Builds abiOf fg fg (arithB op n u v) rs #[.size K, Reg.put gu, Reg.put gv, Reg.put gs] := by
  have tail := fun {R : Array Val} {s nul ex : Nat} (hn : R[n]? = some (.size nv)) (hu : R[u]? = some uv)
    (hv : R[v]? = some vv) (hsr : R[s]? = some (Reg.put sc)) (hnr : R[nul]? = some (Reg.put nc))
    (her : R[ex]? = some (Reg.put ec)) => arithTail_builds (fg := fg) (n := n) (u := u) (v := v) hn hu hgu hv hgv hsr hnr her
      hz hk1 hk2 hk3 hk4 hk5 hk6 hwp hwf hwK hwix hws hwzr hwone hwcut hwg hgu' hgv' hgs' hrt
  have rsc : (Reg.get? (Reg.put sc) : Option Enc) = some sc := hrt sc (by simp)
  have rnl : (Reg.get? (Reg.put nc) : Option Enc) = some nc := hrt nc (by simp)
  have rz : (Reg.get? (Reg.put zc) : Option Enc) = some zc := hrt zc (by simp)
  have key : op = .add ∨ op = .sub ∨ op = .mul := by
    revert hex
    cases op <;> first
      | (intro h; simp only [ArithExact] at h; done)
      | (intro _; left; rfl)
      | (intro _; right; left; rfl)
      | (intro _; right; right; rfl)
  unfold arithB
  simp only [bind_assoc]
  rcases key with rfl | rfl | rfl
  all_goals
    refine Builds.litG fun c0 R h0 m => ?_
    up m [hn hu hv]
    refine Builds.bind1G (constB_builds hn h0 hz) fun z R hz2 m => ?_
    up m [hn hu hv]
    refine Builds.litG fun c1 R h1 m => ?_
    up m [hn hu hv hz2]
    refine Builds.bind1G (constB_builds hn h1 hnl) fun nul R hnul m => ?_
    up m [hn hu hv hz2]
    refine Builds.mB (by rop) hn hu hgu hv hgv hs fun s R hsr m => ?_
    up m [hn hu hv hz2 hnul]
  case' inl =>
    obtain ⟨g1, g2, hm1, hm2, hm3, rg1, rg2⟩ := hex
    refine Builds.mB (by rop) hn hv hgv hz2 rz hm1 fun x1 R hx1 m => ?_
    up m [hn hu hv hz2 hnul hsr]
    refine Builds.mB (by rop) hn hsr rsc hu hgu hm2 fun x2 R hx2 m => ?_
    up m [hn hu hv hnul hsr hx1]
    refine Builds.mB (by rop) hn hx1 rg1 hx2 rg2 hm3 fun ex R hex' m => ?_
    up m [hn hu hv hnul hsr]
  case' inr.inl =>
    obtain ⟨g1, g2, hm1, hm2, hm3, rg1, rg2⟩ := hex
    refine Builds.mB (by rop) hn hv hgv hz2 rz hm1 fun x1 R hx1 m => ?_
    up m [hn hu hv hz2 hnul hsr]
    refine Builds.mB (by rop) hn hsr rsc hu hgu hm2 fun x2 R hx2 m => ?_
    up m [hn hu hv hnul hsr hx1]
    refine Builds.mB (by rop) hn hx1 rg1 hx2 rg2 hm3 fun ex R hex' m => ?_
    up m [hn hu hv hnul hsr]
  case' inr.inr =>
    obtain ⟨g0, g1, g2, g3, hm0, hm1, hm2, hm3, hm4, rg0, rg1, rg2, rg3⟩ := hex
    refine Builds.mB (by rop) hn hu hgu hz2 rz hm0 fun x0 R hx0 m => ?_
    up m [hn hu hv hnul hsr]
    refine Builds.mB (by rop) hn hu hgu hx0 rg0 hm1 fun x1 R hx1 m => ?_
    up m [hn hu hv hnul hsr hx0]
    refine Builds.mB (by rop) hn hsr rsc hx1 rg1 hm2 fun x2 R hx2 m => ?_
    up m [hn hu hv hnul hsr hx0]
    refine Builds.mB (by rop) hn hx2 rg2 hv hgv hm3 fun x3 R hx3 m => ?_
    up m [hn hu hv hnul hsr hx0]
    refine Builds.mB (by rop) hn hx0 rg0 hx3 rg3 hm4 fun ex R hex' m => ?_
    up m [hn hu hv hnul hsr]
  all_goals
    have h := tail hn hu hv hsr hnul hex'
    unfold arithTail at h
    simp only [bind_assoc] at h
    exact h

end Rel.Lang.Plan
