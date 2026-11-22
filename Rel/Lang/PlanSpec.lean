import Rel.Lang.EmitC

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

end Rel.Lang.Plan
