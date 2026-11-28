module

public import Rel.Lang.PlanSpecDiv
public import Rel.Lang.PlanSpecBits

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `compTB` builds `Tab.compSel` (PLAN-THM-E12)

`compTB R s ds ran` is `compSelB bits R S` for the table `S` that `s` builds, read at `nub R.val` (`ds`) or closed. The spec
of `compSelB` itself (`CompSelSpec`: `iteT` of `compBitsB` and `compFromB` under `bitsWinB`) is owed, as `LdivSelSpec`
is for `ldivSelB`: the untaken branch of `iteT` is only built, and no lemma yet proves a builder's run succeeds. `s` is
specified by `SSpec`: the table it builds from a context `D` the caller establishes. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel Rel.Verify

/-- **A plan builder `compSelB bits` of two tables builds `Tab.compSel bits`** (under the facts `Tot` of `R`, `S`): the tables
    `R'`, `S'` hold `R`, `S`, `R.compSel bits S = T'`; `kk` continues with a table of `R'`'s key shape and `S'`'s value
    shape whose registers hold `T'`. The owed spec of `compSelB`. -/
def CompSelSpec (A B C : Obj) (Tot : Tab A B → Tab B C → Prop) (bits : Nat) : Prop :=
  ∀ {R : Tab A B} {S : Tab B C} {T' : Tab A C} {R' S' : TabB} {fg : Array Fun × Array Fun} {rs : Array Val}
    {kk : TabB → Bld (Array Nat)} {out : Array Val},
    ColsOf A R'.key → ColsOf B R'.val → ColsOf B S'.key → ColsOf C S'.val →
    R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
    S'.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
    R.compSel bits S = .ok T' → Tot R S → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape R'.key → Cols.shape W.val = Cols.shape S'.val →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (compSelB bits R' S' >>= kk) rs out

/-- **A table builder `s` of a context builds the table `S`**: in any registers `rs'` where the context `D d` holds, `s d`
    builds a table `S'` of the columns of `S` whose registers hold `S`, and `kk'` continues from it. -/
def SSpec {B C : Obj} (S : Tab B C) (s : Dom → Bld TabB) (D : Dom → Array Val → Prop) : Prop :=
  ∀ {d : Dom} {fg : Array Fun × Array Fun} {rs : Array Val} {kk : TabB → Bld (Array Nat)} {out : Array Val},
    D d rs → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (S' : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → ColsOf B S'.key → ColsOf C S'.val →
      S'.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk S') (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (s d >>= kk) rs out

/-- A `tryCatch` whose body builds is the body: the handler never runs. -/
theorem Builds.tryCatch {α : Type} {fg fg' : Array Fun × Array Fun} {rs out : Array Val} {b : Bld α}
    {h : BErr → Bld α} {k : α → Bld (Array Nat)} (hb : Builds abiOf fg fg' (b >>= k) rs out) :
    Builds abiOf fg fg' (tryCatchThe BErr b h >>= k) rs out := by
  refine Builds.congr (b' := b >>= k) (fun is => ?_) hb
  obtain ⟨js, xs, r, hr, -⟩ := hb.2.2 is
  simp only [StateT.run_bind] at hr ⊢
  cases hx : b.run (is, rs.size, fg) with
  | error e => rw [hx] at hr; cases hr
  | ok p =>
    have : (tryCatchThe BErr b h).run (is, rs.size, fg) = .ok p := by
      have hx' : b (is, rs.size, fg) = .ok p := hx
      simp only [tryCatchThe, MonadExceptOf.tryCatch, StateT.run]
      rw [hx']
      rfl
    rw [this]

/-- The continuation of `compTB`: `compSelB` on `R'` and the table `S'` that `s` built (`hsel`), then `kk`. The two
    forms of `compTB` (`ds`, closed) differ only in how `S'` is built. -/
theorem compSel_cont {A B C : Obj} {Tot : Tab A B → Tab B C → Prop} (hsel : CompSelSpec A B C Tot Tab.bitsMax)
    {R : Tab A B} {S : Tab B C} {T' : Tab A C} {R' : TabB} {fg : Array Fun × Array Fun} {rs : Array Val}
    {kk : TabB → Bld (Array Nat)} {out : Array Val} (hRk : ColsOf A R'.key) (hRv : ColsOf B R'.val)
    (hR : R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)))
    (hT : R.compSel Tab.bitsMax S = .ok T') (hTot : Tot R S)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → ColsOf A W.key → ColsOf C W.val →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) :
    ∀ (fg2 : Array Fun × Array Fun) (S' : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → ColsOf B S'.key → ColsOf C S'.val →
      S'.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (compSelB Tab.bitsMax R' S' >>= kk) (rs ++ ys) out := by
  intro fg2 S' ys he hf ho hSk hSv hS'
  refine hsel hRk hRv hSk hSv (mapM_extends (fun h => get_app h) hR) hS' hT hTot ho ?_
  intro fg3 W ys3 he3 hf3 ho3 hWk hWv hW
  have := hkk fg3 W (ys ++ ys3) (FExt.trans he he3) (hf.trans hf3) ho3 (ColsOf.shape _ hRk hWk)
    (ColsOf.shape _ hSv hWv) (by simpa [Array.append_assoc] using hW)
  simpa [Array.append_assoc] using this

/-- **`compTB` with `ds` builds `Tab.compSel`**: `nubB` of `R'.val` (`nubB_builds`, `hnub`, `hN`, `hpre` its premises),
    `s` at the context `D` that `hD` reads off the `nub` registers (`SSpec`), then `compSelB` (`CompSelSpec`). -/
theorem compTB_builds_ds {A B C : Obj} {Tot : Tab A B → Tab B C → Prop} (hsel : CompSelSpec A B C Tot Tab.bitsMax)
    {s : Dom → Bld TabB} {ran : Option (Nat × Cols)} {D : Dom → Array Val → Prop} {R : Tab A B} {S : Tab B C}
    {T' : Tab A C} {mv : USize} {y : Vals B mv} {R' : TabB} {fg : Array Fun × Array Fun} {rs : Array Val}
    {kk : TabB → Bld (Array Nat)} {out : Array Val} (hs : SSpec S s D) (hRk : ColsOf A R'.key) (hRv : ColsOf B R'.val)
    (hR : R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)))
    (hnub : Vals.nub R.val = .ok ⟨mv, y⟩) (hN : R.n.toNat ≤ 2 ^ 63) (hpre : AscPre R.val)
    (hD : ∀ (k : Nat) (cs' : Cols) (ys : Array Val), ColsOf B cs' →
      (k :: Cols.regs cs').mapM (fun i => (rs ++ ys)[i]?) = some (.size mv :: y.regVals) →
      D { dom := some (k, cs'), ran } (rs ++ ys))
    (hT : R.compSel Tab.bitsMax S = .ok T') (hTot : Tot R S) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → ColsOf A W.key → ColsOf C W.val →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (compTB R' s true ran >>= kk) rs out := by
  have hRe : R'.regs = R'.n :: (Cols.regs R'.key ++ Cols.regs R'.val) := by simp [TabB.regs, Cols.regs_append]
  have hR0 := hR
  rw [hRe] at hR
  obtain ⟨hRn, hR⟩ := mapM_get_cons hR
  obtain ⟨-, hRv'⟩ := mapM_split (ColsOf.regs_length hRk R.key) hR
  obtain ⟨z, hz, hsc⟩ := hpre
  unfold compTB
  simp only [if_true, bind_assoc]
  refine nubB_builds B hRv hRv' hRn hnub hN hz hsc hfo ?_
  intro fg2 k cs' ys he hf ho hshape hr
  have hcs := ColsOf.shape B hRv hshape
  refine hs (hD k cs' ys hcs hr) ho ?_
  have hc := compSel_cont hsel hRk hRv hR0 hT hTot hkk
  intro fg3 S' ys2 he2 hf2 ho2 hSk hSv hS'
  have := hc fg3 S' (ys ++ ys2) (FExt.trans he he2) (hf.trans hf2) ho2 hSk hSv (by simpa [Array.append_assoc] using hS')
  simpa [Array.append_assoc] using this

/-- **`compTB` of a closed `S` builds `Tab.compSel`**, where `s {}` builds (not its fallback): `s` at the context `D {}`
    (`SSpec`), then `compSelB`. -/
theorem compTB_builds_closed {A B C : Obj} {Tot : Tab A B → Tab B C → Prop}
    (hsel : CompSelSpec A B C Tot Tab.bitsMax) {s : Dom → Bld TabB} {ran : Option (Nat × Cols)}
    {D : Dom → Array Val → Prop} {R : Tab A B} {S : Tab B C} {T' : Tab A C} {R' : TabB} {fg : Array Fun × Array Fun}
    {rs : Array Val} {kk : TabB → Bld (Array Nat)} {out : Array Val} (hs : SSpec S s D) (hRk : ColsOf A R'.key)
    (hRv : ColsOf B R'.val) (hR : R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)))
    (hD : D {} rs) (hT : R.compSel Tab.bitsMax S = .ok T') (hTot : Tot R S) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → ColsOf A W.key → ColsOf C W.val →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (compTB R' s false ran >>= kk) rs out := by
  unfold compTB
  simp only [Bool.false_eq_true, if_false, bind_assoc]
  obtain ⟨fg', h⟩ := hs hD hfo (compSel_cont hsel hRk hRv hR hT hTot hkk)
  exact ⟨fg', Builds.tryCatch h⟩

end Rel.Lang.Plan
