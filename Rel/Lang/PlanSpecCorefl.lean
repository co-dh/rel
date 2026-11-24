module

public import Rel.Lang.PlanSpecGather

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `coreflB` means `Tab.dom`/`Tab.ran`, `.conv` means `Tab.conv`

`coreflB` is `nubB` with each row paired with itself, as `Tab.dom` is `Vals.nub` of the key side so paired.
`nodeB`'s `.conv` arm is `canonT` of the swapped table, as `Tab.conv` is `Tab.canon` of the swapped table. Its
`.outl`/`.outr` arms are `canonT` of `⟨n, X, repath …⟩`, `Tab.outl X = Tab.canon ⟨n, X, X.1⟩` by `rfl`, so
`canonT_builds` is their statement once `repath` has one. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

theorem Grows.coreflB (n : Nat) (cs : Cols) : Grows (Plan.coreflB n cs) := by
  unfold Plan.coreflB
  exact (Grows.nubB _ _).bind fun _ => Grows.pure _

theorem Typed.coreflB {m n : Nat} (cs : Cols) (hn : m ≤ n) (hcs : AllGe m (Cols.regs cs)) :
    Typed m (fun U => AllGe m U.regs) (Plan.coreflB n cs) := by
  unfold Plan.coreflB
  refine (Typed.nubB cs hn hcs).bind fun r hr => ?_
  obtain ⟨k, cs'⟩ := r
  refine Typed.pure fun a ha => ?_
  simp only [TabB.regs, Cols.regs_append, List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | ha | ha
  · exact hr.1
  all_goals exact hr.2 a ha

/-- **`coreflB` builds the paired `Vals.nub`**: `nubB_builds`' premises on the side `x` of `A`; `kk` continues with a
    table whose key and value are columns of `cs`'s shape, its registers holding `y` twice. -/
theorem coreflB_builds {fg : Array Fun × Array Fun} (A : Obj) {nv mv : USize} {x : Vals A nv} {y : Vals A mv}
    {cs : Cols} {rs : Array Val} {n : Nat} {z : Enc} {kk : TabB → Bld (Array Nat)} {out : Array Val}
    (hcs : ColsOf A cs) (hx : (Cols.regs cs).mapM (fun i => rs[i]?) = some x.regVals)
    (hn : rs[n]? = some (.size nv)) (hnub : Vals.nub x = .ok ⟨mv, y⟩) (hN : nv.toNat ≤ 2 ^ 63)
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok z)
    (hsc : ∀ es vs p k g f, ValsB.cols x = .ok es → kasc nv es = .ok (vs, p) →
      kseen nv ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 nv (some z) [(nv, z), (nv, g)] [] [] = .ok r) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (U : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      (∃ e, fg2.2 = fg.2 ++ e) → Ordered fg2.1 → Cols.shape U.key = Cols.shape cs → Cols.shape U.val = Cols.shape cs →
      U.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size mv :: (y.regVals ++ y.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk U) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (coreflB n cs >>= kk) rs out := by
  unfold coreflB
  rw [bind_assoc]
  refine nubB_builds A hcs hx hn hnub hN hz hsc hfo fun fg2 k cs' ys he hf ho hs hr => ?_
  simp only [pure_bind]
  refine hkk fg2 ⟨k, cs', cs'⟩ ys he hf ho hs hs ?_
  obtain ⟨hk, hr⟩ := mapM_get_cons hr
  simp only [TabB.regs, Cols.regs_append, List.mapM_cons, hk, List.mapM_append, hr]
  rfl

/-- **`coreflB` of a key side builds `Tab.dom`**: `T` a table of `A`-sided key whose registers hold `R`, `R.dom = R'`. -/
theorem coreflB_dom_builds {fg : Array Fun × Array Fun} {a b : Obj} {R : Tab a b} {R' : Tab a a} {cs : Cols}
    {rs : Array Val} {n : Nat} {z : Enc} {kk : TabB → Bld (Array Nat)} {out : Array Val}
    (hcs : ColsOf a cs) (hx : (Cols.regs cs).mapM (fun i => rs[i]?) = some R.key.regVals)
    (hn : rs[n]? = some (.size R.n)) (hc : R.dom = .ok R') (hN : R.n.toNat ≤ 2 ^ 63)
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) R.n 0 = .ok z)
    (hsc : ∀ es vs p k g f, ValsB.cols R.key = .ok es → kasc R.n es = .ok (vs, p) →
      kseen R.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 R.n (some z) [(R.n, z), (R.n, g)] [] [] = .ok r) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (U : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      (∃ e, fg2.2 = fg.2 ++ e) → Ordered fg2.1 → Cols.shape U.key = Cols.shape cs → Cols.shape U.val = Cols.shape cs →
      U.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size R'.n :: (R'.key.regVals ++ R'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk U) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (coreflB n cs >>= kk) rs out := by
  unfold Tab.dom at hc
  rcases hnub : Vals.nub R.key with e | ⟨m, y⟩
  · simp [hnub, Functor.map, Except.map] at hc
  simp only [hnub, Functor.map, Except.map, Except.ok.injEq] at hc
  subst hc
  exact coreflB_builds a hcs hx hn hnub hN hz hsc hfo hkk

/-- **`coreflB` of a value side builds `Tab.ran`**: as `coreflB_dom_builds`, at `R.val`. -/
theorem coreflB_ran_builds {fg : Array Fun × Array Fun} {a b : Obj} {R : Tab a b} {R' : Tab b b} {cs : Cols}
    {rs : Array Val} {n : Nat} {z : Enc} {kk : TabB → Bld (Array Nat)} {out : Array Val}
    (hcs : ColsOf b cs) (hx : (Cols.regs cs).mapM (fun i => rs[i]?) = some R.val.regVals)
    (hn : rs[n]? = some (.size R.n)) (hc : R.ran = .ok R') (hN : R.n.toNat ≤ 2 ^ 63)
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) R.n 0 = .ok z)
    (hsc : ∀ es vs p k g f, ValsB.cols R.val = .ok es → kasc R.n es = .ok (vs, p) →
      kseen R.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 R.n (some z) [(R.n, z), (R.n, g)] [] [] = .ok r) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (U : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      (∃ e, fg2.2 = fg.2 ++ e) → Ordered fg2.1 → Cols.shape U.key = Cols.shape cs → Cols.shape U.val = Cols.shape cs →
      U.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size R'.n :: (R'.key.regVals ++ R'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk U) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (coreflB n cs >>= kk) rs out := by
  unfold Tab.ran at hc
  rcases hnub : Vals.nub R.val with e | ⟨m, y⟩
  · simp [hnub, Functor.map, Except.map] at hc
  simp only [hnub, Functor.map, Except.map, Except.ok.injEq] at hc
  subst hc
  exact coreflB_builds b hcs hx hn hnub hN hz hsc hfo hkk

/-- **`.conv`'s `canonT` of the swapped table builds `Tab.conv`**: `T` holds `R` (its key `a`-sided, its value
    `b`-sided), `R.conv = R'`; `kk` continues with a table of `T`'s swapped shape holding `R'`. -/
theorem convT_builds {fg : Array Fun × Array Fun} {a b : Obj} {R : Tab a b} {R' : Tab b a} {T : TabB}
    {rs : Array Val} {z : Enc} {kk : TabB → Bld (Array Nat)} {out : Array Val} (hk : ColsOf a T.key)
    (hv : ColsOf b T.val)
    (hT : T.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)))
    (hc : R.conv = .ok R') (hN : R.n.toNat ≤ 2 ^ 63)
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) R.n 0 = .ok z)
    (hsc : ∀ es vs p k g f, ValsB.cols (A := .prod b a) (R.val, R.key) = .ok es → kasc R.n es = .ok (vs, p) →
      kseen R.n ((es.map (·.1)).zip vs) = .ok (k, g, f) →
      ∃ r, kscan .max false .i64 .i64 R.n (some z) [(R.n, z), (R.n, g)] [] [] = .ok r) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (U : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      (∃ e, fg2.2 = fg.2 ++ e) → Ordered fg2.1 → Cols.shape U.key = Cols.shape T.val →
      Cols.shape U.val = Cols.shape T.key →
      U.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size R'.n :: (R'.key.regVals ++ R'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk U) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (canonT ⟨T.n, T.val, T.key⟩ >>= kk) rs out := by
  simp only [TabB.regs] at hT
  obtain ⟨hn, hx⟩ := mapM_get_cons hT
  simp only [Cols.regs_append] at hx
  obtain ⟨hx1, hx2⟩ := mapM_split (ColsOf.regs_length hk R.key) hx
  refine canonT_builds (R := (⟨R.n, R.val, R.key⟩ : Tab b a)) (T := ⟨T.n, T.val, T.key⟩) hv hk ?_ hc hN hz hsc hfo hkk
  simp only [TabB.regs, Cols.regs_append, List.mapM_cons, hn, List.mapM_append, hx2, hx1]
  rfl

end Rel.Lang.Plan
