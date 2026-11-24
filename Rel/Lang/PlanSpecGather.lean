module

public import Rel.Lang.PlanSpec
public import Rel.RepCanon

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `gatherCols` means `ValsB.gather` (`canonT_builds`, stage 1b)

A side `x : ValsB o A n` in registers is `ValsB.regVals x`, in `regsOf` order; `gatherB` of one register is
`kgather` of its `Enc`, which is what `ColB.gather` computes. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- The register values of the side `x`, in `regsOf` order: an atom its `Enc`; a product its two sides'; an array its
    payload's count, `lo`, `hi`, then its payload's; a band sum its one `Opt`; a general sum its tag, then its two
    summands'; `1` none. -/
def _root_.Rel.ValsB.regVals : {o : Bool} → {A : Obj} → {n : USize} → ValsB o A n → List Val
  | _, .atom _, _, x => [Reg.put (ColB.enc x)]
  | _, .prod _ _, _, x => ValsB.regVals x.1 ++ ValsB.regVals x.2
  | _, .arr _, _, ⟨c, lo, hi, f⟩ => [.size c, Reg.put (ColB.enc lo), Reg.put (ColB.enc hi)] ++ ValsB.regVals f
  | _, .sum _ _, _, s => match ValsB.view s with
    | .opt _ x => [Reg.put x.enc]
    | .gen _ tag x y => Reg.put tag.enc :: (ValsB.regVals x ++ ValsB.regVals y)
  | _, .one, _, _ => []

/-- `ColB.gather` is `kgather` of the column's `Enc`, at either ownership. -/
theorem ColB.gather_kgather : ∀ {o : Bool} {t : QAtomicType} {n m : USize} {ix : Enc} {x : ColB o t n}
    {y : ColB o t m}, ColB.gather m ix x = .ok y → kgather m ix n (ColB.enc x) = .ok (ColB.enc y)
  | false, _, n, m, ix, x, y, h => by
    simp only [ColB.gather, Arr.gather] at h
    split at h
    · next o ho => cases h; exact ho
    · cases h
  | true, _, n, m, ix, x, y, h => by
    simp only [ColB.gather, Opt.gather] at h
    split at h
    · next o ho => cases h; exact ho
    · cases h

/-- `gatherB m ix n e`, then `c`: the registers `m`, `n` hold the counts `mv`, `nv`, `ix` and `e` the `Enc`s `iv`,
    `ev`; the new register holds `kgather mv iv nv ev`. -/
theorem gatherB_builds {fg fg' : Array Fun × Array Fun} {rs out : Array Val} {m ix n e : Nat} {mv nv : USize}
    {iv ev ov : Enc} {c : Nat → Bld (Array Nat)}
    (hm : rs[m]? = some (.size mv)) (hi : rs[ix]? = some (Reg.put iv)) (hn : rs[n]? = some (.size nv))
    (he : rs[e]? = some (Reg.put ev)) (hk : kgather mv iv nv ev = .ok ov)
    (hc : Builds abiOf fg fg' (c rs.size) (rs.push (Reg.put ov)) out) :
    Builds abiOf fg fg' (gatherB m ix n e >>= c) rs out := by
  unfold gatherB
  refine Builds.call1 (vs := #[.size mv, Reg.put iv, .size nv, Reg.put ev]) (v := Reg.put ov)
    (by with_unfolding_all simp [abiOf, Rel.Lang.Plan.abi, List.find?]) (by with_unfolding_all rfl) ?_ ?_ rfl hc
  · rw [List.mapM_toArray]
    simp [reg, hm, hi, hn, he]
    rfl
  · have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
    simp [arg, hsz, enc_get_put, hk, Out.out]
    rfl

/-! ### `keysL`: the key registers of a side's columns read as `ValsB.cols` -/

/-- The plan columns `cs` of a side of `A`, node for node as `ValsB` and as `colsOf` builds them: an atom one `atom`
    column of its atom; a product its two sides' columns one after the other; an array one `arr` column over its
    payload's; a band sum (`Obj.band`) one `atom` column, its `Opt`; any other sum one `sum` column over its summands';
    `1` none. Only the shape: what the registers hold is `ValsB.regVals`, read at `regsOf cs`. -/
def ColsOf : Obj → Cols → Prop
  | .atom t, cs => ∃ p e, cs = [.atom p t e]
  | .prod a b, cs => ∃ c1 c2, cs = c1 ++ c2 ∧ ColsOf a c1 ∧ ColsOf b c2
  | .arr b, cs => ∃ p m lo hi f, cs = [.arr p m lo hi f] ∧ ColsOf b f
  | .sum a b, cs => match Obj.band a b with
    | some t => ∃ p e, cs = [.atom p t e]
    | none => ∃ p tag x y, cs = [.sum p tag x y] ∧ ColsOf a x ∧ ColsOf b y
  | .one, cs => cs = []

theorem bld_pure_inj {α : Type} {a b : α} (h : (pure a : Bld α) = pure b) : a = b := by
  have := congrArg (fun m : Bld α => m.run (#[], 0, #[], #[])) h
  change Except.ok (a, _) = Except.ok (b, _) at this
  injection this with h1; injection h1

theorem except_bind_ok {α β : Type} {m : Except String α} {f : α → Except String β} {b : β} (h : m >>= f = .ok b) :
    ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem regsOf_append : ∀ c1 c2 : Cols, regsOf (c1 ++ c2) = (do let a ← regsOf c1; let b ← regsOf c2; pure (a ++ b))
  | [], c2 => by simp [regsOf]
  | c :: c1, c2 => by simp only [List.cons_append, regsOf, regsOf_append c1 c2, bind_assoc, pure_bind, List.append_assoc]

theorem keysL_append (n : Nat) : ∀ c1 c2 : Cols,
    keysL n (c1 ++ c2) = (do let a ← keysL n c1; let b ← keysL n c2; pure (a ++ b))
  | [], c2 => by simp [keysL]
  | c :: c1, c2 => by
    simp only [List.cons_append, keysL, keysL_append n c1 c2, bind_assoc, pure_bind, List.append_assoc]

/-- The columns of a side of `A` have registers, as many as any side of `A` has `regVals`. -/
theorem regsOf_of_colsOf : ∀ (A : Obj) {cs : Cols}, ColsOf A cs →
    ∃ L, regsOf cs = pure L ∧ ∀ {o : Bool} {n : USize} (x : ValsB o A n), x.regVals.length = L.length
  | .atom t, _, ⟨p, e, rfl⟩ => ⟨[e], by simp [regsOf, regsC], fun x => by simp [ValsB.regVals]⟩
  | .prod a b, _, ⟨c1, c2, rfl, h1, h2⟩ => by
    obtain ⟨L1, e1, l1⟩ := regsOf_of_colsOf a h1
    obtain ⟨L2, e2, l2⟩ := regsOf_of_colsOf b h2
    exact ⟨L1 ++ L2, by rw [regsOf_append, e1, e2]; simp, fun x => by simp [ValsB.regVals, l1, l2]⟩
  | .arr b, _, ⟨p, m, lo, hi, f, rfl, hf⟩ => by
    obtain ⟨Lf, ef, lf⟩ := regsOf_of_colsOf b hf
    exact ⟨[m, lo, hi] ++ Lf, by simp [regsOf, regsC, ef], fun ⟨c, xlo, xhi, y⟩ => by simp [ValsB.regVals, lf]⟩
  | .sum a b, cs, h => by
    simp only [ColsOf] at h
    cases hb : Obj.band a b with
    | some t =>
      simp only [hb] at h
      obtain ⟨p, e, rfl⟩ := h
      refine ⟨[e], by simp [regsOf, regsC], fun x => ?_⟩
      cases hv : ValsB.view x with
      | opt _ y => simp [ValsB.regVals, hv]
      | gen h' => rw [hb] at h'; cases h'
    | none =>
      simp only [hb] at h
      obtain ⟨p, tag, xs, ys, rfl, ha, hb'⟩ := h
      obtain ⟨Lx, ex, lx⟩ := regsOf_of_colsOf a ha
      obtain ⟨Ly, ey, ly⟩ := regsOf_of_colsOf b hb'
      refine ⟨tag :: (Lx ++ Ly), by simp [regsOf, regsC, ex, ey], fun x => ?_⟩
      cases hv : ValsB.view x with
      | opt h' => rw [hb] at h'; cases h'
      | gen _ tg y z => simp [ValsB.regVals, hv, lx, ly]
  | .one, _, rfl => ⟨[], by simp [regsOf], fun _ => by simp [ValsB.regVals]⟩

theorem mapM_get_cons {rs : Array Val} {i : Nat} {l : List Nat} {v : Val} {vs : List Val}
    (h : (i :: l).mapM (fun x => rs[x]?) = some (v :: vs)) : rs[i]? = some v ∧ l.mapM (fun x => rs[x]?) = some vs := by
  obtain ⟨w, ws, hw, hl, he⟩ := omapM_cons.mp h
  cases he; exact ⟨hw, hl⟩

/-- Registers `L1 ++ L2` holding `v1 ++ v2`, `L1` as long as `v1`: `L1` holds `v1` and `L2` holds `v2`. -/
theorem mapM_split {rs : Array Val} : ∀ {L1 L2 : List Nat} {v1 v2 : List Val}, L1.length = v1.length →
    (L1 ++ L2).mapM (fun i => rs[i]?) = some (v1 ++ v2) →
    L1.mapM (fun i => rs[i]?) = some v1 ∧ L2.mapM (fun i => rs[i]?) = some v2
  | [], _, [], _, _, h => ⟨rfl, h⟩
  | [], _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _, [], _, hl, _ => by simp at hl
  | i :: L1, L2, v :: v1, v2, hl, h => by
    rw [List.cons_append, List.cons_append] at h
    obtain ⟨hv, hl'⟩ := mapM_get_cons h
    obtain ⟨h1, h2⟩ := mapM_split (by simpa using hl) hl'
    exact ⟨omapM_cons.mpr ⟨_, _, hv, h1, rfl⟩, h2⟩

/-- Registers holding the pairs `vs` hold them in registers extending these. -/
theorem mapM_pair_extends {rs R : Array Val} (m : Extends rs R) : ∀ {ps : List (Nat × Nat)} {vs : List (Val × Val)},
    ps.mapM (fun p => do pure (← rs[p.1]?, ← rs[p.2]?)) = some vs →
    ps.mapM (fun p => do pure (← R[p.1]?, ← R[p.2]?)) = some vs
  | [], _, h => h
  | p :: ps, _, h => by
    obtain ⟨v, vs, hv, hl, rfl⟩ := omapM_cons.mp h
    obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a, rs[p.1]? = some a ∧ ∃ b, rs[p.2]? = some b ∧ v = (a, b) := by
      cases h1 : rs[p.1]? <;> cases h2 : rs[p.2]? <;> simp_all
    exact omapM_cons.mpr ⟨_, _, by simp [m ha, m hb], mapM_pair_extends m hl, rfl⟩

/-- The list `Reg (List (AscKey × Enc))` lays out of the pairs `ps` reads as the pairs read. -/
theorem ascGetL?_foldr : ∀ ps : List (Val × Val),
    ascGetL? ((ps.map fun p => Val.ctor 0 #[p.1, p.2] #[]).foldr (fun v c => .ctor 1 #[v, c] #[]) (.ctor 0 #[] #[])) =
      ps.mapM fun p => do pure (← (Reg.get? p.1 : Option AscKey), ← (Reg.get? p.2 : Option Enc))
  | [] => by rw [ascGetL?.eq_def]; rfl
  | p :: ps => by
    have ih := ascGetL?_foldr ps
    rw [List.map_cons, List.foldr_cons]
    generalize (ps.map fun p => Val.ctor 0 #[p.1, p.2] #[]).foldr (fun v c => Val.ctor 1 #[v, c] #[]) (Val.ctor 0 #[] #[])
      = F
      at ih ⊢
    rw [ascGetL?.eq_def]
    simp [ih, List.mapM_cons, ascPairGet?.eq_def, ascKey_get]

/-- A `cells` key register: its `lo`, `hi`, the list of its payload's keys, the counts `n`, `c`. -/
theorem ascGet?_cells {n c : USize} {lo hi : Enc} (ps : List (Val × Val)) {els : List (AscKey × Enc)}
    (h : ps.mapM (fun p => do pure (← (Reg.get? p.1 : Option AscKey), ← (Reg.get? p.2 : Option Enc))) = some els) :
    (Reg.get? (Val.ctor 1 #[Reg.put lo, Reg.put hi, (ps.map fun p => Val.ctor 0 #[p.1, p.2] #[]).foldr
      (fun v c => .ctor 1 #[v, c] #[]) (.ctor 0 #[] #[])] #[.size n, .size c]) : Option AscKey) =
      some (.cells n c lo hi els) := by
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  have hl := (ascGetL?_foldr ps).trans h
  generalize (ps.map fun p => Val.ctor 0 #[p.1, p.2] #[]).foldr (fun v c => Val.ctor 1 #[v, c] #[]) (Val.ctor 0 #[] #[])
    = F
    at hl ⊢
  rw [ascKey_get, ascGet?.eq_def]
  simp [hsz, enc_get_put, hl]

/-- `ps.mapM g`, `g` the pair constructor, then `c`: each new register holds the pair of what `p`'s two hold. -/
theorem Builds.pairsB {fg fg' : Array Fun × Array Fun} {out : Array Val} {g : Nat × Nat → Bld Nat}
    (hg : ∀ k e, g (k, e) = Plan.ctorB 0 #[k, e] #[]) : ∀ (ps : List (Nat × Nat)) {vs : List (Val × Val)} {rs : Array Val}
      {c : List Nat → Bld (Array Nat)}, ps.mapM (fun p => do Pure.pure (← rs[p.1]?, ← rs[p.2]?)) = some vs →
    (∀ qs R, qs.mapM (fun x => R[x]?) = some (vs.map fun p => Val.ctor 0 #[p.1, p.2] #[]) → Extends rs R →
      Builds abiOf fg fg' (c qs) R out) →
    Builds abiOf fg fg' (ps.mapM g >>= c) rs out
  | [], vs, rs, c, h, hc => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h
    simpa using hc [] rs rfl fun h => h
  | (k, e) :: ps, _, rs, c, h, hc => by
    obtain ⟨v, vs, hv, hl, rfl⟩ := omapM_cons.mp h
    obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a, rs[k]? = some a ∧ ∃ b, rs[e]? = some b ∧ v = (a, b) := by
      cases h1 : rs[k]? <;> cases h2 : rs[e]? <;> simp_all
    simp only [List.mapM_cons, hg, bind_assoc, pure_bind]
    refine Builds.ctorBG (reads_of (l := [k, e]) (vs := [a, b]) (by simp [ha, hb]))
      (reads_of (l := []) (vs := []) rfl) fun q R1 hq m1 => ?_
    refine Builds.pairsB hg ps (mapM_pair_extends m1 hl) fun qs R hqs m => ?_
    exact hc (q :: qs) R (omapM_cons.mpr ⟨_, _, m hq, hqs, rfl⟩) fun h => m (m1 h)

/-- `keysL n [.atom p t e]`, `e` holding the column `ce`: one register pair reading `(.atom t, ce)`. -/
theorem keysL_atom {fg fg' : Array Fun × Array Fun} {out rs : Array Val} {n e : Nat} {p : String} {t : QAtomicType}
    {ce : Enc} {c : List (Nat × Nat) → Bld (Array Nat)} (he : rs[e]? = some (Reg.put ce))
    (hc : ∀ ps R vs, ps.mapM (fun p => do pure (← R[p.1]?, ← R[p.2]?)) = some vs →
      vs.mapM (fun p => do pure (← (Reg.get? p.1 : Option AscKey), ← (Reg.get? p.2 : Option Enc))) =
        some [(.atom t, ce)] → Extends rs R → Builds abiOf fg fg' (c ps) R out) :
    Builds abiOf fg fg' (keysL n [.atom p t e] >>= c) rs out := by
  simp only [keysL, keysB, bind_assoc, pure_bind, List.append_nil]
  refine Builds.litG fun r R0 hr m0 => ?_
  refine Builds.ctorBG (reads_of (l := []) (vs := []) rfl) (reads_of (l := [r]) (vs := [Reg.put t]) (by simp [hr]))
    fun k R1 hk m1 => ?_
  exact hc [(k, e)] R1 [(.ctor 0 #[] #[Reg.put t], Reg.put ce)] (by simp [hk, m1 (m0 he)])
    (by simp [ascGet?_atom, enc_get_put]) fun h => m1 (m0 h)

/-- **`keysL`'s keys are `ValsB.cols`**: the columns `cs` of a side `x` of `A` (`ColsOf`), their registers `regsOf cs`
    holding `x.regVals` and `n` its row count: the `(key, column)` register pairs `keysL n cs` answers read as
    `x.cols`, the list `kasc` and `kseen` sort and compare by. -/
theorem keysL_builds {fg fg' : Array Fun × Array Fun} {out : Array Val} :
    ∀ {o : Bool} (A : Obj) {nv : USize} {x : ValsB o A nv} {cs : Cols} {L : List Nat} {rs : Array Val} {n : Nat}
      {ks : List (AscKey × Enc)} {c : List (Nat × Nat) → Bld (Array Nat)},
    ColsOf A cs → regsOf cs = pure L → L.mapM (fun i => rs[i]?) = some x.regVals → rs[n]? = some (.size nv) →
    x.cols = .ok ks →
    (∀ ps R vs, ps.mapM (fun p => do pure (← R[p.1]?, ← R[p.2]?)) = some vs →
      vs.mapM (fun p => do pure (← (Reg.get? p.1 : Option AscKey), ← (Reg.get? p.2 : Option Enc))) = some ks →
      Extends rs R → Builds abiOf fg fg' (c ps) R out) →
    Builds abiOf fg fg' (keysL n cs >>= c) rs out
  | _, .atom t, nv, x, _, L, rs, n, ks, c, ⟨p, e, rfl⟩, hL, hx, _, hks, hc => by
    obtain rfl : L = [e] := bld_pure_inj (hL.symm.trans (by simp [regsOf, regsC]))
    simp only [ValsB.regVals] at hx
    simp only [ValsB.cols, Except.ok.injEq] at hks
    subst hks
    exact keysL_atom (mapM_get_cons hx).1 hc
  | _, .prod a b, nv, x, _, L, rs, n, ks, c, ⟨c1, c2, rfl, h1, h2⟩, hL, hx, hn, hks, hc => by
    obtain ⟨L1, e1, l1⟩ := regsOf_of_colsOf a h1
    obtain ⟨L2, e2, l2⟩ := regsOf_of_colsOf b h2
    obtain rfl : L = L1 ++ L2 := bld_pure_inj (hL.symm.trans (by rw [regsOf_append, e1, e2]; simp))
    simp only [ValsB.regVals] at hx
    obtain ⟨hx1, hx2⟩ := mapM_split (l1 x.1).symm hx
    simp only [ValsB.cols] at hks
    obtain ⟨ks1, hk1, h'⟩ := except_bind_ok hks
    obtain ⟨ks2, hk2, h''⟩ := except_bind_ok h'
    cases h''
    simp only [keysL_append, bind_assoc, pure_bind]
    refine keysL_builds a h1 e1 hx1 hn hk1 fun ps1 R1 vs1 hp1 hv1 m1 => ?_
    refine keysL_builds b h2 e2 (mapM_extends m1 hx2) (m1 hn) hk2 fun ps2 R2 vs2 hp2 hv2 m2 => ?_
    refine hc (ps1 ++ ps2) R2 (vs1 ++ vs2) ?_ ?_ fun h => m2 (m1 h)
    · rw [List.mapM_append, mapM_pair_extends m2 hp1, hp2]; rfl
    · rw [List.mapM_append, hv1, hv2]; rfl
  | _, .arr b, nv, x, _, L, rs, n, ks, c, ⟨p, m, lo, hi, f, rfl, hf⟩, hL, hx, hn, hks, hc => by
    rcases x with ⟨cnt, xlo, xhi, y⟩
    obtain ⟨Lf, ef, -⟩ := regsOf_of_colsOf b hf
    obtain rfl : L = [m, lo, hi] ++ Lf := bld_pure_inj (hL.symm.trans (by simp [regsOf, regsC, ef]))
    simp only [ValsB.regVals] at hx
    obtain ⟨h3, hxf⟩ := mapM_split (v1 := [.size cnt, Reg.put (ColB.enc xlo), Reg.put (ColB.enc xhi)]) rfl hx
    obtain ⟨hm, h3⟩ := mapM_get_cons h3
    obtain ⟨hlo, h3⟩ := mapM_get_cons h3
    obtain ⟨hhi, -⟩ := mapM_get_cons h3
    simp only [ValsB.cols] at hks
    obtain ⟨ksf, hkf, hk⟩ := except_bind_ok hks
    cases hk
    simp only [keysL, keysB, bind_assoc, pure_bind, List.append_nil]
    refine keysL_builds b hf ef hxf hm hkf fun ps R1 vs hps hvs m1 => ?_
    refine Builds.pairsB (by intro _ _; rfl) ps hps fun qs R2 hqs m2 => ?_
    refine Builds.listBG hqs fun l R3 hl m3 => ?_
    have hK := ascGet?_cells (n := nv) (c := cnt) (lo := ColB.enc xlo) (hi := ColB.enc xhi) vs hvs
    generalize (vs.map fun p => Val.ctor 0 #[p.1, p.2] #[]).foldr (fun v c => Val.ctor 1 #[v, c] #[]) (Val.ctor 0 #[] #[])
      = F at hl hK
    refine Builds.ctorBG (reads_of (l := [lo, hi, l]) (vs := [Reg.put (ColB.enc xlo), Reg.put (ColB.enc xhi), F])
      (by simp [hl, m3 (m2 (m1 hlo)), m3 (m2 (m1 hhi))]))
      (reads_of (l := [n, m]) (vs := [.size nv, .size cnt]) (by simp [m3 (m2 (m1 hn)), m3 (m2 (m1 hm))]))
      fun k R4 hk4 m4 => ?_
    unfold posB
    refine Builds.litG fun q R5 hq m5 => ?_
    exact hc [(k, q)] R5 [(.ctor 1 #[Reg.put (ColB.enc xlo), Reg.put (ColB.enc xhi), F] #[.size nv, .size cnt],
      Reg.put (Enc.pos : Enc))] (by simp [hq, m5 hk4]) (by simp [hK, enc_get_put])
      fun h => m5 (m4 (m3 (m2 (m1 h))))
  | _, .sum a b, nv, x, cs, L, rs, n, ks, c, hcs, hL, hx, hn, hks, hc => by
    simp only [ColsOf] at hcs
    simp only [ValsB.regVals] at hx
    simp only [ValsB.cols] at hks
    cases hv : ValsB.view x with
    | opt hb y =>
      simp only [hb] at hcs
      obtain ⟨p, e, rfl⟩ := hcs
      rw [hv] at hx hks
      obtain rfl : L = [e] := bld_pure_inj (hL.symm.trans (by simp [regsOf, regsC]))
      cases hks
      exact keysL_atom (mapM_get_cons hx).1 hc
    | gen hb tg y z =>
      simp only [hb] at hcs
      obtain ⟨p, tag, xs, ys, rfl, ha, hb'⟩ := hcs
      rw [hv] at hx hks
      obtain ⟨Lx, ex, lx⟩ := regsOf_of_colsOf a ha
      obtain ⟨Ly, ey, -⟩ := regsOf_of_colsOf b hb'
      obtain rfl : L = tag :: (Lx ++ Ly) := bld_pure_inj (hL.symm.trans (by simp [regsOf, regsC, ex, ey]))
      obtain ⟨htag, hxy⟩ := mapM_get_cons hx
      obtain ⟨hxs, hys⟩ := mapM_split (lx y).symm hxy
      obtain ⟨ks1, hk1, h'⟩ := except_bind_ok hks
      obtain ⟨ks2, hk2, h''⟩ := except_bind_ok h'
      cases h''
      simp only [keysL, keysB, bind_assoc, pure_bind, List.append_nil]
      refine Builds.litG fun r R0 hr m0 => ?_
      refine Builds.ctorBG (reads_of (l := []) (vs := []) rfl)
        (reads_of (l := [r]) (vs := [Reg.put QAtomicType.u1]) (by simp [hr])) fun k R1 hk m1 => ?_
      refine keysL_builds a ha ex (mapM_extends (fun h => m1 (m0 h)) hxs) (m1 (m0 hn)) hk1
        fun ps1 R2 vs1 hp1 hv1 m2 => ?_
      refine keysL_builds b hb' ey (mapM_extends (fun h => m2 (m1 (m0 h))) hys) (m2 (m1 (m0 hn))) hk2
        fun ps2 R3 vs2 hp2 hv2 m3 => ?_
      refine hc ((k, tag) :: (ps1 ++ ps2)) R3 ((.ctor 0 #[] #[Reg.put QAtomicType.u1], Reg.put tg.enc) :: (vs1 ++ vs2))
        ?_ ?_ fun h => m3 (m2 (m1 (m0 h)))
      · rw [List.mapM_cons, List.mapM_append, mapM_pair_extends m3 hp1, hp2]
        simp [m3 (m2 hk), m3 (m2 (m1 (m0 htag)))]
      · rw [List.mapM_cons, List.mapM_append, hv1, hv2]
        simp [ascGet?_atom, enc_get_put]
  | _, .one, nv, x, _, L, rs, n, ks, c, rfl, hL, hx, hn, hks, hc => by
    simp only [ValsB.cols, Except.ok.injEq] at hks
    subst hks
    simpa [keysL] using hc [] rs [] rfl rfl fun h => h

/-! ### `ascSeenOnB`: `keysL`, then `kasc`, `sortedB`, `seenB` -/

theorem except_mapM_length {α β : Type} {f : α → Except String β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by rw [List.mapM_nil] at h; cases h; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, -, h'⟩ := except_bind_ok h
    obtain ⟨bs, hbs, h''⟩ := except_bind_ok h'
    cases h''
    simp [except_mapM_length hbs]

theorem option_mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by rw [List.mapM_nil] at h; cases h; rfl
  | a :: l, r, h => by
    obtain ⟨b, bs, -, hbs, rfl⟩ := omapM_cons.mp h
    simp [option_mapM_length hbs]

/-- `kasc` answers one sorted column per key. -/
theorem kasc_length {m : USize} {es : List (AscKey × Enc)} {vs : List Enc} {pv : Enc}
    (h : kasc m es = .ok (vs, pv)) : vs.length = es.length := by
  unfold kasc at h
  obtain ⟨cs, hcs, h⟩ := except_bind_ok h
  dsimp only at h
  obtain ⟨r, -, h⟩ := except_bind_ok h
  obtain ⟨vs', hvs, h⟩ := except_bind_ok h
  obtain ⟨ns, hns, h⟩ := except_bind_ok h
  cases h
  simp [except_mapM_length hvs, except_mapM_length hcs, except_mapM_length hns]

theorem pair_get {α β : Type} [Reg α] [Reg β] (a b : Val) :
    (Reg.get? (Val.ctor 0 #[a, b] #[]) : Option (α × β)) = (do pure (← Reg.get? a, ← Reg.get? b)) := rfl

theorem pairs_get : ∀ kvs : List (Val × Val),
    ((kvs.map fun p => Val.ctor 0 #[p.1, p.2] #[]).mapM Reg.get? : Option (List (AscKey × Enc))) =
      kvs.mapM fun p => do pure (← (Reg.get? p.1 : Option AscKey), ← (Reg.get? p.2 : Option Enc))
  | [] => rfl
  | p :: ps => by rw [List.map_cons, List.mapM_cons, List.mapM_cons, pairs_get ps]; rfl

/-- The first registers of the pairs `ps` hold the first values. -/
theorem mapM_fst {R : Array Val} : ∀ {ps : List (Nat × Nat)} {vs : List (Val × Val)},
    ps.mapM (fun p => do pure (← R[p.1]?, ← R[p.2]?)) = some vs →
    (ps.map (·.1)).mapM (fun x => R[x]?) = some (vs.map (·.1))
  | [], _, h => by rw [List.mapM_nil] at h; cases h; rfl
  | p :: ps, _, h => by
    obtain ⟨v, vs, hv, hl, rfl⟩ := omapM_cons.mp h
    obtain ⟨a, ha, b, -, rfl⟩ : ∃ a, R[p.1]? = some a ∧ ∃ b, R[p.2]? = some b ∧ v = (a, b) := by
      cases h1 : R[p.1]? <;> cases h2 : R[p.2]? <;> simp_all
    exact omapM_cons.mpr ⟨_, _, ha, mapM_fst hl, rfl⟩

/-- The keys `ks` beside the sorted columns `vs`, as `sortedB` lays them, read as the pairs `kseen` takes. -/
theorem sorted_get : ∀ {kvs : List (Val × Val)} {ks : List (AscKey × Enc)} {vs : List Enc},
    kvs.mapM (fun p => do pure (← (Reg.get? p.1 : Option AscKey), ← (Reg.get? p.2 : Option Enc))) = some ks →
    (((kvs.map (·.1)).zip vs).map fun p => Val.ctor 0 #[p.1, Reg.put p.2] #[]).mapM
      (Reg.get? : Val → Option (AscKey × Enc)) = some ((ks.map (·.1)).zip vs)
  | [], _, _, h => by rw [List.mapM_nil] at h; cases h; rfl
  | _ :: _, _, [], _ => by simp
  | p :: kvs, _, v :: vs, h => by
    obtain ⟨w, ws, hw, hl, rfl⟩ := omapM_cons.mp h
    obtain ⟨a, ha, -, -, rfl⟩ : ∃ a, (Reg.get? p.1 : Option AscKey) = some a ∧
        ∃ e, (Reg.get? p.2 : Option Enc) = some e ∧ w = (a, e) := by
      cases h1 : (Reg.get? p.1 : Option AscKey) <;> cases h2 : (Reg.get? p.2 : Option Enc) <;> simp_all
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, sorted_get hl]
    simp [pair_get, ha, enc_get_put]

/-- Registers holding `bs`, which read as `xs`: they read as `xs` (`mapM_bind_split`'s converse). -/
theorem mapM_bind_join {α : Type} [Reg α] {rs : Array Val} : ∀ {es : List Nat} {bs : List Val} {xs : List α},
    es.mapM (fun x => rs[x]?) = some bs → bs.mapM Reg.get? = some xs →
    es.mapM (fun x => rs[x]?.bind Reg.get?) = some xs
  | [], _, _, h, h' => by rw [List.mapM_nil] at h; cases h; exact h'
  | _ :: _, _, _, h, h' => by
    obtain ⟨v, vs, hv, hl, rfl⟩ := omapM_cons.mp h
    obtain ⟨a, as, ha, hs, rfl⟩ := omapM_cons.mp h'
    exact omapM_cons.mpr ⟨a, as, by rw [hv]; exact ha, mapM_bind_join hl hs, rfl⟩

/-- A three-register builder `b` (its theorem stated of `b >>= fun t => pure #[t.1, t.2.1, t.2.2]`), then `k`. -/
theorem Builds.bind3G {abi : String → Option Kernel} {fg fg1 fg' : Array Fun × Array Fun}
    {b : Bld (Nat × Nat × Nat)} {k : Nat × Nat × Nat → Bld (Array Nat)} {rs out : Array Val} {o1 o2 o3 : Val}
    (hb : Builds abi fg fg1 (b >>= fun t => Pure.pure #[t.1, t.2.1, t.2.2]) rs #[o1, o2, o3])
    (hk : ∀ t R, R[t.1]? = some o1 → R[t.2.1]? = some o2 → R[t.2.2]? = some o3 → Extends rs R →
      Builds abi fg1 fg' (k t) R out) : Builds abi fg fg' (b >>= k) rs out := by
  have e : b >>= k = (b >>= fun t => Pure.pure #[t.1, t.2.1, t.2.2]) >>= fun a =>
      k (a[0]?.getD 0, a[1]?.getD 0, a[2]?.getD 0) := by simp
  rw [e]
  refine Builds.bindG hb fun a R h m => ?_
  obtain ⟨x, hx, hX⟩ := holds_at h (i := 0) (v := o1) rfl
  obtain ⟨y, hy, hY⟩ := holds_at h (i := 1) (v := o2) rfl
  obtain ⟨z, hz, hZ⟩ := holds_at h (i := 2) (v := o3) rfl
  rw [show a[0]?.getD 0 = x by simp at hx; simp [hx], show a[1]?.getD 0 = y by simp at hy; simp [hy],
    show a[2]?.getD 0 = z by simp at hz; simp [hz]]
  exact hk (x, y, z) R hX hY hZ m

/-- **`ascSeenOnB` builds**: the columns `cs` of a side `x` (`keysL_builds`' premises), `kasc` of its keys `x.cols`
    answering the sorted columns `vs` and the permutation `p`, `kseen` of the keys beside `vs` answering `k`, `g`,
    `f` (`seenB_builds`' premises): its four registers hold `k`, `g`, `f`, `p`. -/
theorem ascSeenOnB_builds {fg : Array Fun × Array Fun} {o : Bool} (A : Obj) {nv : USize} {x : ValsB o A nv}
    {cs : Cols} {L : List Nat} {rs : Array Val} {n : Nat} {ks : List (AscKey × Enc)} {vs : List Enc} {p : Enc}
    {k : Nat} {g f z : Enc} {r : Enc × Option UInt64} (hcs : ColsOf A cs) (hL : regsOf cs = pure L)
    (hx : L.mapM (fun i => rs[i]?) = some x.regVals) (hn : rs[n]? = some (.size nv)) (hks : x.cols = .ok ks)
    (hN : nv.toNat ≤ 2 ^ 63) (ha : kasc nv ks = .ok (vs, p)) (hk : kseen nv ((ks.map (·.1)).zip vs) = .ok (k, g, f))
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok z)
    (hsc : kscan .max false .i64 .i64 nv (some z) [(nv, z), (nv, g)] [] [] = .ok r) :
    Builds abiOf fg fg (do let (k', g', f', p') ← ascSeenB.ascSeenOnB n cs; Pure.pure #[k', g', f', p']) rs
      #[.size k.toUSize, Reg.put g, Reg.put f, Reg.put p] := by
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  unfold ascSeenB.ascSeenOnB
  simp only [bind_assoc]
  refine keysL_builds A hcs hL hx hn hks fun ps R1 kvs hps hkv m1 => ?_
  refine Builds.pairsB (by intro _ _; rfl) ps hps fun qs R2 hqs m2 => ?_
  refine Builds.listBG hqs fun l R3 hl m3 => ?_
  have hread : (Reg.get? ((kvs.map fun p => Val.ctor 0 #[p.1, p.2] #[]).foldr (fun v c => Val.ctor 1 #[v, c] #[])
      (Val.ctor 0 #[] #[])) : Option (List (AscKey × Enc))) = some ks :=
    (listGet?_foldr _).trans ((pairs_get kvs).trans hkv)
  generalize (kvs.map fun p => Val.ctor 0 #[p.1, p.2] #[]).foldr (fun v c => Val.ctor 1 #[v, c] #[])
    (Val.ctor 0 #[] #[]) = F at hl hread
  refine Builds.callKG (o := #[Reg.put vs, Reg.put p]) (by abiK) rfl
    (reads_of (l := [n, l]) (vs := [.size nv, F]) (by simp [hl, m3 (m2 (m1 hn))])) ?_ rfl fun sp R4 hsp m4 => ?_
  · simp [arg, hsz, hread, ha, Out.out]; rfl
  obtain ⟨p0, hp0, hpR⟩ := holds_at hsp (i := 0) rfl
  obtain ⟨p1, hp1, hpR1⟩ := holds_at hsp (i := 1) rfl
  rw [nth_of (by simpa using hp0), pure_bind]
  have hlen : (kvs.map (·.1)).length = vs.length := by
    rw [List.length_map, ← option_mapM_length hkv, kasc_length ha]
  refine sortedB_builds ps hpR (mapM_fst (mapM_pair_extends (fun h => m4 (m3 (m2 h))) hps)) hlen
    fun es R5 hes m5 => ?_
  refine Builds.bind3G (seenB_builds hN (m5 (m4 (m3 (m2 (m1 hn))))) (mapM_bind_join hes (sorted_get hkv)) hk hz hsc
    fun e _ => enc_get_put e) fun t R6 h1 h2 h3 m6 => ?_
  obtain ⟨k1, g1, f1⟩ := t
  dsimp only at h1 h2 h3 ⊢
  rw [nth_of (by simpa using hp1)]
  simp only [pure_bind]
  exact Builds.pure fun _ => reads_of (l := [k1, g1, f1, p1]) (vs := [.size k.toUSize, Reg.put g, Reg.put f, Reg.put p])
    (by simp [h1, h2, h3, m6 (m5 hpR1)])

theorem withRegs_append : ∀ (c1 c2 : Cols) (rs : List Nat), withRegs (c1 ++ c2) rs =
    (do let (a, rs) ← withRegs c1 rs; let (b, rs) ← withRegs c2 rs; pure (a ++ b, rs))
  | [], c2, rs => by simp [withRegs]
  | c :: c1, c2, rs => by
    simp only [List.cons_append, withRegs, bind_assoc]
    refine congrArg (withReg c rs >>= ·) (funext fun x => ?_)
    obtain ⟨c', r⟩ := x
    simp only [withRegs_append c1 c2 r, bind_assoc]
    refine congrArg (withRegs c1 r >>= ·) (funext fun y => ?_)
    obtain ⟨a, r'⟩ := y
    simp only [bind_assoc, pure_bind]
    refine congrArg (withRegs c2 r' >>= ·) (funext fun z => ?_)
    obtain ⟨b, r''⟩ := z
    rfl

/-- **`ColsOf` survives `withRegs`**: the columns `cs` of a side of `A` relocated to any registers `ps` of their count
    are columns of a side of `A` again, of the same length, holding exactly `ps`. -/
theorem withRegs_colsOf : ∀ (A : Obj) {cs : Cols}, ColsOf A cs → ∀ ps rest, ps.length = (Cols.regs cs).length →
    ∃ cs', withRegs cs (ps ++ rest) = Pure.pure (cs', rest) ∧ ColsOf A cs' ∧ Cols.regs cs' = ps ∧
      cs'.length = cs.length
  | .atom t, _, ⟨p, e, rfl⟩, ps, rest, hl => by
    match ps, hl with
    | [e'], _ => exact ⟨[.atom p t e'], by simp [withRegs, withReg], ⟨p, e', rfl⟩, by simp [Cols.regs, Col.regs], rfl⟩
  | .prod a b, _, ⟨c1, c2, rfl, h1, h2⟩, ps, rest, hl => by
    rw [Cols.regs_append, List.length_append] at hl
    obtain ⟨d1, e1, k1, r1, l1⟩ := withRegs_colsOf a h1 (ps.take (Cols.regs c1).length)
      (ps.drop (Cols.regs c1).length ++ rest) (by rw [List.length_take]; omega)
    obtain ⟨d2, e2, k2, r2, l2⟩ := withRegs_colsOf b h2 (ps.drop (Cols.regs c1).length) rest
      (by rw [List.length_drop]; omega)
    refine ⟨d1 ++ d2, ?_, ⟨d1, d2, rfl, k1, k2⟩, by rw [Cols.regs_append, r1, r2, List.take_append_drop],
      by simp [l1, l2]⟩
    rw [withRegs_append, show ps ++ rest = ps.take (Cols.regs c1).length ++ (ps.drop (Cols.regs c1).length ++ rest)
      by rw [← List.append_assoc, List.take_append_drop], e1, pure_bind]
    simp only [e2, pure_bind]
  | .arr b, _, ⟨p, m, lo, hi, f, rfl, hf⟩, ps, rest, hl => by
    match ps, hl with
    | m' :: lo' :: hi' :: ps, hl =>
      simp [Cols.regs, Col.regs] at hl
      obtain ⟨f', e, k, r, l⟩ := withRegs_colsOf b hf ps rest (by simpa [Cols.regs] using hl)
      refine ⟨[.arr p m' lo' hi' f'], ?_, ⟨p, m', lo', hi', f', rfl, k⟩, by simp [Cols.regs, Col.regs, r], rfl⟩
      simp [withRegs, withReg, e]
  | .sum a b, cs, h, ps, rest, hl => by
    simp only [ColsOf] at h ⊢
    cases hb : Obj.band a b with
    | some t =>
      simp only [hb] at h ⊢
      obtain ⟨p, e, rfl⟩ := h
      match ps, hl with
      | [e'], _ => exact ⟨[.atom p t e'], by simp [withRegs, withReg], ⟨p, e', rfl⟩, by simp [Cols.regs, Col.regs], rfl⟩
    | none =>
      simp only [hb] at h ⊢
      obtain ⟨p, tag, xs, ys, rfl, ha, hb'⟩ := h
      match ps, hl with
      | tag' :: ps, hl =>
        simp [Cols.regs, Col.regs] at hl
        obtain ⟨xs', e1, k1, r1, l1⟩ := withRegs_colsOf a ha (ps.take (Cols.regs xs).length)
          (ps.drop (Cols.regs xs).length ++ rest) (by rw [List.length_take]; omega)
        obtain ⟨ys', e2, k2, r2, l2⟩ := withRegs_colsOf b hb' (ps.drop (Cols.regs xs).length) rest
          (by rw [List.length_drop]; omega)
        refine ⟨[.sum p tag' xs' ys'], ?_, ⟨p, tag', xs', ys', rfl, k1, k2⟩,
          by simp [Cols.regs, Col.regs, r1, r2], rfl⟩
        rw [show tag' :: ps ++ rest = tag' :: (ps.take (Cols.regs xs).length ++ (ps.drop (Cols.regs xs).length ++ rest))
          by rw [← List.append_assoc, List.take_append_drop]; rfl]
        simp [withRegs, withReg, e1, e2]
  | .one, _, rfl, ps, rest, hl => by
    match ps, hl with
    | [], _ => exact ⟨[], by simp [withRegs], rfl, rfl, rfl⟩

/-- **`ascSeenB` builds**: `funV` of `ascSeenOnB` (`funV_builds`) over the columns `cs` of a side `x` of `A`
    (`ascSeenOnB_builds`' premises); `kk` continues with the four registers of the answer, holding `k`, `g`, `f`, `p`,
    under any functions and globals extending `fg`'s. -/
theorem ascSeenB_builds {fg : Array Fun × Array Fun} {o : Bool} (A : Obj) {nv : USize} {x : ValsB o A nv}
    {cs : Cols} {L : List Nat} {rs : Array Val} {n : Nat} {ks : List (AscKey × Enc)} {vs : List Enc} {p : Enc}
    {k : Nat} {g f z : Enc} {r : Enc × Option UInt64} {kk : Nat × Nat × Nat × Nat → Bld (Array Nat)} {out : Array Val}
    (hcs : ColsOf A cs) (hL : regsOf cs = pure L)
    (hx : L.mapM (fun i => rs[i]?) = some x.regVals) (hn : rs[n]? = some (.size nv)) (hks : x.cols = .ok ks)
    (hN : nv.toNat ≤ 2 ^ 63) (ha : kasc nv ks = .ok (vs, p)) (hk : kseen nv ((ks.map (·.1)).zip vs) = .ok (k, g, f))
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok z)
    (hsc : kscan .max false .i64 .i64 nv (some z) [(nv, z), (nv, g)] [] [] = .ok r) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (ys : Array Val) (a b c d : Nat), (∃ e, fg2.1 = fg.1 ++ e) →
      fg2.2 = fg.2 → Ordered fg2.1 → [a, b, c, d].mapM (fun i => (rs ++ ys)[i]?) =
        some [.size k.toUSize, Reg.put g, Reg.put f, Reg.put p] → ∃ fg', Builds abiOf fg2 fg' (kk (a, b, c, d)) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (ascSeenB n cs >>= kk) rs out := by
  obtain rfl : L = Cols.regs cs := pure_inj (hL.symm.trans (regsOf_eq cs))
  obtain ⟨L0, hL0, hlx⟩ := regsOf_of_colsOf A hcs
  obtain rfl : L0 = Cols.regs cs := pure_inj (hL0.symm.trans (regsOf_eq cs))
  let pv : Array Val := (Val.size nv :: x.regVals).toArray
  let ps := List.range' (rs.size + 1) (Cols.regs cs).length
  obtain ⟨cs', hw, hcs', hr', hl'⟩ := withRegs_colsOf A hcs ps [] (by simp [ps])
  rw [List.append_nil] at hw
  have hpv : pv.size = (n :: Cols.regs cs).length := by simp [pv, hlx x]
  -- the parameters' registers in `rs ++ pv`: the count at `rs.size`, the columns `cs'` after it
  have hread := holds_of_reg (mapM_reg_range rs pv "")
  rw [hpv, List.length_cons, List.range'_succ] at hread
  obtain ⟨v0, vs0, hv0, hps, e0⟩ := omapM_cons.mp hread
  simp only [pv, List.cons.injEq] at e0
  obtain ⟨rfl, rfl⟩ := e0
  have hge : AllGe rs.size (Cols.regs cs') := fun a h => by
    rw [hr'] at h; simp only [ps, List.mem_range'] at h; omega
  obtain ⟨ctys, hcl⟩ := Typed.cloTys (fg := fg) (fg1 := fg) (k := (n :: Cols.regs cs).length) (rs := rs)
    (Typed.ascSeenBody cs' (Nat.le_refl _) hge)
  have hB := ascSeenOnB_builds (fg := fg) (rs := rs ++ pv) (n := rs.size) A hcs' (by rw [regsOf_eq, hr'])
    hps hv0 hks hN ha hk hz hsc
  let P : TabB → Prop := fun U => ∃ k g f p : Nat, U = ⟨k, [.atom "" .i64 g, .atom "" .i64 f, .atom "" .i64 p], []⟩
  have heq : ((do let (k, g, f, p) ← ascSeenB.ascSeenOnB rs.size cs'; Pure.pure (⟨k, [.atom "" .i64 g,
      .atom "" .i64 f, .atom "" .i64 p], []⟩ : TabB) : Bld TabB) >>= answerRegs P) =
      (do let (k', g', f', p') ← ascSeenB.ascSeenOnB rs.size cs'; Pure.pure #[k', g', f', p']) := by
    rw [bind_assoc]
    refine congrArg (_ >>= ·) (funext fun t => ?_)
    obtain ⟨k1, g1, f1, p1⟩ := t
    simp only [pure_bind]
    unfold answerRegs
    rw [if_pos ⟨k1, g1, f1, p1, rfl⟩, tabsRegs_eq]
    simp [TabB.regs, Cols.regs, Col.regs]
  unfold ascSeenB
  rw [bind_assoc]
  refine funV_builds (P := P) (fg1 := fg) (Us := []) (T := ⟨rs.size, cs', []⟩) (pv := pv)
    (o := #[.size k.toUSize, Reg.put g, Reg.put f, Reg.put p]) (ctys := ctys)
    (by rw [tabsRegs_eq]; simp [TabB.regs]) (fun _ => reads_of (by rw [List.mapM_cons, hn, hx]; rfl)) ?_
    (by rw [← heq] at hB; exact hB.2.2 #[]) hfo
    (fun _ _ _ => (Grows.ascSeenOnB _ _).bind fun _ => Grows.pure _)
    (fun U body xs R rtys h _ hR hy is => hcl U body _ R rtys h hR hy is) ?_
  · rw [List.length_cons, List.range'_succ]
    simp only [tabsAt, List.foldlM_cons, List.foldlM_nil, List.append_nil]
    rw [hw]
    simp [← hl']
  · rintro U ⟨k0, g0, f0, p0, rfl⟩ fg2 R' V ys he hf ho hR hV
    have hsz := mapM_ok_size (hR "")
    rcases R' with ⟨_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;> simp at hsz
    have hV0 : tabsAt [⟨k0, [.atom "" .i64 g0, .atom "" .i64 f0, .atom "" .i64 p0], []⟩] [a, b, c, d] =
        Pure.pure ([⟨a, [.atom "" .i64 b, .atom "" .i64 c, .atom "" .i64 d], []⟩], []) := by
      first | rfl | with_unfolding_all rfl
    have := pure_inj (hV.symm.trans hV0)
    simp only [Prod.mk.injEq, List.cons.injEq, and_true] at this
    subst this
    simp only [pure_bind]
    exact hkk fg2 ys a b c d he hf ho (holds_of_reg (hR ""))

/-! ### `gatherCols_builds`: columns of one shape, and a product side gathered -/

mutual
theorem Col.size_shape : ∀ c : Col, Col.size (Col.shape c) = Col.size c
  | .atom .. => rfl
  | .arr _ _ _ _ f => by simp only [Col.shape, Col.size, Col.sizes_shape f]
  | .sum _ _ x y => by simp only [Col.shape, Col.size, Col.sizes_shape x, Col.sizes_shape y]
theorem Col.sizes_shape : ∀ cs : Cols, Col.sizes (Cols.shape cs) = Col.sizes cs
  | [] => rfl
  | c :: cs => by simp only [Cols.shape, Col.sizes, Col.size_shape c, Col.sizes_shape cs]
end

/-- Columns of one shape are of one size: the guard `gatherCols` puts on the column `funC` hands back holds. -/
theorem Col.size_of_shape {c c' : Col} (h : Col.shape c' = Col.shape c) : Col.size c' = Col.size c := by
  rw [← Col.size_shape c', h, Col.size_shape]

/-- `gatherCols` gathers each column on its own (`attach` serves only its termination): a product side's columns are
    its two sides' gathered one after the other. -/
theorem gatherCols_append (m ix n : Nat) (xs ys : Cols) : gatherCols m ix n (xs ++ ys) =
    (do let a ← gatherCols m ix n xs; let b ← gatherCols m ix n ys; Pure.pure (a ++ b)) := by
  unfold gatherCols
  rw [List.mapM_subtype (g := fun c => _) (fun _ _ => rfl), List.mapM_subtype (g := fun c => _) (fun _ _ => rfl),
    List.mapM_subtype (g := fun c => _) (fun _ _ => rfl), List.unattach_attach, List.unattach_attach,
    List.unattach_attach, List.mapM_append]

end Rel.Lang.Plan
