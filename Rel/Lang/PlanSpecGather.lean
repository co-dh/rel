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

/-- Every `Enc` is a register that reads back as itself (`foR` its parts, `pos` none). -/
theorem enc_get_put : ∀ e : Enc, (Reg.get? (Reg.put e) : Option Enc) = some e
  | .foR m p => foR_get_put m p
  | .pos => by
    have hp : (Reg.put (Enc.pos : Enc) : Val) = .ctor (Enc.pos : Enc).ctorIdx #[] #[] := by with_unfolding_all rfl
    rw [hp]
    dsimp only [Reg.get?]
    conv => lhs; whnf
    rw [Array.mapM_eq_mapM_toList]
    simp

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

theorem qtype_get_put (t : QAtomicType) : (Reg.get? (Reg.put t) : Option QAtomicType) = some t := by
  cases t <;> rfl

theorem ascKey_get (v : Val) : (Reg.get? v : Option AscKey) = ascGet? v := rfl

theorem ascGet?_atom (t : QAtomicType) : (Reg.get? (Val.ctor 0 #[] #[Reg.put t]) : Option AscKey) = some (.atom t) := by
  rw [ascKey_get, ascGet?.eq_def]
  simp [qtype_get_put]

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

end Rel.Lang.Plan
