module

public import Rel.Lang.PlanSpecCat

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `concatB` builds what `ValsB.concat` answers

`ValsB.concat`'s kernels as the calls the builders make: `ColB.concat` is one `kscan .first` stream at either ownership
(`ColB.concat_kscan`), `ColB.shift` one `kscan` with the post step `(.add, s)` (`ColB.shift_kscan`): `.max`
at both ownerships, `Arr.shift`'s `.first` being the same call on a null-free column (`kscan_max_first`). -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- `Arr.concat` is `Opt.concat`'s `kscan .first` stream of the two columns (`Opt.ofArr` keeps the `Enc`). -/
theorem Arr.concat_kscan {t : QAtomicType} {n₁ n₂ n : USize} {x : Arr t n₁} {y : Arr t n₂} {z : Arr t n}
    (h : Arr.concat n x y = .ok z) :
    ∃ f, kscan .first false t t n none [(n₁, x.enc), (n₂, y.enc)] [] [] = .ok (z.enc, f) := by
  unfold Arr.concat at h
  obtain ⟨w, hz, h⟩ := except_bind_ok h
  obtain ⟨f, hf⟩ := Opt.concat_kscan hz
  have hx : Arr.enc x = (Opt.ofArr x).enc := rfl
  have hy : Arr.enc y = (Opt.ofArr y).enc := rfl
  have hw : z.enc = w.enc := by
    split at h
    · injection h with h; rw [← h]; rfl
    · cases h
  exact ⟨f, by rw [hx, hy, hw]; exact hf⟩

/-- `ColB.concat` is the one `kscan .first` stream of the two columns' `Enc`s, at either ownership. -/
theorem ColB.concat_kscan : ∀ {o : Bool} {t : QAtomicType} {n₁ n₂ n : USize} {x : ColB o t n₁} {y : ColB o t n₂}
    {z : ColB o t n}, ColB.concat n x y = .ok z →
    ∃ f, kscan .first false t t n none [(n₁, ColB.enc x), (n₂, ColB.enc y)] [] [] = .ok (ColB.enc z, f)
  | false, _, _, _, _, _, _, _, h => Arr.concat_kscan h
  | true, _, _, _, _, _, _, _, h => Opt.concat_kscan h

theorem Except.ok_bind' {α β : Type} (a : α) (f : α → Except String β) : (Except.ok a >>= f) = f a := rfl

/-- Two copies of one null-free column: `max` and `first` read the same columns (`first` stays a stream only at no post step). -/
theorem kscanCols_max_first {n : USize} {e : Enc} (hN : hasNul e = false) {s : QAtomicType}
    {pre post : List (Kernel.Op × UInt64)} (hp : post.isEmpty = false) :
    kscanCols .max s n [(n, e), (n, e)] pre post = kscanCols .first s n [(n, e), (n, e)] pre post := by
  unfold kscanCols
  simp [kscanStream, hp, nulFillOf, Kernel.Op.nulFold, hN]

theorem foldlM_congr_mem {α β : Type} (f g : β → α → Except String β) (l : List α) (b : β)
    (h : ∀ a ∈ l, ∀ b, f b a = g b a) : l.foldlM f b = l.foldlM g b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldlM_cons]
    rw [h a (by simp) b]
    cases g b a with
    | error _ => rfl
    | ok b' => exact ih b' fun a ha => h a (List.mem_cons_of_mem _ ha)

/-- **`max` of a column with itself is `first`**: at a column holding no null (`hasNul e = false`, as every `Arr`) and a
    post step, `kscan .max` and `kscan .first` of `[(n, e), (n, e)]` agree: a segment-per-row carry equals its folded
    column, `max w w = w = first w w`, and nothing else reads the op. -/
theorem kscan_max_first {n : USize} {e : Enc} (hN : hasNul e = false) {s t : QAtomicType}
    {pre post : List (Kernel.Op × UInt64)} (hp : post.isEmpty = false) :
    kscan .max false s t n none [(n, e), (n, e)] pre post = kscan .first false s t n none [(n, e), (n, e)] pre post := by
  have hr : kscanRefuses .max n [(n, e), (n, e)] pre post = kscanRefuses .first n [(n, e), (n, e)] pre post := by
    simp [kscanRefuses, Kernel.Op.readsDivisor]
  unfold kscan
  rw [hr, kscanCols_max_first hN hp]
  have hc : kscanCols .first s n [(n, e), (n, e)] pre post =
      (rawAll s n e >>= chainAll pre).bind fun w =>
        (rawAll s n e >>= chainAll pre).bind fun w' => .ok ([w, w'], []) := by
    unfold kscanCols
    have hpn : post ≠ [] := by rintro rfl; simp at hp
    rcases hr : rawAll s n e with _ | w0
    · simp [kscanStream, hpn, hr, bind, Except.bind] <;> rfl
    · rcases hc : chainAll pre w0 with _ | w1 <;>
        simp [kscanStream, hpn, nulFillOf, Kernel.Op.nulFold, hN, noNul, hr, hc, bind, Except.bind] <;> rfl
  rw [hc]
  cases hw : (rawAll s n e >>= chainAll pre) with
  | error _ => rfl
  | ok w =>
    simp only [Except.ok_bind', Except.bind, segAll, Bool.false_eq_true, if_false, List.map_cons, List.map_nil, List.drop_nil,
      List.map_id']
    have hrow : ∀ i ∈ List.range n.toNat, ∀ out, kscanRow .max (Array.replicate n.toNat 1) w [w] out i =
        kscanRow .first (Array.replicate n.toNat 1) w [w] out i := by
      intro i hi out
      have := List.mem_range.1 hi
      simp [kscanRow, Kernel.Op.eval, this, List.foldlM]
    have hnl : ∀ (a b : Kernel.Op) (g : Array UInt64) (sd : Array UInt64), List.foldlM (kscanRow a g sd []) #[] (List.range n.toNat) =
        List.foldlM (kscanRow b g sd []) #[] (List.range n.toNat) :=
      fun a b g sd => foldlM_congr_mem _ _ _ _ fun i _ out => by simp [kscanRow, List.foldlM]
    rw [foldlM_congr_mem _ _ _ _ hrow, hnl _ .first]
    simp only [Kernel.Op.nulFold, Option.elim]

/-- `Arr.shift` is `kscan .max` of the column with itself and the post step `(.add, s)` (`kscan_max_first` from the
    `.first` that `colArr` calls). -/
theorem Arr.shift_kscan {n : USize} {s : UInt64} {x z : Arr .i64 n} (h : Arr.shift s x = .ok z) :
    ∃ f, kscan .max false .i64 .i64 n none [(n, x.enc), (n, x.enc)] [] [(.add, s)] = .ok (z.enc, f) := by
  have hm := colArr_ok h
  unfold colMap at hm
  rw [← kscan_max_first x.plain (pre := []) (post := [(.add, s)]) rfl] at hm
  cases hk : kscan .max false .i64 .i64 n none [(n, x.enc), (n, x.enc)] [] [(.add, s)] with
  | error e => rw [hk] at hm; cases hm
  | ok r => rw [hk] at hm; injection hm with hm; exact ⟨r.2, by rw [← hm]⟩

/-- `ColB.shift` is one `kscan .max` of the column with itself and the post step `(.add, s)`, at either ownership. -/
theorem ColB.shift_kscan {o : Bool} {n : USize} {s : UInt64} {x z : ColB o .i64 n} (h : ColB.shift s x = .ok z) :
    ∃ f, kscan .max false .i64 .i64 n none [(n, ColB.enc x), (n, ColB.enc x)] []
      [(.add, s)] = .ok (ColB.enc z, f) := by
  cases o
  · exact Arr.shift_kscan h
  · exact Opt.shift_kscan h

/-! ### `Grows` -/

theorem Grows.guard (c : Nat) (msg : String) (as : Array Nat) : Grows (Plan.guard c msg as) := by
  unfold Plan.guard discard
  exact Grows.bind (Grows.ite (Grows.pure _) ((Grows.bind (Grows.emit rfl _) fun _ => Grows.pure _).bind
    fun _ => Grows.pure _)) fun _ => Grows.pure _

-- reducible only: a leaf `concatB` (well-founded) must not be unfolded by a failing `exact`
local macro "growsC" : tactic => `(tactic| repeat' first
  | with_reducible exact Grows.pure _ | with_reducible exact Grows.throw _
  | (with_reducible refine Grows.bind ?_ (fun _ => ?_))
  | with_reducible exact Grows.lit _ | with_reducible exact Grows.call1 _ _
  | with_reducible exact Grows.catColB _ _ _ _ _ _ | with_reducible exact Grows.catB _ _
  | with_reducible exact Grows.shiftB _ _ _ | with_reducible exact Grows.guard _ _ _
  | (unfold Plan.sumB; exact Grows.throw _) | (exact Grows.throw (α := Col) _) | dsimp only | split)

/-- `concatColB` of a column of at most `k` nodes grows, given `concatB` of fewer than `k` does. -/
theorem Grows.concatColB_of {k : Nat}
    (ih : ∀ n n₁ n₂ off xs ys, Col.sizes xs < k → Grows (Plan.concatB n n₁ n₂ off xs ys)) :
    ∀ (n n₁ n₂ off : Nat) (x y : Col), x.size ≤ k → Grows (Plan.concatColB n n₁ n₂ off x y) := by
  intro n n₁ n₂ off x y hx
  cases x <;> cases y <;> simp only [Plan.concatColB] <;> (try simp only [Col.size] at hx) <;> growsC
  all_goals first | exact ih _ _ _ _ _ _ (by omega) | skip

/-- Induction on `Col.sizes`, the measure `concatB` terminates by. -/
theorem Grows.concatB : ∀ (k n n₁ n₂ off : Nat) (xs ys : Cols), Col.sizes xs < k →
    Grows (Plan.concatB n n₁ n₂ off xs ys)
  | 0, _, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, n₁, n₂, off, xs, ys, h => by
    unfold Plan.concatB
    refine Grows.mapM (fun ⟨⟨x, y⟩, hxy⟩ => Grows.funC fun zs => ?_) _
    have hm := Col.size_le_of_mem (List.of_mem_zip hxy).1
    split
    · split
      · rename_i hle
        exact (Grows.concatColB_of (fun _ _ _ _ _ _ h' => Grows.concatB k _ _ _ _ _ _ h') _ _ _ _ _ _ (by omega)).bind
          fun _ => Grows.pure _
      · exact Grows.throw _
    · exact Grows.throw _

/-! ### `funC` of two columns -/

/-- The one-column table `⟨n, [c], []⟩` read back from consecutive registers from `s`: a column of `c`'s shape, its
    count at `s` and its registers after. -/
theorem tabsAt_col (n : Nat) (c : Col) (s : Nat) (rest : List Nat) : ∃ c',
    tabsAt [(⟨n, [c], []⟩ : TabB)] (List.range' s ((Col.regs c).length + 1) ++ rest) = Pure.pure ([⟨s, [c'], []⟩], rest) ∧
      Col.shape c' = Col.shape c ∧ Col.regs c' = List.range' (s + 1) (Col.regs c).length := by
  obtain ⟨A', Y, t1, -, -, t4⟩ := tab_spec (⟨n, [c], []⟩ : TabB)
  have hA1 : tabsRegs [(⟨n, [c], []⟩ : TabB)] = Pure.pure (n :: Col.regs c) := by
    rw [tabsRegs_eq]; simp [TabB.regs, Cols.regs]
  obtain rfl := pure_inj (t1.symm.trans hA1)
  obtain ⟨V0, v1, v2, -, v4, v5⟩ := t4 (List.range' s ((Col.regs c).length + 1)) rest (by simp)
  obtain ⟨n0, key, val⟩ := V0
  simp only [Cols.shape] at v4 v5
  obtain rfl : val = [] := by cases val <;> simp_all [Cols.shape]
  obtain ⟨c', rfl, hc'⟩ := Cols.shape_singleton v4
  rw [tabsRegs_eq] at v2
  have v2' := pure_inj v2
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TabB.regs, Cols.regs, List.range'_succ,
    List.cons.injEq] at v2'
  obtain ⟨rfl, hr'⟩ := v2'
  exact ⟨c', v1, hc', by simpa [Cols.regs] using hr'⟩

/-- **`funC` of two columns builds**: `funC_builds` at the two tables `⟨n₁, [c₁], []⟩`, `⟨n₂, [c₂], []⟩`. The body
    reads columns `c₁'`, `c₂'` of `c₁`'s and `c₂`'s shapes in the parameter registers after `rs` (`c₁'`'s count at
    `rs.size`, `c₂'`'s after `c₁'`'s registers) and answers a count and a column of `c₁`'s shape, its registers holding
    `o`; `kk` continues as in `funC_builds`. -/
theorem funC2_builds {abi : String → Option Kernel} {fg : Array Fun × Array Fun} {n₁ n₂ : Nat} {c₁ c₂ : Col}
    {b : List (Nat × Col) → Bld (Nat × Col)} {kk : Col → Bld (Array Nat)} {rs pv o out : Array Val}
    (ha : ∀ who, ((n₁ :: Col.regs c₁) ++ (n₂ :: Col.regs c₂)).toArray.mapM (reg rs who) = .ok pv)
    (ho : o.size = (Col.regs c₁).length + 1)
    (hB : ∀ c₁' c₂', Col.shape c₁' = Col.shape c₁ → Col.shape c₂' = Col.shape c₂ →
      Col.regs c₁' = List.range' (rs.size + 1) (Col.regs c₁).length →
      Col.regs c₂' = List.range' (rs.size + (Col.regs c₁).length + 1 + 1) (Col.regs c₂).length →
      ∃ fg1, Builds abi fg fg1 ((b [(rs.size, c₁'), (rs.size + (Col.regs c₁).length + 1, c₂')] >>=
        fun p => Pure.pure (⟨p.1, [p.2], []⟩ : TabB)) >>=
        answerRegs fun U => U.val = [] ∧ ∃ d, U.key = [d] ∧ Col.shape d = Col.shape c₁) (rs ++ pv) o)
    (hT : ∀ c₁' c₂', Col.shape c₁' = Col.shape c₁ → Col.shape c₂' = Col.shape c₂ →
      Col.regs c₁' = List.range' (rs.size + 1) (Col.regs c₁).length →
      Col.regs c₂' = List.range' (rs.size + (Col.regs c₁).length + 1 + 1) (Col.regs c₂).length →
      Typed rs.size (fun _ => True) (b [(rs.size, c₁'), (rs.size + (Col.regs c₁).length + 1, c₂')]))
    (hb : ∀ ys, Grows (b ys)) (hfo : Ordered fg.1)
    (hk : ∀ (fg2 : Array Fun × Array Fun) (d : Col) (r0 : Nat) (ys : Array Val), (∃ a, fg2.1 = fg.1 ++ a) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Col.shape d = Col.shape c₁ →
      (r0 :: Col.regs d).mapM (fun i => (rs ++ ys)[i]?) = some o.toList → ∃ fg', Builds abi fg2 fg' (kk d) (rs ++ ys) out) :
    ∃ fg', Builds abi fg fg' (funC [(n₁, c₁), (n₂, c₂)] b >>= kk) rs out := by
  have hA : tabsRegs [(⟨n₁, [c₁], []⟩ : TabB), ⟨n₂, [c₂], []⟩] =
      Pure.pure ((n₁ :: Col.regs c₁) ++ (n₂ :: Col.regs c₂)) := by
    rw [tabsRegs_eq]; simp [TabB.regs, Cols.regs]
  obtain ⟨c₁', e1, hs1, hr1⟩ := tabsAt_col n₁ c₁ rs.size
    (List.range' (rs.size + (Col.regs c₁).length + 1) ((Col.regs c₂).length + 1))
  obtain ⟨c₂', e2, hs2, hr2⟩ := tabsAt_col n₂ c₂ (rs.size + (Col.regs c₁).length + 1) []
  have hUs : tabsAt [(⟨n₁, [c₁], []⟩ : TabB), ⟨n₂, [c₂], []⟩]
      (List.range' rs.size ((n₁ :: Col.regs c₁) ++ (n₂ :: Col.regs c₂)).length) =
      Pure.pure ([⟨rs.size, [c₁'], []⟩, ⟨rs.size + (Col.regs c₁).length + 1, [c₂'], []⟩], []) := by
    have hsplit : List.range' rs.size ((n₁ :: Col.regs c₁) ++ (n₂ :: Col.regs c₂)).length =
        List.range' rs.size ((Col.regs c₁).length + 1) ++
          List.range' (rs.size + (Col.regs c₁).length + 1) ((Col.regs c₂).length + 1) := by
      rw [Nat.add_assoc, List.range'_append_1]
      congr 1; simp; omega
    rw [List.append_nil] at e2
    rw [hsplit, show [(⟨n₁, [c₁], []⟩ : TabB), ⟨n₂, [c₂], []⟩] = [⟨n₁, [c₁], []⟩] ++ [⟨n₂, [c₂], []⟩] from rfl,
      tabsAt_append, e1]
    simp only [pure_bind]; rw [e2]; rfl
  let P : TabB → Prop := fun U => U.val = [] ∧ ∃ d, U.key = [d] ∧ Col.shape d = Col.shape c₁
  let b' : List TabB → Bld TabB := fun Ts => do
    let (m, c) ← b (← Ts.mapM fun T => match T.key with
      | [c] => Pure.pure (T.n, c)
      | _ => throw "a column function: not one column")
    Pure.pure ⟨m, [c], []⟩
  have hb' : b' [⟨rs.size, [c₁'], []⟩, ⟨rs.size + (Col.regs c₁).length + 1, [c₂'], []⟩] =
      (b [(rs.size, c₁'), (rs.size + (Col.regs c₁).length + 1, c₂')] >>=
        fun p => Pure.pure (⟨p.1, [p.2], []⟩ : TabB)) := by
    simp only [b', List.mapM_cons, List.mapM_nil, pure_bind]
  obtain ⟨fg1, ⟨a1, ha1⟩, hb1, hB1⟩ := hB c₁' c₂' hs1 hs2 hr1 hr2
  have hTy : Typed rs.size (fun _ => True)
      (b' [⟨rs.size, [c₁'], []⟩, ⟨rs.size + (Col.regs c₁).length + 1, [c₂'], []⟩]) := by
    rw [hb']; exact (hT c₁' c₂' hs1 hs2 hr1 hr2).bind fun _ _ => Typed.pure trivial
  obtain ⟨ctys, hcl⟩ := Typed.cloTys (fg := fg) (fg1 := fg1)
    (k := ((n₁ :: Col.regs c₁) ++ (n₂ :: Col.regs c₂)).length) hTy
  unfold Plan.funC
  simp only [bind_assoc]
  refine funT_builds (P := P) (b := b')
    (Us := [⟨rs.size, [c₁'], []⟩, ⟨rs.size + (Col.regs c₁).length + 1, [c₂'], []⟩]) (ctys := ctys) hA ha hUs
    (by rw [hb']; exact hB1 #[]) hfo ?_
    (fun U body xs R rtys h _ hR hy is => hcl U body _ R rtys h hR hy is) ?_
  · exact fun Ts => (Grows.mapM (fun T => by split <;> first | exact Grows.pure _ | exact Grows.throw _) _).bind
      fun l => (hb l).bind fun p => by obtain ⟨_, _⟩ := p; exact Grows.pure _
  · rintro U ⟨hv, d, hd, hdc⟩ fg2 R' V ys he hf ho' hR hV
    obtain ⟨un, ukey, uval⟩ := U
    simp only at hv hd
    subst hv hd
    obtain ⟨AU, YU, u1, -, -, u4⟩ := tab_spec (⟨un, [d], []⟩ : TabB)
    rw [tabsRegs_eq] at u1
    obtain rfl := (pure_inj u1).symm
    have hl : R'.toList.length = (un :: Col.regs d).length := by
      have h1 := mapM_ok_size (hR "")
      have h2 : (Col.regs d).length = (Col.regs c₁).length := by rw [← Col.regs_shape d, hdc, Col.regs_shape]
      simp only [Array.length_toList, List.length_cons, h2]; omega
    obtain ⟨V', f1, f2, -, f4, f5⟩ := u4 R'.toList [] (by simpa [TabB.regs, Cols.regs] using hl)
    rw [List.append_nil] at f1
    obtain rfl : V = V' := by
      have := pure_inj (hV.symm.trans f1); simp only [Prod.mk.injEq, List.cons.injEq, and_true] at this; exact this
    obtain ⟨vn, vkey, vval⟩ := V
    simp only [Cols.shape] at f4 f5
    obtain rfl : vval = [] := by cases vval <;> simp_all [Cols.shape]
    obtain ⟨d', rfl, hd'⟩ := Cols.shape_singleton f4
    rw [tabsRegs_eq] at f2
    have f2' := pure_inj f2
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TabB.regs, Cols.regs] at f2'
    have hread := holds_of_reg (hR "")
    rw [← f2'] at hread
    simp only [pure_bind]
    obtain ⟨e2, he2⟩ := he
    exact hk fg2 d' vn ys ⟨a1 ++ e2, by rw [he2, ha1, Array.append_assoc]⟩ (by rw [hf]; exact hb1) ho'
      (hd'.trans hdc) hread

/-! ### `Typed`: `n` is read only as `kscan`'s declared row count, so a captured register is typed -/

/-- `Plan.callK` whose every argument below `m` the kernel's declaration types (`Typed.call1Of` for a multi-result kernel). -/
theorem Typed.callKOf {m : Nat} {k : Kernel} {args : Array Nat}
    (h : ∀ fs, ∀ a ∈ args, a < m → ∃ t, useTy fs a (.call k.sym args) = some t) :
    Typed m (fun r => ∀ a ∈ r, m ≤ a) (Plan.callK k args) :=
  Typed.emit (fun fs a ha hlt => h fs a (by simpa [reads] using ha) hlt) _

/-- `kscan` declares all nine arguments, so every register of a nine-argument call is typed. -/
theorem useTy_kscan (fs : Array Fun) (args : Array Nat) (hl : args.size = 9) (a : Nat) (ha : a ∈ args) :
    ∃ t, useTy fs a (.call (kernel% Rel.Kernel.kscan).sym args) = some t := by
  obtain ⟨j, hj, hjl⟩ := idxOf?_of_mem (l := args.toList) (by simpa using ha)
  simp only [Array.length_toList, hl] at hjl
  simp only [useTy, hj, Option.bind_some]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | exact absurd hjl (by omega) | exact ⟨_, by with_unfolding_all rfl⟩

/-- `Typed.catColB` with no bound on the row count `n`: it is only `kscan`'s declared `n`, typed wherever it lives. -/
theorem Typed.catColBOf {m : Nat} {t : QAtomicType} {n n₁ n₂ x y : Nat} (h1 : m ≤ n₁) (h2 : m ≤ n₂)
    (hx : m ≤ x) (hy : m ≤ y) : Typed m (fun r => m ≤ r) (Plan.catColB t n n₁ n₂ x y) := by
  unfold Plan.catColB
  refine (Typed.lit _).bind fun c0 h0 => (Typed.lit _).bind fun c1 h1' => (Typed.lit _).bind fun c2 h2' =>
    (Typed.lit _).bind fun c3 h3 => (Typed.ctorB (by simp) (by simp) 0).bind fun g hg =>
    (Typed.srcB h1 hx).bind fun x' hx' => (Typed.srcB h2 hy).bind fun y' hy' =>
    (Typed.listB (rs := [x', y']) (by intro a ha; simp at ha; omega)).bind fun l hl =>
    (Typed.lit _).bind fun c4 h4 => (Typed.lit _).bind fun c5 h5 =>
    (Typed.callKOf fun fs a ha _ => useTy_kscan fs _ rfl a ha).bind fun o ho => Typed.nth ho 0 "kscan"

theorem Typed.guard {m : Nat} {c : Nat} {msg : String} {as : Array Nat} (hc : m ≤ c) (has : ∀ a ∈ as, m ≤ a) :
    Typed m (fun _ : Unit => True) (Plan.guard c msg as) := by
  unfold Plan.guard discard
  exact (Typed.ite hc (Typed.pure fun _ h => by simp at h)
    ((Typed.emitGe (i := .fail msg as) (by simpa [reads] using has) 0).bind fun _ _ => Typed.pure fun _ h => by simp at h)).bind
    fun _ _ => Typed.pure trivial

/-- `concatColB` of columns of at most `k` nodes, given `concatB` of fewer than `k`: the row count `n` is a register above
    `m` or captured (of `S`), every register it answers is too. -/
theorem Typed.concatColB_of {m : Nat} {S : List Nat} {k : Nat}
    (ih : ∀ n n₁ n₂ off xs ys, Col.sizes xs < k → (m ≤ n ∨ n ∈ S) → m ≤ n₁ → m ≤ n₂ → AllGe m (Cols.regs xs) →
      AllGe m (Cols.regs ys) → Typed m (fun r => ∀ a ∈ Cols.regs r, m ≤ a ∨ a ∈ S) (Plan.concatB n n₁ n₂ off xs ys)) :
    ∀ (n n₁ n₂ off : Nat) (x y : Col), x.size ≤ k → (m ≤ n ∨ n ∈ S) → m ≤ n₁ → m ≤ n₂ → AllGe m (Col.regs x) →
      AllGe m (Col.regs y) → Typed m (fun c => ∀ a ∈ Col.regs c, m ≤ a ∨ a ∈ S) (Plan.concatColB n n₁ n₂ off x y) := by
  intro n n₁ n₂ off x y hk hn h1 h2 hx hy
  rcases x with ⟨p, t, e⟩ | ⟨p, m₁, lo₁, hi₁, f₁⟩ | ⟨p, tg₁, x₁, y₁⟩ <;>
    rcases y with ⟨q, u, e'⟩ | ⟨q, m₂, lo₂, hi₂, f₂⟩ | ⟨q, tg₂, x₂, y₂⟩ <;> simp only [Plan.concatColB]
  · exact (Typed.catColBOf h1 h2 (hx _ (by simp [Col.regs])) (hy _ (by simp [Col.regs]))).bind fun r hr =>
      Typed.pure fun a ha => by simp [Col.regs] at ha; exact .inl (ha ▸ hr)
  · first | exact Typed.throw _ | (simp only [Plan.sumB]; exact Typed.throw _)
  · first | exact Typed.throw _ | (simp only [Plan.sumB]; exact Typed.throw _)
  · first | exact Typed.throw _ | (simp only [Plan.sumB]; exact Typed.throw _)
  · have hm₁ : m ≤ m₁ := hx _ (by simp [Col.regs])
    have hm₂ : m ≤ m₂ := hy _ (by simp [Col.regs])
    have hl₁ : m ≤ lo₁ := hx _ (by simp [Col.regs])
    have hl₂ : m ≤ lo₂ := hy _ (by simp [Col.regs])
    have hh₁ : m ≤ hi₁ := hx _ (by simp [Col.regs])
    have hh₂ : m ≤ hi₂ := hy _ (by simp [Col.regs])
    have hf₁ : AllGe m (Cols.regs f₁) := fun a ha => hx a (by simp [Col.regs, ha])
    have hf₂ : AllGe m (Cols.regs f₂) := fun a ha => hy a (by simp [Col.regs, ha])
    simp only [Col.size] at hk
    refine (Typed.catB hm₁ hm₂).bind fun ⟨m', o⟩ ho => (Typed.lit _).bind fun l hl =>
      (Typed.call1 (by simp; omega)).bind fun c hc => (Typed.guard hc (by simp; omega)).bind fun _ _ => ?_
    dsimp only
    have hb : ∀ x₁ x₂, m ≤ x₁ → m ≤ x₂ → Typed m (fun r => m ≤ r)
        (do let s ← Plan.shiftB n₂ x₂ m₁; Plan.catColB QAtomicType.i64 n n₁ n₂ x₁ s) :=
      fun x₁ x₂ a b => (Typed.shiftB h2 b).bind fun s hs => Typed.catColBOf h1 h2 a hs
    refine (hb lo₁ lo₂ hl₁ hl₂).bind fun lo' hlo' => (hb hi₁ hi₂ hh₁ hh₂).bind fun hi' hhi' =>
      (ih m' m₁ m₂ o f₁ f₂ (by omega) (.inl ho.1) hm₁ hm₂ hf₁ hf₂).bind fun f' hf' => Typed.pure fun a ha => ?_
    simp only [Col.regs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with (rfl | rfl | rfl) | ha
    · exact .inl ho.1
    · exact .inl hlo'
    · exact .inl hhi'
    · exact hf' a ha
  · first | exact Typed.throw _ | (simp only [Plan.sumB]; exact Typed.throw _)
  · first | exact Typed.throw _ | (simp only [Plan.sumB]; exact Typed.throw _)
  · first | exact Typed.throw _ | (simp only [Plan.sumB]; exact Typed.throw _)
  · have ht₁ : m ≤ tg₁ := hx _ (by simp [Col.regs])
    have ht₂ : m ≤ tg₂ := hy _ (by simp [Col.regs])
    have hx₁ : AllGe m (Cols.regs x₁) := fun a ha => hx a (by simp [Col.regs, ha])
    have hy₁ : AllGe m (Cols.regs y₁) := fun a ha => hx a (by simp [Col.regs, ha])
    have hx₂ : AllGe m (Cols.regs x₂) := fun a ha => hy a (by simp [Col.regs, ha])
    have hy₂ : AllGe m (Cols.regs y₂) := fun a ha => hy a (by simp [Col.regs, ha])
    simp only [Col.size] at hk
    refine (Typed.catColBOf h1 h2 ht₁ ht₂).bind fun tg ht => (ih n n₁ n₂ off x₁ x₂ (by omega) hn h1 h2 hx₁ hx₂).bind
      fun X hX => (ih n n₁ n₂ off y₁ y₂ (by omega) hn h1 h2 hy₁ hy₂).bind fun Y hY => Typed.pure fun a ha => ?_
    simp only [Col.regs, List.mem_append, List.mem_singleton] at ha
    rcases ha with (rfl | ha) | ha
    · exact .inl ht
    · exact hX a ha
    · exact hY a ha

/-- **`concatB` types**: the row count `n` a register above `m` or captured (of `S`), the answer's registers are too
    (`Typed.gatherColsOf`'s shape; the pair counts `n₁ n₂` and `off` are only passed on). -/
theorem Typed.concatBOf {m : Nat} {S : List Nat} : ∀ (k n n₁ n₂ off : Nat) (xs ys : Cols), Col.sizes xs < k →
    (m ≤ n ∨ n ∈ S) → m ≤ n₁ → m ≤ n₂ → AllGe m (Cols.regs xs) → AllGe m (Cols.regs ys) →
    Typed m (fun r => ∀ a ∈ Cols.regs r, m ≤ a ∨ a ∈ S) (Plan.concatB n n₁ n₂ off xs ys)
  | 0, _, _, _, _, _, _, h, _, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, n, n₁, n₂, off, xs, ys, h, hn, h1, h2, hxs, hys => by
    unfold Plan.concatB
    refine (Typed.mapM fun ⟨⟨x, y⟩, hxy⟩ _ => ?_).mono fun bs hb => (Cols.regs_all bs).2 hb
    have hm := Col.size_le_of_mem (List.of_mem_zip hxy).1
    have hxc : AllGe m (Col.regs x) := ((Cols.regs_all xs).1 hxs) x (List.of_mem_zip hxy).1
    have hyc : AllGe m (Col.regs y) := ((Cols.regs_all ys).1 hys) y (List.of_mem_zip hxy).2
    refine Typed.funCOf (S := S) (fun p hp => ?_) fun zs hzs => ?_
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨h1, hxc⟩
      · exact ⟨h2, hyc⟩
    · rcases zs with _ | ⟨⟨n₁', x'⟩, _ | ⟨⟨n₂', y'⟩, _ | ⟨_, _⟩⟩⟩
      · exact Typed.throw _
      · exact Typed.throw _
      · have g1 := hzs (n₁', x') (by simp)
        have g2 := hzs (n₂', y') (by simp)
        refine Typed.dite (fun hle => ?_) fun _ => Typed.throw _
        exact (Typed.concatColB_of (fun _ _ _ _ _ _ h' => Typed.concatBOf k _ _ _ _ _ _ h') n n₁' n₂' off x' y'
          (by omega) hn g1.1 g2.1 g1.2 g2.2).bind fun c hc => Typed.pure ⟨hn, hc⟩
      · exact Typed.throw _

/-- `concatB` concatenates each column pair on its own (`attach` serves only its termination): a product side's columns
    are its two sides' concatenated one after the other. -/
theorem concatB_append (n n₁ n₂ off : Nat) {xs xs' ys ys' : Cols} (hl : xs.length = ys.length) :
    Plan.concatB n n₁ n₂ off (xs ++ xs') (ys ++ ys') =
      (do let a ← Plan.concatB n n₁ n₂ off xs ys; let b ← Plan.concatB n n₁ n₂ off xs' ys'; Pure.pure (a ++ b)) := by
  unfold Plan.concatB
  rw [List.mapM_subtype (g := fun c => _) (fun _ _ => rfl), List.mapM_subtype (g := fun c => _) (fun _ _ => rfl),
    List.mapM_subtype (g := fun c => _) (fun _ _ => rfl), List.unattach_attach, List.unattach_attach,
    List.unattach_attach, List.zip_append hl, List.mapM_append]

/-- The body `concatB` hands `funC` for one pair of columns, `x` the original of the first. -/
def concatBody (n off : Nat) (x : Col) : List (Nat × Col) → Bld (Nat × Col)
  | [(n₁, x'), (n₂, y')] =>
    if _h : x'.size ≤ x.size then return (n, ← concatColB n n₁ n₂ off x' y')
    else throw "concat: a column larger than the column it renames"
  | _ => throw "concat: not two columns"

theorem concatB_single (n n₁ n₂ off : Nat) (c d : Col) :
    Plan.concatB n n₁ n₂ off [c] [d] =
      (funC [(n₁, c), (n₂, d)] (concatBody n off c) >>= fun z => Pure.pure [z]) := by
  unfold Plan.concatB
  simp
  rfl

theorem concatBody_grows (n off : Nat) (c : Col) (ys : List (Nat × Col)) : Grows (concatBody n off c ys) := by
  unfold concatBody
  split
  · split
    · rename_i hle
      exact (Grows.concatColB_of (k := c.size) (fun _ _ _ _ _ _ h' => Grows.concatB c.size _ _ _ _ _ _ h') _ _ _ _ _ _
        hle).bind fun _ => Grows.pure _
    · exact Grows.throw _
  · exact Grows.throw _

/-- `funC2_builds` at the pair of columns `c`, `d` of two sides of `A` that `concatB` hands its body: the parameter
    registers after `rs` hold the counts `n1v`, `n2v` and `x`'s, `y`'s registers; `hB` is the body's `concatColB`, with
    any continuation `kc` that holds on the column `e` of `c`'s shape whose registers hold `z`'s (`z` the concatenation). -/
theorem concatCol_funC {A : Obj} {o : Bool} {nv n1v n2v : USize} {x : ValsB o A n1v} {y : ValsB o A n2v}
    {z : ValsB o A nv} {c d : Col} {fg : Array Fun × Array Fun} {rs : Array Val} {n n₁ n₂ off : Nat}
    {kk : Cols → Bld (Array Nat)} {out : Array Val}
    (hA : ColsOf A [c])
    (hx : (Col.regs c).mapM (fun i => rs[i]?) = some x.regVals)
    (hy : (Col.regs d).mapM (fun i => rs[i]?) = some y.regVals)
    (hn : rs[n]? = some (.size nv)) (h1 : rs[n₁]? = some (.size n1v)) (h2 : rs[n₂]? = some (.size n2v))
    (hfo : Ordered fg.1)
    (hB : ∀ (c' d' : Col) (a₁ a₂ : Nat) (rs' out' : Array Val) (kc : Col → Bld (Array Nat)),
       Col.shape c' = Col.shape c → Col.shape d' = Col.shape d → Extends rs rs' →
       rs'[a₁]? = some (.size n1v) → rs'[a₂]? = some (.size n2v) →
       (Col.regs c').mapM (fun i => rs'[i]?) = some x.regVals → (Col.regs d').mapM (fun i => rs'[i]?) = some y.regVals →
       (∀ (fg3 : Array Fun × Array Fun) (e : Col) (R : Array Val), Extends rs' R → Col.shape e = Col.shape c →
          (Col.regs e).mapM (fun i => R[i]?) = some z.regVals → Builds abiOf fg3 fg3 (kc e) R out') →
       ∃ fg', Builds abiOf fg fg' (concatColB n a₁ a₂ off c' d' >>= kc) rs' out')
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (cs' : Cols) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Cols.shape cs' = Cols.shape [c] →
      (Cols.regs cs').mapM (fun i => (rs ++ ys)[i]?) = some z.regVals → ∃ fg', Builds abiOf fg2 fg' (kk cs') (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (concatB n n₁ n₂ off [c] [d] >>= kk) rs out := by
  have hlx := mapM_get_length hx
  have hly := mapM_get_length hy
  have hlz : (Col.regs c).length = z.regVals.length := by simpa [Cols.regs] using ColsOf.regs_length hA z
  rw [concatB_single]
  simp only [bind_assoc, pure_bind]
  have hpa : (rs.push (Val.size n1v) ++ x.regVals.toArray).push (Val.size n2v) ++ y.regVals.toArray =
      rs ++ (Val.size n1v :: x.regVals ++ Val.size n2v :: y.regVals).toArray := by simp
  refine funC2_builds (pv := (Val.size n1v :: x.regVals ++ Val.size n2v :: y.regVals).toArray)
    (o := (Val.size nv :: z.regVals).toArray) (c₁ := c) (c₂ := d) (b := concatBody n off c) (kk := fun w => kk [w])
    (fun _ => reads_of (by rw [List.mapM_append, List.mapM_cons, List.mapM_cons, h1, hx, h2, hy]; rfl))
    (by simp [hlz]) ?_ ?_ (fun ys => concatBody_grows n off c ys) hfo ?_
  · intro c₁' c₂' hs1 hs2 hr1 hr2
    have hle := Nat.le_of_eq (Col.size_of_shape hs1)
    simp only [concatBody, dif_pos hle, bind_assoc, pure_bind]
    have e1 : (rs.push (Val.size n1v) ++ x.regVals.toArray) ++ (Val.size n2v :: y.regVals).toArray =
        rs ++ (Val.size n1v :: x.regVals ++ Val.size n2v :: y.regVals).toArray := by simp
    have g1 := mapM_range_append (rs.push (.size n1v)) x.regVals
    rw [Array.size_push, ← hlx, ← hr1] at g1
    have g2 := mapM_range_append ((rs.push (Val.size n1v) ++ x.regVals.toArray).push (Val.size n2v)) y.regVals
    rw [hpa] at g2
    have hsz : ((rs.push (Val.size n1v) ++ x.regVals.toArray).push (Val.size n2v)).size =
        rs.size + (Col.regs c).length + 1 + 1 := by simp [hlx]; omega
    rw [hsz, ← hly, ← hr2] at g2
    refine hB c₁' c₂' _ _ _ _ _ hs1 hs2 (fun h => get_app h) (by simp) ?_ (by rw [← e1]; exact mapM_get_app g1) g2 ?_
    · rw [← hpa, hlx]
      refine get_app ?_
      have h := Array.getElem?_push_size (xs := rs.push (Val.size n1v) ++ x.regVals.toArray) (x := Val.size n2v)
      simp only [Array.size_append, Array.size_push, List.size_toArray] at h
      rwa [show rs.size + 1 + x.regVals.length = rs.size + x.regVals.length + 1 by omega] at h
    · intro fg3 e R hext hse hr
      refine Builds.answerRegs ⟨rfl, e, rfl, hse⟩ (tabsRegs_eq _) fun _ => reads_of ?_
      simp only [List.flatMap_cons, List.flatMap_nil, TabB.regs, Cols.regs, List.append_nil]
      exact omapM_cons.mpr ⟨.size nv, z.regVals, hext (get_app hn), by simpa [Cols.regs] using hr, rfl⟩
  · intro c₁' c₂' hs1 hs2 hr1 hr2
    have hle := Nat.le_of_eq (Col.size_of_shape hs1)
    simp only [concatBody, dif_pos hle]
    refine (Typed.concatColB_of (S := [n]) (k := c.size) (m := rs.size)
      (fun _ _ _ _ _ _ h' => Typed.concatBOf c.size _ _ _ _ _ _ h') n _ _ off c₁' c₂' hle (.inr (List.mem_singleton_self _))
      (Nat.le_refl _) (by omega) ?_ ?_).bind fun _ _ => Typed.pure trivial
    · intro a ha; rw [hr1, List.mem_range'_1] at ha; omega
    · intro a ha; rw [hr2, List.mem_range'_1] at ha; omega
  · intro fg2 d' r0 ys he hf ho hs hrd
    obtain ⟨-, hd⟩ := mapM_get_cons (by simpa using hrd)
    exact hkk fg2 [d'] ys he hf ho (by simp [Cols.shape, hs]) (by simpa [Cols.regs] using hd)

/-- **`concatB` of one atom column pair builds** (an atom side, or a band sum's `Opt`): `catColB_builds` at the one
    `kscan .first` stream `ColB.concat_kscan` states, `kk` continuing on the column it answers. -/
theorem concatAtom_builds {A : Obj} {o : Bool} {nv n1v n2v : USize} {x : ValsB o A n1v} {y : ValsB o A n2v}
    {z : ValsB o A nv} {p q : String} {t : QAtomicType} {e e' : Nat} {ev ev' ov : Enc} {f : Option UInt64}
    {fg : Array Fun × Array Fun} {rs : Array Val} {n n₁ n₂ off : Nat} {kk : Cols → Bld (Array Nat)} {out : Array Val}
    (hA : ColsOf A [.atom p t e]) (hxv : x.regVals = [Reg.put ev]) (hyv : y.regVals = [Reg.put ev'])
    (hzv : z.regVals = [Reg.put ov])
    (hx : (Col.regs (.atom p t e)).mapM (fun i => rs[i]?) = some x.regVals)
    (hy : (Col.regs (.atom q t e')).mapM (fun i => rs[i]?) = some y.regVals)
    (hn : rs[n]? = some (.size nv)) (h1 : rs[n₁]? = some (.size n1v)) (h2 : rs[n₂]? = some (.size n2v))
    (hk : kscan .first false t t nv none [(n1v, ev), (n2v, ev')] [] [] = .ok (ov, f)) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (cs' : Cols) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Cols.shape cs' = Cols.shape [.atom p t e] →
      (Cols.regs cs').mapM (fun i => (rs ++ ys)[i]?) = some z.regVals → ∃ fg', Builds abiOf fg2 fg' (kk cs') (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (concatB n n₁ n₂ off [.atom p t e] [.atom q t e'] >>= kk) rs out := by
  refine concatCol_funC hA hx hy hn h1 h2 hfo ?_ hkk
  intro c' d' a₁ a₂ rs' out' kc hs hs' hext ha1 ha2 hr1 hr2 hkc
  cases c' <;> simp only [Col.shape, Col.atom.injEq, reduceCtorEq] at hs
  cases d' <;> simp only [Col.shape, Col.atom.injEq, reduceCtorEq] at hs'
  obtain ⟨rfl, rfl, -⟩ := hs
  rename_i e1 e2
  simp only [hxv, Col.regs] at hr1
  simp only [hyv, Col.regs] at hr2
  obtain ⟨hx1, -⟩ := mapM_get_cons hr1
  obtain ⟨hy1, -⟩ := mapM_get_cons hr2
  simp only [Plan.concatColB, bind_assoc, pure_bind]
  refine ⟨fg, Builds.bind1G (catColB_builds (hext hn) ha1 ha2 hx1 (enc_get_put _) hy1 (enc_get_put _) hk) fun r R hr hE => ?_⟩
  exact hkc _ _ R hE (by simp [Col.shape])
    (omapM_cons.mpr ⟨_, _, hr, rfl, by simp [hzv]⟩)


end Rel.Lang.Plan
