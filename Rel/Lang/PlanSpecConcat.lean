module

public import Rel.Lang.PlanSpecCat

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `concatB` builds what `ValsB.concat` answers

`ValsB.concat`'s kernels as the calls the builders make: `ColB.concat` is one `kscan .first` stream at either ownership
(`ColB.concat_kscan`), `ColB.shift` one `kscan` with the post step `(.add, s)` (`ColB.shift_kscan`), whose op is
`.first` on an owned column (`Arr.shift`) and `.max` on a nullable one (`Opt.shift`); `shiftB` calls `.max` at both. -/

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

/-- `Arr.shift` is `kscan .first` of the column with itself and the post step `(.add, s)`. -/
theorem Arr.shift_kscan {n : USize} {s : UInt64} {x z : Arr .i64 n} (h : Arr.shift s x = .ok z) :
    ∃ f, kscan .first false .i64 .i64 n none [(n, x.enc), (n, x.enc)] [] [(.add, s)] = .ok (z.enc, f) := by
  have hm := colArr_ok h
  unfold colMap at hm
  cases hk : kscan .first false .i64 .i64 n none [(n, x.enc), (n, x.enc)] [] [(.add, s)] with
  | error e => rw [hk] at hm; cases hm
  | ok r => rw [hk] at hm; injection hm with hm; exact ⟨r.2, by rw [← hm]⟩

/-- `ColB.shift` is one `kscan` of the column with itself and the post step `(.add, s)`: `.first` on an owned column,
    `.max` on a nullable one (where `.first` refuses a null row). -/
theorem ColB.shift_kscan {o : Bool} {n : USize} {s : UInt64} {x z : ColB o .i64 n} (h : ColB.shift s x = .ok z) :
    ∃ f, kscan (if o then .max else .first) false .i64 .i64 n none [(n, ColB.enc x), (n, ColB.enc x)] []
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
      (∃ a, fg2.2 = fg.2 ++ a) → Ordered fg2.1 → Col.shape d = Col.shape c₁ →
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
  obtain ⟨fg1, ⟨a1, ha1⟩, ⟨b1, hb1⟩, hB1⟩ := hB c₁' c₂' hs1 hs2 hr1 hr2
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
    exact hk fg2 d' vn ys ⟨a1 ++ e2, by rw [he2, ha1, Array.append_assoc]⟩ ⟨b1, by rw [hf, hb1]⟩ ho'
      (hd'.trans hdc) hread

end Rel.Lang.Plan
