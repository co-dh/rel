module

public import Rel.Lang.PlanSpecCat
public import Rel.Lang.GenKBits

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `noneB` means `Vals.none`, `zeroB` means `Tab.zero`, `repath` keeps the registers

`noneB z A` writes, for each atom column of a side of `A`, `mapB .add z c c t` of the zero words `c = wordsB z 0`: at
`z` holding `0` that is `colMap .add 0 c c t`, which is `Arr.zeros t 0` (and `Opt.nuls t 0`, `tagCol 0 false`) as the
column the kernels answer for no row (`none_enc`). `repath` has no spec counterpart: it renames the paths of a side's
columns for `Tab.pair`'s key rebracketing, so it keeps `ColsOf` and the registers (`repath_eq`). -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel Rel.Verify

/-- A one-register builder `b`, then `k` on its register in registers `rs ++ xs`. -/
theorem Builds.bind1 {abi : String → Option Kernel} {fg fg1 fg' : Array Fun × Array Fun} {b : Bld Nat}
    {k : Nat → Bld (Array Nat)} {rs out : Array Val} {o : Val}
    (hb : Builds abi fg fg1 (do let r ← b; Pure.pure #[r]) rs #[o])
    (hk : ∀ r xs, (rs ++ xs)[r]? = some o → Builds abi fg1 fg' (k r) (rs ++ xs) out) :
    Builds abi fg fg' (b >>= k) rs out := by
  have e : b >>= k = (do let r ← b; Pure.pure #[r]) >>= fun a => k (a[0]?.getD 0) := by simp
  rw [e]
  refine Builds.bind hb fun a xs h => ?_
  obtain ⟨r, hr, hR⟩ := holds_at (holds_of_reg (h "")) (i := 0) (v := o) rfl
  rw [show a[0]?.getD 0 = r by simp at hr; simp [hr]]
  exact hk r xs hR

/-- `wordsB n w` builds the register `constB_builds` describes: `nv` rows of the word `w`. -/
theorem wordsB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n : Nat} {nv : USize} {w : UInt64} {c : Enc}
    (hn : rs[n]? = some (.size nv)) (hk : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv w = .ok c) :
    Builds abiOf fg fg (do let r ← wordsB n w; Pure.pure #[r]) rs #[Reg.put c] := by
  unfold wordsB
  simp only [bind_assoc]
  refine Builds.litG fun r R hr ext => ?_
  exact constB_builds (ext hn) hr hk

/-! ### The column of no row

Every kernel answer of no row is `wordsFoR #[]`: `colMap_enc` says it is `wordsFoR` of its own words, and there are
none. So the column `noneB` writes and the ones `Vals.none` names (`Arr.zeros`, `Opt.nuls`, `tagCol` at `0`) are one
`Enc`, with no kernel evaluated. -/

/-- A `colMap` answer of no row is `wordsFoR #[]`. -/
theorem colMap_zero {op : Kernel.Op} {t s : QAtomicType} {a b o : Enc} {pre post : List (Kernel.Op × UInt64)}
    (h : colMap op 0 a b t s pre post = .ok o) (hs : kscanStream op [(0, a), (0, b)] pre post = false)
    (hn : op ≠ .null) (hF : op.nulFold = none ∨ ∀ p ∈ [((0 : USize), a), (0, b)], hasNul p.2 = false) :
    o = wordsFoR #[] := by
  obtain ⟨ho, -, -, hz, -⟩ := colMap_enc h hs hn hF
  rw [ho, Array.eq_empty_of_size_eq_zero (xs := Enc.raw .i64 0 o) (by simpa using hz)]

/-- A column `Enc.WF` at `t` has a width at `t`. -/
theorem Enc.WF.width {t : QAtomicType} {n : USize} {e : Enc} (h : Enc.WF t n e) : t.width.isSome := by
  unfold Enc.WF at h
  split at h
  · exact h.1
  · simp [QAtomicType.width]
  · exact h.elim

/-- A `colArr` of no row is `wordsFoR #[]`, at a type with a width. -/
theorem colArr_zero {op : Kernel.Op} {a b : Enc} {t s : QAtomicType} {pre post : List (Kernel.Op × UInt64)} {hs hF} {y : Arr t 0}
    (h : colArr op 0 a b t s pre post hs hF = .ok y) (hn : op ≠ .null) : y.enc = wordsFoR #[] ∧ t.width.isSome := by
  unfold colArr at h
  split at h
  · rename_i o ho
    cases h
    exact ⟨colMap_zero ho hs hn hF, Enc.WF.width (colMap_closed hs ho hF).2.1⟩
  · cases h

theorem Arr.zeros_zero {t : QAtomicType} {y : Arr t 0} (h : Arr.zeros t 0 = .ok y) :
    y.enc = wordsFoR #[] ∧ t.width.isSome :=
  by unfold Arr.zeros at h; exact colArr_zero h (by decide)

theorem tagCol_zero {y : Arr .u1 0} (h : tagCol 0 false = .ok y) : y.enc = wordsFoR #[] :=
  by unfold tagCol at h; exact (colArr_zero h (by decide)).1

theorem Opt.nuls_zero {t : QAtomicType} {y : Opt t 0} (h : Opt.nuls t 0 = .ok y) :
    y.enc = wordsFoR #[] ∧ t.width.isSome := by
  unfold Opt.nuls at h
  split at h
  · rename_i ht
    cases h
    exact ⟨by simp [Opt.enc, nulMap, packOf], ht⟩
  · cases h

/-- The `kscatter` `wordsB z 0` runs at no row answers. -/
theorem zeros_scatter : ∃ c, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) 0 0 = .ok c :=
  have hv := (wordsFoR_closed #[] (n := 0) (by simp)).1
  kscatter_ok (op := .last) (fill := 0) (n := 0) hv hv (hasNul_wordsFoR _) (hasNul_wordsFoR _)
    (fun k hk => by simp at hk) (fun k hk => by simp at hk)

/-- … and `colMap .add` of its answer, at a type with a width, answers `wordsFoR #[]`: `noneB`'s column. -/
theorem zeros_map {t : QAtomicType} {c : Enc} (ht : t.width.isSome)
    (hc : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) 0 0 = .ok c) :
    ∃ f, kscan .add false .i64 t 0 none [(0, c), (0, c)] [] [] = .ok (wordsFoR #[], f) := by
  obtain ⟨-, cs, -⟩ := kscatter_closed hc
  have cN := kscatter_plain hc (hasNul_wordsFoR _)
  obtain ⟨o, ho⟩ := colMap_ok (op := .add) ht cs cs cN cN (fun i hi => by simp at hi)
  have ho0 := colMap_zero ho (kscanStream_ne (by decide) _ _ _) (by decide) (Or.inr (by simp [cN]))
  subst ho0
  unfold colMap at ho
  obtain ⟨r, hr, hr1⟩ := except_bind_ok ho
  refine ⟨r.2, ?_⟩
  rw [hr]
  cases r
  cases hr1
  rfl

theorem reg_ty (t : QAtomicType) : (Reg.get? (Reg.put t) : Option QAtomicType) = some t := by cases t <;> rfl

theorem reg_add : (Reg.get? (Reg.put Kernel.Op.add) : Option Kernel.Op) = some .add := by with_unfolding_all rfl

theorem reg_nil : (Reg.get? (Reg.put ([] : List (Kernel.Op × UInt64))) : Option (List (Kernel.Op × UInt64))) = some [] := by
  with_unfolding_all rfl

/-- `mapB .add z c c t` at `z` holding `0` and `c` the zero words, then `k` on its register: `wordsFoR #[]`. -/
theorem zeroMapB_builds {fg fg' : Array Fun × Array Fun} {rs : Array Val} {z c : Nat} {t : QAtomicType} {cc : Enc}
    {k : Nat → Bld (Array Nat)} {out : Array Val} (hz : rs[z]? = some (.size 0)) (ht : t.width.isSome)
    (hc : rs[c]? = some (Reg.put cc)) (hcc : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) 0 0 = .ok cc)
    (hk : ∀ r xs, (rs ++ xs)[r]? = some (Reg.put (wordsFoR #[])) → Builds abiOf fg fg' (k r) (rs ++ xs) out) :
    Builds abiOf fg fg' (mapB .add z c c t >>= k) rs out := by
  obtain ⟨f, hk2⟩ := zeros_map ht hcc
  exact Builds.bind1 (mapB_builds hz hc (enc_get_put _) hc (enc_get_put _) reg_add (reg_ty _) (reg_ty _)
    reg_nil reg_nil hk2) hk

/-- `noneAtomB z t p` builds one atom column whose register holds `wordsFoR #[]`. -/
theorem noneAtomB_builds {fg fg' : Array Fun × Array Fun} {rs : Array Val} {z : Nat} {t : QAtomicType} {p : String}
    {kk : Cols → Bld (Array Nat)} {out : Array Val} (hz : rs[z]? = some (.size 0)) (ht : t.width.isSome)
    (hkk : ∀ (U : Cols) (ys : Array Val), (∃ e, U = [.atom p t e]) →
      (Cols.regs U).mapM (fun i => (rs ++ ys)[i]?) = some [Reg.put (wordsFoR #[])] →
      Builds abiOf fg fg' (kk U) (rs ++ ys) out) :
    Builds abiOf fg fg' (noneAtomB z t p >>= kk) rs out := by
  unfold noneAtomB
  simp only [bind_assoc]
  obtain ⟨cc, hcc⟩ := zeros_scatter
  refine Builds.bind1 (wordsB_builds hz hcc) fun c xs hc => zeroMapB_builds (get_app hz) ht hc hcc fun r xs1 hr => ?_
  simp only [pure_bind]
  rw [Array.append_assoc] at hr ⊢
  exact hkk _ _ ⟨r, rfl⟩ (by simp [Cols.regs, Col.regs, hr])

/-- Lifting a side to a dense sum's summand (`Opt.ofArr` per atom) leaves its storage, so its registers. -/
theorem Vals.regVals_lift : ∀ {A : Obj} {n : USize} (x : Vals A n), (Vals.lift x).regVals = x.regVals
  | .atom _, _, _ => rfl
  | .prod _ _, _, x => by
    simp only [Vals.lift, ValsB.regVals, Vals.regVals_lift x.1, Vals.regVals_lift x.2]
  | .arr _, _, ⟨_, _, _, _⟩ => rfl
  | .sum _ _, _, _ => rfl
  | .one, _, _ => rfl

/-- `noneB z A p` builds the columns of a side of `A` (`ColsOf`) whose registers hold `Vals.none A`'s, `z` holding
    the count `0`. -/
theorem noneB_builds {fg fg' : Array Fun × Array Fun} {z : Nat} (A : Obj) :
    ∀ {p : String} {rs : Array Val} {x : Vals A 0} {kk : Cols → Bld (Array Nat)} {out : Array Val},
    rs[z]? = some (.size 0) → Vals.none A = .ok x →
    (∀ (U : Cols) (ys : Array Val), ColsOf A U → (Cols.regs U).mapM (fun i => (rs ++ ys)[i]?) = some x.regVals →
      Builds abiOf fg fg' (kk U) (rs ++ ys) out) →
    Builds abiOf fg fg' (noneB z A p >>= kk) rs out := by
  induction A with
  | atom t =>
    intro p rs x kk out hz hx hkk
    obtain ⟨he, ht⟩ := Arr.zeros_zero (by unfold Vals.none at hx; exact hx)
    unfold noneB
    exact noneAtomB_builds hz ht fun U ys ⟨e, hU⟩ hr => hkk U ys ⟨p, e, hU⟩
      (by rw [hr]; simp [ValsB.regVals, ColB.enc, he])
  | prod a b iha ihb =>
    intro p rs x kk out hz hx hkk
    unfold Vals.none at hx
    obtain ⟨xa, ha, hx⟩ := except_bind_ok hx
    obtain ⟨xb, hb, hx⟩ := except_bind_ok hx
    cases hx
    unfold noneB
    simp only [bind_assoc, pure_bind]
    refine iha hz ha fun U ys hU hr => ihb (get_app hz) hb fun U2 ys2 hU2 hr2 => ?_
    rw [Array.append_assoc] at hr2 ⊢
    refine hkk (U ++ U2) (ys ++ ys2) ⟨U, U2, rfl, hU, hU2⟩ ?_
    rw [Cols.regs_append, List.mapM_append, ← Array.append_assoc, mapM_get_app hr, Array.append_assoc, hr2]
    rfl
  | arr b ih =>
    intro p rs x kk out hz hx hkk
    unfold Vals.none at hx
    obtain ⟨lo, hlo, hx⟩ := except_bind_ok hx
    obtain ⟨hi, hhi, hx⟩ := except_bind_ok hx
    obtain ⟨f, hf, hx⟩ := except_bind_ok hx
    cases hx
    obtain ⟨cc, hcc⟩ := zeros_scatter
    unfold noneB
    simp only [bind_assoc, pure_bind]
    refine Builds.bind1 (wordsB_builds hz hcc) fun c xs hc => zeroMapB_builds (get_app hz) rfl hc hcc
      fun r1 xs1 h1 => ?_
    simp only [Array.append_assoc] at h1 ⊢
    refine zeroMapB_builds (get_app hz) rfl (by simpa only [Array.append_assoc] using get_app (xs := xs1) hc) hcc
      fun r2 xs2 h2 => ?_
    simp only [Array.append_assoc] at h2 ⊢
    refine ih (get_app hz) hf fun U ys hU hr => ?_
    simp only [Array.append_assoc] at hr ⊢
    refine hkk _ _ ⟨p, z, r1, r2, U, rfl, hU⟩ ?_
    have e1 : (rs ++ (xs ++ (xs1 ++ (xs2 ++ ys))))[z]? = some (.size 0) := get_app hz
    have e2 : (rs ++ (xs ++ (xs1 ++ (xs2 ++ ys))))[r1]? = some (Reg.put (wordsFoR #[])) := by
      simpa only [Array.append_assoc] using get_app (xs := xs2 ++ ys) h1
    have e3 : (rs ++ (xs ++ (xs1 ++ (xs2 ++ ys))))[r2]? = some (Reg.put (wordsFoR #[])) := by
      simpa only [Array.append_assoc] using get_app (xs := ys) h2
    simp [Cols.regs, Col.regs, ValsB.regVals, ColB.enc, (Arr.zeros_zero hlo).1, (Arr.zeros_zero hhi).1, e1, e2, e3, hr]
  | one =>
    intro p rs x kk out hz hx hkk
    unfold noneB
    simp only [pure_bind]
    have h := hkk [] #[] rfl rfl
    rwa [Array.append_empty] at h
  | sum a b iha ihb =>
    intro p rs x kk out hz hx hkk
    unfold Vals.none at hx
    unfold noneB
    split at hx
    · rename_i t hband
      obtain ⟨y, hy, hx⟩ := except_bind_ok hx
      cases hx
      obtain ⟨he, ht⟩ := Opt.nuls_zero hy
      simp only [hband]
      exact noneAtomB_builds hz ht fun U ys ⟨e, hU⟩ hr => hkk U ys (by simp only [ColsOf, hband]; exact ⟨p, e, hU⟩)
        (by rw [hr]; simp [ValsB.regVals, ValsB.view_ofOpt, he])
    · rename_i hband
      obtain ⟨tag, htag, hx⟩ := except_bind_ok hx
      obtain ⟨xa, ha, hx⟩ := except_bind_ok hx
      obtain ⟨xb, hb, hx⟩ := except_bind_ok hx
      cases hx
      obtain ⟨cc, hcc⟩ := zeros_scatter
      simp only [hband, bind_assoc, pure_bind]
      refine Builds.bind1 (wordsB_builds hz hcc) fun c xs hc => zeroMapB_builds (get_app hz) rfl hc hcc
        fun r1 xs1 h1 => ?_
      simp only [Array.append_assoc] at h1 ⊢
      refine iha (get_app hz) ha fun U ys hU hr => ?_
      simp only [Array.append_assoc] at hr ⊢
      refine ihb (get_app hz) hb fun U2 ys2 hU2 hr2 => ?_
      simp only [Array.append_assoc] at hr2 ⊢
      refine hkk _ _ (by simp only [ColsOf, hband]; exact ⟨p, r1, U, U2, rfl, hU, hU2⟩) ?_
      have e1 : (rs ++ (xs ++ (xs1 ++ (ys ++ ys2))))[r1]? = some (Reg.put (wordsFoR #[])) := by
        simpa only [Array.append_assoc] using get_app (xs := ys ++ ys2) h1
      have e2 : (Cols.regs U).mapM (fun i => (rs ++ (xs ++ (xs1 ++ (ys ++ ys2))))[i]?) = some xa.regVals := by
        simpa only [Array.append_assoc] using mapM_get_app (xs := ys2) hr
      simp [Cols.regs, Col.regs, ValsB.regVals, ValsB.view_ofGen, Vals.regVals_lift, tagCol_zero htag, e1, e2, hr2]

/-- `zeroB A B` builds a table whose registers hold `Tab.zero`'s: the count `0`, then `noneB` of each side. -/
theorem zeroB_builds {fg fg' : Array Fun × Array Fun} {A B : Obj} {R : Tab A B} {rs : Array Val}
    {kk : TabB → Bld (Array Nat)} {out : Array Val} (hR : Tab.zero = .ok R)
    (hkk : ∀ (U : TabB) (ys : Array Val), ColsOf A U.key → ColsOf B U.val →
      U.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
      Builds abiOf fg fg' (kk U) (rs ++ ys) out) :
    Builds abiOf fg fg' (zeroB A B >>= kk) rs out := by
  unfold Tab.zero at hR
  obtain ⟨xa, ha, hR⟩ := except_bind_ok hR
  obtain ⟨xb, hb, hR⟩ := except_bind_ok hR
  cases hR
  unfold zeroB
  simp only [bind_assoc, pure_bind]
  refine Builds.lit ?_
  rw [show rs.push (Val.size 0) = rs ++ #[Val.size 0] by simp]
  have hz : (rs ++ #[Val.size 0])[rs.size]? = some (.size 0) := by simp
  refine noneB_builds A hz ha fun U ys hU hr => noneB_builds B (get_app hz) hb fun U2 ys2 hU2 hr2 => ?_
  simp only [Array.append_assoc] at hr hr2 ⊢
  refine hkk ⟨rs.size, U, U2⟩ _ hU hU2 ?_
  have e2 : (Cols.regs U).mapM (fun i => (rs ++ (#[Val.size 0] ++ (ys ++ ys2)))[i]?) = some xa.regVals := by
    simpa only [Array.append_assoc] using mapM_get_app (xs := ys2) hr
  have e0 : (rs ++ (#[Val.size 0] ++ (ys ++ ys2)))[rs.size]? = some (.size 0) := by
    have h := get_app (xs := ys ++ ys2) hz; rwa [Array.append_assoc] at h
  simp only [TabB.regs, Cols.regs_append, List.mapM_append, List.mapM_cons, e0, e2, hr2]
  rfl

/-- The columns of a side of `A` are `objWidth A` many. -/
theorem ColsOf.length_eq : ∀ {A : Obj} {cs : Cols}, ColsOf A cs → cs.length = objWidth A
  | .atom _, _, ⟨_, _, h⟩ => by subst h; simp [objWidth]
  | .prod _ _, _, ⟨_, _, h, h1, h2⟩ => by subst h; simp [objWidth, ColsOf.length_eq h1, ColsOf.length_eq h2]
  | .arr _, _, ⟨_, _, _, _, _, h, _⟩ => by subst h; simp [objWidth]
  | .one, _, h => by subst h; simp [objWidth]
  | .sum a b, _, h => by
    unfold ColsOf at h
    split at h
    · obtain ⟨_, _, h⟩ := h; subst h; simp [objWidth]
    · obtain ⟨_, _, _, _, h, -⟩ := h; subst h; simp [objWidth]

/-- `repath A pre` has no spec counterpart: it renames the paths of a side's columns (`Tab.pair`'s key rebracketing in
    `pairB`), so it keeps `ColsOf A` and the registers, never failing on a side of `A`. -/
theorem repath_eq : ∀ (A : Obj) {pre : String} {cs : Cols}, ColsOf A cs →
    ∃ cs', repath A pre cs = pure cs' ∧ ColsOf A cs' ∧ Cols.regs cs' = Cols.regs cs
  | .atom t, pre, _, ⟨p, e, h⟩ => by
    subst h; exact ⟨[.atom pre t e], by simp [repath], ⟨pre, e, rfl⟩, by simp [Cols.regs, Col.regs]⟩
  | .prod a b, pre, _, ⟨c1, c2, h, h1, h2⟩ => by
    subst h
    obtain ⟨d1, e1, g1, r1⟩ := repath_eq a (pre := pre ++ ".1") h1
    obtain ⟨d2, e2, g2, r2⟩ := repath_eq b (pre := pre ++ ".2") h2
    refine ⟨d1 ++ d2, ?_, ⟨d1, d2, rfl, g1, g2⟩, by simp [Cols.regs_append, r1, r2]⟩
    have ht : (c1 ++ c2).take (objWidth a) = c1 := by simp [← ColsOf.length_eq h1]
    have hd : (c1 ++ c2).drop (objWidth a) = c2 := by simp [← ColsOf.length_eq h1]
    simp [repath, ht, hd, e1, e2]
  | .arr b, pre, _, ⟨p, m, lo, hi, f, h, hf⟩ => by
    subst h
    obtain ⟨f', e, g, r⟩ := repath_eq b (pre := pre ++ ".e") hf
    exact ⟨[.arr pre m lo hi f'], by simp [repath, e], ⟨pre, m, lo, hi, f', rfl, g⟩, by simp [Cols.regs, Col.regs, r]⟩
  | .one, pre, _, h => by subst h; exact ⟨[], by simp [repath], rfl, rfl⟩
  | .sum a b, pre, cs, h => by
    unfold ColsOf at h
    split at h
    · rename_i t hband
      obtain ⟨p, e, h⟩ := h; subst h
      refine ⟨[.atom pre t e], by simp [repath, hband], by simp only [ColsOf, hband]; exact ⟨pre, e, rfl⟩,
        by simp [Cols.regs, Col.regs]⟩
    · rename_i hband
      obtain ⟨p, tag, x, y, h, hx, hy⟩ := h; subst h
      obtain ⟨x', ex, gx, rx⟩ := repath_eq a (pre := pre ++ ".l") hx
      obtain ⟨y', ey, gy, ry⟩ := repath_eq b (pre := pre ++ ".r") hy
      refine ⟨[.sum pre tag x' y'], by simp [repath, hband, ex, ey],
        by simp only [ColsOf, hband]; exact ⟨pre, tag, x', y', rfl, gx, gy⟩, by simp [Cols.regs, Col.regs, rx, ry]⟩

/-! ### `Grows`, `Typed` -/

theorem Grows.noneAtomB (z : Nat) (t : QAtomicType) (p : String) : Grows (Plan.noneAtomB z t p) := by
  unfold Plan.noneAtomB
  exact (Grows.wordsB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => Grows.pure _

theorem Grows.noneB (z : Nat) (A : Obj) : ∀ p, Grows (Plan.noneB z A p) := by
  induction A with
  | atom t => intro p; unfold Plan.noneB; exact Grows.noneAtomB _ _ _
  | prod a b iha ihb =>
    intro p; unfold Plan.noneB
    exact (iha _).bind fun _ => (ihb _).bind fun _ => Grows.pure _
  | arr b ih =>
    intro p; unfold Plan.noneB
    exact (Grows.wordsB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
      (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (ih _).bind fun _ => Grows.pure _
  | one => intro p; unfold Plan.noneB; exact Grows.pure _
  | sum a b iha ihb =>
    intro p; unfold Plan.noneB
    split
    · exact Grows.noneAtomB _ _ _
    · exact (Grows.wordsB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
        (iha _).bind fun _ => (ihb _).bind fun _ => Grows.pure _

theorem Grows.zeroB (A B : Obj) : Grows (Plan.zeroB A B) := by
  unfold Plan.zeroB
  exact (Grows.lit _).bind fun _ => (Grows.noneB _ _ _).bind fun _ => (Grows.noneB _ _ _).bind fun _ => Grows.pure _


theorem Typed.noneAtomB {m z : Nat} {t : QAtomicType} {p : String} (hz : m ≤ z) :
    Typed m (fun r => AllGe m (Cols.regs r)) (Plan.noneAtomB z t p) := by
  unfold Plan.noneAtomB
  exact Typed.wordsB.bind fun c hc => (Typed.mapB hz hc hc).bind fun e he =>
    Typed.pure fun a ha => by simp [Cols.regs, Col.regs] at ha; omega

theorem Typed.noneB {m z : Nat} (hz : m ≤ z) (A : Obj) :
    ∀ p, Typed m (fun r => AllGe m (Cols.regs r)) (Plan.noneB z A p) := by
  induction A with
  | atom t => intro p; unfold Plan.noneB; exact Typed.noneAtomB hz
  | prod a b iha ihb =>
    intro p; unfold Plan.noneB
    exact (iha _).bind fun x hx => (ihb _).bind fun y hy => Typed.pure fun a ha => by
      rw [Cols.regs_append] at ha; rcases List.mem_append.1 ha with ha | ha <;> first | exact hx a ha | exact hy a ha
  | arr b ih =>
    intro p; unfold Plan.noneB
    exact Typed.wordsB.bind fun c hc => (Typed.mapB hz hc hc).bind fun lo hlo =>
      (Typed.mapB hz hc hc).bind fun hi hhi => (ih _).bind fun f hf => Typed.pure fun a ha => by
        simp only [Cols.regs, Col.regs, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with (rfl | rfl | rfl) | ha <;> first | exact hz | exact hlo | exact hhi | exact hf _ ha
  | one => intro p; unfold Plan.noneB; exact Typed.pure fun a ha => by simp [Cols.regs] at ha
  | sum a b iha ihb =>
    intro p; unfold Plan.noneB
    split
    · exact Typed.noneAtomB hz
    · exact Typed.wordsB.bind fun c hc => (Typed.mapB hz hc hc).bind fun tag htag =>
        (iha _).bind fun x hx => (ihb _).bind fun y hy => Typed.pure fun a ha => by
          simp only [Cols.regs, Col.regs, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
            List.append_nil] at ha
          rcases ha with (rfl | ha) | ha <;> first | exact htag | exact hx _ ha | exact hy _ ha

theorem Typed.zeroB {m : Nat} (A B : Obj) :
    Typed m (fun T : TabB => AllGe m T.regs) (Plan.zeroB A B) := by
  unfold Plan.zeroB
  exact (Typed.lit _).bind fun z hz => (Typed.noneB hz A "").bind fun x hx =>
    (Typed.noneB hz B "").bind fun y hy => Typed.pure fun a ha => by
      simp only [TabB.regs, List.mem_cons, List.mem_append, Cols.regs_append] at ha
      rcases ha with rfl | ha | ha <;> first | exact hz | exact hx _ ha | exact hy _ ha

/-- A sub-list of the columns holds registers among theirs. -/
theorem AllGe.sub {m : Nat} {cs ds : Cols} (h : AllGe m (Cols.regs cs)) (hs : ∀ c ∈ ds, c ∈ cs) :
    AllGe m (Cols.regs ds) := (Cols.regs_all ds).2 fun c hc => (Cols.regs_all cs).1 h c (hs c hc)

theorem Typed.repath {m : Nat} (A : Obj) :
    ∀ (pre : String) (cs : Cols), AllGe m (Cols.regs cs) →
      Typed m (fun r => AllGe m (Cols.regs r)) (Plan.repath A pre cs) := by
  induction A with
  | atom t =>
    intro pre cs hcs
    rcases cs with _ | ⟨⟨p, t', e⟩ | ⟨p, m', lo, hi, f⟩ | ⟨p, tag, x, y⟩, _ | ⟨d, cs⟩⟩ <;> simp only [Plan.repath] <;>
      first | exact Typed.throw _ | exact Typed.pure fun a ha => hcs a (by simpa [Cols.regs, Col.regs] using ha)
  | prod a b iha ihb =>
    intro pre cs hcs; simp only [Plan.repath]
    exact (iha _ _ (hcs.sub fun c hc => List.mem_of_mem_take hc)).bind fun x hx =>
      (ihb _ _ (hcs.sub fun c hc => List.mem_of_mem_drop hc)).bind fun y hy => Typed.pure fun r hr => by
        rw [Cols.regs_append] at hr
        rcases List.mem_append.1 hr with hr | hr <;> first | exact hx r hr | exact hy r hr
  | arr b ih =>
    intro pre cs hcs
    rcases cs with _ | ⟨⟨p, t', e⟩ | ⟨p, m', lo, hi, f⟩ | ⟨p, tag, x, y⟩, _ | ⟨d, cs⟩⟩ <;> simp only [Plan.repath] <;>
      first | exact Typed.throw _ | skip
    have hf : AllGe m (Cols.regs f) := fun a ha => hcs a (by simp [Cols.regs, Col.regs, ha])
    exact (ih _ _ hf).bind fun f' hf' => Typed.pure fun a ha => by
      simp only [Cols.regs, Col.regs, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with (rfl | rfl | rfl) | ha <;>
        first | exact hf' _ ha | exact hcs _ (by simp [Cols.regs, Col.regs])
  | one =>
    intro pre cs hcs
    rcases cs with _ | ⟨⟨p, t', e⟩ | ⟨p, m', lo, hi, f⟩ | ⟨p, tag, x, y⟩, _ | ⟨d, cs⟩⟩ <;> simp only [Plan.repath] <;>
      first | exact Typed.throw _ | exact Typed.pure fun a ha => by simp [Cols.regs] at ha
  | sum a b iha ihb =>
    intro pre cs hcs
    rcases hb : Obj.band a b with _ | t
    · rcases cs with _ | ⟨⟨p, t', e⟩ | ⟨p, m', lo, hi, f⟩ | ⟨p, tag, x, y⟩, _ | ⟨d, cs⟩⟩ <;>
        simp only [Plan.repath, hb] <;> first | exact Typed.throw _ | skip
      have hx : AllGe m (Cols.regs x) := fun a ha => hcs a (by simp [Cols.regs, Col.regs, ha])
      have hy : AllGe m (Cols.regs y) := fun a ha => hcs a (by simp [Cols.regs, Col.regs, ha])
      exact (iha _ _ hx).bind fun x' hx' => (ihb _ _ hy).bind fun y' hy' => Typed.pure fun a ha => by
        simp only [Cols.regs, Col.regs, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
          List.append_nil] at ha
        rcases ha with (rfl | ha) | ha <;>
          first | exact hx' _ ha | exact hy' _ ha | exact hcs _ (by simp [Cols.regs, Col.regs])
    · rcases cs with _ | ⟨⟨p, t', e⟩ | ⟨p, m', lo, hi, f⟩ | ⟨p, tag, x, y⟩, _ | ⟨d, cs⟩⟩ <;>
        simp only [Plan.repath, hb] <;>
        first | exact Typed.throw _ | exact Typed.pure fun a ha => hcs a (by simpa [Cols.regs, Col.regs] using ha)

theorem Grows.repath (A : Obj) : ∀ (pre : String) (cs : Cols), Grows (Plan.repath A pre cs) := by
  induction A with
  | atom t =>
    intro pre cs
    rcases cs with _ | ⟨⟨p, t', e⟩ | ⟨p, m', lo, hi, f⟩ | ⟨p, tag, x, y⟩, _ | ⟨d, cs⟩⟩ <;> simp only [Plan.repath] <;>
      first | exact Grows.throw _ | exact Grows.pure _
  | prod a b iha ihb =>
    intro pre cs; simp only [Plan.repath]
    exact (iha _ _).bind fun _ => (ihb _ _).bind fun _ => Grows.pure _
  | arr b ih =>
    intro pre cs
    rcases cs with _ | ⟨⟨p, t', e⟩ | ⟨p, m', lo, hi, f⟩ | ⟨p, tag, x, y⟩, _ | ⟨d, cs⟩⟩ <;> simp only [Plan.repath] <;>
      first | exact Grows.throw _ | exact (ih _ _).bind fun _ => Grows.pure _
  | one =>
    intro pre cs
    rcases cs with _ | ⟨⟨p, t', e⟩ | ⟨p, m', lo, hi, f⟩ | ⟨p, tag, x, y⟩, _ | ⟨d, cs⟩⟩ <;> simp only [Plan.repath] <;>
      first | exact Grows.throw _ | exact Grows.pure _
  | sum a b iha ihb =>
    intro pre cs
    rcases hb : Obj.band a b with _ | t <;>
      rcases cs with _ | ⟨⟨p, t', e⟩ | ⟨p, m', lo, hi, f⟩ | ⟨p, tag, x, y⟩, _ | ⟨d, cs⟩⟩ <;>
      simp only [Plan.repath, hb] <;>
      first | exact Grows.throw _ | exact Grows.pure _ | exact (iha _ _).bind fun _ => (ihb _ _).bind fun _ => Grows.pure _

end Rel.Lang.Plan

