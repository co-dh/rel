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

/-- The `kscatter` `wordsB z 0` runs at no row, and `colMap .add` of it at a type with a width: `noneB`'s column. -/
theorem zeros_kernels {t : QAtomicType} (ht : t.width.isSome) :
    ∃ c f, kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) 0 0 = .ok c ∧
      kscan .add false .i64 t 0 none [(0, c), (0, c)] [] [] = .ok (wordsFoR #[], f) := by
  have hv := (wordsFoR_closed #[] (n := 0) (by simp)).1
  obtain ⟨c, hc⟩ := kscatter_ok (op := .last) (fill := 0) (n := 0) hv hv (hasNul_wordsFoR _) (hasNul_wordsFoR _)
    (fun k hk => by simp at hk) (fun k hk => by simp at hk)
  obtain ⟨-, cs, -⟩ := kscatter_closed hc
  have cN := kscatter_plain hc (hasNul_wordsFoR _)
  obtain ⟨o, ho⟩ := colMap_ok (op := .add) ht cs cs cN cN (fun i hi => by simp at hi)
  have ho0 := colMap_zero ho (kscanStream_ne (by decide) _ _ _) (by decide) (Or.inr (by simp [cN]))
  subst ho0
  unfold colMap at ho
  obtain ⟨r, hr, hr1⟩ := except_bind_ok ho
  refine ⟨c, r.2, hc, ?_⟩
  rw [hr]
  cases r
  cases hr1
  rfl

theorem reg_ty (t : QAtomicType) : (Reg.get? (Reg.put t) : Option QAtomicType) = some t := by cases t <;> rfl

theorem reg_add : (Reg.get? (Reg.put Kernel.Op.add) : Option Kernel.Op) = some .add := by with_unfolding_all rfl

theorem reg_nil : (Reg.get? (Reg.put ([] : List (Kernel.Op × UInt64))) : Option (List (Kernel.Op × UInt64))) = some [] := by
  with_unfolding_all rfl

/-- `wordsB z 0` then `mapB .add z c c t` at `z` holding `0`, then `k` on its register, which holds `wordsFoR #[]`. -/
theorem zerosB_builds {fg fg' : Array Fun × Array Fun} {rs : Array Val} {z : Nat} {t : QAtomicType}
    {k : Nat → Bld (Array Nat)} {out : Array Val} (hz : rs[z]? = some (.size 0)) (ht : t.width.isSome)
    (hk : ∀ r xs, (rs ++ xs)[r]? = some (Reg.put (wordsFoR #[])) → Builds abiOf fg fg' (k r) (rs ++ xs) out) :
    Builds abiOf fg fg' (wordsB z 0 >>= fun c => mapB .add z c c t >>= k) rs out := by
  obtain ⟨c, f, hc, hk2⟩ := zeros_kernels ht
  refine Builds.bind1 (wordsB_builds hz hc) fun r xs hr => ?_
  refine Builds.bind1 (mapB_builds (get_app hz) hr (enc_get_put _) hr (enc_get_put _) reg_add (reg_ty _) (reg_ty _)
    reg_nil reg_nil hk2) fun r2 xs2 hr2 => ?_
  rw [Array.append_assoc] at hr2 ⊢
  exact hk r2 _ hr2

/-- `noneAtomB z t p` builds one atom column whose register holds `wordsFoR #[]`. -/
theorem noneAtomB_builds {fg fg' : Array Fun × Array Fun} {rs : Array Val} {z : Nat} {t : QAtomicType} {p : String}
    {kk : Cols → Bld (Array Nat)} {out : Array Val} (hz : rs[z]? = some (.size 0)) (ht : t.width.isSome)
    (hkk : ∀ (U : Cols) (ys : Array Val), (∃ e, U = [.atom p t e]) →
      (Cols.regs U).mapM (fun i => (rs ++ ys)[i]?) = some [Reg.put (wordsFoR #[])] →
      Builds abiOf fg fg' (kk U) (rs ++ ys) out) :
    Builds abiOf fg fg' (noneAtomB z t p >>= kk) rs out := by
  unfold noneAtomB
  simp only [bind_assoc]
  refine zerosB_builds hz ht fun r xs hr => ?_
  simp only [pure_bind]
  exact hkk _ _ ⟨r, rfl⟩ (by simp [Cols.regs, Col.regs, hr])

end Rel.Lang.Plan
