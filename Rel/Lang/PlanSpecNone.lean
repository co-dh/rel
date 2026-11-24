module

public import Rel.Lang.PlanSpecGather

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `noneB` means `Vals.none`, `zeroB` means `Tab.zero`, `repath` keeps the registers

`noneB z A` writes, for each atom column of a side of `A`, `mapB .add z c c t` of the zero words `c = wordsB z 0`: at
`z` holding `0` that is `colMap .add 0 c c t`, which is `Arr.zeros t 0` (and `Opt.nuls t 0`, `tagCol 0 false`) as the
column the kernels answer for no row (`none_enc`). `repath` has no spec counterpart: it renames the paths of a side's
columns for `Tab.pair`'s key rebracketing, so it keeps `ColsOf` and the registers (`repath_eq`). -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

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

/-- `mapB op n a b t s pre post` builds the register holding `colMap op nv ea eb t s pre post`: the registers `n`, `a`,
    `b` hold the count and the two columns, and the lists and types read back as themselves. -/
theorem mapB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {op : Kernel.Op} {n a b : Nat} {t s : QAtomicType}
    {pre post : List (Kernel.Op × UInt64)} {nv : USize} {ea eb o : Enc}
    (hn : rs[n]? = some (.size nv)) (ha : rs[a]? = some (Reg.put ea)) (hb : rs[b]? = some (Reg.put eb))
    (hop : (Reg.get? (Reg.put op) : Option Kernel.Op) = some op)
    (hs : (Reg.get? (Reg.put s) : Option QAtomicType) = some s)
    (ht : (Reg.get? (Reg.put t) : Option QAtomicType) = some t)
    (hpre : (Reg.get? (Reg.put pre) : Option (List (Kernel.Op × UInt64))) = some pre)
    (hpost : (Reg.get? (Reg.put post) : Option (List (Kernel.Op × UInt64))) = some post)
    (hc : colMap op nv ea eb t s pre post = .ok o) :
    Builds abiOf fg fg (do let r ← mapB op n a b t s pre post; Pure.pure #[r]) rs #[Reg.put o] := by
  obtain ⟨r, hk, hro⟩ : ∃ r, kscan op false s t nv none [(nv, ea), (nv, eb)] pre post = .ok r ∧ r.1 = o := by
    unfold colMap at hc
    obtain ⟨r, hk, hr⟩ := except_bind_ok hc
    exact ⟨r, hk, Except.ok.inj hr⟩
  have hgn : (Reg.get? (Val.size nv) : Option USize) = some nv := rfl
  have hgb : [Reg.put ea, Reg.put eb].mapM (Reg.get? (α := Enc)) = some [ea, eb] := by simp [enc_get_put]
  have hl : (Reg.get? (Val.ctor 1 #[Val.ctor 0 #[.size nv, Reg.put ea] #[],
      Val.ctor 1 #[Val.ctor 0 #[.size nv, Reg.put eb] #[], Val.ctor 0 #[] #[]] #[]] #[]) :
      Option (List (USize × Enc))) = some [(nv, ea), (nv, eb)] :=
    (listGet?_foldr (α := USize × Enc) [Val.ctor 0 #[.size nv, Reg.put ea] #[], Val.ctor 0 #[.size nv, Reg.put eb] #[]]).trans
      (mapM_pair hgn [Reg.put ea, Reg.put eb] hgb)
  have hgv : (Reg.get? (Val.ctor 0 #[] #[]) : Option (Option Enc)) = some none := rfl
  unfold mapB
  simp only [bind_assoc, srcB]
  refine Builds.litG fun r1 R1 h1 e1 => ?_
  replace hn := e1 hn; replace ha := e1 ha; replace hb := e1 hb
  refine Builds.litG fun r2 R2 h2 e2 => ?_
  replace hn := e2 hn; replace ha := e2 ha; replace hb := e2 hb; replace h1 := e2 h1
  refine Builds.litG fun r3 R3 h3 e3 => ?_
  replace hn := e3 hn; replace ha := e3 ha; replace hb := e3 hb; replace h1 := e3 h1; replace h2 := e3 h2
  refine Builds.litG fun r4 R4 h4 e4 => ?_
  replace hn := e4 hn; replace ha := e4 ha; replace hb := e4 hb; replace h1 := e4 h1; replace h2 := e4 h2
  replace h3 := e4 h3
  refine Builds.ctorBG (reads_of (l := []) (vs := []) rfl) (reads_of (l := []) (vs := []) rfl) fun r5 R5 h5 e5 => ?_
  replace hn := e5 hn; replace ha := e5 ha; replace hb := e5 hb; replace h1 := e5 h1; replace h2 := e5 h2
  replace h3 := e5 h3; replace h4 := e5 h4
  refine Builds.ctorBG (reads_of (l := [n, a]) (vs := [.size nv, Reg.put ea]) (by simp [hn, ha]))
    (reads_of (l := []) (vs := []) rfl) fun r6 R6 h6 e6 => ?_
  replace hn := e6 hn; replace ha := e6 ha; replace hb := e6 hb; replace h1 := e6 h1; replace h2 := e6 h2
  replace h3 := e6 h3; replace h4 := e6 h4; replace h5 := e6 h5
  refine Builds.ctorBG (reads_of (l := [n, b]) (vs := [.size nv, Reg.put eb]) (by simp [hn, hb]))
    (reads_of (l := []) (vs := []) rfl) fun r7 R7 h7 e7 => ?_
  replace hn := e7 hn; replace h1 := e7 h1; replace h2 := e7 h2
  replace h3 := e7 h3; replace h4 := e7 h4; replace h5 := e7 h5; replace h6 := e7 h6
  refine Builds.listBG (l := [r6, r7]) (vs := [Val.ctor 0 #[.size nv, Reg.put ea] #[], Val.ctor 0 #[.size nv, Reg.put eb] #[]])
    (by simp [h6, h7]) fun r8 R8 h8 e8 => ?_
  replace hn := e8 hn; replace h1 := e8 h1; replace h2 := e8 h2
  replace h3 := e8 h3; replace h4 := e8 h4; replace h5 := e8 h5
  refine Builds.litG fun r9 R9 h9 e9 => ?_
  replace hn := e9 hn; replace h1 := e9 h1; replace h2 := e9 h2
  replace h3 := e9 h3; replace h4 := e9 h4; replace h5 := e9 h5; replace h8 := e9 h8
  refine Builds.litG fun r10 R10 h10 e10 => ?_
  replace hn := e10 hn; replace h1 := e10 h1; replace h2 := e10 h2
  replace h3 := e10 h3; replace h4 := e10 h4; replace h5 := e10 h5; replace h8 := e10 h8; replace h9 := e10 h9
  refine Builds.callKG (o := #[Reg.put r.1, Reg.put r.2])
    (by with_unfolding_all simp [abiOf, Rel.Lang.Plan.abi]) rfl
    (reads_of (vs := [Reg.put op, .bit false, Reg.put s, Reg.put t, .size nv, Val.ctor 0 #[] #[],
      Val.ctor 1 #[Val.ctor 0 #[.size nv, Reg.put ea] #[],
        Val.ctor 1 #[Val.ctor 0 #[.size nv, Reg.put eb] #[], Val.ctor 0 #[] #[]] #[]] #[], Reg.put pre, Reg.put post])
      (by simp [h1, h2, h3, h4, hn, h5, h8, h9, h10])) ?_ rfl ?_
  · simp [arg, hop, hs, ht, hgn, hgv, hl, hpre, hpost, hk, Out.out]
    rfl
  · intro a R hR eR
    obtain ⟨q, hq, hRq⟩ := holds_at hR (i := 0) (v := Reg.put r.1) rfl
    rw [nth_of (i := 0) (r := q) (by simpa using hq), pure_bind]
    refine Builds.pure fun who => ?_
    rw [← hro]
    exact reads_of (l := [q]) (vs := [Reg.put r.1]) (by simp [hRq])

end Rel.Lang.Plan
