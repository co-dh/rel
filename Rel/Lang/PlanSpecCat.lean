module

public import Rel.Lang.PlanSpecGather

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # The kernel wrappers `scatterB`, `catB`, `u64B`, `catColB`, `shiftB` build what their specs answer

Each is one kernel call (`catB` three, `shiftB` one over a post chain built at run time), so each lemma has the shape of
`gatherB_builds`: the argument registers hold the kernel's arguments, and the new register holds what the kernel
answers. `catColB` is `Opt.concat`'s `kscan` and `shiftB` is `Opt.shift`'s `colMap`, the same call as their spec.
`catB` is not `catRows` and `shiftCol`: its count is `USize.add` (equal to `catRows` where that succeeds) and its cells
`off` are `kscan .add` of the positions and a constant column, which no spec states (`concatB` hands `off` down and
`ValsB.concat` has no counterpart), so its lemma takes the kernel answers as premises, as `arithB_builds` does. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- `scatterB op rows dst x cells fill`: the registers hold the counts `rv`, `cv`, the `Enc`s `dv`, `xv`; the new
    register holds `kscatter op rv dv xv cv fill`. -/
theorem scatterB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {op : Kernel.Op} {rows dst x cells : Nat}
    {fill : UInt64} {rv cv : USize} {dv xv ov : Enc}
    (hr : rs[rows]? = some (.size rv)) (hd : rs[dst]? = some (Reg.put dv)) (hx : rs[x]? = some (Reg.put xv))
    (hc : rs[cells]? = some (.size cv)) (hop : (Reg.get? (Reg.put op) : Option Kernel.Op) = some op)
    (hk : kscatter op rv dv xv cv fill = .ok ov) :
    Builds abiOf fg fg (do let r ← scatterB op rows dst x cells fill; Pure.pure #[r]) rs #[Reg.put ov] := by
  unfold scatterB
  simp only [bind_assoc]
  refine Builds.litG fun c0 R0 h0 m0 => ?_
  up m0 [hr hd hx hc]
  refine Builds.litG fun c1 R1 h1 m1 => ?_
  up m1 [h0 hr hd hx hc]
  refine Builds.call1G (vs := #[Reg.put op, .size rv, Reg.put dv, Reg.put xv, .size cv, .u64 fill]) (v := Reg.put ov)
    (by abiK) (by rop) ?_ ?_ rfl fun r R hR m => Builds.pure fun who => ?_
  · rw [List.mapM_toArray]
    simp [reg, h0, h1, hr, hd, hx, hc]
    rfl
  · have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
    simp [arg, hop, hsz, enc_get_put, hk, Out.out]
    rfl
  · simp [reg, hR]
    rfl

/-- `u64B s`, the register `s` holding the size `sv`: the new register holds the word `sv.toUInt64`. -/
theorem u64B_builds {fg : Array Fun × Array Fun} {rs : Array Val} {s : Nat} {sv : USize}
    (hs : rs[s]? = some (.size sv)) :
    Builds abiOf fg fg (do let r ← u64B s; Pure.pure #[r]) rs #[.u64 sv.toUInt64] := by
  unfold u64B
  refine Builds.call1G (vs := #[.size sv]) (v := .u64 sv.toUInt64) (by abiK) (by rop) ?_ ?_ rfl
    fun r R hR m => Builds.pure fun who => ?_
  · rw [List.mapM_toArray]
    simp [reg, hs]
    rfl
  · simp [arg]
    rfl
  · simp [reg, hR]
    rfl

/-- The `kscan` of the sources `(n₁, a)`, `(n₂, b)` into `n` rows (`mapB`, `catColB`): the registers hold the counts and
    the two columns; the new register holds the column `kscan` answers. Neither builder has the scan's segment column
    or an operand chain beyond the registers `pre`, `post` (`Reg.put` of the lists). -/
theorem kscan2_builds {fg : Array Fun × Array Fun} {rs : Array Val} {op : Kernel.Op} {s t : QAtomicType}
    {pre post : List (Kernel.Op × UInt64)} {n n₁ n₂ a b : Nat} {nv n1 n2 : USize} {ua ub : Val} {ca cb rc : Enc}
    {f : Option UInt64} (hn : rs[n]? = some (.size nv)) (h1 : rs[n₁]? = some (.size n1))
    (h2 : rs[n₂]? = some (.size n2)) (ha : rs[a]? = some ua) (hga : Reg.get? ua = some ca) (hb : rs[b]? = some ub)
    (hgb : Reg.get? ub = some cb) (hop : (Reg.get? (Reg.put op) : Option Kernel.Op) = some op)
    (hs : (Reg.get? (Reg.put s) : Option QAtomicType) = some s) (ht : (Reg.get? (Reg.put t) : Option QAtomicType) = some t)
    (hpre : (Reg.get? (Reg.put pre) : Option (List (Kernel.Op × UInt64))) = some pre)
    (hpost : (Reg.get? (Reg.put post) : Option (List (Kernel.Op × UInt64))) = some post)
    (hk : kscan op false s t nv none [(n1, ca), (n2, cb)] pre post = .ok (rc, f)) :
    Builds abiOf fg fg (do
      let r ← nth (← callK (kernel% Rel.Kernel.kscan) #[← lit (Reg.put op), ← lit (.bit false), ← lit (Reg.put s),
        ← lit (Reg.put t), n, ← ctorB 0 #[] #[], ← listB [← srcB n₁ a, ← srcB n₂ b], ← lit (Reg.put pre),
        ← lit (Reg.put post)]) 0 "kscan"
      Pure.pure #[r]) rs #[Reg.put rc] := by
  refine Builds.litG fun c0 R0 h0 m0 => ?_
  up m0 [hn h1 h2 ha hb]
  refine Builds.litG fun c1 R1 h1' m1 => ?_
  up m1 [hn h1 h2 ha hb h0]
  refine Builds.litG fun c2 R2 h2' m2 => ?_
  up m2 [hn h1 h2 ha hb h0 h1']
  refine Builds.litG fun c3 R3 h3 m3 => ?_
  up m3 [hn h1 h2 ha hb h0 h1' h2']
  refine Builds.ctorBG (reads_of (l := []) (vs := []) rfl) (reads_of (l := []) (vs := []) rfl) fun g R4 hg m4 => ?_
  up m4 [hn h1 h2 ha hb h0 h1' h2' h3]
  refine Builds.ctorBG (os := #[.size n1, ua]) (reads_of (l := [n₁, a]) (vs := [.size n1, ua]) (by simp [h1, ha]))
    (reads_of (l := []) (vs := []) rfl) fun x R5 hx m5 => ?_
  up m5 [hn h2 hb h0 h1' h2' h3 hg]
  refine Builds.ctorBG (os := #[.size n2, ub]) (reads_of (l := [n₂, b]) (vs := [.size n2, ub]) (by simp [h2, hb]))
    (reads_of (l := []) (vs := []) rfl) fun y R6 hy m6 => ?_
  up m6 [hn h0 h1' h2' h3 hg hx]
  refine Builds.listBG (l := [x, y]) (vs := [.ctor 0 #[.size n1, ua] #[], .ctor 0 #[.size n2, ub] #[]])
    (by simp [hx, hy]) fun l R7 hl m7 => ?_
  up m7 [hn h0 h1' h2' h3 hg]
  refine Builds.litG fun c4 R8 h4 m8 => ?_
  up m8 [hn h0 h1' h2' h3 hg hl]
  refine Builds.litG fun c5 R9 h5 m9 => ?_
  up m9 [hn h0 h1' h2' h3 hg hl h4]
  have hv1 : (Reg.get? (Val.ctor 0 #[.size n1, ua] #[]) : Option (USize × Enc)) = some (n1, ca) := by
    show (do pure (← Reg.get? (Val.size n1), ← Reg.get? ua)) = _; rw [hga]; rfl
  have hv2 : (Reg.get? (Val.ctor 0 #[.size n2, ub] #[]) : Option (USize × Enc)) = some (n2, cb) := by
    show (do pure (← Reg.get? (Val.size n2), ← Reg.get? ub)) = _; rw [hgb]; rfl
  have hlist : (Reg.get? (Val.ctor 1 #[Val.ctor 0 #[.size n1, ua] #[], Val.ctor 1 #[Val.ctor 0 #[.size n2, ub] #[],
      Val.ctor 0 #[] #[]] #[]] #[]) : Option (List (USize × Enc))) = some [(n1, ca), (n2, cb)] := by
    have h := listGet?_foldr (α := USize × Enc) [Val.ctor 0 #[.size n1, ua] #[], Val.ctor 0 #[.size n2, ub] #[]]
    simp only [List.foldr] at h; rw [h]; simp [hv1, hv2]
  have hgv : (Reg.get? (Val.ctor 0 #[] #[]) : Option (Option Enc)) = some none := rfl
  refine Builds.callKG (vs := #[Reg.put op, .bit false, Reg.put s, Reg.put t, .size nv, .ctor 0 #[] #[],
      [Val.ctor 0 #[.size n1, ua] #[], .ctor 0 #[.size n2, ub] #[]].foldr (fun v c => Val.ctor 1 #[v, c] #[])
        (.ctor 0 #[] #[]), Reg.put pre, Reg.put post])
    (o := #[Reg.put rc, Reg.put f]) (by abiK) (by rop) ?_ ?_ rfl fun a' R hR m => ?_
  · refine reads_of (l := [c0, c1, c2, c3, n, g, l, c4, c5]) (vs := _) ?_
    simp [h0, h1', h2', h3, hn, hg, hl, h4, h5]
  · simp [arg, hop, hs, ht, hpre, hpost, hlist, hgv, hk, Out.out]
    rfl
  · obtain ⟨p, hp0, hpR⟩ := holds_at hR (i := 0) (v := Reg.put rc) rfl
    rw [nth_of (by simpa using hp0), pure_bind]
    exact Builds.pure fun who => by simp [reg, hpR]; rfl

end Rel.Lang.Plan
