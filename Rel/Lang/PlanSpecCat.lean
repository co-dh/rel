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

/-- `Opt.concat` is the one `kscan .first` stream of the two columns. -/
theorem Opt.concat_kscan {t : QAtomicType} {n₁ n₂ n : USize} {x : Opt t n₁} {y : Opt t n₂} {z : Opt t n}
    (h : Opt.concat n x y = .ok z) :
    ∃ f, kscan .first false t t n none [(n₁, x.enc), (n₂, y.enc)] [] [] = .ok (z.enc, f) := by
  unfold Opt.concat at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i r hr
          cases h
          exact ⟨r.2, hr⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- `Opt.shift` is `kscan .max` of the column with itself and the post step `(.add, s)`. -/
theorem Opt.shift_kscan {n : USize} {s : UInt64} {x z : Opt .i64 n} (h : Opt.shift s x = .ok z) :
    ∃ f, kscan .max false .i64 .i64 n none [(n, x.enc), (n, x.enc)] [] [(.add, s)] = .ok (z.enc, f) := by
  unfold Opt.shift at h
  split at h
  · rename_i o ho
    cases h
    unfold colMap at ho
    cases hk : kscan .max false .i64 .i64 n none [(n, x.enc), (n, x.enc)] [] [(.add, s)] with
    | error e => rw [hk] at ho; cases ho
    | ok r =>
      rw [hk] at ho
      cases ho
      exact ⟨r.2, rfl⟩
  · cases h

/-- `mapB op n a b t s pre post`: the registers hold the count `nv` and the columns `ca`, `cb`; the new register holds
    the column of `kscan op` with every row a segment (`MapCol` where `pre`, `post` are empty). -/
theorem mapB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {op : Kernel.Op} {s t : QAtomicType}
    {pre post : List (Kernel.Op × UInt64)} {n a b : Nat} {nv : USize} {ua ub : Val} {ca cb rc : Enc} {f : Option UInt64}
    (hn : rs[n]? = some (.size nv)) (ha : rs[a]? = some ua) (hga : Reg.get? ua = some ca) (hb : rs[b]? = some ub)
    (hgb : Reg.get? ub = some cb) (hop : (Reg.get? (Reg.put op) : Option Kernel.Op) = some op)
    (hs : (Reg.get? (Reg.put s) : Option QAtomicType) = some s) (ht : (Reg.get? (Reg.put t) : Option QAtomicType) = some t)
    (hpre : (Reg.get? (Reg.put pre) : Option (List (Kernel.Op × UInt64))) = some pre)
    (hpost : (Reg.get? (Reg.put post) : Option (List (Kernel.Op × UInt64))) = some post)
    (hk : kscan op false s t nv none [(nv, ca), (nv, cb)] pre post = .ok (rc, f)) :
    Builds abiOf fg fg (do let r ← mapB op n a b t s pre post; Pure.pure #[r]) rs #[Reg.put rc] := by
  unfold mapB
  simp only [bind_assoc]
  exact kscan2_builds (n₁ := n) (n₂ := n) hn hn hn ha hga hb hgb hop hs ht hpre hpost hk

/-- `catColB t n n₁ n₂ x y`: the registers hold the counts and the columns `xc`, `yc`; the new register holds the
    column of the one `kscan .first` stream `Opt.concat` runs (`Opt.concat_kscan`). -/
theorem catColB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {t : QAtomicType} {n n₁ n₂ x y : Nat}
    {nv n1 n2 : USize} {ux uy : Val} {xc yc rc : Enc} {f : Option UInt64}
    (hn : rs[n]? = some (.size nv)) (h1 : rs[n₁]? = some (.size n1)) (h2 : rs[n₂]? = some (.size n2))
    (hx : rs[x]? = some ux) (hgx : Reg.get? ux = some xc) (hy : rs[y]? = some uy) (hgy : Reg.get? uy = some yc)
    (hk : kscan .first false t t nv none [(n1, xc), (n2, yc)] [] [] = .ok (rc, f)) :
    Builds abiOf fg fg (do let r ← catColB t n n₁ n₂ x y; Pure.pure #[r]) rs #[Reg.put rc] := by
  unfold catColB
  simp only [bind_assoc]
  exact kscan2_builds (pre := []) (post := []) hn h1 h2 hx hgx hy hgy (by rop) (qtype_get_put t) (qtype_get_put t) (by rop) (by rop) hk

theorem catRows_add {a b p : USize} (h : catRows a b = .ok p) : a + b = p := by
  unfold catRows at h
  split at h
  · rename_i hlt
    cases h
    apply USize.toNat_inj.1
    simp [USize.toNat_add, Nat.toUSize, Nat.mod_eq_of_lt hlt]
  · cases h

/-- `catB n₁ n₂`, the registers holding the counts `a`, `b`: its count register holds `catRows a b`, and the cells
    `off` the column `kscan .add` answers over the positions and the constant column `kscatter` of the word `a`
    (`concatB` only hands `off` down: `ValsB.concat` has no counterpart, so the kernel answers are premises). -/
theorem catB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n₁ n₂ : Nat} {a b p : USize} {zc oc : Enc}
    {f : Option UInt64} (h1 : rs[n₁]? = some (.size a)) (h2 : rs[n₂]? = some (.size b)) (hp : catRows a b = .ok p)
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) b a.toUInt64 = .ok zc)
    (hk : kscan .add false .i64 .i64 b none [(b, .pos), (b, zc)] [] [] = .ok (oc, f)) :
    Builds abiOf fg fg (do let (n, off) ← catB n₁ n₂; Pure.pure #[n, off]) rs #[.size p, Reg.put oc] := by
  have hap := catRows_add hp
  unfold catB
  simp only [bind_assoc, pure_bind]
  refine Builds.call1G (vs := #[.size a, .size b]) (v := .size (a + b)) (by abiK) (by rop) ?_ ?_ rfl
    fun r1 R1 hr1 m1 => ?_
  · rw [List.mapM_toArray]
    simp [reg, h1, h2]
    rfl
  · simp [arg]
    rfl
  up m1 [h1 h2]
  unfold posB
  refine Builds.litG fun rp R2 hrp m2 => ?_
  up m2 [h1 h2 hr1]
  refine Builds.call1G (vs := #[.size a]) (v := .u64 a.toUInt64) (by abiK) (by rop) ?_ ?_ rfl
    fun r3 R3 hr3 m3 => ?_
  · rw [List.mapM_toArray]
    simp [reg, h1]
    rfl
  · simp [arg]
    rfl
  up m3 [h1 h2 hr1 hrp]
  refine Builds.bind1G (constB_builds h2 hr3 hz) fun z R4 hz4 m4 => ?_
  up m4 [h2 hr1 hrp]
  refine Builds.bind1G (mapB_builds (n := n₂) (a := rp) (b := z) h2 hrp (enc_get_put _) hz4 (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (pre := []) (post := []) (by rop) (by rop) hk) fun o R5 ho5 m5 => ?_
  up m5 [hr1]
  exact Builds.pure fun who => by simp [reg, hr1, ho5, ← hap]; rfl

/-- `shiftB n x s`, the registers holding the count `nv`, the column `xc` and the size `sv`: the new register holds the
    column of `Opt.shift sv.toUInt64`'s `colMap .max` (`Opt.shift_kscan`), `kscan .max` of `x` with itself and the post
    step `(.add, sv.toUInt64)`: the same call as its spec. -/
theorem shiftB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n x s : Nat} {nv sv : USize} {ux : Val}
    {xc rc : Enc} {f : Option UInt64} (hn : rs[n]? = some (.size nv)) (hx : rs[x]? = some ux)
    (hgx : Reg.get? ux = some xc) (hs : rs[s]? = some (.size sv))
    (hk : kscan .max false .i64 .i64 nv none [(nv, xc), (nv, xc)] [] [(.add, sv.toUInt64)] = .ok (rc, f)) :
    Builds abiOf fg fg (do let r ← shiftB n x s; Pure.pure #[r]) rs #[Reg.put rc] := by
  unfold shiftB
  simp only [bind_assoc]
  refine Builds.litG fun c0 R0 h0 m0 => ?_
  up m0 [hn hx hs]
  refine Builds.litG fun c1 R1 h1 m1 => ?_
  up m1 [hn hx hs h0]
  refine Builds.litG fun c2 R2 h2 m2 => ?_
  up m2 [hn hx hs h0 h1]
  refine Builds.litG fun c3 R3 h3 m3 => ?_
  up m3 [hn hx hs h0 h1 h2]
  refine Builds.ctorBG (reads_of (l := []) (vs := []) rfl) (reads_of (l := []) (vs := []) rfl) fun g R4 hg m4 => ?_
  up m4 [hn hx hs h0 h1 h2 h3]
  refine Builds.ctorBG (os := #[.size nv, ux]) (reads_of (l := [n, x]) (vs := [.size nv, ux]) (by simp [hn, hx]))
    (reads_of (l := []) (vs := []) rfl) fun y1 R5 hy1 m5 => ?_
  up m5 [hn hx hs h0 h1 h2 h3 hg]
  refine Builds.ctorBG (os := #[.size nv, ux]) (reads_of (l := [n, x]) (vs := [.size nv, ux]) (by simp [hn, hx]))
    (reads_of (l := []) (vs := []) rfl) fun y2 R6 hy2 m6 => ?_
  up m6 [hn hx hs h0 h1 h2 h3 hg hy1]
  refine Builds.listBG (l := [y1, y2]) (vs := [.ctor 0 #[.size nv, ux] #[], .ctor 0 #[.size nv, ux] #[]])
    (by simp [hy1, hy2]) fun l R7 hl m7 => ?_
  up m7 [hn hx hs h0 h1 h2 h3 hg]
  refine Builds.listBG (l := []) (vs := []) rfl fun pr R8 hpr m8 => ?_
  up m8 [hn hx hs h0 h1 h2 h3 hg hl]
  refine Builds.litG fun ca R9 hca m9 => ?_
  up m9 [hn hx hs h0 h1 h2 h3 hg hl hpr]
  refine Builds.bind1G (u64B_builds hs) fun w R10 hw m10 => ?_
  up m10 [hn hx h0 h1 h2 h3 hg hl hpr hca]
  refine Builds.ctorBG (os := #[Reg.put Kernel.Op.add, .u64 sv.toUInt64])
    (reads_of (l := [ca, w]) (vs := [Reg.put Kernel.Op.add, .u64 sv.toUInt64]) (by simp [hca, hw]))
    (reads_of (l := []) (vs := []) rfl) fun pp R11 hpp m11 => ?_
  up m11 [hn hx h0 h1 h2 h3 hg hl hpr]
  refine Builds.listBG (l := [pp]) (vs := [.ctor 0 #[Reg.put Kernel.Op.add, .u64 sv.toUInt64] #[]])
    (by simp [hpp]) fun po R12 hpo m12 => ?_
  up m12 [hn h0 h1 h2 h3 hg hl hpr]
  have hop : ∀ o : Kernel.Op, o = .max ∨ o = .add → (Reg.get? (Reg.put o) : Option Kernel.Op) = some o := by
    rintro o (rfl | rfl) <;> rop
  have hv1 : (Reg.get? (Val.ctor 0 #[.size nv, ux] #[]) : Option (USize × Enc)) = some (nv, xc) := by
    show (do pure (← Reg.get? (Val.size nv), ← Reg.get? ux)) = _; rw [hgx]; rfl
  have hlist : (Reg.get? (Val.ctor 1 #[Val.ctor 0 #[.size nv, ux] #[], Val.ctor 1 #[Val.ctor 0 #[.size nv, ux] #[],
      Val.ctor 0 #[] #[]] #[]] #[]) : Option (List (USize × Enc))) = some [(nv, xc), (nv, xc)] := by
    have h := listGet?_foldr (α := USize × Enc) [Val.ctor 0 #[.size nv, ux] #[], Val.ctor 0 #[.size nv, ux] #[]]
    simp only [List.foldr] at h; rw [h]; simp [hv1]
  have hpair : (Reg.get? (Val.ctor 0 #[Reg.put Kernel.Op.add, .u64 sv.toUInt64] #[]) : Option (Kernel.Op × UInt64)) =
      some (.add, sv.toUInt64) := by
    show (do pure (← Reg.get? (Reg.put Kernel.Op.add), ← Reg.get? (Val.u64 sv.toUInt64))) = _
    rw [hop _ (Or.inr rfl)]; rfl
  have hpost : (Reg.get? (Val.ctor 1 #[Val.ctor 0 #[Reg.put Kernel.Op.add, .u64 sv.toUInt64] #[], Val.ctor 0 #[] #[]]
      #[]) : Option (List (Kernel.Op × UInt64))) = some [(.add, sv.toUInt64)] := by
    have h := listGet?_foldr (α := Kernel.Op × UInt64) [Val.ctor 0 #[Reg.put Kernel.Op.add, .u64 sv.toUInt64] #[]]
    simp only [List.foldr] at h; rw [h]; simp [hpair]
  have hpre : (Reg.get? (Val.ctor 0 #[] #[]) : Option (List (Kernel.Op × UInt64))) = some [] := by rop
  have hgv : (Reg.get? (Val.ctor 0 #[] #[]) : Option (Option Enc)) = some none := rfl
  refine Builds.callKG (vs := #[Reg.put Kernel.Op.max, .bit false, Reg.put QAtomicType.i64, Reg.put QAtomicType.i64,
      .size nv, .ctor 0 #[] #[], .ctor 1 #[.ctor 0 #[.size nv, ux] #[], .ctor 1 #[.ctor 0 #[.size nv, ux] #[],
        .ctor 0 #[] #[]] #[]] #[], .ctor 0 #[] #[], .ctor 1 #[.ctor 0 #[Reg.put Kernel.Op.add, .u64 sv.toUInt64] #[],
        .ctor 0 #[] #[]] #[]])
    (o := #[Reg.put rc, Reg.put f]) (by abiK) (by rop) ?_ ?_ rfl fun a' R hR m => ?_
  · refine reads_of (l := [c0, c1, c2, c3, n, g, l, pr, po]) (vs := _) ?_
    simp [h0, h1, h2, h3, hn, hg, hl, hpr, hpo]
  · simp [arg, hop _ (Or.inl rfl), qtype_get_put, hpre, hpost, hlist, hgv, hk, Out.out]
    rfl
  · obtain ⟨p, hp0, hpR⟩ := holds_at hR (i := 0) (v := Reg.put rc) rfl
    rw [nth_of (by simpa using hp0), pure_bind]
    exact Builds.pure fun who => by simp [reg, hpR]; rfl

/-! ### `Grows`, `Typed` -/

-- `PlanSpec`'s `grows`, `typed` and `ge` are `local` there, so this file states the leaves its five builders use
local macro "growsCat" : tactic => `(tactic| repeat' first
  | exact Grows.pure _ | (with_reducible refine Grows.bind ?_ (fun _ => ?_)) | exact Grows.lit _
  | exact Grows.call1 _ _ | exact Grows.callK _ _ | exact Grows.nth _ _ _ | exact Grows.ctorB _ _ _
  | exact Grows.srcB _ _ | exact Grows.listB _ | exact Grows.posB | exact Grows.constB _ _
  | exact Grows.mapB _ _ _ _ _ _ _ _ | dsimp only)

theorem Grows.scatterB (op : Kernel.Op) (rows dst x cells : Nat) (fill : UInt64) :
    Grows (Plan.scatterB op rows dst x cells fill) := by
  unfold Plan.scatterB; growsCat

theorem Grows.u64B (s : Nat) : Grows (Plan.u64B s) := Grows.call1 _ _

theorem Grows.catB (n₁ n₂ : Nat) : Grows (Plan.catB n₁ n₂) := by
  unfold Plan.catB; growsCat

theorem Grows.catColB (t : QAtomicType) (n n₁ n₂ x y : Nat) : Grows (Plan.catColB t n n₁ n₂ x y) := by
  unfold Plan.catColB; growsCat

theorem Grows.shiftB (n x s : Nat) : Grows (Plan.shiftB n x s) := by
  unfold Plan.shiftB; growsCat

/-- `kscatter` declares all six arguments, so a `scatterB` is typed at every `m`, its registers captured or not. -/
theorem Typed.scatterB {m : Nat} {op : Kernel.Op} {rows dst x cells : Nat} {fill : UInt64} :
    Typed m (fun r => m ≤ r) (Plan.scatterB op rows dst x cells fill) := by
  unfold Plan.scatterB
  refine (Typed.lit _).bind fun a ha => (Typed.lit _).bind fun b hb => Typed.call1Of fun fs a' ha' _ => ?_
  obtain ⟨j, hj, hjl⟩ := idxOf?_of_mem (l := [a, rows, dst, x, cells, b]) (by simpa using ha')
  simp only [List.length_cons, List.length_nil] at hjl
  simp only [useTy, hj, Option.bind_some]
  rcases j with _ | _ | _ | _ | _ | _ | j <;> first | exact absurd hjl (by omega) | exact ⟨_, by with_unfolding_all rfl⟩

/-- `USize.toUInt64` declares its argument, so a `u64B` is typed at every `m`. -/
theorem Typed.u64B {m : Nat} {s : Nat} : Typed m (fun r => m ≤ r) (Plan.u64B s) := by
  unfold Plan.u64B
  refine Typed.call1Of fun fs a' ha' _ => ?_
  obtain ⟨j, hj, hjl⟩ := idxOf?_of_mem (l := [s]) (by simpa using ha')
  simp only [List.length_cons, List.length_nil] at hjl
  simp only [useTy, hj, Option.bind_some]
  rcases j with _ | j <;> first | exact absurd hjl (by omega) | exact ⟨_, by with_unfolding_all rfl⟩

/-- The `kscan` call of two sources (`mapB`, `catColB`, `shiftB`): every register it reads is at least `m`, so is the
    answer's. -/
theorem Typed.mapB {m : Nat} {op : Kernel.Op} {n a b : Nat} {t s : QAtomicType} {pre post : List (Kernel.Op × UInt64)}
    (hn : m ≤ n) (ha : m ≤ a) (hb : m ≤ b) : Typed m (fun r => m ≤ r) (Plan.mapB op n a b t s pre post) := by
  unfold Plan.mapB
  refine (Typed.lit _).bind fun c0 h0 => (Typed.lit _).bind fun c1 h1 => (Typed.lit _).bind fun c2 h2 =>
    (Typed.lit _).bind fun c3 h3 => (Typed.ctorB (by simp) (by simp) 0).bind fun g hg =>
    (Typed.srcB hn ha).bind fun x hx => (Typed.srcB hn hb).bind fun y hy =>
    (Typed.listB (rs := [x, y]) (by intro a ha; simp at ha; omega)).bind fun l hl =>
    (Typed.lit _).bind fun c4 h4 => (Typed.lit _).bind fun c5 h5 =>
    (Typed.callK (by intro a ha; simp at ha; omega)).bind fun o ho => Typed.nth ho 0 "kscan"

theorem Typed.catColB {m : Nat} {t : QAtomicType} {n n₁ n₂ x y : Nat} (hn : m ≤ n) (h1 : m ≤ n₁) (h2 : m ≤ n₂)
    (hx : m ≤ x) (hy : m ≤ y) : Typed m (fun r => m ≤ r) (Plan.catColB t n n₁ n₂ x y) := by
  unfold Plan.catColB
  refine (Typed.lit _).bind fun c0 h0 => (Typed.lit _).bind fun c1 h1' => (Typed.lit _).bind fun c2 h2' =>
    (Typed.lit _).bind fun c3 h3 => (Typed.ctorB (by simp) (by simp) 0).bind fun g hg =>
    (Typed.srcB h1 hx).bind fun x' hx' => (Typed.srcB h2 hy).bind fun y' hy' =>
    (Typed.listB (rs := [x', y']) (by intro a ha; simp at ha; omega)).bind fun l hl =>
    (Typed.lit _).bind fun c4 h4 => (Typed.lit _).bind fun c5 h5 =>
    (Typed.callK (by intro a ha; simp at ha; omega)).bind fun o ho => Typed.nth ho 0 "kscan"

theorem Typed.shiftB {m : Nat} {n x s : Nat} (hn : m ≤ n) (hx : m ≤ x) : Typed m (fun r => m ≤ r) (Plan.shiftB n x s) := by
  unfold Plan.shiftB
  refine (Typed.lit _).bind fun c0 h0 => (Typed.lit _).bind fun c1 h1 => (Typed.lit _).bind fun c2 h2 =>
    (Typed.lit _).bind fun c3 h3 => (Typed.ctorB (by simp) (by simp) 0).bind fun g hg =>
    (Typed.srcB hn hx).bind fun y1 hy1 => (Typed.srcB hn hx).bind fun y2 hy2 =>
    (Typed.listB (rs := [y1, y2]) (by intro a ha; simp at ha; omega)).bind fun l hl =>
    (Typed.listB (rs := []) (fun _ h => nomatch h)).bind fun pr hpr => (Typed.lit _).bind fun ca hca =>
    Typed.u64B.bind fun w hw => (Typed.ctorB (objs := #[ca, w]) (by intro a ha; simp at ha; omega) (by simp) 0).bind fun pp hpp =>
    (Typed.listB (rs := [pp]) (by intro a ha; simp at ha; omega)).bind fun po hpo =>
    (Typed.callK (by intro a ha; simp at ha; omega)).bind fun o ho => Typed.nth ho 0 "kscan"

theorem Typed.catB {m : Nat} {n₁ n₂ : Nat} (h1 : m ≤ n₁) (h2 : m ≤ n₂) :
    Typed m (fun r : Nat × Nat => m ≤ r.1 ∧ m ≤ r.2) (Plan.catB n₁ n₂) := by
  unfold Plan.catB
  exact (Typed.call1 (by simp; omega)).bind fun a ha => Typed.posB.bind fun p hp =>
    (Typed.call1 (by simp; omega)).bind fun c hc => (Typed.constB h2 hc).bind fun z hz =>
    (Typed.mapB h2 hp hz).bind fun o ho => Typed.pure ⟨ha, ho⟩

end Rel.Lang.Plan
